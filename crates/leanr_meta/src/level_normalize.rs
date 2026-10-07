//! Meta's `Level.normalize`, ported from `Lean/Level.lean:270-406`
//! (toolchain leanprover/lean4:v4.33.0-rc1).
//!
//! This is NOT the kernel's `normalize` (`level.cpp:439-501`, ported as
//! [`Level::normalize`] in `leanr_kernel`). `Level.normalize` is plain
//! Lean with no `@[extern]`, and every Meta/Elab caller
//! (`isLevelDefEqAux` LevelDefEq.lean:154/156, `normalizeLevel`
//! Basic.lean:2110, `inferForallType` InferType.lean:185) runs it. The
//! two algorithms disagree observably:
//!
//! - the rebuild is LEFT-nested through `accMax` with a raw
//!   `mkLevelMax` (the kernel right-nests through its simplifying
//!   `mk_max`), so `max (max 1 ?a) ?b` is already normal here while the
//!   kernel turns it into `max 1 (max ?a ?b)`;
//! - the sort key is `ctorToNat` (`zero < param < mvar < succ < max <
//!   imax`; the kernel puts `max`/`imax` before `param`);
//! - names compare by `Name.cmp` (Name.lean:67-80): a shorter name is
//!   smaller, a `num` component is smaller than a `str` component, and
//!   only names of equal shape compare their components root-first.
//!
//! The kernel's normalize stays as is: it is the TCB's own `is_equivalent`.

use std::cmp::Ordering;
use std::sync::Arc;

use leanr_kernel::{KernelError, Level, Name, RecGuard};

/// oracle: `Level.normalize` (Level.lean:382-406).
pub(crate) fn normalize(l: &Arc<Level>, g: &mut RecGuard) -> Result<Arc<Level>, KernelError> {
    // `isAlreadyNormalizedCheap` (:304-309): `succ^k` of a leaf.
    let (u, k) = Level::to_offset(l);
    match u.as_ref() {
        Level::Zero | Level::Param(_) | Level::MVar(_) => Ok(Arc::clone(l)),
        Level::Max(l1, l2) => {
            let (l1, l2) = (Arc::clone(l1), Arc::clone(l2));
            g.enter(|g| {
                let mut lvls = Vec::new();
                get_max_args(&l1, false, &mut lvls, g)?;
                get_max_args(&l2, false, &mut lvls, g)?;
                qsort(&mut lvls, g)?;
                let first_non_explicit = skip_explicit(&lvls);
                // `firstNonExplicit - 1` is Nat subtraction: 0 stays 0.
                let i = if is_explicit_subsumed(&lvls, first_non_explicit) {
                    first_non_explicit
                } else {
                    first_non_explicit.saturating_sub(1)
                };
                let (prev, prev_k) = Level::to_offset(&lvls[i]);
                mk_max_aux(&lvls, k, i + 1, Arc::clone(prev), prev_k, g)
            })
        }
        Level::IMax(l1, l2) => {
            let (l1, l2) = (Arc::clone(l1), Arc::clone(l2));
            g.enter(|g| {
                if Level::is_never_zero(&l2, g)? {
                    let m = Arc::new(Level::Max(l1, l2));
                    Ok(add_offset(normalize(&m, g)?, k))
                } else {
                    let l1 = normalize(&l1, g)?;
                    let l2 = normalize(&l2, g)?;
                    Ok(add_offset(mk_imax_aux(l1, l2, g)?, k))
                }
            })
        }
        Level::Succ(_) => unreachable!("to_offset strips all Succ nodes"),
    }
}

/// oracle: `addOffset` (Level.lean:227-232).
fn add_offset(mut u: Arc<Level>, n: u64) -> Arc<Level> {
    for _ in 0..n {
        u = Level::mk_succ(u);
    }
    u
}

/// oracle: `ctorToNat` (Level.lean:267-273).
fn ctor_to_nat(l: &Level) -> u8 {
    match l {
        Level::Zero => 0,
        Level::Param(_) => 1,
        Level::MVar(_) => 2,
        Level::Succ(_) => 3,
        Level::Max(..) => 4,
        Level::IMax(..) => 5,
    }
}

/// oracle: `Name.cmp` (Name.lean:67-80), iteratively. Walking both names
/// leaf-to-root in lockstep, the first `anonymous` or `num`/`str`
/// mismatch decides; only when both reach `anonymous` together are the
/// components compared, root first.
fn name_cmp(a: &Name, b: &Name) -> Ordering {
    let mut pairs = Vec::new();
    let (mut x, mut y) = (a, b);
    loop {
        match (x, y) {
            (Name::Anonymous, Name::Anonymous) => break,
            (Name::Anonymous, _) => return Ordering::Less,
            (_, Name::Anonymous) => return Ordering::Greater,
            (Name::Num { .. }, Name::Str { .. }) => return Ordering::Less,
            (Name::Str { .. }, Name::Num { .. }) => return Ordering::Greater,
            (Name::Num { parent: px, .. }, Name::Num { parent: py, .. })
            | (Name::Str { parent: px, .. }, Name::Str { parent: py, .. }) => {
                pairs.push((x, y));
                x = px;
                y = py;
            }
        }
    }
    for (x, y) in pairs.into_iter().rev() {
        let ord = match (x, y) {
            (Name::Num { part: p, .. }, Name::Num { part: q, .. }) => p.0.cmp(&q.0),
            (Name::Str { part: p, .. }, Name::Str { part: q, .. }) => p.as_str().cmp(q.as_str()),
            _ => unreachable!("pairs hold same-kind components only"),
        };
        if ord != Ordering::Equal {
            return ord;
        }
    }
    Ordering::Equal
}

/// oracle: `normLt`/`normLtAux` (Level.lean:275-302). The two `succ`
/// arms peel both offsets, which is `to_offset` on each side.
fn norm_lt(a: &Arc<Level>, b: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
    let (l1, k1) = Level::to_offset(a);
    let (l2, k2) = Level::to_offset(b);
    match (l1.as_ref(), l2.as_ref()) {
        (Level::Max(a1, a2), Level::Max(b1, b2)) | (Level::IMax(a1, a2), Level::IMax(b1, b2)) => {
            if Level::structural_eq(l1, l2, g)? {
                return Ok(k1 < k2);
            }
            let (a1, a2, b1, b2) = (
                Arc::clone(a1),
                Arc::clone(a2),
                Arc::clone(b1),
                Arc::clone(b2),
            );
            g.enter(|g| {
                if !Level::structural_eq(&a1, &b1, g)? {
                    norm_lt(&a1, &b1, g)
                } else {
                    norm_lt(&a2, &b2, g)
                }
            })
        }
        (Level::Param(n1), Level::Param(n2)) | (Level::MVar(n1), Level::MVar(n2)) => {
            if n1 == n2 {
                Ok(k1 < k2)
            } else {
                Ok(name_cmp(n1, n2) == Ordering::Less)
            }
        }
        _ => {
            if Level::structural_eq(l1, l2, g)? {
                Ok(k1 < k2)
            } else {
                Ok(ctor_to_nat(l1) < ctor_to_nat(l2))
            }
        }
    }
}

/// oracle: `getMaxArgsAux` (Level.lean:319-322): flatten `max` nodes,
/// normalizing each non-`max` leaf once and flattening its result too.
fn get_max_args(
    l: &Arc<Level>,
    already_normalized: bool,
    lvls: &mut Vec<Arc<Level>>,
    g: &mut RecGuard,
) -> Result<(), KernelError> {
    match l.as_ref() {
        Level::Max(l1, l2) => {
            let (l1, l2) = (Arc::clone(l1), Arc::clone(l2));
            g.enter(|g| {
                get_max_args(&l1, already_normalized, lvls, g)?;
                get_max_args(&l2, already_normalized, lvls, g)
            })
        }
        _ if !already_normalized => {
            let n = normalize(l, g)?;
            g.enter(|g| get_max_args(&n, true, lvls, g))
        }
        _ => {
            lvls.push(Arc::clone(l));
            Ok(())
        }
    }
}

/// oracle: `Array.qsort` (Init/Data/Array/QSort/Basic.lean), ported
/// exactly rather than via `sort_by`: the result order of equal-keyed
/// elements is the algorithm's, and `normLt` is only a `Bool` predicate.
fn qsort(v: &mut [Arc<Level>], g: &mut RecGuard) -> Result<(), KernelError> {
    if v.is_empty() {
        return Ok(());
    }
    qsort_range(v, 0, v.len() - 1, g)
}

fn qsort_range(
    v: &mut [Arc<Level>],
    lo: usize,
    hi: usize,
    g: &mut RecGuard,
) -> Result<(), KernelError> {
    if lo >= hi {
        return Ok(());
    }
    let mid = qpartition(v, lo, hi, g)?;
    if mid >= hi {
        return Ok(());
    }
    g.enter(|g| {
        qsort_range(v, lo, mid, g)?;
        qsort_range(v, mid + 1, hi, g)
    })
}

/// oracle: `Array.qpartition` (QSort/Basic.lean): median-of-three into
/// `hi`, then a Lomuto pass.
fn qpartition(
    v: &mut [Arc<Level>],
    lo: usize,
    hi: usize,
    g: &mut RecGuard,
) -> Result<usize, KernelError> {
    let mid = (lo + hi) / 2;
    if norm_lt(&v[mid], &v[lo], g)? {
        v.swap(lo, mid);
    }
    if norm_lt(&v[hi], &v[lo], g)? {
        v.swap(lo, hi);
    }
    if norm_lt(&v[mid], &v[hi], g)? {
        v.swap(mid, hi);
    }
    let pivot = Arc::clone(&v[hi]);
    let mut i = lo;
    for k in lo..hi {
        if norm_lt(&v[k], &pivot, g)? {
            v.swap(i, k);
            i += 1;
        }
    }
    v.swap(i, hi);
    Ok(i)
}

/// oracle: `skipExplicit` (Level.lean:353-357).
fn skip_explicit(lvls: &[Arc<Level>]) -> usize {
    lvls.iter()
        .position(|l| !Level::to_offset(l).0.is_zero())
        .unwrap_or(lvls.len())
}

/// oracle: `isExplicitSubsumed`/`isExplicitSubsumedAux` (Level.lean:367-380).
fn is_explicit_subsumed(lvls: &[Arc<Level>], first_non_explicit: usize) -> bool {
    if first_non_explicit == 0 {
        return false;
    }
    let max = Level::to_offset(&lvls[first_non_explicit - 1]).1;
    lvls[first_non_explicit..]
        .iter()
        .any(|l| Level::to_offset(l).1 >= max)
}

/// oracle: `accMax` (Level.lean:324-326) — a raw `mkLevelMax`, no
/// simplification.
fn acc_max(result: Arc<Level>, prev: Arc<Level>, offset: u64) -> Arc<Level> {
    if result.is_zero() {
        add_offset(prev, offset)
    } else {
        Arc::new(Level::Max(result, add_offset(prev, offset)))
    }
}

/// oracle: `mkMaxAux` (Level.lean:337-346), as a loop: an argument with
/// the same base as its predecessor replaces it (the array is sorted, so
/// the later one has the larger offset).
fn mk_max_aux(
    lvls: &[Arc<Level>],
    extra_k: u64,
    start: usize,
    mut prev: Arc<Level>,
    mut prev_k: u64,
    g: &mut RecGuard,
) -> Result<Arc<Level>, KernelError> {
    let mut result = Arc::new(Level::Zero);
    for lvl in &lvls[start..] {
        let (curr, curr_k) = Level::to_offset(lvl);
        if !Level::structural_eq(curr, &prev, g)? {
            result = acc_max(result, prev, extra_k.saturating_add(prev_k));
        }
        prev = Arc::clone(curr);
        prev_k = curr_k;
    }
    Ok(acc_max(result, prev, extra_k.saturating_add(prev_k)))
}

/// oracle: `mkIMaxAux` (Level.lean:312-316).
fn mk_imax_aux(
    u1: Arc<Level>,
    u2: Arc<Level>,
    g: &mut RecGuard,
) -> Result<Arc<Level>, KernelError> {
    if u2.is_zero() {
        return Ok(u2);
    }
    if u1.is_zero() {
        return Ok(u2);
    }
    if let Level::Succ(inner) = u1.as_ref() {
        if inner.is_zero() {
            return Ok(u2);
        }
    }
    if Level::structural_eq(&u1, &u2, g)? {
        return Ok(u1);
    }
    Ok(Arc::new(Level::IMax(u1, u2)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zero() -> Arc<Level> {
        Arc::new(Level::Zero)
    }
    fn succ(l: Arc<Level>) -> Arc<Level> {
        Level::mk_succ(l)
    }
    fn one() -> Arc<Level> {
        succ(zero())
    }
    fn name(parts: &[&str]) -> Arc<Name> {
        parts.iter().fold(Arc::new(Name::Anonymous), |parent, p| {
            Arc::new(Name::Str {
                parent,
                part: (*p).to_string(),
            })
        })
    }
    fn param(n: &str) -> Arc<Level> {
        Arc::new(Level::Param(name(&[n])))
    }
    fn mvar(n: u64) -> Arc<Level> {
        Arc::new(Level::MVar(Arc::new(Name::Num {
            parent: name(&["_uniq"]),
            part: leanr_kernel::Nat::from(n),
        })))
    }
    fn max(a: Arc<Level>, b: Arc<Level>) -> Arc<Level> {
        Arc::new(Level::Max(a, b))
    }
    fn imax(a: Arc<Level>, b: Arc<Level>) -> Arc<Level> {
        Arc::new(Level::IMax(a, b))
    }
    fn norm(l: &Arc<Level>) -> Arc<Level> {
        normalize(l, &mut RecGuard::new()).expect("normalize")
    }
    fn assert_level(got: &Arc<Level>, want: &Arc<Level>) {
        assert!(
            Level::structural_eq(got, want, &mut RecGuard::new()).unwrap(),
            "got {}, want {}",
            show(got),
            show(want)
        );
    }
    fn show(l: &Level) -> String {
        match l {
            Level::Zero => "0".into(),
            Level::Succ(a) => format!("succ {}", show(a)),
            Level::Max(a, b) => format!("max ({}) ({})", show(a), show(b)),
            Level::IMax(a, b) => format!("imax ({}) ({})", show(a), show(b)),
            Level::Param(n) | Level::MVar(n) => format!("{n:?}"),
        }
    }

    /// The `lvl/eqMk` shape: already normal under `accMax`'s left
    /// nesting; the kernel's normalize right-nests it.
    #[test]
    fn left_nested_max_is_already_normal() {
        let l = max(max(one(), mvar(6)), mvar(7));
        assert_level(&norm(&l), &l);
    }

    /// `lvl/nest3`: three params come back left-nested.
    #[test]
    fn rebuild_is_left_nested() {
        let l = max(
            max(one(), param("u")),
            max(max(one(), param("v")), param("w")),
        );
        let want = max(max(max(one(), param("u")), param("v")), param("w"));
        assert_level(&norm(&l), &want);
    }

    /// `lvl/imaxOrder`: `ctorToNat` puts `param` before `imax`.
    #[test]
    fn param_sorts_before_imax() {
        let l = max(max(one(), imax(param("u"), param("v"))), param("u"));
        let want = max(max(one(), param("u")), imax(param("u"), param("v")));
        assert_level(&norm(&l), &want);
    }

    /// `ctorToNat` puts `param` before `mvar` and `mvar` before `max`.
    #[test]
    fn param_sorts_before_mvar() {
        let l = max(mvar(1), param("u"));
        assert_level(&norm(&l), &max(param("u"), mvar(1)));
    }

    /// `Name.cmp`: a shorter name is smaller whatever its components,
    /// so `b < a.c` (component-wise lexicographic order says `a.c < b`).
    #[test]
    fn shorter_name_sorts_first() {
        let ac = Arc::new(Level::Param(name(&["a", "c"])));
        let l = max(ac.clone(), param("b"));
        assert_level(&norm(&l), &max(param("b"), ac));
        assert_eq!(name_cmp(&name(&["b"]), &name(&["a", "c"])), Ordering::Less);
        assert_eq!(
            name_cmp(&name(&["a", "b"]), &name(&["a", "c"])),
            Ordering::Less
        );
        assert_eq!(
            name_cmp(&name(&["a", "b"]), &name(&["a", "b"])),
            Ordering::Equal
        );
    }

    /// `Name.cmp` decides a `num`/`str` mismatch before comparing the
    /// prefix: `b.1 < a.x` although `b > a`.
    #[test]
    fn num_component_sorts_before_str_first() {
        let b1 = Arc::new(Name::Num {
            parent: name(&["b"]),
            part: leanr_kernel::Nat::from(1),
        });
        assert_eq!(name_cmp(&b1, &name(&["a", "x"])), Ordering::Less);
    }

    /// Explicit levels: the largest survives, and is dropped when some
    /// other argument's offset reaches it (`isExplicitSubsumed`).
    #[test]
    fn explicit_levels_and_subsumption() {
        assert_level(&norm(&max(one(), succ(param("u")))), &succ(param("u")));
        let two = succ(one());
        assert_level(
            &norm(&max(succ(param("u")), two.clone())),
            &max(two.clone(), succ(param("u"))),
        );
        assert_level(&norm(&max(one(), two.clone())), &two);
        assert_level(&norm(&max(zero(), param("u"))), &param("u"));
        assert_level(&norm(&max(zero(), zero())), &zero());
    }

    /// Duplicates keep the larger offset, and an outer offset is pushed
    /// inside every argument.
    #[test]
    fn duplicates_and_outer_offset() {
        let l = max(param("u"), succ(param("u")));
        assert_level(&norm(&l), &succ(param("u")));
        let l = succ(max(param("u"), param("v")));
        assert_level(&norm(&l), &max(succ(param("u")), succ(param("v"))));
    }

    /// `imax` arms: a never-zero rhs becomes `max`; otherwise `mkIMaxAux`.
    #[test]
    fn imax_cases() {
        assert_level(
            &norm(&imax(param("v"), succ(param("u")))),
            &max(succ(param("u")), param("v")),
        );
        assert_level(&norm(&imax(param("u"), zero())), &zero());
        assert_level(&norm(&imax(zero(), param("u"))), &param("u"));
        assert_level(&norm(&imax(one(), param("u"))), &param("u"));
        assert_level(&norm(&imax(param("u"), param("u"))), &param("u"));
        let l = imax(param("u"), param("v"));
        assert_level(&norm(&l), &l);
    }

    /// A sort of many arguments goes through the ported `qsort`'s
    /// recursion; the result is ordered and deduplicated.
    #[test]
    fn many_arguments_sort() {
        let names = ["e", "b", "d", "a", "c", "b", "a"];
        let l = names
            .iter()
            .map(|n| param(n))
            .reduce(|acc, p| max(p, acc))
            .unwrap();
        let want = ["a", "b", "c", "d", "e"]
            .iter()
            .map(|n| param(n))
            .reduce(max)
            .unwrap();
        assert_level(&norm(&l), &want);
    }
}
