//! Id-twin of `crate::inductive` — mutual, non-nested inductive
//! admission with recursor generation, plus nested-inductive
//! elimination (oracle: src/kernel/inductive.cpp:120-790 for the
//! ordinary pipeline, :792-1181 for nested elimination, pinned githash
//! b4812ae53eea93439ad5dce5a5c26591c31cb697, toolchain
//! leanprover/lean4:v4.32.0-rc1). Porting is representation-only:
//! `Arc<Name>`/`Arc<Expr>`/`Arc<Level>` become `NameId`/`ExprId`/
//! `LevelId` via the phase-1 bank (spec:
//! docs/superpowers/specs/2026-07-06-term-bank-kernel-migration-design.md);
//! every oracle citation below is copied verbatim from the Arc source,
//! and the `operator()`/`add_inductive` pipeline orders are preserved
//! exactly.
//!
//! ## Deviations from the Arc port (documented, per Task 4 precedent)
//!
//! 1. **No real `Environment` to mutate.** The brief's entry points
//!    (`add_inductive`) take a caller-supplied scratch `&mut Store` +
//!    `EnvView` and RETURN the `ConstantInfo`s to admit, rather than
//!    mutating a shared environment in place — there is no id-native
//!    `Environment` yet (Task 6). This eliminates the Arc port's
//!    failure-rollback machinery entirely: the Arc `AddInductiveFn`
//!    tracks `added: Vec<Arc<Name>>` and undoes every `env.add_core` via
//!    `env.remove_core` on error (module doc, `run_add_inductive_fn`'s
//!    `Err` arm, inductive.cpp:1120-1123's `aux_env` discard); here, an
//!    `Err` return means the caller simply drops the whole `extra` map
//!    (and the scratch store interns backing it) — there is nothing to
//!    undo. `added` becomes `extra: HashMap<NameId, ConstantInfo>` (see
//!    point 3), which doubles as both "what later checker calls in this
//!    run can see" and "the function's own return value".
//! 2. **`env: &Environment`/`&mut Environment` parameters disappear.**
//!    The Arc port threads `env` through nearly every method solely
//!    because `AddInductiveFn` could not itself hold both a mutable
//!    `Environment` and a `TypeChecker` borrowing it (module doc point
//!    1). Here, `AddInductiveFn` owns `view: &'a EnvView<'a>` and
//!    `scratch: &'a mut Store` as fields, so every method reaches them
//!    via `self` directly — a pure plumbing simplification the Arc port
//!    could not take, not an algorithmic change.
//! 3. **Nested-inductive scratch env is a fresh `extra` map, not a
//!    cloned `Environment`** (spec §2 / brief's Interfaces note): where
//!    Arc `add_inductive`'s nested branch clones the whole `Environment`
//!    (`let mut scratch = env.clone()`, inductive.cpp's nested branch)
//!    and runs the enlarged (aux) block's admission against that clone,
//!    this port runs the SAME `run_add_inductive_fn` against the SAME
//!    persistent `view` + `scratch: &mut Store`, but with a **fresh,
//!    empty** `HashMap<NameId, ConstantInfo>` as that inner run's own
//!    `extra` accumulator — never mixed with the outer run's `extra`.
//!    That inner map plays the role of the Arc port's `aux_env`
//!    everywhere it calls `aux_env.get(name)`; there is no second
//!    `Store` region (transient decls and checking transients share the
//!    one scratch store and die together, per the design spec).
//! 4. **Name-surgery helpers stay on the Arc side, bridged at the call
//!    site** — `append_after_str`/`append_index_after`/`replace_prefix`/
//!    `name_append` (and the `has_macro_scopes`/`erase_macro_scopes_aux`/
//!    `modify_base`/`NameComp` machinery underneath the first two) do
//!    string-formatting surgery on a `Name`'s `part`, which is not a
//!    "structural" operation the interning invariant collapses — unlike
//!    Task 4's `Expr::structural_eq`-to-`==` rule, two different-looking
//!    names are genuinely different names. Rather than re-deriving this
//!    string surgery id-natively for cold, once-or-twice-per-admission
//!    call sites, these functions are copied VERBATIM (unchanged,
//!    `Arc<Name>` in, `Arc<Name>` out) and bridged in/out via
//!    `Store::to_name`/`Store::intern_name` at each call site — the same
//!    "non-structural operation stays on the Arc side" precedent Task 4
//!    used for `Level::is_equivalent`/`mk_max_pair`/`mk_imax_pair`.
//!    `mk_simple_name`/`mk_rec_name`/`nested_prefix` (trivial fixed-
//!    string or single-suffix constructions with no macro-scope
//!    handling) are instead ported id-natively — they need no string
//!    surgery, just `Store::intern_str`/`name_str`.
//! 5. **`is_geq`/`is_geq_core` stay on the Arc side too, bridged at
//!    their one call site** (`check_constructors`'s universe-bound
//!    check): these perform real (non-structural) universe-level
//!    comparison (`Level::normalize`, `Level::to_offset`), the same
//!    category Task 4 kept Arc-side for `mk_max_pair`/`mk_imax_pair`/
//!    `is_equivalent`. `Level::is_never_zero`/`is_equivalent` are
//!    likewise bridged at their call sites. Plain `Level::is_zero`
//!    checks against a `LevelId` are instead answered natively via a
//!    top-level `LevelRow::Zero` match (genuinely structural — no
//!    normalization involved), avoiding an unnecessary bridge.
//! 6. **`Expr::structural_eq(a, b, g)?` calls become plain `==`** on
//!    `ExprId` (Task 4's porting-rule table, applied verbatim here too):
//!    `is_valid_ind_app_i`'s head/param comparisons,
//!    `elim_only_at_universe_zero`'s result-arg comparison, and
//!    `ElimNestedInductiveFn::replace_if_nested`'s already-lifted-aux
//!    lookup are all comparisons between ids already interned in the
//!    same store, which the interning invariant makes exactly
//!    structural — no guard, no `Result`, no re-derivation needed.
//! 7. **`check_name`/`check_duplicated_univ_params`/
//!    `check_no_metavar_no_fvar`** are ported id-natively as private
//!    free functions INSIDE this file (they belong to `bank/env.rs`
//!    conceptually — Arc's `env.rs:18-56` — but that module doesn't
//!    exist until Task 6; a later task should hoist/re-export them from
//!    there). Region correctness matters: declaration-position
//!    `NameId`s here may be scratch-region (freshly bridged admission
//!    input), so error construction always goes through
//!    `scratch.to_name(Some(view.store), Some(n))` (never
//!    `EnvView::get_with`'s bare miss-path `to_name(None, ...)`).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::decl::{
    ConstantInfo, ConstantVal, ConstructorVal, InductiveType, InductiveVal, RecursorRule,
    RecursorVal,
};
use super::local_ctx::{FVarIdGen, LocalContext};
use super::names::NameRow;
use super::subst::{abstract_fvars, instantiate, instantiate_level_params, instantiate_rev};
use super::tc::{EnvView, TypeChecker};
use super::terms::Node;
use super::{ExprId, LevelId, NameId, Store};
use crate::{BinderInfo, KernelError, Level, Name, Nat, RecGuard};

// ---------------------------------------------------------------------
// Small id-native name/expr helpers (free functions).
// ---------------------------------------------------------------------

/// A single-component name with an anonymous parent, id-native (no
/// macro-scope handling needed — always a fresh literal).
fn mk_simple_name_id(st: &mut Store, base: Option<&Store>, s: &str) -> Result<NameId, KernelError> {
    let part = st.intern_str(base, s)?;
    st.name_str(base, None, part)
}

/// oracle: inductive.cpp:22-24 (`mk_rec_name`) — `I ++ \`rec\``.
fn mk_rec_name_id(st: &mut Store, base: Option<&Store>, i: NameId) -> Result<NameId, KernelError> {
    let part = st.intern_str(base, "rec")?;
    st.name_str(base, Some(i), part)
}

/// oracle: `name("_nested")` (inductive.cpp:1216 `g_nested`).
fn nested_prefix_id(st: &mut Store, base: Option<&Store>) -> Result<NameId, KernelError> {
    mk_simple_name_id(st, base, "_nested")
}

/// oracle: level.cpp:530-535 (`lparams_to_levels`) — purely structural
/// (`Level::Param(p)` for each), so this is id-native, no Arc bridge.
fn lparams_to_levels_id(
    st: &mut Store,
    base: Option<&Store>,
    ps: &[NameId],
) -> Result<Vec<LevelId>, KernelError> {
    ps.iter().map(|&p| st.level_param(base, Some(p))).collect()
}

/// Structural (top-level-constructor) zero check — no normalization
/// involved, unlike `is_geq`/`is_never_zero`/`is_equivalent`, so this is
/// answered natively rather than bridged.
fn level_is_zero(st: &Store, base: Option<&Store>, l: LevelId) -> bool {
    matches!(*st.level_row(base, l), super::levels::LevelRow::Zero)
}

// ---------------------------------------------------------------------
// Name-surgery helpers — Arc-side, unchanged (see module doc point 4).
// Verbatim copies of `crate::inductive`'s private helpers of the same
// name.
// ---------------------------------------------------------------------

/// oracle: Init/Prelude.lean:5599-5602 (`Name.hasMacroScopes`).
fn has_macro_scopes(n: &Arc<Name>) -> bool {
    let mut cur = n;
    loop {
        match cur.as_ref() {
            Name::Str { part, .. } => return part == "_hyg",
            Name::Num { parent, .. } => cur = parent,
            Name::Anonymous => return false,
        }
    }
}

/// oracle: Init/Prelude.lean:5604-5609 (`eraseMacroScopesAux`).
fn erase_macro_scopes_aux(n: &Arc<Name>) -> Arc<Name> {
    let mut cur = Arc::clone(n);
    loop {
        match cur.as_ref() {
            Name::Str { parent, part } => {
                if part == "_@" {
                    return Arc::clone(parent);
                }
                let p = Arc::clone(parent);
                cur = p;
            }
            Name::Num { parent, .. } => {
                let p = Arc::clone(parent);
                cur = p;
            }
            Name::Anonymous => return Arc::new(Name::Anonymous),
        }
    }
}

/// oracle: Init/Meta/Defs.lean:309-314 (`Name.modifyBase`).
fn modify_base(n: &Arc<Name>, f: impl FnOnce(&Arc<Name>) -> Arc<Name>) -> Arc<Name> {
    if has_macro_scopes(n) {
        let base = erase_macro_scopes_aux(n);
        let new_base = f(&base);
        replace_prefix(n, &base, &new_base)
    } else {
        f(n)
    }
}

/// oracle: Init/Meta/Defs.lean:315-318 (`Name.appendAfter`).
fn append_after_str(n: &Arc<Name>, suffix: &str) -> Arc<Name> {
    modify_base(n, |base| match base.as_ref() {
        Name::Str { parent, part } => Arc::new(Name::Str {
            parent: Arc::clone(parent),
            part: format!("{part}{suffix}"),
        }),
        _ => Arc::new(Name::Str {
            parent: Arc::clone(base),
            part: suffix.to_string(),
        }),
    })
}

/// oracle: Init/Meta/Defs.lean:320-323 (`Name.appendIndexAfter`).
fn append_index_after(n: &Arc<Name>, idx: usize) -> Arc<Name> {
    modify_base(n, |base| match base.as_ref() {
        Name::Str { parent, part } => Arc::new(Name::Str {
            parent: Arc::clone(parent),
            part: format!("{part}_{idx}"),
        }),
        _ => Arc::new(Name::Str {
            parent: Arc::clone(base),
            part: format!("_{idx}"),
        }),
    })
}

/// Suffix component captured while walking a name toward its root.
enum NameComp {
    Str(String),
    Num(Nat),
}

/// oracle: `name::replace_prefix` (util/name.cpp).
fn replace_prefix(n: &Arc<Name>, pre: &Arc<Name>, new_pre: &Arc<Name>) -> Arc<Name> {
    let mut comps: Vec<NameComp> = Vec::new();
    let mut cur = Arc::clone(n);
    loop {
        if cur.as_ref() == pre.as_ref() {
            let mut result = Arc::clone(new_pre);
            for c in comps.into_iter().rev() {
                result = match c {
                    NameComp::Str(s) => Arc::new(Name::Str {
                        parent: result,
                        part: s,
                    }),
                    NameComp::Num(v) => Arc::new(Name::Num {
                        parent: result,
                        part: v,
                    }),
                };
            }
            return result;
        }
        match cur.as_ref() {
            Name::Anonymous => return Arc::clone(n),
            Name::Str { parent, part } => {
                comps.push(NameComp::Str(part.clone()));
                let p = Arc::clone(parent);
                cur = p;
            }
            Name::Num { parent, part } => {
                comps.push(NameComp::Num(part.clone()));
                let p = Arc::clone(parent);
                cur = p;
            }
        }
    }
}

/// oracle: util/name.cpp:302-318 (`operator+`).
fn name_append(n1: &Arc<Name>, n2: &Arc<Name>) -> Arc<Name> {
    let mut comps: Vec<NameComp> = Vec::new();
    let mut cur = Arc::clone(n2);
    loop {
        match cur.as_ref() {
            Name::Anonymous => break,
            Name::Str { parent, part } => {
                comps.push(NameComp::Str(part.clone()));
                cur = Arc::clone(parent);
            }
            Name::Num { parent, part } => {
                comps.push(NameComp::Num(part.clone()));
                cur = Arc::clone(parent);
            }
        }
    }
    let mut result = Arc::clone(n1);
    for c in comps.into_iter().rev() {
        result = match c {
            NameComp::Str(s) => Arc::new(Name::Str {
                parent: result,
                part: s,
            }),
            NameComp::Num(v) => Arc::new(Name::Num {
                parent: result,
                part: v,
            }),
        };
    }
    result
}

/// Bridge wrapper: `append_after_str` at the id boundary. `n` is
/// `Option<NameId>` (not a declaration-position name — this is always
/// used to build a LOCAL BINDER name, e.g. the induction-hypothesis
/// fvar's name in `mk_rec_infos`, and a source binder can legitimately
/// be anonymous), so the result is threaded straight into `mk_local`
/// without an anonymity assertion.
fn append_after_str_id(
    st: &mut Store,
    base: Option<&Store>,
    n: Option<NameId>,
    suffix: &str,
) -> Result<Option<NameId>, KernelError> {
    let arc_n = st.to_name(base, n);
    let arc_r = append_after_str(&arc_n, suffix);
    st.intern_name(base, &arc_r)
}

/// Bridge wrapper: `replace_prefix` at the id boundary. Returns
/// `Option<NameId>` since one call site (`mk_rec_infos`'s `minor_name`)
/// replaces a prefix with `Name::Anonymous` on purpose (a LOCAL BINDER
/// name, which can legitimately be anonymous); declaration-position
/// call sites assert `Some` themselves.
fn replace_prefix_id(
    st: &mut Store,
    base: Option<&Store>,
    n: NameId,
    pre: NameId,
    new_pre: Option<NameId>,
) -> Result<Option<NameId>, KernelError> {
    let arc_n = st.to_name(base, Some(n));
    let arc_pre = st.to_name(base, Some(pre));
    let arc_new_pre = st.to_name(base, new_pre);
    let arc_r = replace_prefix(&arc_n, &arc_pre, &arc_new_pre);
    st.intern_name(base, &arc_r)
}

/// Bridge wrapper: `name_append` at the id boundary. Every call site
/// concatenates two non-anonymous names (`nested_prefix`/a real
/// inductive name), so the result is always real.
fn name_append_id(
    st: &mut Store,
    base: Option<&Store>,
    n1: NameId,
    n2: NameId,
) -> Result<NameId, KernelError> {
    let arc_n1 = st.to_name(base, Some(n1));
    let arc_n2 = st.to_name(base, Some(n2));
    let arc_r = name_append(&arc_n1, &arc_n2);
    st.intern_name(base, &arc_r)?
        .ok_or(KernelError::BankExhausted)
}

/// Bridge wrapper: `append_index_after` at the id boundary. Every call
/// site indexes a concrete (never-empty) base name, so the result is
/// always real.
fn append_index_after_id(
    st: &mut Store,
    base: Option<&Store>,
    n: NameId,
    idx: usize,
) -> Result<NameId, KernelError> {
    let arc_n = st.to_name(base, Some(n));
    let arc_r = append_index_after(&arc_n, idx);
    st.intern_name(base, &arc_r)?
        .ok_or(KernelError::BankExhausted)
}

// ---------------------------------------------------------------------
// Level non-structural ops — Arc-side, bridged (module doc point 5).
// ---------------------------------------------------------------------

/// oracle: level.cpp:527-528 (`is_geq`).
fn is_geq(a: &Arc<Level>, b: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
    g.enter(|g| {
        let na = Level::normalize(a, g)?;
        let nb = Level::normalize(b, g)?;
        is_geq_core(&na, &nb, g)
    })
}

/// oracle: level.cpp:508-526 (`is_geq_core`).
fn is_geq_core(l1: &Arc<Level>, l2: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
    if Level::structural_eq(l1, l2, g)? || l2.is_zero() {
        return Ok(true);
    }
    if let Level::Max(a, b) = l2.as_ref() {
        return Ok(is_geq(l1, a, g)? && is_geq(l1, b, g)?);
    }
    if let Level::Max(a, b) = l1.as_ref() {
        if is_geq(a, l2, g)? || is_geq(b, l2, g)? {
            return Ok(true);
        }
    }
    if let Level::IMax(a, b) = l2.as_ref() {
        return Ok(is_geq(l1, a, g)? && is_geq(l1, b, g)?);
    }
    if let Level::IMax(_, b) = l1.as_ref() {
        return is_geq(b, l2, g);
    }
    let (b1, k1) = Level::to_offset(l1);
    let (b2, k2) = Level::to_offset(l2);
    if Level::structural_eq(b1, b2, g)? || b2.is_zero() {
        return Ok(k1 >= k2);
    }
    if k1 == k2 && k1 > 0 {
        return is_geq(b1, b2, g);
    }
    Ok(false)
}

/// Bridge wrapper: `is_geq` at the id boundary (its one call site,
/// `AddInductiveFn::check_constructors`'s universe-bound check).
fn is_geq_id(
    st: &Store,
    base: Option<&Store>,
    a: LevelId,
    b: LevelId,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    let arc_a = st.to_level(base, a);
    let arc_b = st.to_level(base, b);
    is_geq(&arc_a, &arc_b, g)
}

/// Bridge wrapper: `Level::is_never_zero` at the id boundary.
fn level_is_never_zero_id(
    st: &Store,
    base: Option<&Store>,
    l: LevelId,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    let arc_l = st.to_level(base, l);
    Level::is_never_zero(&arc_l, g)
}

/// Bridge wrapper: `Level::is_equivalent` at the id boundary.
fn level_is_equivalent_id(
    st: &Store,
    base: Option<&Store>,
    a: LevelId,
    b: LevelId,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    let arc_a = st.to_level(base, a);
    let arc_b = st.to_level(base, b);
    Level::is_equivalent(&arc_a, &arc_b, g)
}

// ---------------------------------------------------------------------
// Id-native app-spine / node-kind helpers (duplicated free-function
// equivalents of the private methods already in `bank::tc::TypeChecker`
// — same precedent as `bvar_index_nat`'s duplication across
// `bank/subst.rs`/`bank/tc.rs`; `AddInductiveFn`/`ElimNestedInductiveFn`
// are not a `TypeChecker` and cannot reach its private methods).
// ---------------------------------------------------------------------

fn get_app_fn(st: &Store, base: Option<&Store>, e: ExprId) -> ExprId {
    let mut cur = e;
    while let Node::App { f, .. } = st.expr_node(base, cur) {
        cur = f;
    }
    cur
}

fn get_app_args(st: &Store, base: Option<&Store>, e: ExprId) -> Vec<ExprId> {
    let mut args = Vec::new();
    let mut cur = e;
    while let Node::App { f, arg } = st.expr_node(base, cur) {
        args.push(arg);
        cur = f;
    }
    args.reverse();
    args
}

fn get_app_num_args(st: &Store, base: Option<&Store>, e: ExprId) -> usize {
    let mut n = 0usize;
    let mut cur = e;
    while let Node::App { f, .. } = st.expr_node(base, cur) {
        n += 1;
        cur = f;
    }
    n
}

fn mk_app_spine(
    st: &mut Store,
    base: Option<&Store>,
    f: ExprId,
    args: &[ExprId],
) -> Result<ExprId, KernelError> {
    let mut r = f;
    for &a in args {
        r = st.expr_app(base, r, a)?;
    }
    Ok(r)
}

fn is_app(st: &Store, base: Option<&Store>, e: ExprId) -> bool {
    matches!(st.expr_node(base, e), Node::App { .. })
}

fn const_name(st: &Store, base: Option<&Store>, e: ExprId) -> Option<NameId> {
    match st.expr_node(base, e) {
        Node::Const { name, .. } => name,
        _ => None,
    }
}

/// `(binder_name, binder_type, body, binder_info)` of a `Forall` node,
/// or `None` — id-twin of the Arc port's `peel_forall`.
type ForallParts = (Option<NameId>, ExprId, ExprId, BinderInfo);
fn peel_forall(st: &Store, base: Option<&Store>, e: ExprId) -> Option<ForallParts> {
    match st.expr_node(base, e) {
        Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Some((binder_name, binder_type, body, binder_info)),
        _ => None,
    }
}

/// oracle: expr.h:39 (`is_explicit(binder_info)`).
fn is_explicit_bi(bi: BinderInfo) -> bool {
    matches!(bi, BinderInfo::Default)
}

/// oracle: Lean/Expr.lean:1740-1747 (`consumeTypeAnnotations`).
fn consume_type_annotations(st: &Store, base: Option<&Store>, e: ExprId) -> ExprId {
    let mut cur = e;
    loop {
        let fn0 = get_app_fn(st, base, cur);
        let name = match const_name(st, base, fn0) {
            Some(n) => n,
            None => return cur,
        };
        let part = match st.name_row(base, name) {
            NameRow::Str { parent: None, part } => st.str_at(base, *part),
            _ => return cur,
        };
        let nargs = get_app_num_args(st, base, cur);
        let strip = matches!(
            (part, nargs),
            ("optParam", 2) | ("autoParam", 2) | ("outParam", 1) | ("semiOutParam", 1)
        );
        if !strip {
            return cur;
        }
        let args = get_app_args(st, base, cur);
        cur = args[0];
    }
}

// ---------------------------------------------------------------------
// Guarded structural walkers — id-native (module doc: purely structural
// tree walks, no non-structural semantics, so no Arc bridge needed).
// ---------------------------------------------------------------------

/// oracle: expr.cpp:389-409 (`has_loose_bvar`).
fn has_loose_bvar(
    st: &Store,
    base: Option<&Store>,
    e: ExprId,
    i: u64,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    if let Some(r) = st.expr_data(base, e).loose_bvar_range_exact() {
        if i >= r as u64 {
            return Ok(false);
        }
    }
    match st.expr_node(base, e) {
        Node::BVar { idx } => Ok(idx as u64 == i),
        Node::BVarBig { idx } => Ok(st.nat_at(base, idx).clone() == Nat::from(i)),
        Node::App { f, arg } => g.enter(|g| {
            Ok(has_loose_bvar(st, base, f, i, g)? || has_loose_bvar(st, base, arg, i, g)?)
        }),
        Node::Lam {
            binder_type, body, ..
        }
        | Node::Forall {
            binder_type, body, ..
        } => g.enter(|g| {
            Ok(has_loose_bvar(st, base, binder_type, i, g)?
                || has_loose_bvar(st, base, body, i + 1, g)?)
        }),
        Node::LetE {
            ty, value, body, ..
        } => g.enter(|g| {
            Ok(has_loose_bvar(st, base, ty, i, g)?
                || has_loose_bvar(st, base, value, i, g)?
                || has_loose_bvar(st, base, body, i + 1, g)?)
        }),
        Node::MData { expr, .. } => g.enter(|g| has_loose_bvar(st, base, expr, i, g)),
        Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
            g.enter(|g| has_loose_bvar(st, base, structure, i, g))
        }
        _ => Ok(false),
    }
}

/// oracle: expr.cpp:370-387 (`has_loose_bvars_in_domain`).
fn has_loose_bvars_in_domain(
    st: &Store,
    base: Option<&Store>,
    b0: ExprId,
    vidx0: u64,
    strict: bool,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    let mut b = b0;
    let mut vidx = vidx0;
    loop {
        match st.expr_node(base, b) {
            Node::Forall {
                binder_type,
                body,
                binder_info,
                ..
            } => {
                if has_loose_bvar(st, base, binder_type, vidx, g)?
                    && (is_explicit_bi(binder_info)
                        || g.enter(|g| has_loose_bvars_in_domain(st, base, body, 0, strict, g))?)
                {
                    return Ok(true);
                }
                b = body;
                vidx += 1;
            }
            _ => {
                if strict {
                    return Ok(false);
                } else {
                    return has_loose_bvar(st, base, b, vidx, g);
                }
            }
        }
    }
}

/// oracle: expr.cpp:480-500 (`infer_implicit`, `num_params = max`,
/// `strict = true`).
fn infer_implicit(
    st: &mut Store,
    base: Option<&Store>,
    t: ExprId,
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    let mut binders: Vec<(Option<NameId>, ExprId, BinderInfo)> = Vec::new();
    let mut cur = t;
    while let Some((bn, bt, body, bi)) = peel_forall(st, base, cur) {
        binders.push((bn, bt, bi));
        cur = body;
    }
    let mut result = cur;
    for (bn, bt, bi) in binders.into_iter().rev() {
        let new_bi = if !is_explicit_bi(bi) {
            bi
        } else if has_loose_bvars_in_domain(st, base, result, 0, true, g)? {
            BinderInfo::Implicit
        } else {
            bi
        };
        result = st.expr_forall(base, bn, bt, result, new_bi)?;
    }
    Ok(result)
}

/// oracle: inductive.cpp:369-379 (`is_ind_occ`/`has_ind_occ`).
fn expr_has_ind_occ(
    st: &Store,
    base: Option<&Store>,
    e: ExprId,
    names: &HashSet<NameId>,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    match st.expr_node(base, e) {
        Node::Const {
            name: Some(name), ..
        } => Ok(names.contains(&name)),
        Node::Const { name: None, .. } => Ok(false),
        Node::App { f, arg } => g.enter(|g| {
            Ok(expr_has_ind_occ(st, base, f, names, g)?
                || expr_has_ind_occ(st, base, arg, names, g)?)
        }),
        Node::Lam {
            binder_type, body, ..
        }
        | Node::Forall {
            binder_type, body, ..
        } => g.enter(|g| {
            Ok(expr_has_ind_occ(st, base, binder_type, names, g)?
                || expr_has_ind_occ(st, base, body, names, g)?)
        }),
        Node::LetE {
            ty, value, body, ..
        } => g.enter(|g| {
            Ok(expr_has_ind_occ(st, base, ty, names, g)?
                || expr_has_ind_occ(st, base, value, names, g)?
                || expr_has_ind_occ(st, base, body, names, g)?)
        }),
        Node::MData { expr, .. } => g.enter(|g| expr_has_ind_occ(st, base, expr, names, g)),
        Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
            g.enter(|g| expr_has_ind_occ(st, base, structure, names, g))
        }
        _ => Ok(false),
    }
}

/// oracle: inductive.cpp:936-944 — does `e` contain a `Const` whose name
/// is one of the block's (current) type names?
fn expr_contains_new_type(
    st: &Store,
    base: Option<&Store>,
    e: ExprId,
    names: &HashSet<NameId>,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    // Same recurrence as `expr_has_ind_occ`; kept as a separate function
    // (verbatim Arc port precedent — the Arc source also keeps
    // `expr_contains_new_type` and `expr_has_ind_occ` as two functions
    // with the same body shape, since they serve different phases:
    // ordinary positivity vs. nested-elimination detection).
    expr_has_ind_occ(st, base, e, names, g)
}

// ---------------------------------------------------------------------
// `check_name`/`check_duplicated_univ_params`/`check_no_metavar_no_fvar`
// — id-native ports of `crate::env`'s admission-pipeline helpers
// (module doc point 7). Region-correct: `n` may be a scratch-region id.
// ---------------------------------------------------------------------

fn check_name(scratch: &Store, view: &EnvView, n: NameId) -> Result<(), KernelError> {
    if view.get(n).is_some() {
        return Err(KernelError::AlreadyDeclared(
            scratch.to_name(Some(view.store), Some(n)),
        ));
    }
    Ok(())
}

fn check_duplicated_univ_params(
    scratch: &Store,
    view: &EnvView,
    ls: &[NameId],
) -> Result<(), KernelError> {
    for (i, &p) in ls.iter().enumerate() {
        if ls[i + 1..].contains(&p) {
            return Err(KernelError::DuplicateUnivParam(
                scratch.to_name(Some(view.store), Some(p)),
            ));
        }
    }
    Ok(())
}

fn check_no_metavar_no_fvar(
    scratch: &Store,
    view: &EnvView,
    n: NameId,
    e: ExprId,
) -> Result<(), KernelError> {
    let d = scratch.expr_data(Some(view.store), e);
    if d.has_expr_mvar() || d.has_level_mvar() {
        return Err(KernelError::HasMetavars(
            scratch.to_name(Some(view.store), Some(n)),
        ));
    }
    if d.has_fvar() {
        return Err(KernelError::HasFVars(
            scratch.to_name(Some(view.store), Some(n)),
        ));
    }
    Ok(())
}

/// Extend `view` with an additional `extra` layer without disturbing its
/// other fields — a free function (not a `&self` method) so callers can
/// invoke it via direct field projections (`extend_view(self.view,
/// &self.extra)`), preserving disjoint-field borrows: the caller can
/// still take `&mut *self.scratch` in the same scope afterward, which a
/// `&self`-taking method would foreclose (a method call borrows all of
/// `self`, not just the fields it happens to touch).
fn extend_view<'x>(view: &'x EnvView<'x>, extra: &'x HashMap<NameId, ConstantInfo>) -> EnvView<'x> {
    EnvView {
        consts: view.consts,
        extra: Some(extra),
        quot_initialized: view.quot_initialized,
        store: view.store,
    }
}

// =====================================================================
// AddInductiveFn — the ordinary (non-nested) admission pipeline
// (oracle: inductive.cpp:124-160 struct, :778-789 `operator()`).
// =====================================================================

/// oracle: inductive.cpp:150-155 (`struct rec_info`).
struct RecInfo {
    c: ExprId,
    minors: Vec<ExprId>,
    indices: Vec<ExprId>,
    major: ExprId,
}

/// Id-twin of the Arc `AddInductiveFn` (module doc points 1-2: no
/// `added`/rollback field — `extra` IS the running admitted set and the
/// eventual return value; no `env` parameter threading — `view`/
/// `scratch` are owned fields instead).
struct AddInductiveFn<'a> {
    view: &'a EnvView<'a>,
    scratch: &'a mut Store,
    extra: HashMap<NameId, ConstantInfo>,
    lparams: Vec<NameId>,
    is_unsafe: bool,
    nnested: Nat,
    nparams: usize,
    ind_types: Vec<InductiveType>,
    guard: RecGuard,
    lctx: LocalContext,
    fvar_gen: FVarIdGen,
    // Computed by check_inductive_types.
    levels: Vec<LevelId>,
    result_level: LevelId,
    is_not_zero: bool,
    nindices: Vec<usize>,
    params: Vec<ExprId>,
    ind_cnsts: Vec<ExprId>,
    ind_names: HashSet<NameId>,
    // Computed by init_elim_level / init_k_target / mk_rec_infos.
    elim_level: LevelId,
    k_target: bool,
    rec_infos: Vec<RecInfo>,
}

impl<'a> AddInductiveFn<'a> {
    fn base(&self) -> Option<&'a Store> {
        Some(self.view.store)
    }

    fn new(
        view: &'a EnvView<'a>,
        scratch: &'a mut Store,
        lparams: Vec<NameId>,
        nparams: usize,
        ind_types: Vec<InductiveType>,
        is_unsafe: bool,
        nnested: Nat,
    ) -> Result<AddInductiveFn<'a>, KernelError> {
        let base = Some(view.store);
        let zero = scratch.level_zero(base)?;
        Ok(AddInductiveFn {
            view,
            scratch,
            extra: HashMap::new(),
            lparams,
            is_unsafe,
            nnested,
            nparams,
            ind_types,
            guard: RecGuard::new(),
            lctx: LocalContext::default(),
            fvar_gen: FVarIdGen::default(),
            levels: Vec::new(),
            result_level: zero,
            is_not_zero: false,
            nindices: Vec::new(),
            params: Vec::new(),
            ind_cnsts: Vec::new(),
            ind_names: HashSet::new(),
            elim_level: zero,
            k_target: false,
            rec_infos: Vec::new(),
        })
    }

    /// Bridge for error payloads: the first type's name, or `Anonymous`
    /// if the block is empty (matching the Arc `name0`'s fallback).
    fn name0(&self) -> Arc<Name> {
        let id = self.ind_types.first().map(|t| t.name);
        self.scratch.to_name(self.base(), id)
    }

    fn node(&self, e: ExprId) -> Node {
        self.scratch.expr_node(self.base(), e)
    }

    fn check_name(&self, n: NameId) -> Result<(), KernelError> {
        let view = extend_view(self.view, &self.extra);
        check_name(self.scratch, &view, n)
    }

    fn mk_pi(&mut self, fvars: &[ExprId], e: ExprId) -> Result<ExprId, KernelError> {
        let base = self.base();
        super::subst::mk_pi(self.scratch, base, &self.lctx, fvars, e, &mut self.guard)
    }

    fn mk_lambda(&mut self, fvars: &[ExprId], e: ExprId) -> Result<ExprId, KernelError> {
        let base = self.base();
        super::subst::mk_lambda(self.scratch, base, &self.lctx, fvars, e, &mut self.guard)
    }

    fn instantiate(&mut self, e: ExprId, sub: ExprId) -> Result<ExprId, KernelError> {
        let base = self.base();
        instantiate(self.scratch, base, e, sub, &mut self.guard)
    }

    /// Run a checker op, sharing this struct's persistent local context/
    /// fvar generator (id-twin of the Arc `run_tc`, module doc point 2 —
    /// no `env` parameter, `self.view`/`self.extra` supply it).
    fn run_tc<R>(
        &mut self,
        f: impl FnOnce(&mut TypeChecker<'_>) -> Result<R, KernelError>,
    ) -> Result<R, KernelError> {
        let lctx = std::mem::take(&mut self.lctx);
        let fvar_gen = std::mem::take(&mut self.fvar_gen);
        let view = extend_view(self.view, &self.extra);
        let mut tc = TypeChecker::new_with(view, &mut *self.scratch, lctx, fvar_gen);
        let r = f(&mut tc);
        let (lctx, fvar_gen) = tc.into_parts();
        self.lctx = lctx;
        self.fvar_gen = fvar_gen;
        r
    }

    /// oracle: inductive.cpp:178-180 (`mk_local_decl`) — consumes leading
    /// type annotations on the domain.
    fn mk_local(
        &mut self,
        name: Option<NameId>,
        ty: ExprId,
        bi: BinderInfo,
    ) -> Result<ExprId, KernelError> {
        let base = self.base();
        let t = consume_type_annotations(self.scratch, base, ty);
        self.lctx
            .mk_local_decl(self.scratch, base, &mut self.fvar_gen, name, t, bi)
    }

    /// oracle: inductive.cpp:174-176 (`get_param_type`).
    fn get_param_type(&self, i: usize) -> ExprId {
        match self.node(self.params[i]) {
            Node::FVar { id: Some(id) } => {
                self.lctx
                    .get(id)
                    .expect("param fvar declared in local context")
                    .ty
            }
            _ => unreachable!("params contains only fvars"),
        }
    }

    fn has_ind_occ(&mut self, e: ExprId) -> Result<bool, KernelError> {
        let base = self.base();
        expr_has_ind_occ(self.scratch, base, e, &self.ind_names, &mut self.guard)
    }

    fn add(&mut self, info: ConstantInfo) {
        self.extra.insert(info.name(), info);
    }

    /// oracle: inductive.cpp:778-789 (`operator()`).
    fn run(&mut self) -> Result<(), KernelError> {
        // oracle: inductive.cpp:1050 — the empty-block guard dominates
        // every `ind_types[0]` index below (elim_only_at_universe_zero,
        // init_K_target); see the Arc port's `run` doc comment.
        if self.ind_types.is_empty() {
            return Err(KernelError::InvalidInductive {
                name: Arc::new(Name::Anonymous),
                what: "empty inductive block",
            });
        }
        {
            let view = extend_view(self.view, &self.extra);
            check_duplicated_univ_params(self.scratch, &view, &self.lparams)?;
        }
        self.check_inductive_types()?;
        self.declare_inductive_types()?;
        self.check_constructors()?;
        self.declare_constructors()?;
        self.init_elim_level()?;
        self.init_k_target();
        self.mk_rec_infos()?;
        self.declare_recursors()?;
        Ok(())
    }

    /// oracle: inductive.cpp:211-262 (`check_inductive_types`).
    fn check_inductive_types(&mut self) -> Result<(), KernelError> {
        let base = self.base();
        self.levels = lparams_to_levels_id(self.scratch, base, &self.lparams)?;
        let lparams = self.lparams.clone();
        let ntypes = self.ind_types.len();
        let mut first = true;
        for idx in 0..ntypes {
            let ind_name = self.ind_types[idx].name;
            let type0 = self.ind_types[idx].ty;
            self.check_name(ind_name)?;
            let rec_name = mk_rec_name_id(self.scratch, base, ind_name)?;
            self.check_name(rec_name)?;
            check_no_metavar_no_fvar(self.scratch, self.view, ind_name, type0)?;
            {
                let lp = lparams.clone();
                self.run_tc(move |tc| {
                    tc.check(type0, &lp)?;
                    Ok(())
                })?;
            }
            self.nindices.push(0);
            let mut i = 0usize;
            let mut ty = self.run_tc(move |tc| tc.whnf(type0))?;
            while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, base, ty) {
                if i < self.nparams {
                    if first {
                        let param = self.mk_local(bn, bt, bi)?;
                        self.params.push(param);
                        ty = self.instantiate(body, param)?;
                    } else {
                        let pt = self.get_param_type(i);
                        let eq = self.run_tc(move |tc| tc.is_def_eq(bt, pt))?;
                        if !eq {
                            return Err(KernelError::InvalidInductive {
                                name: self.scratch.to_name(base, Some(ind_name)),
                                what: "parameters must match",
                            });
                        }
                        let p_i = self.params[i];
                        ty = self.instantiate(body, p_i)?;
                    }
                    i += 1;
                } else {
                    let local = self.mk_local(bn, bt, bi)?;
                    ty = self.instantiate(body, local)?;
                    *self.nindices.last_mut().unwrap() += 1;
                }
                ty = self.run_tc(move |tc| tc.whnf(ty))?;
            }
            if i != self.nparams {
                return Err(KernelError::InvalidInductive {
                    name: self.scratch.to_name(base, Some(ind_name)),
                    what: "number of parameters mismatch",
                });
            }
            let sort_expr = self.run_tc(move |tc| tc.ensure_sort(ty))?;
            let lvl = match self.node(sort_expr) {
                Node::Sort { level } => level,
                _ => return Err(KernelError::TypeExpected),
            };
            if first {
                self.result_level = lvl;
                self.is_not_zero =
                    level_is_never_zero_id(self.scratch, base, lvl, &mut self.guard)?;
            } else {
                let eq = level_is_equivalent_id(
                    self.scratch,
                    base,
                    lvl,
                    self.result_level,
                    &mut self.guard,
                )?;
                if !eq {
                    return Err(KernelError::InvalidInductive {
                        name: self.scratch.to_name(base, Some(ind_name)),
                        what: "mutually inductive types must live in the same universe",
                    });
                }
            }
            let levels_list = self.scratch.intern_level_list(base, &self.levels)?;
            let cnst = self.scratch.expr_const(base, Some(ind_name), levels_list)?;
            self.ind_cnsts.push(cnst);
            self.ind_names.insert(ind_name);
            first = false;
        }
        Ok(())
    }

    /// oracle: inductive.cpp:264-286 (`is_rec`).
    fn is_rec(&mut self) -> Result<bool, KernelError> {
        for idx in 0..self.ind_types.len() {
            for c in 0..self.ind_types[idx].ctors.len() {
                let mut t = self.ind_types[idx].ctors[c].1;
                while let Some((_, dom, body, _)) = peel_forall(self.scratch, self.base(), t) {
                    if self.has_ind_occ(dom)? {
                        return Ok(true);
                    }
                    t = body;
                }
            }
        }
        Ok(false)
    }

    /// oracle: inductive.cpp:294-309 (`is_reflexive`).
    fn is_reflexive(&mut self) -> Result<bool, KernelError> {
        for idx in 0..self.ind_types.len() {
            for c in 0..self.ind_types[idx].ctors.len() {
                let mut t = self.ind_types[idx].ctors[c].1;
                while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, self.base(), t) {
                    if matches!(self.node(bt), Node::Forall { .. }) && self.has_ind_occ(bt)? {
                        return Ok(true);
                    }
                    let local = self.mk_local(bn, bt, bi)?;
                    t = self.instantiate(body, local)?;
                }
            }
        }
        Ok(false)
    }

    /// oracle: inductive.cpp:317-332 (`declare_inductive_types`).
    fn declare_inductive_types(&mut self) -> Result<(), KernelError> {
        let rec = self.is_rec()?;
        let reflexive = self.is_reflexive()?;
        let all: Vec<NameId> = self.ind_types.iter().map(|t| t.name).collect();
        for idx in 0..self.ind_types.len() {
            let n = self.ind_types[idx].name;
            let ty = self.ind_types[idx].ty;
            let ctors: Vec<NameId> = self.ind_types[idx]
                .ctors
                .iter()
                .map(|(cn, _)| *cn)
                .collect();
            self.check_name(n)?;
            let val = InductiveVal {
                val: ConstantVal {
                    name: n,
                    level_params: self.lparams.clone(),
                    ty,
                },
                num_params: Nat::from(self.nparams as u64),
                num_indices: Nat::from(self.nindices[idx] as u64),
                all: all.clone(),
                ctors,
                num_nested: self.nnested.clone(),
                is_rec: rec,
                is_unsafe: self.is_unsafe,
                is_reflexive: reflexive,
            };
            self.add(ConstantInfo::Induct(val));
        }
        Ok(())
    }
}

impl<'a> AddInductiveFn<'a> {
    /// oracle: inductive.cpp:338-357 (`is_valid_ind_app(t, i)`). The Arc
    /// `Expr::structural_eq` calls become plain `==` (module doc point 6).
    fn is_valid_ind_app_i(&mut self, t: ExprId, i: usize) -> Result<bool, KernelError> {
        let base = self.base();
        let head = get_app_fn(self.scratch, base, t);
        let args = get_app_args(self.scratch, base, t);
        if head != self.ind_cnsts[i] {
            return Ok(false);
        }
        if args.len() != self.nparams + self.nindices[i] {
            return Ok(false);
        }
        for (p, a) in self.params.iter().zip(args.iter()).take(self.nparams) {
            if p != a {
                return Ok(false);
            }
        }
        for &arg in args.iter().skip(self.nparams) {
            if self.has_ind_occ(arg)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// oracle: inductive.cpp:359-366 (`is_valid_ind_app(t)`).
    fn is_valid_ind_app(&mut self, t: ExprId) -> Result<Option<usize>, KernelError> {
        for i in 0..self.ind_types.len() {
            if self.is_valid_ind_app_i(t, i)? {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    /// oracle: inductive.cpp:383-390 (`is_rec_argument`).
    fn is_rec_argument(&mut self, t0: ExprId) -> Result<Option<usize>, KernelError> {
        let mut t = self.run_tc(move |tc| tc.whnf(t0))?;
        while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, self.base(), t) {
            let local = self.mk_local(bn, bt, bi)?;
            let inst = self.instantiate(body, local)?;
            t = self.run_tc(move |tc| tc.whnf(inst))?;
        }
        self.is_valid_ind_app(t)
    }

    /// oracle: inductive.cpp:393-409 (`check_positivity`).
    fn check_positivity(&mut self, t0: ExprId, cnstr_name: NameId) -> Result<(), KernelError> {
        let mut t = self.run_tc(move |tc| tc.whnf(t0))?;
        loop {
            if !self.has_ind_occ(t)? {
                return Ok(()); // nonrecursive argument
            }
            match peel_forall(self.scratch, self.base(), t) {
                Some((bn, bt, body, bi)) => {
                    if self.has_ind_occ(bt)? {
                        let base = self.base();
                        return Err(KernelError::InvalidInductive {
                            name: self.scratch.to_name(base, Some(cnstr_name)),
                            what: "positivity",
                        });
                    }
                    let local = self.mk_local(bn, bt, bi)?;
                    let inst = self.instantiate(body, local)?;
                    t = self.run_tc(move |tc| tc.whnf(inst))?;
                }
                None => {
                    let base = self.base();
                    return if self.is_valid_ind_app(t)?.is_some() {
                        Ok(()) // recursive argument
                    } else {
                        Err(KernelError::InvalidInductive {
                            name: self.scratch.to_name(base, Some(cnstr_name)),
                            what: "invalid occurrence",
                        })
                    };
                }
            }
        }
    }

    /// oracle: inductive.cpp:413-453 (`check_constructors`).
    fn check_constructors(&mut self) -> Result<(), KernelError> {
        let lparams = self.lparams.clone();
        for idx in 0..self.ind_types.len() {
            let mut found: HashSet<NameId> = HashSet::new();
            for c in 0..self.ind_types[idx].ctors.len() {
                let n = self.ind_types[idx].ctors[c].0;
                let t0 = self.ind_types[idx].ctors[c].1;
                let base = self.base();
                if found.contains(&n) {
                    return Err(KernelError::InvalidInductive {
                        name: self.scratch.to_name(base, Some(n)),
                        what: "duplicate constructor",
                    });
                }
                found.insert(n);
                self.check_name(n)?;
                check_no_metavar_no_fvar(self.scratch, self.view, n, t0)?;
                {
                    let lp = lparams.clone();
                    self.run_tc(move |tc| {
                        tc.check(t0, &lp)?;
                        Ok(())
                    })?;
                }
                let mut t = t0;
                let mut i = 0usize;
                while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, self.base(), t) {
                    if i < self.nparams {
                        let pt = self.get_param_type(i);
                        let eq = self.run_tc(move |tc| tc.is_def_eq(bt, pt))?;
                        if !eq {
                            let base = self.base();
                            return Err(KernelError::InvalidInductive {
                                name: self.scratch.to_name(base, Some(n)),
                                what: "constructor parameter mismatch",
                            });
                        }
                        let p_i = self.params[i];
                        t = self.instantiate(body, p_i)?;
                    } else {
                        let s = self.run_tc(move |tc| {
                            let ty = tc.infer_type(bt)?;
                            tc.ensure_sort(ty)
                        })?;
                        let s_level = match self.node(s) {
                            Node::Sort { level } => level,
                            _ => return Err(KernelError::TypeExpected),
                        };
                        // oracle:439 — level <= inductive level OR the
                        // inductive is a Prop (result level zero).
                        let base = self.base();
                        let ok = is_geq_id(
                            self.scratch,
                            base,
                            self.result_level,
                            s_level,
                            &mut self.guard,
                        )? || level_is_zero(self.scratch, base, self.result_level);
                        if !ok {
                            return Err(KernelError::InvalidInductive {
                                name: self.scratch.to_name(base, Some(n)),
                                what: "universe too small",
                            });
                        }
                        if !self.is_unsafe {
                            self.check_positivity(bt, n)?;
                        }
                        let local = self.mk_local(bn, bt, bi)?;
                        t = self.instantiate(body, local)?;
                    }
                    i += 1;
                }
                if !self.is_valid_ind_app_i(t, idx)? {
                    let base = self.base();
                    return Err(KernelError::InvalidInductive {
                        name: self.scratch.to_name(base, Some(n)),
                        what: "invalid return type",
                    });
                }
            }
        }
        Ok(())
    }

    /// oracle: inductive.cpp:456-476 (`declare_constructors`).
    fn declare_constructors(&mut self) -> Result<(), KernelError> {
        for idx in 0..self.ind_types.len() {
            let ind_name = self.ind_types[idx].name;
            for c in 0..self.ind_types[idx].ctors.len() {
                let n = self.ind_types[idx].ctors[c].0;
                let t = self.ind_types[idx].ctors[c].1;
                let mut arity = 0usize;
                let mut it = t;
                while let Some((_, _, body, _)) = peel_forall(self.scratch, self.base(), it) {
                    it = body;
                    arity += 1;
                }
                // arity >= nparams is guaranteed by check_constructors.
                let nfields = arity.saturating_sub(self.nparams);
                self.check_name(n)?;
                let val = ConstructorVal {
                    val: ConstantVal {
                        name: n,
                        level_params: self.lparams.clone(),
                        ty: t,
                    },
                    induct: ind_name,
                    cidx: Nat::from(c as u64),
                    num_params: Nat::from(self.nparams as u64),
                    num_fields: Nat::from(nfields as u64),
                    is_unsafe: self.is_unsafe,
                };
                self.add(ConstantInfo::Ctor(val));
            }
        }
        Ok(())
    }
}

impl<'a> AddInductiveFn<'a> {
    /// oracle: inductive.cpp:479-534 (`elim_only_at_universe_zero`). The
    /// Arc `Expr::structural_eq` result-arg scan becomes `Vec::contains`
    /// on `ExprId` (module doc point 6).
    fn elim_only_at_universe_zero(&mut self) -> Result<bool, KernelError> {
        if self.is_not_zero {
            return Ok(false);
        }
        if self.ind_types.len() > 1 {
            return Ok(true);
        }
        let num_intros = self.ind_types[0].ctors.len();
        if num_intros > 1 {
            return Ok(true);
        }
        if num_intros == 0 {
            return Ok(false);
        }
        let mut ty = self.ind_types[0].ctors[0].1;
        let mut i = 0usize;
        let mut to_check: Vec<ExprId> = Vec::new();
        while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, self.base(), ty) {
            let fvar = self.mk_local(bn, bt, bi)?;
            if i >= self.nparams {
                let s = self.run_tc(move |tc| {
                    let ty = tc.infer_type(bt)?;
                    tc.ensure_sort(ty)
                })?;
                let is_zero = match self.node(s) {
                    Node::Sort { level } => level_is_zero(self.scratch, self.base(), level),
                    _ => false,
                };
                if !is_zero {
                    to_check.push(fvar);
                }
            }
            ty = self.instantiate(body, fvar)?;
            i += 1;
        }
        let base = self.base();
        let result_args = get_app_args(self.scratch, base, ty);
        for arg in &to_check {
            if !result_args.contains(arg) {
                return Ok(true); // condition 2 failed
            }
        }
        Ok(false)
    }

    /// oracle: inductive.cpp:536-549 (`init_elim_level`). The Arc
    /// `append_index_after(&mk_simple_name("u"), i)` fallback for a
    /// plain, never-macro-scoped one-component name reduces to
    /// `"u_<i>"`, built natively rather than through the general bridge
    /// (this is always a freshly-minted literal, never decoded input).
    fn init_elim_level(&mut self) -> Result<(), KernelError> {
        if self.elim_only_at_universe_zero()? {
            let base = self.base();
            self.elim_level = self.scratch.level_zero(base)?;
        } else {
            let base = self.base();
            let mut u = mk_simple_name_id(self.scratch, base, "u")?;
            let mut i = 1usize;
            while self.lparams.contains(&u) {
                u = mk_simple_name_id(self.scratch, base, &format!("u_{i}"))?;
                i += 1;
            }
            self.elim_level = self.scratch.level_param(base, Some(u))?;
        }
        Ok(())
    }

    /// oracle: inductive.cpp:551-573 (`init_K_target`).
    fn init_k_target(&mut self) {
        self.k_target = self.ind_types.len() == 1
            && level_is_zero(self.scratch, self.base(), self.result_level)
            && self.ind_types[0].ctors.len() == 1;
        if !self.k_target {
            return;
        }
        let mut it = self.ind_types[0].ctors[0].1;
        let mut i = 0usize;
        while let Some((_, _, body, _)) = peel_forall(self.scratch, self.base(), it) {
            if i < self.nparams {
                it = body;
            } else {
                self.k_target = false;
                break;
            }
            i += 1;
        }
    }

    /// oracle: inductive.cpp:578-586 (`get_I_indices`).
    fn get_i_indices(
        &mut self,
        t: ExprId,
        indices: &mut Vec<ExprId>,
    ) -> Result<usize, KernelError> {
        let r = match self.is_valid_ind_app(t)? {
            Some(r) => r,
            None => {
                return Err(KernelError::InvalidInductive {
                    name: self.name0(),
                    what: "invalid recursor argument",
                })
            }
        };
        let base = self.base();
        let all_args = get_app_args(self.scratch, base, t);
        for &arg in all_args.iter().skip(self.nparams) {
            indices.push(arg);
        }
        Ok(r)
    }

    /// oracle: inductive.cpp:588-674 (`mk_rec_infos`).
    fn mk_rec_infos(&mut self) -> Result<(), KernelError> {
        let ntypes = self.ind_types.len();
        // Phase 1: motive `C`, indices, and major premise per type.
        for d_idx in 0..ntypes {
            let type0 = self.ind_types[d_idx].ty;
            let mut indices: Vec<ExprId> = Vec::new();
            let mut i = 0usize;
            let mut t = self.run_tc(move |tc| tc.whnf(type0))?;
            while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, self.base(), t) {
                if i < self.nparams {
                    let p_i = self.params[i];
                    t = self.instantiate(body, p_i)?;
                } else {
                    let idxv = self.mk_local(bn, bt, bi)?;
                    indices.push(idxv);
                    t = self.instantiate(body, idxv)?;
                }
                i += 1;
                t = self.run_tc(move |tc| tc.whnf(t))?;
            }
            // major : `I params indices`.
            let base = self.base();
            let mut major_ty = self.ind_cnsts[d_idx];
            for &p in &self.params {
                major_ty = self.scratch.expr_app(base, major_ty, p)?;
            }
            for &ix in &indices {
                major_ty = self.scratch.expr_app(base, major_ty, ix)?;
            }
            let t_name = mk_simple_name_id(self.scratch, base, "t")?;
            let major = self.mk_local(Some(t_name), major_ty, BinderInfo::Default)?;
            // C_ty = Π indices, Π major, Sort elim_level.
            let sort = self.scratch.expr_sort(base, self.elim_level)?;
            let c_ty = {
                let mut fvars = indices.clone();
                fvars.push(major);
                self.mk_pi(&fvars, sort)?
            };
            let motive_name = mk_simple_name_id(self.scratch, base, "motive")?;
            let c_name = if ntypes > 1 {
                append_index_after_id(self.scratch, base, motive_name, d_idx + 1)?
            } else {
                motive_name
            };
            let c = self.mk_local(Some(c_name), c_ty, BinderInfo::Default)?;
            self.rec_infos.push(RecInfo {
                c,
                minors: Vec::new(),
                indices,
                major,
            });
        }
        // Phase 2: minor premises.
        for d_idx in 0..ntypes {
            let ind_type_name = self.ind_types[d_idx].name;
            for c in 0..self.ind_types[d_idx].ctors.len() {
                let cnstr_name = self.ind_types[d_idx].ctors[c].0;
                let cnstr_ty = self.ind_types[d_idx].ctors[c].1;
                let mut b_u: Vec<ExprId> = Vec::new();
                let mut u: Vec<ExprId> = Vec::new();
                let mut t = cnstr_ty;
                let mut i = 0usize;
                while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, self.base(), t) {
                    if i < self.nparams {
                        let p_i = self.params[i];
                        t = self.instantiate(body, p_i)?;
                    } else {
                        let l = self.mk_local(bn, bt, bi)?;
                        b_u.push(l);
                        if self.is_rec_argument(bt)?.is_some() {
                            u.push(l);
                        }
                        t = self.instantiate(body, l)?;
                    }
                    i += 1;
                }
                let mut it_indices: Vec<ExprId> = Vec::new();
                let it_idx = self.get_i_indices(t, &mut it_indices)?;
                let base = self.base();
                let mut c_app = self.rec_infos[it_idx].c;
                for &ix in &it_indices {
                    c_app = self.scratch.expr_app(base, c_app, ix)?;
                }
                let levels_list = self.scratch.intern_level_list(base, &self.levels)?;
                let cnstr_const = self
                    .scratch
                    .expr_const(base, Some(cnstr_name), levels_list)?;
                let mut intro_app = cnstr_const;
                for &p in &self.params {
                    intro_app = self.scratch.expr_app(base, intro_app, p)?;
                }
                for &x in &b_u {
                    intro_app = self.scratch.expr_app(base, intro_app, x)?;
                }
                c_app = self.scratch.expr_app(base, c_app, intro_app)?;
                // Induction hypotheses `v`, one per recursive argument `u_i`.
                let mut v: Vec<ExprId> = Vec::new();
                for u_i in u.clone() {
                    let mut u_i_ty = self.run_tc(move |tc| {
                        let ty = tc.infer_type(u_i)?;
                        tc.whnf(ty)
                    })?;
                    let mut xs: Vec<ExprId> = Vec::new();
                    while let Some((bn, bt, body, bi)) =
                        peel_forall(self.scratch, self.base(), u_i_ty)
                    {
                        let x = self.mk_local(bn, bt, bi)?;
                        xs.push(x);
                        let inst = self.instantiate(body, x)?;
                        u_i_ty = self.run_tc(move |tc| tc.whnf(inst))?;
                    }
                    let mut it_indices2: Vec<ExprId> = Vec::new();
                    let it_idx2 = self.get_i_indices(u_i_ty, &mut it_indices2)?;
                    let base = self.base();
                    let mut c_app2 = self.rec_infos[it_idx2].c;
                    for &ix in &it_indices2 {
                        c_app2 = self.scratch.expr_app(base, c_app2, ix)?;
                    }
                    let mut u_app = u_i;
                    for &x in &xs {
                        u_app = self.scratch.expr_app(base, u_app, x)?;
                    }
                    c_app2 = self.scratch.expr_app(base, c_app2, u_app)?;
                    let v_i_ty = self.mk_pi(&xs, c_app2)?;
                    let user_name = match self.node(u_i) {
                        Node::FVar { id: Some(id) } => {
                            self.lctx
                                .get(id)
                                .expect("recursive-arg fvar declared")
                                .binder_name
                        }
                        _ => unreachable!("u holds only fvars"),
                    };
                    let v_i_name = append_after_str_id(self.scratch, base, user_name, "_ih")?;
                    let v_i = self.mk_local(v_i_name, v_i_ty, BinderInfo::Default)?;
                    v.push(v_i);
                }
                let minor_ty = {
                    let inner = self.mk_pi(&v, c_app)?;
                    self.mk_pi(&b_u, inner)?
                };
                let minor_name =
                    replace_prefix_id(self.scratch, base, cnstr_name, ind_type_name, None)?;
                let minor = self.mk_local(minor_name, minor_ty, BinderInfo::Default)?;
                self.rec_infos[d_idx].minors.push(minor);
            }
        }
        Ok(())
    }

    /// oracle: inductive.cpp:677-682 (`get_rec_levels`).
    fn get_rec_levels(&self) -> Vec<LevelId> {
        match *self.scratch.level_row(self.base(), self.elim_level) {
            super::levels::LevelRow::Param(_) => {
                let mut ls = vec![self.elim_level];
                ls.extend(self.levels.iter().copied());
                ls
            }
            _ => self.levels.clone(),
        }
    }

    /// oracle: inductive.cpp:685-690 (`get_rec_lparams`).
    fn get_rec_lparams(&self) -> Vec<NameId> {
        match *self.scratch.level_row(self.base(), self.elim_level) {
            super::levels::LevelRow::Param(Some(u)) => {
                let mut ps = vec![u];
                ps.extend(self.lparams.iter().copied());
                ps
            }
            _ => self.lparams.clone(),
        }
    }

    /// oracle: inductive.cpp:693-697 (`collect_Cs`).
    fn collect_cs(&self) -> Vec<ExprId> {
        (0..self.ind_types.len())
            .map(|i| self.rec_infos[i].c)
            .collect()
    }

    /// oracle: inductive.cpp:699-703 (`collect_minor_premises`).
    fn collect_minors(&self) -> Vec<ExprId> {
        let mut ms = Vec::new();
        for i in 0..self.ind_types.len() {
            ms.extend(self.rec_infos[i].minors.iter().copied());
        }
        ms
    }

    /// oracle: inductive.cpp:705-749 (`mk_rec_rules`).
    fn mk_rec_rules(
        &mut self,
        d_idx: usize,
        cs: &[ExprId],
        minors: &[ExprId],
        minor_idx: &mut usize,
    ) -> Result<Vec<RecursorRule>, KernelError> {
        let lvls = self.get_rec_levels();
        let params = self.params.clone();
        let mut rules = Vec::new();
        for c in 0..self.ind_types[d_idx].ctors.len() {
            let cnstr_name = self.ind_types[d_idx].ctors[c].0;
            let cnstr_ty = self.ind_types[d_idx].ctors[c].1;
            let mut b_u: Vec<ExprId> = Vec::new();
            let mut u: Vec<ExprId> = Vec::new();
            let mut t = cnstr_ty;
            let mut i = 0usize;
            while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, self.base(), t) {
                if i < self.nparams {
                    let p_i = self.params[i];
                    t = self.instantiate(body, p_i)?;
                } else {
                    let l = self.mk_local(bn, bt, bi)?;
                    b_u.push(l);
                    if self.is_rec_argument(bt)?.is_some() {
                        u.push(l);
                    }
                    t = self.instantiate(body, l)?;
                }
                i += 1;
            }
            // Recursive calls `v`, one per recursive argument `u_i`.
            let mut v: Vec<ExprId> = Vec::new();
            for u_i in u.clone() {
                let mut u_i_ty = self.run_tc(move |tc| {
                    let ty = tc.infer_type(u_i)?;
                    tc.whnf(ty)
                })?;
                let mut xs: Vec<ExprId> = Vec::new();
                while let Some((bn, bt, body, bi)) = peel_forall(self.scratch, self.base(), u_i_ty)
                {
                    let x = self.mk_local(bn, bt, bi)?;
                    xs.push(x);
                    let inst = self.instantiate(body, x)?;
                    u_i_ty = self.run_tc(move |tc| tc.whnf(inst))?;
                }
                let mut it_indices: Vec<ExprId> = Vec::new();
                let it_idx = self.get_i_indices(u_i_ty, &mut it_indices)?;
                let base = self.base();
                let rec_name = mk_rec_name_id(self.scratch, base, self.ind_types[it_idx].name)?;
                let lvls_list = self.scratch.intern_level_list(base, &lvls)?;
                let rec_const = self.scratch.expr_const(base, Some(rec_name), lvls_list)?;
                let mut rec_app = rec_const;
                for &p in &params {
                    rec_app = self.scratch.expr_app(base, rec_app, p)?;
                }
                for &cc in cs {
                    rec_app = self.scratch.expr_app(base, rec_app, cc)?;
                }
                for &mm in minors {
                    rec_app = self.scratch.expr_app(base, rec_app, mm)?;
                }
                for &ix in &it_indices {
                    rec_app = self.scratch.expr_app(base, rec_app, ix)?;
                }
                let mut u_app = u_i;
                for &x in &xs {
                    u_app = self.scratch.expr_app(base, u_app, x)?;
                }
                rec_app = self.scratch.expr_app(base, rec_app, u_app)?;
                let lam = self.mk_lambda(&xs, rec_app)?;
                v.push(lam);
            }
            // e_app = (minor b_u) v.
            let base = self.base();
            let mut e_app = minors[*minor_idx];
            for &x in &b_u {
                e_app = self.scratch.expr_app(base, e_app, x)?;
            }
            for &vi in &v {
                e_app = self.scratch.expr_app(base, e_app, vi)?;
            }
            // comp_rhs = λ params, λ Cs, λ minors, λ b_u, e_app.
            let comp_rhs = {
                let l1 = self.mk_lambda(&b_u, e_app)?;
                let l2 = self.mk_lambda(minors, l1)?;
                let l3 = self.mk_lambda(cs, l2)?;
                self.mk_lambda(&params, l3)?
            };
            rules.push(RecursorRule {
                ctor: cnstr_name,
                nfields: Nat::from(b_u.len() as u64),
                rhs: comp_rhs,
            });
            *minor_idx += 1;
        }
        Ok(rules)
    }

    /// oracle: inductive.cpp:752-776 (`declare_recursors`).
    fn declare_recursors(&mut self) -> Result<(), KernelError> {
        let cs = self.collect_cs();
        let minors = self.collect_minors();
        let nminors = minors.len();
        let nmotives = cs.len();
        let all: Vec<NameId> = self.ind_types.iter().map(|t| t.name).collect();
        let params = self.params.clone();
        let mut minor_idx = 0usize;
        for d_idx in 0..self.ind_types.len() {
            let (c, indices, major) = {
                let info = &self.rec_infos[d_idx];
                (info.c, info.indices.clone(), info.major)
            };
            let base = self.base();
            // C_app = C indices major.
            let mut c_app = c;
            for &ix in &indices {
                c_app = self.scratch.expr_app(base, c_app, ix)?;
            }
            c_app = self.scratch.expr_app(base, c_app, major)?;
            // rec_ty = Π params, Π Cs, Π minors, Π indices, Π major, C_app.
            let mut rec_ty = self.mk_pi(std::slice::from_ref(&major), c_app)?;
            rec_ty = self.mk_pi(&indices, rec_ty)?;
            rec_ty = self.mk_pi(&minors, rec_ty)?;
            rec_ty = self.mk_pi(&cs, rec_ty)?;
            rec_ty = self.mk_pi(&params, rec_ty)?;
            let rec_ty = {
                let base = self.base();
                infer_implicit(self.scratch, base, rec_ty, &mut self.guard)?
            };
            let rules = self.mk_rec_rules(d_idx, &cs, &minors, &mut minor_idx)?;
            let base = self.base();
            let rec_name = mk_rec_name_id(self.scratch, base, self.ind_types[d_idx].name)?;
            let rec_lparams = self.get_rec_lparams();
            self.check_name(rec_name)?;
            let val = RecursorVal {
                val: ConstantVal {
                    name: rec_name,
                    level_params: rec_lparams,
                    ty: rec_ty,
                },
                all: all.clone(),
                num_params: Nat::from(self.nparams as u64),
                num_indices: Nat::from(self.nindices[d_idx] as u64),
                num_motives: Nat::from(nmotives as u64),
                num_minors: Nat::from(nminors as u64),
                rules,
                k: self.k_target,
                is_unsafe: self.is_unsafe,
            };
            self.add(ConstantInfo::Rec(val));
        }
        Ok(())
    }
}

/// Runs the ordinary (non-nested) `AddInductiveFn` machinery on an
/// already nesting-eliminated block. `nnested` is the count of auxiliary
/// nested types the caller lifted into the block (0 for a genuinely
/// non-nested declaration). Id-twin of the Arc `run_add_inductive_fn`
/// (inductive.cpp-adjacent helper) MINUS its rollback: there is nothing
/// to roll back here (module doc point 1) — an `Err` means the caller
/// discards `f.extra` (never returned) along with the scratch interns
/// backing it.
fn run_add_inductive_fn<'a>(
    scratch: &'a mut Store,
    view: &'a EnvView<'a>,
    lparams: Vec<NameId>,
    nparams: Nat,
    types: Vec<InductiveType>,
    is_unsafe: bool,
    nnested: Nat,
) -> Result<HashMap<NameId, ConstantInfo>, KernelError> {
    let nparams_small = match nparams.to_usize() {
        Some(v) => v,
        None => {
            let name0 = scratch.to_name(Some(view.store), types.first().map(|t| t.name));
            return Err(KernelError::InvalidInductive {
                name: name0,
                what: "too many parameters",
            });
        }
    };
    let mut f = AddInductiveFn::new(
        view,
        scratch,
        lparams,
        nparams_small,
        types,
        is_unsafe,
        nnested,
    )?;
    f.run()?;
    Ok(f.extra)
}

// =====================================================================
// Nested-inductive elimination (oracle: inductive.cpp:792-1181). See
// module doc point 3 for how the Arc port's cloned-`Environment`
// "scratch env" becomes a fresh `extra` map at the `add_inductive` call
// site (`run_add_inductive_fn`'s return value) — this struct itself only
// ever reads the REAL persistent `view` (other, already-declared
// inductives), never the in-progress block, so it needs no `extra` of
// its own.
// =====================================================================

/// oracle: `elim_nested_inductive_fn` (inductive.cpp:882-1077).
struct ElimNestedInductiveFn<'a> {
    view: &'a EnvView<'a>,
    scratch: &'a mut Store,
    ngen: FVarIdGen,
    /// oracle `m_params_lctx`.
    params_lctx: LocalContext,
    /// oracle `m_params`.
    params: Vec<ExprId>,
    /// oracle `m_nested_aux`: `(I Ds canonicalized over m_params, auxName)`.
    nested_aux: Vec<(ExprId, NameId)>,
    /// oracle `m_lvls`.
    lvls: Vec<LevelId>,
    /// oracle `m_new_types`: the (growing) enlarged block.
    new_types: Vec<InductiveType>,
    new_type_names: HashSet<NameId>,
    /// oracle `m_next_idx`.
    next_idx: u64,
    nparams: usize,
    name0: Option<NameId>,
}

/// oracle: `elim_nested_inductive_result` (inductive.cpp:796-873).
struct ElimResult {
    /// oracle `m_params`.
    params: Vec<ExprId>,
    /// oracle `m_aux2nested`: auxName → `I Ds` (canonical over m_params).
    aux2nested: HashMap<NameId, ExprId>,
    /// The enlarged (aux) block's types.
    aux_types: Vec<InductiveType>,
    /// oracle `m_ngen`, advanced as `restore_nested` mints peel fvars.
    ngen: FVarIdGen,
}

impl<'a> ElimNestedInductiveFn<'a> {
    fn new(
        scratch: &'a mut Store,
        view: &'a EnvView<'a>,
        lparams: &[NameId],
        nparams: usize,
        types: &[InductiveType],
    ) -> Result<ElimNestedInductiveFn<'a>, KernelError> {
        let base = Some(view.store);
        let name0 = types.first().map(|t| t.name);
        let new_types = types.to_vec();
        let new_type_names = new_types.iter().map(|t| t.name).collect();
        let lvls = lparams_to_levels_id(scratch, base, lparams)?;
        Ok(ElimNestedInductiveFn {
            view,
            scratch,
            ngen: FVarIdGen::default(),
            params_lctx: LocalContext::default(),
            params: Vec::new(),
            nested_aux: Vec::new(),
            lvls,
            new_types,
            new_type_names,
            next_idx: 1,
            nparams,
            name0,
        })
    }

    fn base(&self) -> Option<&'a Store> {
        Some(self.view.store)
    }

    fn ill_formed(&self) -> KernelError {
        // oracle: inductive.cpp:906-908 (`throw_ill_formed`).
        KernelError::InvalidInductive {
            name: self.scratch.to_name(self.base(), self.name0),
            what: "invalid nested inductive datatype, ill-formed declaration",
        }
    }

    /// oracle: inductive.cpp:898-904 (`mk_unique_name`).
    fn mk_unique_name(&mut self, base_name: NameId) -> Result<NameId, KernelError> {
        loop {
            let r = append_index_after_id(
                self.scratch,
                self.base(),
                base_name,
                self.next_idx as usize,
            )?;
            self.next_idx += 1;
            if self.view.get(r).is_none() {
                return Ok(r);
            }
        }
    }

    /// oracle: inductive.cpp:1035-1043 (`get_params`) — peel `nparams`
    /// Π-binders into fresh fvars recorded in `lctx`. A free-standing
    /// function (explicit field refs, not `&mut self`) so a caller may
    /// point `lctx` at `self.params_lctx` or a fresh local one.
    #[allow(clippy::too_many_arguments)]
    fn get_params(
        scratch: &mut Store,
        base: Option<&Store>,
        ngen: &mut FVarIdGen,
        nparams: usize,
        name0: Option<NameId>,
        lctx: &mut LocalContext,
        mut ty: ExprId,
        g: &mut RecGuard,
    ) -> Result<(ExprId, Vec<ExprId>), KernelError> {
        let mut params = Vec::with_capacity(nparams);
        for _ in 0..nparams {
            let (bn, bt, body, bi) = match peel_forall(scratch, base, ty) {
                Some(p) => p,
                None => {
                    return Err(KernelError::InvalidInductive {
                        name: scratch.to_name(base, name0),
                        what: "incorrect number of parameters",
                    })
                }
            };
            let fv = lctx.mk_local_decl(scratch, base, ngen, bn, bt, bi)?;
            params.push(fv);
            ty = instantiate(scratch, base, body, fv, g)?;
        }
        Ok((ty, params))
    }

    /// oracle: inductive.cpp:910-913 (`replace_params`) — rewrite the
    /// per-constructor params `as_` back to the canonical `m_params`.
    fn replace_params(
        &mut self,
        e: ExprId,
        as_: &[ExprId],
        g: &mut RecGuard,
    ) -> Result<ExprId, KernelError> {
        let base = self.base();
        let t = abstract_fvars(self.scratch, base, e, as_, g)?;
        instantiate_rev(self.scratch, base, t, &self.params, g)
    }

    /// oracle: inductive.cpp:954-960 (`instantiate_pi_params`).
    fn instantiate_pi_params(
        &mut self,
        mut e: ExprId,
        params: &[ExprId],
        g: &mut RecGuard,
    ) -> Result<ExprId, KernelError> {
        let base = self.base();
        for _ in 0..params.len() {
            e = match self.scratch.expr_node(base, e) {
                Node::Forall { body, .. } => body,
                _ => return Err(self.ill_formed()),
            };
        }
        instantiate_rev(self.scratch, base, e, params, g)
    }

    /// oracle: inductive.cpp:920-952 (`is_nested_inductive_app`).
    fn is_nested_inductive_app(
        &mut self,
        e: ExprId,
        g: &mut RecGuard,
    ) -> Result<Option<InductiveVal>, KernelError> {
        let base = self.base();
        if !is_app(self.scratch, base, e) {
            return Ok(None);
        }
        let fn0 = get_app_fn(self.scratch, base, e);
        let fn_name = match const_name(self.scratch, base, fn0) {
            Some(n) => n,
            None => return Ok(None),
        };
        let info = match self.view.get(fn_name) {
            Some(ConstantInfo::Induct(v)) => v.clone(),
            _ => return Ok(None),
        };
        let args = get_app_args(self.scratch, base, e);
        let nparams = info
            .num_params
            .to_usize()
            .ok_or_else(|| self.ill_formed())?;
        if nparams > args.len() {
            return Ok(None);
        }
        let mut is_nested = false;
        let mut loose = false;
        for &a in &args[0..nparams] {
            // `has_loose_bvars(a)`: exact iff the packed range is 0 (a
            // saturated range is still nonzero — reported as loose).
            if self.scratch.expr_data(base, a).loose_bvar_range() != 0 {
                loose = true;
            }
            if expr_contains_new_type(self.scratch, base, a, &self.new_type_names, g)? {
                is_nested = true;
            }
        }
        if !is_nested {
            return Ok(None);
        }
        if loose {
            // oracle: inductive.cpp:949-950.
            return Err(KernelError::InvalidInductive {
                name: self.scratch.to_name(base, Some(fn_name)),
                what: "nested inductive parameters cannot contain local variables",
            });
        }
        Ok(Some(info))
    }

    /// oracle: inductive.cpp:963-1028 (`replace_if_nested`). If `e` is a
    /// nested occurrence `I Ds is`, return `Iaux As is` (creating aux
    /// types on first encounter), else `None`.
    fn replace_if_nested(
        &mut self,
        lctx: &LocalContext,
        as_: &[ExprId],
        e: ExprId,
        g: &mut RecGuard,
    ) -> Result<Option<ExprId>, KernelError> {
        let i_val = match self.is_nested_inductive_app(e, g)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let base = self.base();
        let args = get_app_args(self.scratch, base, e);
        let fn0 = get_app_fn(self.scratch, base, e);
        let (i_name, i_lvls) = match self.scratch.expr_node(base, fn0) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, self.scratch.level_list_at(base, levels).to_vec()),
            _ => return Ok(None),
        };
        let i_nparams = i_val
            .num_params
            .to_usize()
            .ok_or_else(|| self.ill_formed())?;
        // IAs = I Ds (the parametric prefix).
        let i_as = mk_app_spine(self.scratch, base, fn0, &args[0..i_nparams])?;
        let i_params = self.replace_params(i_as, as_, g)?;
        // Already lifted?
        let mut found: Option<NameId> = None;
        for &(p_expr, p_name) in &self.nested_aux {
            // module doc point 6: `Expr::structural_eq` -> `==`.
            if p_expr == i_params {
                found = Some(p_name);
                break;
            }
        }
        if let Some(aux_name) = found {
            let base = self.base();
            let levels_list = self.scratch.intern_level_list(base, &self.lvls)?;
            let aux_i = self.scratch.expr_const(base, Some(aux_name), levels_list)?;
            let aux_i = mk_app_spine(self.scratch, base, aux_i, as_)?;
            return Ok(Some(mk_app_spine(
                self.scratch,
                base,
                aux_i,
                &args[i_nparams..],
            )?));
        }
        // Copy every inductive `J` mutual with `I` into the block.
        let mut result: Option<ExprId> = None;
        let all = i_val.all.clone();
        for &j_name in &all {
            let j_ind = match self.view.get(j_name) {
                Some(ConstantInfo::Induct(v)) => v.clone(),
                _ => return Err(self.ill_formed()),
            };
            let base = self.base();
            let i_lvls_list = self.scratch.intern_level_list(base, &i_lvls)?;
            let j_const = self.scratch.expr_const(base, Some(j_name), i_lvls_list)?;
            let j_as = mk_app_spine(self.scratch, base, j_const, &args[0..i_nparams])?;
            let nested_pref = nested_prefix_id(self.scratch, base)?;
            let aux_prefix = name_append_id(self.scratch, base, nested_pref, j_name)?;
            let aux_j_name = self.mk_unique_name(aux_prefix)?;
            // auxJ_type = (Π As, J's index telescope with Ds substituted).
            let mut aux_j_type = instantiate_level_params(
                self.scratch,
                base,
                j_ind.val.ty,
                &j_ind.val.level_params,
                &i_lvls,
                g,
            )?;
            aux_j_type = self.instantiate_pi_params(aux_j_type, &args[0..i_nparams], g)?;
            aux_j_type = super::subst::mk_pi(self.scratch, base, lctx, as_, aux_j_type, g)?;
            let j_as_canon = self.replace_params(j_as, as_, g)?;
            self.nested_aux.push((j_as_canon, aux_j_name));
            if j_name == i_name {
                let base = self.base();
                let lvls_list2 = self.scratch.intern_level_list(base, &self.lvls)?;
                let aux_i = self
                    .scratch
                    .expr_const(base, Some(aux_j_name), lvls_list2)?;
                let aux_i = mk_app_spine(self.scratch, base, aux_i, as_)?;
                result = Some(mk_app_spine(self.scratch, base, aux_i, &args[i_nparams..])?);
            }
            // Copy J's constructors (still referencing J; fixed when the
            // aux type is itself dequeued in the main loop).
            let mut aux_ctors: Vec<(NameId, ExprId)> = Vec::with_capacity(j_ind.ctors.len());
            for &j_cnstr_name in &j_ind.ctors {
                let c_val = match self.view.get(j_cnstr_name) {
                    Some(ConstantInfo::Ctor(v)) => v.clone(),
                    _ => return Err(self.ill_formed()),
                };
                let base = self.base();
                let aux_c_name =
                    replace_prefix_id(self.scratch, base, j_cnstr_name, j_name, Some(aux_j_name))?
                        .ok_or_else(|| self.ill_formed())?;
                let mut aux_c_type = instantiate_level_params(
                    self.scratch,
                    base,
                    c_val.val.ty,
                    &c_val.val.level_params,
                    &i_lvls,
                    g,
                )?;
                aux_c_type = self.instantiate_pi_params(aux_c_type, &args[0..i_nparams], g)?;
                aux_c_type = super::subst::mk_pi(self.scratch, base, lctx, as_, aux_c_type, g)?;
                aux_ctors.push((aux_c_name, aux_c_type));
            }
            self.new_type_names.insert(aux_j_name);
            self.new_types.push(InductiveType {
                name: aux_j_name,
                ty: aux_j_type,
                ctors: aux_ctors,
            });
        }
        match result {
            Some(r) => Ok(Some(r)),
            None => Err(self.ill_formed()),
        }
    }

    /// oracle: inductive.cpp:1030-1033 (`replace_all_nested`).
    fn replace_all_nested(
        &mut self,
        lctx: &LocalContext,
        as_: &[ExprId],
        e: ExprId,
        g: &mut RecGuard,
    ) -> Result<ExprId, KernelError> {
        if let Some(r) = self.replace_if_nested(lctx, as_, e, g)? {
            return Ok(r);
        }
        let base = self.base();
        match self.scratch.expr_node(base, e) {
            Node::App { f, arg } => {
                let (f2, a2) = g.enter(|g| {
                    Ok((
                        self.replace_all_nested(lctx, as_, f, g)?,
                        self.replace_all_nested(lctx, as_, arg, g)?,
                    ))
                })?;
                self.scratch.expr_app(base, f2, a2)
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (bt2, bd2) = g.enter(|g| {
                    Ok((
                        self.replace_all_nested(lctx, as_, binder_type, g)?,
                        self.replace_all_nested(lctx, as_, body, g)?,
                    ))
                })?;
                self.scratch
                    .expr_lam(base, binder_name, bt2, bd2, binder_info)
            }
            Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (bt2, bd2) = g.enter(|g| {
                    Ok((
                        self.replace_all_nested(lctx, as_, binder_type, g)?,
                        self.replace_all_nested(lctx, as_, body, g)?,
                    ))
                })?;
                self.scratch
                    .expr_forall(base, binder_name, bt2, bd2, binder_info)
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let (t2, v2, b2) = g.enter(|g| {
                    Ok((
                        self.replace_all_nested(lctx, as_, ty, g)?,
                        self.replace_all_nested(lctx, as_, value, g)?,
                        self.replace_all_nested(lctx, as_, body, g)?,
                    ))
                })?;
                self.scratch.expr_let(base, decl_name, t2, v2, b2, non_dep)
            }
            Node::MData { data, expr } => {
                let e2 = g.enter(|g| self.replace_all_nested(lctx, as_, expr, g))?;
                self.scratch.expr_mdata(base, data, e2)
            }
            node @ (Node::Proj { .. } | Node::ProjBig { .. }) => {
                let (type_name, structure) = match node {
                    Node::Proj {
                        type_name,
                        structure,
                        ..
                    }
                    | Node::ProjBig {
                        type_name,
                        structure,
                        ..
                    } => (type_name, structure),
                    _ => unreachable!(),
                };
                let idx_nat = match node {
                    Node::Proj { idx, .. } => Nat::from(idx as u64),
                    Node::ProjBig { idx, .. } => self.scratch.nat_at(base, idx).clone(),
                    _ => unreachable!(),
                };
                let s2 = g.enter(|g| self.replace_all_nested(lctx, as_, structure, g))?;
                self.scratch.expr_proj(base, type_name, &idx_nat, s2)
            }
            _ => Ok(e),
        }
    }

    /// oracle: inductive.cpp:1045-1076 (`operator()`).
    fn run(&mut self, g: &mut RecGuard) -> Result<ElimResult, KernelError> {
        if self.new_types.is_empty() {
            // oracle: inductive.cpp:1050.
            return Err(KernelError::InvalidInductive {
                name: Arc::new(Name::Anonymous),
                what: "empty inductive block",
            });
        }
        let base = self.base();
        // Initialize m_params / m_params_lctx from the first type.
        let type0 = self.new_types[0].ty;
        let (_, params) = Self::get_params(
            self.scratch,
            base,
            &mut self.ngen,
            self.nparams,
            self.name0,
            &mut self.params_lctx,
            type0,
            g,
        )?;
        self.params = params;
        // Main elimination loop — `new_types` grows as aux types are
        // pushed, so re-read `.len()` each iteration.
        let mut qhead = 0;
        while qhead < self.new_types.len() {
            let ind_type = self.new_types[qhead].clone();
            let mut new_cnstrs: Vec<(NameId, ExprId)> = Vec::with_capacity(ind_type.ctors.len());
            for &(cn, ct) in &ind_type.ctors {
                let mut lctx = LocalContext::default();
                // Re-create the params per constructor to preserve
                // binder_info (oracle comment inductive.cpp:1062-1064).
                let (cnstr_type, as_) = Self::get_params(
                    self.scratch,
                    base,
                    &mut self.ngen,
                    self.nparams,
                    self.name0,
                    &mut lctx,
                    ct,
                    g,
                )?;
                let new_ct = self.replace_all_nested(&lctx, &as_, cnstr_type, g)?;
                let new_ct = super::subst::mk_pi(self.scratch, base, &lctx, &as_, new_ct, g)?;
                new_cnstrs.push((cn, new_ct));
            }
            self.new_types[qhead] = InductiveType {
                name: ind_type.name,
                ty: ind_type.ty,
                ctors: new_cnstrs,
            };
            qhead += 1;
        }
        let aux2nested = self.nested_aux.iter().map(|&(e, n)| (n, e)).collect();
        Ok(ElimResult {
            params: self.params.clone(),
            aux2nested,
            aux_types: self.new_types.clone(),
            ngen: std::mem::take(&mut self.ngen),
        })
    }
}

// ---------------------------------------------------------------------
// Restoring nested inductives into the real (outer) result — oracle:
// inductive.cpp:796-873 (`elim_nested_inductive_result`'s `restore_*`
// methods) plus :1088-1180 (`mk_aux_rec_name_map`, `process_rec`,
// `environment::add_inductive`'s nested branch). `aux_env: &Environment`
// becomes `aux_map: &HashMap<NameId, ConstantInfo>` (module doc point
// 3); `env: &mut Environment` + `added: &mut Vec<Arc<Name>>` become
// `extra: &mut HashMap<NameId, ConstantInfo>` (module doc point 1).
// ---------------------------------------------------------------------

/// oracle: inductive.cpp:811-818 (`get_nested_if_aux_constructor`).
fn get_nested_if_aux_constructor(
    aux_map: &HashMap<NameId, ConstantInfo>,
    c: NameId,
    aux2nested: &HashMap<NameId, ExprId>,
) -> Option<(ExprId, NameId)> {
    let cv = match aux_map.get(&c) {
        Some(ConstantInfo::Ctor(v)) => v,
        _ => return None,
    };
    let aux_i_name = cv.induct;
    let nested = aux2nested.get(&aux_i_name)?;
    Some((*nested, aux_i_name))
}

impl ElimResult {
    /// oracle: inductive.cpp:820-826 (`restore_constructor_name`).
    fn restore_constructor_name(
        &self,
        scratch: &mut Store,
        base: Option<&Store>,
        aux_map: &HashMap<NameId, ConstantInfo>,
        cnstr_name: NameId,
    ) -> Result<NameId, KernelError> {
        let fail = |scratch: &Store| KernelError::InvalidInductive {
            name: scratch.to_name(base, Some(cnstr_name)),
            what: "invalid nested constructor",
        };
        let (nested, aux_i_name) =
            get_nested_if_aux_constructor(aux_map, cnstr_name, &self.aux2nested)
                .ok_or_else(|| fail(scratch))?;
        let i_name = match const_name(scratch, base, get_app_fn(scratch, base, nested)) {
            Some(n) => n,
            None => return Err(fail(scratch)),
        };
        replace_prefix_id(scratch, base, cnstr_name, aux_i_name, Some(i_name))?
            .ok_or_else(|| fail(scratch))
    }

    /// oracle: inductive.cpp:837-870 (the `restore_nested` `replace`
    /// callback). Returns the rewritten node or `None` to keep descending.
    #[allow(clippy::too_many_arguments)]
    fn restore_node(
        &self,
        scratch: &mut Store,
        base: Option<&Store>,
        t: ExprId,
        as_: &[ExprId],
        aux_map: &HashMap<NameId, ConstantInfo>,
        rec_map: &HashMap<NameId, NameId>,
        g: &mut RecGuard,
    ) -> Result<Option<ExprId>, KernelError> {
        // Aux recursor constant → renamed real recursor.
        if let Node::Const {
            name: Some(name),
            levels,
        } = scratch.expr_node(base, t)
        {
            if let Some(&rec_name) = rec_map.get(&name) {
                return Ok(Some(scratch.expr_const(base, Some(rec_name), levels)?));
            }
        }
        let fn0 = get_app_fn(scratch, base, t);
        let fn_name = match const_name(scratch, base, fn0) {
            Some(n) => n,
            None => return Ok(None),
        };
        // Aux type application `Iaux As is` → `I Ds is`.
        if let Some(&nested) = self.aux2nested.get(&fn_name) {
            let args = get_app_args(scratch, base, t);
            if args.len() < self.params.len() {
                return Err(KernelError::InvalidInductive {
                    name: scratch.to_name(base, Some(fn_name)),
                    what: "ill-formed nested application",
                });
            }
            let tmp = abstract_fvars(scratch, base, nested, &self.params, g)?;
            let new_head = instantiate_rev(scratch, base, tmp, as_, g)?;
            return Ok(Some(mk_app_spine(
                scratch,
                base,
                new_head,
                &args[self.params.len()..],
            )?));
        }
        // Aux constructor application `Iaux.c As is` → `I.c Ds is`.
        if let Some((nested, aux_i_name)) =
            get_nested_if_aux_constructor(aux_map, fn_name, &self.aux2nested)
        {
            let args = get_app_args(scratch, base, t);
            if args.len() < self.params.len() {
                return Err(KernelError::InvalidInductive {
                    name: scratch.to_name(base, Some(fn_name)),
                    what: "ill-formed nested application",
                });
            }
            let tmp = abstract_fvars(scratch, base, nested, &self.params, g)?;
            let new_nested = instantiate_rev(scratch, base, tmp, as_, g)?;
            let new_head_fn = get_app_fn(scratch, base, new_nested);
            let (i_name, i_levels) = match scratch.expr_node(base, new_head_fn) {
                Node::Const {
                    name: Some(n),
                    levels,
                } => (n, levels),
                _ => {
                    return Err(KernelError::InvalidInductive {
                        name: scratch.to_name(base, Some(fn_name)),
                        what: "ill-formed nested application",
                    })
                }
            };
            let i_args = get_app_args(scratch, base, new_nested);
            let new_fn_name = replace_prefix_id(scratch, base, fn_name, aux_i_name, Some(i_name))?
                .ok_or_else(|| KernelError::InvalidInductive {
                    name: scratch.to_name(base, Some(fn_name)),
                    what: "ill-formed nested application",
                })?;
            let new_fn = scratch.expr_const(base, Some(new_fn_name), i_levels)?;
            let head = mk_app_spine(scratch, base, new_fn, &i_args)?;
            return Ok(Some(mk_app_spine(
                scratch,
                base,
                head,
                &args[self.params.len()..],
            )?));
        }
        Ok(None)
    }

    /// The `replace` walk of `restore_nested` (top-down, value-depth ⇒
    /// guarded); `&self` throughout (no mutation), so the recursion needs
    /// no borrow gymnastics.
    #[allow(clippy::too_many_arguments)]
    fn restore_replace(
        &self,
        scratch: &mut Store,
        base: Option<&Store>,
        e: ExprId,
        as_: &[ExprId],
        aux_map: &HashMap<NameId, ConstantInfo>,
        rec_map: &HashMap<NameId, NameId>,
        g: &mut RecGuard,
    ) -> Result<ExprId, KernelError> {
        if let Some(r) = self.restore_node(scratch, base, e, as_, aux_map, rec_map, g)? {
            return Ok(r);
        }
        match scratch.expr_node(base, e) {
            Node::App { f, arg } => {
                let (f2, a2) = g.enter(|g| {
                    Ok((
                        self.restore_replace(scratch, base, f, as_, aux_map, rec_map, g)?,
                        self.restore_replace(scratch, base, arg, as_, aux_map, rec_map, g)?,
                    ))
                })?;
                scratch.expr_app(base, f2, a2)
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (bt2, bd2) = g.enter(|g| {
                    Ok((
                        self.restore_replace(scratch, base, binder_type, as_, aux_map, rec_map, g)?,
                        self.restore_replace(scratch, base, body, as_, aux_map, rec_map, g)?,
                    ))
                })?;
                scratch.expr_lam(base, binder_name, bt2, bd2, binder_info)
            }
            Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (bt2, bd2) = g.enter(|g| {
                    Ok((
                        self.restore_replace(scratch, base, binder_type, as_, aux_map, rec_map, g)?,
                        self.restore_replace(scratch, base, body, as_, aux_map, rec_map, g)?,
                    ))
                })?;
                scratch.expr_forall(base, binder_name, bt2, bd2, binder_info)
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let (t2, v2, b2) = g.enter(|g| {
                    Ok((
                        self.restore_replace(scratch, base, ty, as_, aux_map, rec_map, g)?,
                        self.restore_replace(scratch, base, value, as_, aux_map, rec_map, g)?,
                        self.restore_replace(scratch, base, body, as_, aux_map, rec_map, g)?,
                    ))
                })?;
                scratch.expr_let(base, decl_name, t2, v2, b2, non_dep)
            }
            Node::MData { data, expr } => {
                let e2 = g.enter(|g| {
                    self.restore_replace(scratch, base, expr, as_, aux_map, rec_map, g)
                })?;
                scratch.expr_mdata(base, data, e2)
            }
            node @ (Node::Proj { .. } | Node::ProjBig { .. }) => {
                let (type_name, structure) = match node {
                    Node::Proj {
                        type_name,
                        structure,
                        ..
                    }
                    | Node::ProjBig {
                        type_name,
                        structure,
                        ..
                    } => (type_name, structure),
                    _ => unreachable!(),
                };
                let idx_nat = match node {
                    Node::Proj { idx, .. } => Nat::from(idx as u64),
                    Node::ProjBig { idx, .. } => scratch.nat_at(base, idx).clone(),
                    _ => unreachable!(),
                };
                let s2 = g.enter(|g| {
                    self.restore_replace(scratch, base, structure, as_, aux_map, rec_map, g)
                })?;
                scratch.expr_proj(base, type_name, &idx_nat, s2)
            }
            _ => Ok(e),
        }
    }

    /// oracle: inductive.cpp:828-872 (`restore_nested`) — peel the block
    /// params, rewrite aux occurrences, re-wrap the telescope. `&mut
    /// self` (unlike `restore_node`/`restore_replace`): mints peel fvars
    /// via `self.ngen`.
    #[allow(clippy::too_many_arguments)]
    fn restore_nested(
        &mut self,
        scratch: &mut Store,
        base: Option<&Store>,
        e: ExprId,
        aux_map: &HashMap<NameId, ConstantInfo>,
        rec_map: &HashMap<NameId, NameId>,
        g: &mut RecGuard,
    ) -> Result<ExprId, KernelError> {
        let mut lctx = LocalContext::default();
        let mut as_: Vec<ExprId> = Vec::with_capacity(self.params.len());
        let pi = matches!(scratch.expr_node(base, e), Node::Forall { .. });
        let mut cur = e;
        for _ in 0..self.params.len() {
            let (bn, bt, body, bi) = match scratch.expr_node(base, cur) {
                Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                }
                | Node::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => (binder_name, binder_type, body, binder_info),
                _ => {
                    return Err(KernelError::InvalidInductive {
                        name: Arc::new(Name::Anonymous),
                        what: "ill-formed nested declaration",
                    })
                }
            };
            let fv = lctx.mk_local_decl(scratch, base, &mut self.ngen, bn, bt, bi)?;
            as_.push(fv);
            cur = instantiate(scratch, base, body, fv, g)?;
        }
        let body2 = self.restore_replace(scratch, base, cur, &as_, aux_map, rec_map, g)?;
        if pi {
            super::subst::mk_pi(scratch, base, &lctx, &as_, body2, g)
        } else {
            super::subst::mk_lambda(scratch, base, &lctx, &as_, body2, g)
        }
    }
}

/// oracle: inductive.cpp:1088-1114 (`mk_aux_rec_name_map`). Only called
/// when aux types were created, so the recursors for indices `>= ntypes`
/// are the aux ones to rename.
fn mk_aux_rec_name_map(
    scratch: &mut Store,
    base: Option<&Store>,
    aux_map: &HashMap<NameId, ConstantInfo>,
    orig_types: &[InductiveType],
) -> Result<(Vec<NameId>, HashMap<NameId, NameId>), KernelError> {
    let ntypes = orig_types.len();
    let main_name = orig_types[0].name;
    let main_iv = match aux_map.get(&main_name) {
        Some(ConstantInfo::Induct(v)) => v.clone(),
        _ => {
            return Err(KernelError::InvalidInductive {
                name: scratch.to_name(base, Some(main_name)),
                what: "missing aux inductive",
            })
        }
    };
    let mut old_rec_names = Vec::new();
    let mut rec_map = HashMap::new();
    let mut next_idx = 1usize;
    for (i, &ind_name) in main_iv.all.iter().enumerate() {
        if i >= ntypes {
            let old = mk_rec_name_id(scratch, base, ind_name)?;
            let main_rec = mk_rec_name_id(scratch, base, main_name)?;
            let new = append_index_after_id(scratch, base, main_rec, next_idx)?;
            next_idx += 1;
            old_rec_names.push(old);
            rec_map.insert(old, new);
        }
    }
    Ok((old_rec_names, rec_map))
}

/// oracle: inductive.cpp:1131-1153 (`process_rec`) — restore one
/// recursor (main or aux) into the outer `extra` accumulator.
#[allow(clippy::too_many_arguments)]
fn process_rec(
    scratch: &mut Store,
    view: &EnvView,
    res: &mut ElimResult,
    aux_map: &HashMap<NameId, ConstantInfo>,
    rec_name: NameId,
    rec_map: &HashMap<NameId, NameId>,
    all_ind_names: &[NameId],
    extra: &mut HashMap<NameId, ConstantInfo>,
    g: &mut RecGuard,
) -> Result<(), KernelError> {
    let base = Some(view.store);
    let new_rec_name = rec_map.get(&rec_name).copied().unwrap_or(rec_name);
    let rv = match aux_map.get(&rec_name) {
        Some(ConstantInfo::Rec(v)) => v.clone(),
        _ => {
            return Err(KernelError::InvalidInductive {
                name: scratch.to_name(base, Some(rec_name)),
                what: "missing aux recursor",
            })
        }
    };
    let new_rec_type = res.restore_nested(scratch, base, rv.val.ty, aux_map, rec_map, g)?;
    let renamed = new_rec_name != rec_name;
    let mut new_rules = Vec::with_capacity(rv.rules.len());
    for rule in &rv.rules {
        let new_rhs = res.restore_nested(scratch, base, rule.rhs, aux_map, rec_map, g)?;
        let new_cnstr = if renamed {
            res.restore_constructor_name(scratch, base, aux_map, rule.ctor)?
        } else {
            rule.ctor
        };
        new_rules.push(RecursorRule {
            ctor: new_cnstr,
            nfields: rule.nfields.clone(),
            rhs: new_rhs,
        });
    }
    check_name(scratch, &extend_view(view, extra), new_rec_name)?;
    let new_rv = RecursorVal {
        val: ConstantVal {
            name: new_rec_name,
            level_params: rv.val.level_params.clone(),
            ty: new_rec_type,
        },
        all: all_ind_names.to_vec(),
        num_params: rv.num_params.clone(),
        num_indices: rv.num_indices.clone(),
        num_motives: rv.num_motives.clone(),
        num_minors: rv.num_minors.clone(),
        rules: new_rules,
        k: rv.k,
        is_unsafe: rv.is_unsafe,
    };
    extra.insert(new_rec_name, ConstantInfo::Rec(new_rv));
    Ok(())
}

/// oracle: inductive.cpp:1124-1180 (the nested branch of
/// `environment::add_inductive`). Copies the restored inductives, their
/// constructors, and their recursors (main + renamed aux) into the
/// outer `extra` accumulator.
#[allow(clippy::too_many_arguments)]
fn restore_nested_inductives(
    scratch: &mut Store,
    view: &EnvView,
    aux_map: &HashMap<NameId, ConstantInfo>,
    res: &mut ElimResult,
    orig_types: &[InductiveType],
    extra: &mut HashMap<NameId, ConstantInfo>,
    g: &mut RecGuard,
) -> Result<(), KernelError> {
    let base = Some(view.store);
    let all_ind_names: Vec<NameId> = orig_types.iter().map(|t| t.name).collect();
    let (aux_rec_names, rec_map) = mk_aux_rec_name_map(scratch, base, aux_map, orig_types)?;
    let empty_map: HashMap<NameId, NameId> = HashMap::new();
    for ind_type in orig_types {
        let iv = match aux_map.get(&ind_type.name) {
            Some(ConstantInfo::Induct(v)) => v.clone(),
            _ => {
                return Err(KernelError::InvalidInductive {
                    name: scratch.to_name(base, Some(ind_type.name)),
                    what: "missing aux inductive",
                })
            }
        };
        check_name(scratch, &extend_view(view, extra), ind_type.name)?;
        let new_iv = InductiveVal {
            val: ConstantVal {
                name: iv.val.name,
                level_params: iv.val.level_params.clone(),
                ty: iv.val.ty,
            },
            num_params: iv.num_params.clone(),
            num_indices: iv.num_indices.clone(),
            all: all_ind_names.clone(),
            ctors: iv.ctors.clone(),
            num_nested: iv.num_nested.clone(),
            is_rec: iv.is_rec,
            is_unsafe: iv.is_unsafe,
            is_reflexive: iv.is_reflexive,
        };
        extra.insert(ind_type.name, ConstantInfo::Induct(new_iv));
        for &cnstr_name in &iv.ctors {
            let cv = match aux_map.get(&cnstr_name) {
                Some(ConstantInfo::Ctor(v)) => v.clone(),
                _ => {
                    return Err(KernelError::InvalidInductive {
                        name: scratch.to_name(base, Some(cnstr_name)),
                        what: "missing aux constructor",
                    })
                }
            };
            let new_type = res.restore_nested(scratch, base, cv.val.ty, aux_map, &empty_map, g)?;
            check_name(scratch, &extend_view(view, extra), cnstr_name)?;
            let new_cv = ConstructorVal {
                val: ConstantVal {
                    name: cv.val.name,
                    level_params: cv.val.level_params.clone(),
                    ty: new_type,
                },
                induct: cv.induct,
                cidx: cv.cidx.clone(),
                num_params: cv.num_params.clone(),
                num_fields: cv.num_fields.clone(),
                is_unsafe: cv.is_unsafe,
            };
            extra.insert(cnstr_name, ConstantInfo::Ctor(new_cv));
        }
        let rec_name = mk_rec_name_id(scratch, base, ind_type.name)?;
        process_rec(
            scratch,
            view,
            res,
            aux_map,
            rec_name,
            &rec_map,
            &all_ind_names,
            extra,
            g,
        )?;
    }
    for &aux_rec in &aux_rec_names {
        process_rec(
            scratch,
            view,
            res,
            aux_map,
            aux_rec,
            &rec_map,
            &all_ind_names,
            extra,
            g,
        )?;
    }
    Ok(())
}

/// The pipeline entry (oracle: `environment::add_inductive`,
/// inductive.cpp:1116-1181; mirrored per the brief's Interfaces note —
/// see module doc points 1-3). Eliminates nested occurrences, runs the
/// ordinary machinery on the enlarged block, and (when nesting occurred)
/// restores the real nested inductives — returning every `ConstantInfo`
/// to admit rather than mutating a shared environment.
pub fn add_inductive(
    scratch: &mut Store,
    view: &EnvView,
    lparams: Vec<NameId>,
    nparams: Nat,
    types: Vec<InductiveType>,
    is_unsafe: bool,
) -> Result<Vec<ConstantInfo>, KernelError> {
    let base = Some(view.store);
    let nparams_usize = match nparams.to_usize() {
        Some(v) => v,
        None => {
            let name0 = scratch.to_name(base, types.first().map(|t| t.name));
            return Err(KernelError::InvalidInductive {
                name: name0,
                what: "too many parameters",
            });
        }
    };
    let mut g = RecGuard::new();
    // Eliminate nested occurrences (borrow of `scratch` released with `elim`).
    let mut res = {
        let mut elim =
            ElimNestedInductiveFn::new(&mut *scratch, view, &lparams, nparams_usize, &types)?;
        elim.run(&mut g)?
    };
    let nnested = res.aux2nested.len();
    if nnested == 0 {
        // No nesting: the aux block is the (rebuilt, structurally
        // identical) original. Admit it as-is, returning the full set.
        let admitted = run_add_inductive_fn(
            scratch,
            view,
            lparams,
            nparams,
            res.aux_types.clone(),
            is_unsafe,
            Nat::from(0u64),
        )?;
        Ok(admitted.into_values().collect())
    } else {
        // Nesting: run the machinery on the enlarged block against a
        // FRESH `extra` map (module doc point 3 — the "scratch env"),
        // then restore the real nested inductives into the OUTER `extra`.
        let aux_map = run_add_inductive_fn(
            &mut *scratch,
            view,
            lparams,
            nparams,
            res.aux_types.clone(),
            is_unsafe,
            Nat::from(nnested as u64),
        )?;
        let mut extra: HashMap<NameId, ConstantInfo> = HashMap::new();
        restore_nested_inductives(
            scratch, view, &aux_map, &mut res, &types, &mut extra, &mut g,
        )?;
        Ok(extra.into_values().collect())
    }
}

#[cfg(test)]
mod tests;
