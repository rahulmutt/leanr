use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::sync::Arc;

use crate::{KernelError, Name, RecGuard};

/// Universe level (oracle: src/Lean/Level.lean:90-103). The oracle also
/// stores a computed `data` u64 (hash/depth/flags); we drop it on
/// decode and recompute in M1b. `MVar` is decoded faithfully; the
/// checker rejects metavariables, not the parser (spec).
///
/// No derived Eq/Ord/Hash: adversarial depth makes derived recursive
/// traversals a stack-overflow hazard; M1b adds hash-consed comparison.
/// Manual iterative Debug impl (see Name for pattern): depth is
/// attacker-controlled and recursion is forbidden.
pub enum Level {
    Zero,
    Succ(Arc<Level>),
    Max(Arc<Level>, Arc<Level>),
    IMax(Arc<Level>, Arc<Level>),
    Param(Arc<Name>),
    MVar(Arc<Name>),
}

/// Manual (non-derived) impl: iterative formatting instead of recursing
/// into Arc children, so it stays safe on adversarially deep chains.
/// Renders as `Level::Zero`, `Level::Succ(..)`, etc.
impl fmt::Debug for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Level::Zero => f.write_str("Level::Zero"),
            Level::Succ(_) => f.write_str("Level::Succ(..)"),
            Level::Max(_, _) => f.write_str("Level::Max(.., ..)"),
            Level::IMax(_, _) => f.write_str("Level::IMax(.., ..)"),
            Level::Param(n) => write!(f, "Level::Param({:?})", n),
            Level::MVar(n) => write!(f, "Level::MVar({:?})", n),
        }
    }
}

impl Drop for Level {
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Level>> = Vec::new();
        take_level_children(self, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_level_children(&mut owned, &mut stack);
            }
        }
    }
}

/// Detach `Arc<Level>` children into `stack`, leaving cheap leaves
/// behind so the node's own drop is O(1).
fn take_level_children(l: &mut Level, stack: &mut Vec<Arc<Level>>) {
    let zero = || Arc::new(Level::Zero);
    match l {
        Level::Zero | Level::Param(_) | Level::MVar(_) => {}
        Level::Succ(a) => stack.push(mem::replace(a, zero())),
        Level::Max(a, b) | Level::IMax(a, b) => {
            stack.push(mem::replace(a, zero()));
            stack.push(mem::replace(b, zero()));
        }
    }
}

// ---------------------------------------------------------------------
// M1b Task 2: equality, hashing, normalize, is_equivalent.
//
// Oracle: src/kernel/level.cpp at githash b4812ae53eea93439ad5dce5a5c26591c31cb697
// (tag v4.32.0-rc1). Every ported fn below cites its oracle line range.
//
// Recursion discipline (crate-wide invariant, see lib.rs/guard.rs):
// the only sanctioned recursive descent is through `RecGuard::enter`.
// `to_offset` is the one exception explicitly sanctioned by the task
// brief: it is an iterative loop over `Succ`, never recursion, so it
// needs no guard and can't be affected by adversarial depth.
// ---------------------------------------------------------------------

impl Level {
    /// oracle: kernel/level.cpp:33 (`mk_succ`) — trivial smart
    /// constructor; `Succ` has no normalization rule of its own.
    pub fn mk_succ(l: Arc<Level>) -> Arc<Level> {
        Arc::new(Level::Succ(l))
    }

    /// oracle: kernel/level.cpp:67-73 (`to_offset`) — peel `Succ` nodes
    /// into `(base, k)` with `l == succ^k(base)`. Iterative (a `while`
    /// loop, not recursion) so it stays safe on adversarially deep succ
    /// chains without needing a `RecGuard`. `k` saturates at `u64::MAX`
    /// instead of overflowing/panicking (checked-arithmetic discipline);
    /// no real or adversarial chain reaches that count in practice.
    pub fn to_offset(l: &Arc<Level>) -> (&Arc<Level>, u64) {
        let mut cur = l;
        let mut k: u64 = 0;
        while let Level::Succ(inner) = cur.as_ref() {
            cur = inner;
            k = k.saturating_add(1);
        }
        (cur, k)
    }

    /// Trivial, non-recursive: `Zero` is a leaf variant.
    pub fn is_zero(&self) -> bool {
        matches!(self, Level::Zero)
    }

    /// oracle: kernel/level.cpp:160-172 (`is_not_zero`). Guarded: `Max`
    /// recurses into both children, `IMax` into its rhs only, matching
    /// the oracle exactly.
    pub fn is_never_zero(l: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
        match l.as_ref() {
            Level::Zero | Level::Param(_) | Level::MVar(_) => Ok(false),
            Level::Succ(_) => Ok(true),
            Level::Max(a, b) => {
                let (a, b) = (Arc::clone(a), Arc::clone(b));
                g.enter(|g| Ok(Level::is_never_zero(&a, g)? || Level::is_never_zero(&b, g)?))
            }
            Level::IMax(_, rhs) => {
                let rhs = Arc::clone(rhs);
                g.enter(|g| Level::is_never_zero(&rhs, g))
            }
        }
    }

    /// oracle: kernel/level.cpp:125-150 (`operator==`). We add an
    /// `Arc::ptr_eq` fast path (the brief's requirement; analogous to
    /// the oracle's own `is_eqp` pointer check at line 128) and skip the
    /// oracle's cached-hash/cached-depth pre-checks (lines 126-127, 137)
    /// since this port does not retain those caches (see the module doc
    /// comment on `Level` above) — dropping them changes performance,
    /// not the result.
    pub fn structural_eq(
        a: &Arc<Level>,
        b: &Arc<Level>,
        g: &mut RecGuard,
    ) -> Result<bool, KernelError> {
        if Arc::ptr_eq(a, b) {
            return Ok(true);
        }
        match (a.as_ref(), b.as_ref()) {
            (Level::Zero, Level::Zero) => Ok(true),
            (Level::Param(na), Level::Param(nb)) => Ok(na == nb),
            (Level::MVar(na), Level::MVar(nb)) => Ok(na == nb),
            (Level::Succ(la), Level::Succ(lb)) => {
                let (la, lb) = (Arc::clone(la), Arc::clone(lb));
                g.enter(|g| Level::structural_eq(&la, &lb, g))
            }
            (Level::Max(la, ra), Level::Max(lb, rb))
            | (Level::IMax(la, ra), Level::IMax(lb, rb)) => {
                let (la, ra, lb, rb) = (
                    Arc::clone(la),
                    Arc::clone(ra),
                    Arc::clone(lb),
                    Arc::clone(rb),
                );
                g.enter(|g| {
                    Ok(Level::structural_eq(&la, &lb, g)? && Level::structural_eq(&ra, &rb, g)?)
                })
            }
            _ => Ok(false),
        }
    }

    /// oracle: no single oracle line — the C++ runtime caches a hash in
    /// each level's `data` word (`lean_level_mk_data`, level.cpp:44-50)
    /// and reads it back via `lean_level_hash`/`level::hash()` (line 37).
    /// We dropped that cache on decode (module doc comment), so this
    /// recomputes an equivalent structural hash directly, guarded so it
    /// can report `DeepRecursion` instead of overflowing the stack. Reuses
    /// `Name`'s own `Hash` impl (name.rs) for the `Param`/`MVar` leaves,
    /// as instructed.
    pub fn hash_val(l: &Arc<Level>, g: &mut RecGuard) -> Result<u64, KernelError> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn go(
            l: &Arc<Level>,
            state: &mut DefaultHasher,
            g: &mut RecGuard,
        ) -> Result<(), KernelError> {
            match l.as_ref() {
                Level::Zero => {
                    state.write_u8(0);
                    Ok(())
                }
                Level::Succ(a) => {
                    state.write_u8(1);
                    let a = Arc::clone(a);
                    g.enter(|g| go(&a, state, g))
                }
                Level::Max(a, b) => {
                    state.write_u8(2);
                    let (a, b) = (Arc::clone(a), Arc::clone(b));
                    g.enter(|g| {
                        go(&a, state, g)?;
                        go(&b, state, g)
                    })
                }
                Level::IMax(a, b) => {
                    state.write_u8(3);
                    let (a, b) = (Arc::clone(a), Arc::clone(b));
                    g.enter(|g| {
                        go(&a, state, g)?;
                        go(&b, state, g)
                    })
                }
                Level::Param(n) => {
                    state.write_u8(4);
                    n.hash(state);
                    Ok(())
                }
                Level::MVar(n) => {
                    state.write_u8(5);
                    n.hash(state);
                    Ok(())
                }
            }
        }

        let mut state = DefaultHasher::new();
        go(l, &mut state, g)?;
        Ok(state.finish())
    }

    /// oracle: kernel/level.cpp:81-98 (`mk_max`) — the normalizing
    /// binary smart constructor for `max`.
    pub fn mk_max_pair(
        l1: Arc<Level>,
        l2: Arc<Level>,
        g: &mut RecGuard,
    ) -> Result<Arc<Level>, KernelError> {
        if is_explicit(&l1) && is_explicit(&l2) {
            let k1 = Level::to_offset(&l1).1;
            let k2 = Level::to_offset(&l2).1;
            return Ok(if k1 >= k2 { l1 } else { l2 });
        }
        if Level::structural_eq(&l1, &l2, g)? {
            return Ok(l1);
        }
        if matches!(l1.as_ref(), Level::Zero) {
            return Ok(l2);
        }
        if matches!(l2.as_ref(), Level::Zero) {
            return Ok(l1);
        }
        if let Level::Max(a, b) = l2.as_ref() {
            if Level::structural_eq(a, &l1, g)? || Level::structural_eq(b, &l1, g)? {
                return Ok(Arc::clone(&l2));
            }
        }
        if let Level::Max(a, b) = l1.as_ref() {
            if Level::structural_eq(a, &l2, g)? || Level::structural_eq(b, &l2, g)? {
                return Ok(Arc::clone(&l1));
            }
        }
        let same_base = {
            let (b1, _) = Level::to_offset(&l1);
            let (b2, _) = Level::to_offset(&l2);
            Level::structural_eq(b1, b2, g)?
        };
        if same_base {
            let k1 = Level::to_offset(&l1).1;
            let k2 = Level::to_offset(&l2).1;
            return Ok(if k1 > k2 { l1 } else { l2 });
        }
        Ok(Arc::new(Level::Max(l1, l2)))
    }

    /// oracle: kernel/level.cpp:112-121 (`mk_imax`) — the normalizing
    /// binary smart constructor for `imax`.
    pub fn mk_imax_pair(
        l1: Arc<Level>,
        l2: Arc<Level>,
        g: &mut RecGuard,
    ) -> Result<Arc<Level>, KernelError> {
        if Level::is_never_zero(&l2, g)? {
            return Level::mk_max_pair(l1, l2, g);
        }
        if matches!(l2.as_ref(), Level::Zero) {
            return Ok(l2); // imax u 0 = 0 for any u
        }
        if matches!(l1.as_ref(), Level::Zero) || is_one(&l1) {
            return Ok(l2); // imax 0 u = imax 1 u = u for any u
        }
        if Level::structural_eq(&l1, &l2, g)? {
            return Ok(l1); // imax u u = u
        }
        Ok(Arc::new(Level::IMax(l1, l2)))
    }

    /// oracle: kernel/level.cpp:302-323 (`instantiate`), specialized to
    /// a `(params, args)` substitution list. Mirrors the oracle's
    /// `replace_level_fn` skip rule (level.cpp:352-370): only descend
    /// where `has_param` holds, and rebuild through the smart
    /// constructors exactly like `update_succ`/`update_max`
    /// (level.cpp:286-300) do — so a substitution renormalizes locally
    /// exactly as the oracle's does. Returns the same `Arc` unchanged
    /// (checked via `Arc::ptr_eq`) when nothing in the subtree changed,
    /// preserving decoder sharing (brief's sharing discipline).
    pub fn instantiate_params(
        l: &Arc<Level>,
        params: &[Arc<Name>],
        args: &[Arc<Level>],
        g: &mut RecGuard,
    ) -> Result<Arc<Level>, KernelError> {
        if !Level::has_param(l, g)? {
            return Ok(Arc::clone(l));
        }
        match l.as_ref() {
            // has_param(l) is false for Zero/MVar, so these arms are
            // unreachable in practice; kept as a safe (non-panicking)
            // fallback rather than `unreachable!()` since this match is
            // keyed off adversarially-decoded data.
            Level::Zero | Level::MVar(_) => Ok(Arc::clone(l)),
            Level::Param(n) => {
                for (p, a) in params.iter().zip(args.iter()) {
                    if p.as_ref() == n.as_ref() {
                        return Ok(Arc::clone(a));
                    }
                }
                Ok(Arc::clone(l))
            }
            Level::Succ(a) => {
                let a = Arc::clone(a);
                let a2 = g.enter(|g| Level::instantiate_params(&a, params, args, g))?;
                if Arc::ptr_eq(&a2, &a) {
                    Ok(Arc::clone(l))
                } else {
                    Ok(Level::mk_succ(a2))
                }
            }
            Level::Max(a, b) => {
                let (a, b) = (Arc::clone(a), Arc::clone(b));
                let (a2, b2) = g.enter(|g| {
                    Ok((
                        Level::instantiate_params(&a, params, args, g)?,
                        Level::instantiate_params(&b, params, args, g)?,
                    ))
                })?;
                if Arc::ptr_eq(&a2, &a) && Arc::ptr_eq(&b2, &b) {
                    Ok(Arc::clone(l))
                } else {
                    Level::mk_max_pair(a2, b2, g)
                }
            }
            Level::IMax(a, b) => {
                let (a, b) = (Arc::clone(a), Arc::clone(b));
                let (a2, b2) = g.enter(|g| {
                    Ok((
                        Level::instantiate_params(&a, params, args, g)?,
                        Level::instantiate_params(&b, params, args, g)?,
                    ))
                })?;
                if Arc::ptr_eq(&a2, &a) && Arc::ptr_eq(&b2, &b) {
                    Ok(Arc::clone(l))
                } else {
                    Level::mk_imax_pair(a2, b2, g)
                }
            }
        }
    }

    /// oracle: no single oracle line — `has_mvar`/`lean_level_has_mvar`
    /// read the runtime-cached bit from the `data` word built by
    /// `lean_level_mk_data` (level.cpp:44-50, combining children's
    /// flags at construction time). We dropped that cache on decode, so
    /// this is the guarded structural walk that maintains the same
    /// invariant ("does this tree contain an `MVar` anywhere").
    pub fn has_mvar(l: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
        match l.as_ref() {
            Level::Zero | Level::Param(_) => Ok(false),
            Level::MVar(_) => Ok(true),
            Level::Succ(a) => {
                let a = Arc::clone(a);
                g.enter(|g| Level::has_mvar(&a, g))
            }
            Level::Max(a, b) | Level::IMax(a, b) => {
                let (a, b) = (Arc::clone(a), Arc::clone(b));
                g.enter(|g| Ok(Level::has_mvar(&a, g)? || Level::has_mvar(&b, g)?))
            }
        }
    }

    /// oracle: no single oracle line — see `has_mvar` above;
    /// `has_param`/`lean_level_has_param` is the same cached-bit read,
    /// mirrored here as the guarded structural walk.
    pub fn has_param(l: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
        match l.as_ref() {
            Level::Zero | Level::MVar(_) => Ok(false),
            Level::Param(_) => Ok(true),
            Level::Succ(a) => {
                let a = Arc::clone(a);
                g.enter(|g| Level::has_param(&a, g))
            }
            Level::Max(a, b) | Level::IMax(a, b) => {
                let (a, b) = (Arc::clone(a), Arc::clone(b));
                g.enter(|g| Ok(Level::has_param(&a, g)? || Level::has_param(&b, g)?))
            }
        }
    }

    /// oracle: kernel/level.cpp:439-501 (`normalize`).
    pub fn normalize(l: &Arc<Level>, g: &mut RecGuard) -> Result<Arc<Level>, KernelError> {
        let (base, k) = Level::to_offset(l);
        match base.as_ref() {
            // oracle returns `l` (the untouched original) unchanged here,
            // not a rebuilt copy — preserves sharing trivially.
            Level::Zero | Level::Param(_) | Level::MVar(_) => Ok(Arc::clone(l)),
            Level::IMax(lhs, rhs) => {
                let (lhs, rhs) = (Arc::clone(lhs), Arc::clone(rhs));
                g.enter(|g| {
                    let l1 = Level::normalize(&lhs, g)?;
                    let l2 = Level::normalize(&rhs, g)?;
                    let im = Level::mk_imax_pair(l1, l2, g)?;
                    Ok(mk_succ_n(im, k))
                })
            }
            Level::Max(_, _) => {
                let base = Arc::clone(base);
                g.enter(|g| normalize_max(&base, k, g))
            }
            // `to_offset` strips every `Succ` layer by construction, so
            // `base` can never itself be `Succ`; this is a code
            // invariant (not data-dependent), matching the oracle's own
            // `lean_unreachable()` at the same spot (level.cpp:443).
            Level::Succ(_) => unreachable!("to_offset strips all Succ nodes"),
        }
    }

    /// oracle: kernel/level.cpp:503-506 (`is_equivalent`):
    /// `lhs == rhs || normalize(lhs) == normalize(rhs)`.
    pub fn is_equivalent(
        a: &Arc<Level>,
        b: &Arc<Level>,
        g: &mut RecGuard,
    ) -> Result<bool, KernelError> {
        if Level::structural_eq(a, b, g)? {
            return Ok(true);
        }
        let na = Level::normalize(a, g)?;
        let nb = Level::normalize(b, g)?;
        Level::structural_eq(&na, &nb, g)
    }
}

/// oracle: kernel/level.cpp:54-65 (`is_explicit`) — true iff `l` is a
/// pure numeral `succ^k(zero)`. Implemented via `to_offset` (equivalent
/// by construction: `is_explicit` recurses through `Succ` exactly as
/// `to_offset` loops through it) so it needs no extra recursion/guard.
fn is_explicit(l: &Arc<Level>) -> bool {
    matches!(Level::to_offset(l).0.as_ref(), Level::Zero)
}

/// oracle: kernel/level.cpp:106-107 (`mk_level_one`/`is_one`) — `1` is
/// `succ(zero)`. Implemented via `to_offset` for the same reason as
/// `is_explicit` above.
fn is_one(l: &Arc<Level>) -> bool {
    let (base, k) = Level::to_offset(l);
    k == 1 && matches!(base.as_ref(), Level::Zero)
}

/// Kind rank mirroring the oracle's `level_kind` enum order (level.h:30:
/// `Zero, Succ, Max, IMax, Param, MVar`), used by `is_norm_lt` below.
fn kind_rank(l: &Level) -> u8 {
    match l {
        Level::Zero => 0,
        Level::Succ(_) => 1,
        Level::Max(..) => 2,
        Level::IMax(..) => 3,
        Level::Param(_) => 4,
        Level::MVar(_) => 5,
    }
}

/// Total order on `Name`s mirroring the oracle's `name::cmp_core`
/// (util/name.cpp:191-216, at the same pinned githash): compares
/// components root-to-leaf, `Str` sorts after `Num` when kinds differ
/// at a given position, otherwise lexicographic within kind; a name
/// that is a strict prefix of the other sorts first. `Name`'s own
/// fields are public (see name.rs / leanr_olean's interp.rs, which
/// already constructs `Name::Str`/`Name::Num` directly from outside
/// the module), so this can match on them without a new method on
/// `Name` itself. Iterative (collects components into a `Vec`, as
/// name.rs's own `Display` impl does) so it stays safe on
/// adversarially deep parent chains.
fn name_cmp(a: &Name, b: &Name) -> Ordering {
    fn components(n: &Name) -> Vec<&Name> {
        let mut v = Vec::new();
        let mut cur = n;
        loop {
            match cur {
                Name::Anonymous => break,
                Name::Str { parent, .. } | Name::Num { parent, .. } => {
                    v.push(cur);
                    cur = parent;
                }
            }
        }
        v.reverse();
        v
    }
    let ca = components(a);
    let cb = components(b);
    for (x, y) in ca.iter().zip(cb.iter()) {
        let ord = match (x, y) {
            (Name::Str { part: pa, .. }, Name::Str { part: pb, .. }) => pa.cmp(pb),
            (Name::Num { part: pa, .. }, Name::Num { part: pb, .. }) => pa.0.cmp(&pb.0),
            (Name::Str { .. }, Name::Num { .. }) => Ordering::Greater,
            (Name::Num { .. }, Name::Str { .. }) => Ordering::Less,
            _ => unreachable!("components() never pushes Anonymous"),
        };
        if ord != Ordering::Equal {
            return ord;
        }
    }
    ca.len().cmp(&cb.len())
}

/// oracle: kernel/level.cpp:380-403 (`is_norm_lt`) — the total order
/// `normalize` sorts `max` arguments by. Guarded (recurses into
/// `Max`/`IMax` children).
///
/// Kind ranks follow the oracle's literal `level_kind` enum order
/// (level.h:30: `Zero, Succ, Max, IMax, Param, MVar`, restricted here
/// to the kinds a `to_offset` base can have — `Succ` never appears).
/// NOTE: the task brief's port note paraphrased this ordering as
/// "Zero < Param < MVar < Max < IMax", which does not match the cited
/// oracle enum order; re-reading level.h:30 confirms the enum order
/// above, so we followed the oracle literally rather than the brief's
/// paraphrase. This choice cannot affect observable behavior either
/// way: `is_norm_lt` only needs to be *some* valid strict total order
/// for `normalize`'s own internal canonicalization (it sorts, then
/// dedups adjacent equal-base runs) — any consistent total order
/// produces the same canonical result, so this does not need to
/// match the oracle's tie-break byte-for-byte to be a faithful port.
fn is_norm_lt(a: &Arc<Level>, b: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
    if Arc::ptr_eq(a, b) {
        return Ok(false);
    }
    let (l1, k1) = Level::to_offset(a);
    let (l2, k2) = Level::to_offset(b);
    if Level::structural_eq(l1, l2, g)? {
        return Ok(k1 < k2);
    }
    let (r1, r2) = (kind_rank(l1), kind_rank(l2));
    if r1 != r2 {
        return Ok(r1 < r2);
    }
    match (l1.as_ref(), l2.as_ref()) {
        (Level::Param(na), Level::Param(nb)) => Ok(name_cmp(na, nb) == Ordering::Less),
        (Level::MVar(na), Level::MVar(nb)) => Ok(name_cmp(na, nb) == Ordering::Less),
        (Level::Max(la, ra), Level::Max(lb, rb)) | (Level::IMax(la, ra), Level::IMax(lb, rb)) => {
            let (la, ra, lb, rb) = (
                Arc::clone(la),
                Arc::clone(ra),
                Arc::clone(lb),
                Arc::clone(rb),
            );
            g.enter(|g| {
                if !Level::structural_eq(&la, &lb, g)? {
                    is_norm_lt(&la, &lb, g)
                } else {
                    is_norm_lt(&ra, &rb, g)
                }
            })
        }
        // Zero/Zero: unreachable (structural_eq above would have caught
        // it); kept as a safe non-panicking default rather than a hard
        // assert since `l1`/`l2` are adversarially-decoded data.
        _ => Ok(false),
    }
}

/// oracle: kernel/level.cpp:405-412 (`push_max_args`) — flatten nested
/// `Max` nodes into a flat argument list. Guarded (adversarially deep
/// `Max` chains recurse proportionally to depth).
fn push_max_args(l: &Arc<Level>, g: &mut RecGuard) -> Result<Vec<Arc<Level>>, KernelError> {
    match l.as_ref() {
        Level::Max(a, b) => {
            let (a, b) = (Arc::clone(a), Arc::clone(b));
            g.enter(|g| {
                let mut left = push_max_args(&a, g)?;
                let mut right = push_max_args(&b, g)?;
                left.append(&mut right);
                Ok(left)
            })
        }
        _ => Ok(vec![Arc::clone(l)]),
    }
}

/// oracle: kernel/level.cpp:431-437 (`mk_succ(level, unsigned)`) —
/// apply `Succ` `k` times. A loop over `k` (bounded by a `u64` already
/// produced by `to_offset`'s saturating counter), not recursion.
fn mk_succ_n(mut l: Arc<Level>, k: u64) -> Arc<Level> {
    for _ in 0..k {
        l = Level::mk_succ(l);
    }
    l
}

/// oracle: kernel/level.cpp:414-429 (`mk_max(buffer<level> const&)`) —
/// right-associate a flat, already-deduped argument list back into a
/// `max` tree via the binary smart constructor. A loop over `args`
/// (bounded by argument count), not recursion.
fn mk_max_list(args: Vec<Arc<Level>>, g: &mut RecGuard) -> Result<Arc<Level>, KernelError> {
    let n = args.len();
    if n == 0 {
        // Defensive: the oracle asserts non-empty (`push_max_args`
        // always yields >= 1 element for a well-formed `Max` node); we
        // never panic on this internal invariant either.
        return Ok(Arc::new(Level::Zero));
    }
    if n == 1 {
        return Ok(Arc::clone(&args[0]));
    }
    let mut r = Level::mk_max_pair(Arc::clone(&args[n - 2]), Arc::clone(&args[n - 1]), g)?;
    let mut i = n - 2;
    while i > 0 {
        i -= 1;
        r = Level::mk_max_pair(Arc::clone(&args[i]), r, g)?;
    }
    Ok(r)
}

/// oracle: kernel/level.cpp:439-500, `Max` branch of `normalize`. Split
/// out of `Level::normalize` for readability; called already inside a
/// `g.enter` frame.
fn normalize_max(base: &Arc<Level>, k: u64, g: &mut RecGuard) -> Result<Arc<Level>, KernelError> {
    let todo = push_max_args(base, g)?;
    let mut args: Vec<Arc<Level>> = Vec::new();
    for a in &todo {
        let na = Level::normalize(a, g)?;
        let mut flat = push_max_args(&na, g)?;
        args.append(&mut flat);
    }

    // Sort by is_norm_lt. `sort_by` needs a full `Ordering` from our
    // strict less-than, and needs to be infallible, so we derive
    // Ordering from two one-directional comparisons and stash the
    // first error to propagate after the sort (the array's order no
    // longer matters once we know we're going to return `Err`).
    let mut err: Option<KernelError> = None;
    args.sort_by(|x, y| {
        if err.is_some() {
            return Ordering::Equal;
        }
        match is_norm_lt(x, y, g) {
            Ok(true) => return Ordering::Less,
            Ok(false) => {}
            Err(e) => {
                err = Some(e);
                return Ordering::Equal;
            }
        }
        match is_norm_lt(y, x, g) {
            Ok(true) => Ordering::Greater,
            Ok(false) => Ordering::Equal,
            Err(e) => {
                err = Some(e);
                Ordering::Equal
            }
        }
    });
    if let Some(e) = err {
        return Err(e);
    }

    let mut rargs: Vec<Arc<Level>> = Vec::new();
    let mut i: usize = 0;
    if is_explicit(&args[i]) {
        // find max explicit universe
        while i + 1 < args.len() && is_explicit(&args[i + 1]) {
            i += 1;
        }
        let k_max = Level::to_offset(&args[i]).1;
        // an explicit universe k_max is subsumed by any succ^k'(l) with
        // k' >= k_max (every level's value is >= 0).
        let mut j = i + 1;
        while j < args.len() {
            if Level::to_offset(&args[j]).1 >= k_max {
                break;
            }
            j += 1;
        }
        if j < args.len() {
            i += 1;
        }
    }
    rargs.push(Arc::clone(&args[i]));
    let (mut prev_base, mut prev_k) = {
        let (b, o) = Level::to_offset(&args[i]);
        (Arc::clone(b), o)
    };
    i += 1;
    while i < args.len() {
        let (curr_base, curr_k) = {
            let (b, o) = Level::to_offset(&args[i]);
            (Arc::clone(b), o)
        };
        if Level::structural_eq(&prev_base, &curr_base, g)? {
            if prev_k < curr_k {
                prev_k = curr_k;
                prev_base = curr_base;
                rargs.pop();
                rargs.push(Arc::clone(&args[i]));
            }
        } else {
            prev_base = curr_base;
            prev_k = curr_k;
            rargs.push(Arc::clone(&args[i]));
        }
        i += 1;
    }

    let rargs: Vec<Arc<Level>> = rargs.into_iter().map(|a| mk_succ_n(a, k)).collect();
    mk_max_list(rargs, g)
}

#[cfg(test)]
mod m1b_tests {
    use super::*;
    use crate::{KernelError, RecGuard};
    use std::sync::Arc;

    // `Name::from_str` doesn't exist (see name.rs): `Name` has no
    // constructor helpers at all, just the plain enum variants, which
    // are public (leanr_olean's interp.rs already builds `Name::Str`
    // directly from another crate). Build a single-component name with
    // an `Anonymous` parent by hand instead.
    fn nm(s: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })
    }
    fn p(s: &str) -> Arc<Level> {
        Arc::new(Level::Param(nm(s)))
    }
    fn z() -> Arc<Level> {
        Arc::new(Level::Zero)
    }
    fn s(l: Arc<Level>) -> Arc<Level> {
        Level::mk_succ(l)
    }
    fn max(a: Arc<Level>, b: Arc<Level>) -> Arc<Level> {
        Arc::new(Level::Max(a, b))
    }
    fn imax(a: Arc<Level>, b: Arc<Level>) -> Arc<Level> {
        Arc::new(Level::IMax(a, b))
    }
    fn equiv(a: &Arc<Level>, b: &Arc<Level>) -> bool {
        Level::is_equivalent(a, b, &mut RecGuard::new()).unwrap()
    }

    #[test]
    fn equivalence_table() {
        // max is commutative/idempotent up to normalization
        assert!(equiv(&max(p("u"), p("v")), &max(p("v"), p("u"))));
        assert!(equiv(&max(p("u"), p("u")), &p("u")));
        // succ distributes over max under normalization
        assert!(equiv(&s(max(p("u"), p("v"))), &max(s(p("u")), s(p("v")))));
        // imax with succ rhs is max (rhs never zero)
        assert!(equiv(&imax(p("u"), s(p("v"))), &max(p("u"), s(p("v")))));
        // imax u 0 = 0
        assert!(equiv(&imax(p("u"), z()), &z()));
        // imax 0 u = u
        assert!(equiv(&imax(z(), p("u")), &p("u")));
        // distinct params are NOT equivalent
        assert!(!equiv(&p("u"), &p("v")));
        assert!(!equiv(&s(p("u")), &p("u")));
    }

    #[test]
    fn structural_eq_and_hash_agree() {
        let mut g = RecGuard::new();
        let a = max(s(p("u")), imax(p("v"), z()));
        let b = max(s(p("u")), imax(p("v"), z()));
        assert!(Level::structural_eq(&a, &b, &mut g).unwrap());
        assert_eq!(
            Level::hash_val(&a, &mut g).unwrap(),
            Level::hash_val(&b, &mut g).unwrap()
        );
    }

    #[test]
    fn instantiate_params_substitutes() {
        let mut g = RecGuard::new();
        let u = nm("u");
        let l = max(Arc::new(Level::Param(Arc::clone(&u))), z());
        let r = Level::instantiate_params(&l, &[u], &[s(z())], &mut g).unwrap();
        assert!(equiv(&r, &s(z())));
    }

    #[test]
    fn adversarial_depth_errors_not_crashes() {
        let mut l = z();
        for _ in 0..2_000_000 {
            l = s(l);
        }
        // to_offset peels iteratively — must not be affected by depth
        assert_eq!(Level::to_offset(&l).1, 2_000_000);
        // a 2M-deep *alternating* tree exceeds the guard in normalize
        let mut t = z();
        for i in 0..2_000_000u64 {
            t = if i % 2 == 0 { s(t) } else { max(t, z()) };
        }
        assert_eq!(
            Level::normalize(&t, &mut RecGuard::new()).unwrap_err(),
            KernelError::DeepRecursion
        );
    }

    // Not in the brief's table verbatim, but the brief's self-review
    // checklist explicitly asks whether Arc-sharing is "tested or at
    // least exercised" — these two make it an explicit assertion rather
    // than an incidental property.
    #[test]
    fn instantiate_params_preserves_sharing_when_unchanged() {
        let mut g = RecGuard::new();
        let l = max(p("u"), s(p("v")));
        let other = nm("w"); // not present in `l` at all
        let r = Level::instantiate_params(&l, &[other], &[z()], &mut g).unwrap();
        assert!(Arc::ptr_eq(&l, &r));
    }

    #[test]
    fn normalize_preserves_sharing_when_already_normal() {
        let mut g = RecGuard::new();
        let l = p("u");
        let r = Level::normalize(&l, &mut g).unwrap();
        assert!(Arc::ptr_eq(&l, &r));
    }
}
