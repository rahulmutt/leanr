//! Scratch region → base promotion (spec §2's `add_core` primitive).
//! `Store::scratch()` already reads/interns through `base` everywhere
//! (Tasks 2-7 built the `base: Option<&Store>` threading in); what's
//! missing is the reverse direction — copying a scratch-region term
//! (and every scratch name/level/pool row it references) permanently
//! into the persistent `Store` once a declaration is accepted.

use super::terms::Node;
use super::{ExprId, LevelId, NameId, Store};
use crate::KernelError;

/// Translate one leaf `NameId` from `scratch` into `base`: a persistent
/// id passes through unchanged (no work, no base mutation); a scratch id
/// is rebuilt via `to_name` (routes through `base` for any persistent
/// segments of the chain) and re-interned into `base` alone. `pub` per
/// the migration Task 6 brief — `bank::env::promote_constant_info` calls
/// this directly on `ConstantInfo`'s (never-anonymous, see `decl.rs`'s
/// module doc) declaration-position `NameId` fields, which is why the
/// signature takes a plain `NameId` rather than the `Option<NameId>`
/// leaves an expression tree can carry (`promote_name_opt` below handles
/// those, and is defined in terms of this function).
pub fn promote_name(base: &mut Store, scratch: &Store, id: NameId) -> Result<NameId, KernelError> {
    if !id.is_scratch() {
        return Ok(id);
    }
    let name = scratch.to_name(Some(base), Some(id));
    // `name` is non-`Anonymous` (it was rebuilt from a real `NameRow`),
    // so `intern_name` always returns `Some` here — mirrors `decl.rs`'s
    // `intern_name_req`'s identical "reject, don't assert" posture on
    // the same never-actually-`None` case.
    base.intern_name(None, &name)?
        .ok_or(KernelError::BankExhausted)
}

/// `promote_name`, but for the `Option<NameId>` leaves an expression
/// tree can carry (`Name::Anonymous` fvar/mvar ids, binder names, proj
/// type names) — `None` (anonymous) passes through untouched.
fn promote_name_opt(
    base: &mut Store,
    scratch: &Store,
    id: Option<NameId>,
) -> Result<Option<NameId>, KernelError> {
    match id {
        None => Ok(None),
        Some(nid) => promote_name(base, scratch, nid).map(Some),
    }
}

/// Translate one `LevelId` from `scratch` into `base`, same
/// pass-through-if-persistent shape as `promote_name`. `pub` per the
/// migration Task 6 brief (exact signature specified there); already
/// took a plain `LevelId` (no `Option` — a level tree is never
/// "anonymous" the way a name leaf can be), so no `_opt` variant is
/// needed here.
pub fn promote_level(
    base: &mut Store,
    scratch: &Store,
    id: LevelId,
) -> Result<LevelId, KernelError> {
    if !id.is_scratch() {
        return Ok(id);
    }
    let level = scratch.to_level(Some(base), id);
    base.intern_level(None, &level)
}

/// Copy a scratch-region term (Task 9 / spec §2's `add_core` promotion
/// primitive) — and every scratch name/level/pool row it transitively
/// references — into the persistent `base`, returning the equivalent
/// base-region `ExprId`. Persistent ids pass through unchanged
/// (including the id `promote` itself just returned, so repeated calls
/// are idempotent). Iterative two-phase (`Enter`/`Exit`) explicit-stack
/// walk — exactly `intern_expr`/`to_expr`'s shape (terms.rs) — so
/// attacker-depth scratch terms can't blow the native stack; a memo
/// keyed by scratch `ExprId` gives dedup/stability (same scratch id ⇒
/// same promoted id every time).
///
/// Lifecycle contract: once `promote` has run, the ids it minted in
/// `scratch` are no longer canonical with respect to this
/// `(base, scratch)` pair — `base` now holds a *persistent* id for the
/// same term that `scratch` still answers with a *scratch* id, so the
/// two stores disagree and must not both be consulted afterward.
/// Callers must not keep interning through `scratch` against this
/// `base` past this point; per spec §2's "drop wholesale" lifecycle,
/// `scratch` (its table and all id-keyed caches) must be dropped at
/// declaration completion. `promote` is meant to be the last operation
/// performed on a scratch region before that drop — phase 2's
/// `add_core` calls it once per admitted root and then discards the
/// scratch store.
pub fn promote(base: &mut Store, scratch: &Store, id: ExprId) -> Result<ExprId, KernelError> {
    use std::collections::HashMap;
    enum Frame {
        Enter(ExprId),
        Exit(ExprId),
    }
    let mut memo: HashMap<ExprId, ExprId> = HashMap::new();
    let mut out: Vec<ExprId> = Vec::new();
    let mut stack = vec![Frame::Enter(id)];
    while let Some(fr) = stack.pop() {
        match fr {
            Frame::Enter(sid) => {
                if !sid.is_scratch() {
                    out.push(sid);
                    continue;
                }
                if let Some(&pid) = memo.get(&sid) {
                    out.push(pid);
                    continue;
                }
                match scratch.expr_node(Some(base), sid) {
                    Node::BVar { .. }
                    | Node::BVarBig { .. }
                    | Node::FVar { .. }
                    | Node::MVar { .. }
                    | Node::Sort { .. }
                    | Node::Const { .. }
                    | Node::LitNat { .. }
                    | Node::LitStr { .. } => stack.push(Frame::Exit(sid)),
                    Node::App { f, arg } => {
                        stack.push(Frame::Exit(sid));
                        stack.push(Frame::Enter(arg));
                        stack.push(Frame::Enter(f));
                    }
                    Node::Lam {
                        binder_type, body, ..
                    }
                    | Node::Forall {
                        binder_type, body, ..
                    } => {
                        stack.push(Frame::Exit(sid));
                        stack.push(Frame::Enter(body));
                        stack.push(Frame::Enter(binder_type));
                    }
                    Node::LetE {
                        ty, value, body, ..
                    } => {
                        stack.push(Frame::Exit(sid));
                        stack.push(Frame::Enter(body));
                        stack.push(Frame::Enter(value));
                        stack.push(Frame::Enter(ty));
                    }
                    Node::MData { expr, .. } => {
                        stack.push(Frame::Exit(sid));
                        stack.push(Frame::Enter(expr));
                    }
                    Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                        stack.push(Frame::Exit(sid));
                        stack.push(Frame::Enter(structure));
                    }
                }
            }
            Frame::Exit(sid) => {
                // Read the scratch node FIRST into an owned `Node`
                // (Copy) — the borrow of `base` this needs ends here,
                // before any of the `&mut base` intern calls below.
                let node = scratch.expr_node(Some(base), sid);
                let pid = match node {
                    Node::BVar { idx } => base.expr_bvar(None, &crate::Nat::from(idx as u64))?,
                    Node::BVarBig { idx } => {
                        let n = scratch.nat_at(Some(base), idx).clone();
                        base.expr_bvar(None, &n)?
                    }
                    Node::FVar { id: n } => {
                        let n = promote_name_opt(base, scratch, n)?;
                        base.expr_fvar(None, n)?
                    }
                    Node::MVar { id: n } => {
                        let n = promote_name_opt(base, scratch, n)?;
                        base.expr_mvar(None, n)?
                    }
                    Node::Sort { level } => {
                        let l = promote_level(base, scratch, level)?;
                        base.expr_sort(None, l)?
                    }
                    Node::Const { name, levels } => {
                        let n = promote_name_opt(base, scratch, name)?;
                        // Copy the pooled list out first: `level_list_at`
                        // borrows `base` immutably (routing), which must
                        // end before `promote_level`'s `&mut base` calls.
                        let src: Vec<LevelId> = scratch.level_list_at(Some(base), levels).to_vec();
                        let mut level_ids = Vec::with_capacity(src.len());
                        for l in src {
                            level_ids.push(promote_level(base, scratch, l)?);
                        }
                        let ls = base.intern_level_list(None, &level_ids)?;
                        base.expr_const(None, n, ls)?
                    }
                    Node::App { .. } => {
                        let arg = out.pop().expect("child pushed by Enter");
                        let f = out.pop().expect("child pushed by Enter");
                        base.expr_app(None, f, arg)?
                    }
                    Node::Lam {
                        binder_name,
                        binder_info,
                        ..
                    } => {
                        let body = out.pop().expect("child pushed by Enter");
                        let binder_type = out.pop().expect("child pushed by Enter");
                        let n = promote_name_opt(base, scratch, binder_name)?;
                        base.expr_lam(None, n, binder_type, body, binder_info)?
                    }
                    Node::Forall {
                        binder_name,
                        binder_info,
                        ..
                    } => {
                        let body = out.pop().expect("child pushed by Enter");
                        let binder_type = out.pop().expect("child pushed by Enter");
                        let n = promote_name_opt(base, scratch, binder_name)?;
                        base.expr_forall(None, n, binder_type, body, binder_info)?
                    }
                    Node::LetE {
                        decl_name, non_dep, ..
                    } => {
                        // Task 9 brief's LetE spill note: the spill row
                        // is already resolved into `decl_name`/`body`
                        // by `expr_node` above; `body` was walked as an
                        // ordinary child, so all that's left is
                        // translating `decl_name` and re-spilling via
                        // `base.expr_let`.
                        let body = out.pop().expect("child pushed by Enter");
                        let value = out.pop().expect("child pushed by Enter");
                        let ty = out.pop().expect("child pushed by Enter");
                        let n = promote_name_opt(base, scratch, decl_name)?;
                        base.expr_let(None, n, ty, value, body, non_dep)?
                    }
                    Node::LitNat { v } => {
                        let n = scratch.nat_at(Some(base), v).clone();
                        base.expr_lit_nat(None, &n)?
                    }
                    Node::LitStr { v } => {
                        let s = scratch.str_at(Some(base), v).to_string();
                        base.expr_lit_str(None, &s)?
                    }
                    Node::MData { data, .. } => {
                        let expr = out.pop().expect("child pushed by Enter");
                        let m = scratch.to_kvmap(Some(base), data);
                        let d = base.intern_kvmap(None, &m)?;
                        base.expr_mdata(None, d, expr)?
                    }
                    Node::Proj { type_name, idx, .. } => {
                        let structure = out.pop().expect("child pushed by Enter");
                        let n = promote_name_opt(base, scratch, type_name)?;
                        base.expr_proj(None, n, &crate::Nat::from(idx as u64), structure)?
                    }
                    Node::ProjBig { type_name, idx, .. } => {
                        let structure = out.pop().expect("child pushed by Enter");
                        let n = promote_name_opt(base, scratch, type_name)?;
                        let idx = scratch.nat_at(Some(base), idx).clone();
                        base.expr_proj(None, n, &idx, structure)?
                    }
                };
                memo.insert(sid, pid);
                out.push(pid);
            }
        }
    }
    Ok(out.pop().expect("root"))
}

#[cfg(test)]
mod tests {
    use super::promote;
    use crate::bank::Store;
    use crate::{Expr, Nat, RecGuard};
    use std::sync::Arc;

    #[test]
    fn scratch_reuses_persistent_ids() {
        let mut base = Store::persistent();
        let e = Expr::app(Expr::bvar(Nat::from(0u64)), Expr::bvar(Nat::from(1u64)));
        let pid = base.intern_expr(None, &e).unwrap();
        let mut scr = Store::scratch();
        let sid = scr.intern_expr(Some(&base), &e).unwrap();
        assert_eq!(sid, pid, "term already in base ⇒ base id, no scratch row");
        assert!(!sid.is_scratch());
    }

    #[test]
    fn scratch_novel_terms_get_scratch_ids_and_read_back() {
        let mut g = RecGuard::new();
        let mut base = Store::persistent();
        // Base knows the leaf, scratch builds a new parent over it.
        let leaf = Expr::bvar(Nat::from(0u64));
        let leaf_id = base.intern_expr(None, &leaf).unwrap();
        let mut scr = Store::scratch();
        let parent = Expr::app(Arc::clone(&leaf), leaf);
        let sid = scr.intern_expr(Some(&base), &parent).unwrap();
        assert!(sid.is_scratch());
        match scr.expr_node(Some(&base), sid) {
            crate::bank::terms::Node::App { f, arg } => {
                assert_eq!(f, leaf_id, "child resolves to the base id");
                assert_eq!(arg, leaf_id);
            }
            other => panic!("expected App, got {other:?}"),
        }
        let back = scr.to_expr(Some(&base), sid, &mut g).unwrap();
        assert!(Expr::structural_eq(
            &back,
            &Expr::app(Expr::bvar(Nat::from(0u64)), Expr::bvar(Nat::from(0u64))),
            &mut g
        )
        .unwrap());
    }

    #[test]
    fn promote_translates_scratch_terms_into_base() {
        let mut g = RecGuard::new();
        let mut base = Store::persistent();
        let mut scr = Store::scratch();
        let e = Expr::lam(
            Arc::new(crate::Name::Str {
                parent: Arc::new(crate::Name::Anonymous),
                part: "x".to_string(),
            }),
            Expr::bvar(Nat::from(0u64)),
            Expr::app(Expr::bvar(Nat::from(0u64)), Expr::bvar(Nat::from(0u64))),
            crate::BinderInfo::Default,
        );
        let sid = scr.intern_expr(Some(&base), &e).unwrap();
        assert!(sid.is_scratch());
        let pid = promote(&mut base, &scr, sid).unwrap();
        assert!(!pid.is_scratch());
        // The promoted term reads back structurally identical from base alone.
        let back = base.to_expr(None, pid, &mut g).unwrap();
        assert!(Expr::structural_eq(&back, &e, &mut g).unwrap());
        // Promoting a persistent id is the identity.
        assert_eq!(promote(&mut base, &scr, pid).unwrap(), pid);
        // Promotion is stable (memo/dedup): same input ⇒ same output id.
        assert_eq!(promote(&mut base, &scr, sid).unwrap(), pid);
    }

    #[test]
    fn dropping_scratch_frees_without_touching_base() {
        let base = Store::persistent();
        let before = base.terms_len();
        {
            let mut scr = Store::scratch();
            let e = Expr::app(Expr::bvar(Nat::from(5u64)), Expr::bvar(Nat::from(6u64)));
            let _ = scr.intern_expr(Some(&base), &e).unwrap();
        } // scratch dropped wholesale
        assert_eq!(
            base.terms_len(),
            before,
            "scratch interning never mutates base"
        );
    }
}
