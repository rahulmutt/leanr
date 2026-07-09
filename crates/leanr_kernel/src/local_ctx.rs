//! Id-twin local contexts (the bank-native counterpart of
//! `crate::local_ctx`; oracle: src/kernel/local_ctx.h,
//! src/kernel/local_ctx.cpp, pinned githash
//! b4812ae53eea93439ad5dce5a5c26591c31cb697, toolchain
//! leanprover/lean4:v4.32.0-rc1 — see ARCHITECTURE.md for the pin).
//! `Arc<Name>` -> `NameId`, `Arc<Expr>` -> `ExprId` via the phase-1 bank
//! (spec: docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md).
//! Porting is representation-only: no algorithmic change from
//! `local_ctx.rs`.
//!
//! `mk_pi`/`mk_lambda` (Arc `local_ctx.rs:181-208`, whose shared
//! `mk_binding` at `local_ctx.rs:225-249` calls `abstract_fvars` —
//! `crate::subst`) are NOT ported here: the bank's `bank/subst.rs`
//! (Task 3) doesn't exist yet. They will be implemented in Task 3's
//! file as free functions taking `&LocalContext`, per this task's
//! brief. Everything that does not depend on `abstract_fvars`
//! (`LocalDecl`, `LocalContext::{mk_local_decl, mk_let_decl, get}`,
//! `FVarIdGen`) is ported below.

use std::collections::HashMap;

use crate::bank::{ExprId, NameId, Store};
use crate::{BinderInfo, KernelError, Nat};

/// oracle: local_ctx.h:20-47 (`local_decl` — the `cdecl`/`ldecl`
/// inductive in the header comment). `id` is the fresh fvar id
/// (`local_decl::get_name`); `binder_name` is the user-facing name
/// (`get_user_name`) kept purely for pretty-printing/re-elaboration,
/// not looked at by the kernel's own equality/reduction. `id` is never
/// `Name::Anonymous` (freshly minted by `FVarIdGen`, see below), so it
/// bridges to a plain `NameId` (same posture as `bank/decl.rs`'s
/// declaration-position names); `binder_name` mirrors phase-1's
/// expr-row binder-name encoding instead (`Option<NameId>` — see
/// `terms.rs`'s `expr_lam`/`expr_forall`), since a source binder can
/// legitimately be anonymous.
#[derive(Debug, Clone)]
pub struct LocalDecl {
    pub id: NameId,
    pub binder_name: Option<NameId>,
    pub ty: ExprId,
    pub binder_info: BinderInfo,
    pub value: Option<ExprId>,
}

/// oracle: local_ctx.h:49+ (`local_ctx` — insertion-ordered map from
/// fvar id to `local_decl`). `decls` preserves declaration order (the
/// order `mk_pi`/`mk_lambda`'s telescope-folding relies on, Task 3);
/// `index` gives O(1) lookup by id.
#[derive(Default)]
pub struct LocalContext {
    decls: Vec<LocalDecl>,
    index: HashMap<NameId, usize>,
}

/// Fresh ids `_kernel_fresh.<n>` (oracle: type_checker.cpp:24
/// `g_kernel_fresh`, constructed as `name_generator(*g_kernel_fresh)` at
/// type_checker.cpp:46; `util/name_generator.cpp:16-30` — `m_next_idx`
/// starts at 0 and each `next()` call returns `name(prefix, idx)` then
/// increments, so the first id minted is `_kernel_fresh.0`).
#[derive(Default)]
pub struct FVarIdGen {
    next: u64,
}

/// Builds the next `_kernel_fresh.<n>` name and advances the counter
/// (id-twin of the Arc `fresh_fvar_id` free function). Kept as a free
/// function (not a public method), same rationale as the Arc side: the
/// brief's interface for `FVarIdGen` exposes only the `next: u64`
/// field, and the two `LocalContext` methods below are the only
/// callers. Re-interning `_kernel_fresh` on every call is idempotent —
/// the dedup pool returns the same `NameId` back — so this stays cheap
/// just like the Arc side's shared `Arc<Name>` prefix.
fn fresh_fvar_id(
    st: &mut Store,
    base: Option<&Store>,
    gen: &mut FVarIdGen,
) -> Result<NameId, KernelError> {
    let idx = gen.next;
    gen.next += 1;
    let prefix_str = st.intern_str(base, "_kernel_fresh")?;
    let prefix = st.name_str(base, None, prefix_str)?;
    let idx_id = st.intern_nat(base, &Nat::from(idx))?;
    st.name_num(base, Some(prefix), idx_id)
}

impl LocalContext {
    /// Record `decl` and return its `Expr::fvar` reference (oracle:
    /// `local_decl::mk_ref`, local_ctx.cpp:39-41 — `mk_fvar(get_name())`).
    fn push(
        &mut self,
        st: &mut Store,
        base: Option<&Store>,
        decl: LocalDecl,
    ) -> Result<ExprId, KernelError> {
        let id = decl.id;
        self.index.insert(id, self.decls.len());
        self.decls.push(decl);
        st.expr_fvar(base, Some(id))
    }

    /// oracle: local_ctx.h:64-66 (`mk_local_decl(name_generator&, name
    /// const&, expr const&, binder_info)` — the `cdecl` overload).
    pub fn mk_local_decl(
        &mut self,
        st: &mut Store,
        base: Option<&Store>,
        gen: &mut FVarIdGen,
        binder_name: Option<NameId>,
        ty: ExprId,
        bi: BinderInfo,
    ) -> Result<ExprId, KernelError> {
        let id = fresh_fvar_id(st, base, gen)?;
        self.push(
            st,
            base,
            LocalDecl {
                id,
                binder_name,
                ty,
                binder_info: bi,
                value: None,
            },
        )
    }

    /// oracle: local_ctx.h:68-70 (`mk_local_decl(name_generator&, name
    /// const&, expr const&, expr const& value)` — the `ldecl` overload).
    pub fn mk_let_decl(
        &mut self,
        st: &mut Store,
        base: Option<&Store>,
        gen: &mut FVarIdGen,
        binder_name: Option<NameId>,
        ty: ExprId,
        value: ExprId,
    ) -> Result<ExprId, KernelError> {
        let id = fresh_fvar_id(st, base, gen)?;
        self.push(
            st,
            base,
            LocalDecl {
                id,
                binder_name,
                ty,
                // oracle: local_ctx.cpp:35-37 — `get_info` reads the
                // packed runtime object regardless of cdecl/ldecl, but
                // Task 3's `mk_pi`/`mk_lambda` (mirroring the Arc
                // `decl.value.is_some()` branch) never reads
                // `binder_info` for a let-bound decl — it takes the
                // `mk_let` path unconditionally — so this value is
                // inert; `Default` is just a placeholder, exactly as
                // on the Arc side.
                binder_info: BinderInfo::Default,
                value: Some(value),
            },
        )
    }

    /// oracle: local_ctx.h:76-78 (`get_local_decl`/`find_local_decl`).
    pub fn get(&self, fvar_id: NameId) -> Option<&LocalDecl> {
        self.index.get(&fvar_id).map(|&i| &self.decls[i])
    }

    /// Support for the type checker's `flet<local_ctx> save_lctx(m_lctx,
    /// m_lctx)` idiom (type_checker.cpp:117/135/199/693 etc.): the
    /// checker extends the context under a binder and must pop those
    /// decls again on the way out. `save` records the current decl
    /// count; `restore` drops every decl added since (fvar ids are
    /// globally unique via `FVarIdGen`, so a dropped id is never
    /// reintroduced — the truncation is exact). Id-twin of the Arc
    /// port's `LocalContext::save`/`restore`
    /// (`crate::local_ctx.rs:154-164`) — NOT ported in Task 2 (that
    /// task's `LocalContext` doesn't need them; the checker, Task 4,
    /// does), added here per the module's own precedent rather than
    /// duplicated inside `bank/tc.rs`. `pub(crate)`: only the in-crate
    /// checker uses it.
    pub(crate) fn save(&self) -> usize {
        self.decls.len()
    }

    /// Restore to a `save` checkpoint, removing later decls from both
    /// the insertion-ordered `decls` and the id `index`.
    pub(crate) fn restore(&mut self, checkpoint: usize) {
        for decl in self.decls.drain(checkpoint..) {
            self.index.remove(&decl.id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bank::terms::Node;
    use crate::bank::Store;
    use crate::{BinderInfo, Nat};
    use std::sync::Arc;

    /// Build a single-component `Name` (no `Name::from_str` exists —
    /// see every prior task's test helpers).
    fn nm(s: &str) -> Arc<crate::Name> {
        Arc::new(crate::Name::Str {
            parent: Arc::new(crate::Name::Anonymous),
            part: s.to_string(),
        })
    }

    /// Fresh ids `_kernel_fresh.0, .1, ...`: bridge the bank's minted
    /// ids out with `to_name` (oracle: type_checker.cpp:24 — the Arc
    /// kernel's own `FVarIdGen`/`LocalContext` produced the same
    /// `_kernel_fresh.<n>` names before migration Task 8 deleted them;
    /// this direct pin is the independent assertion that survives that
    /// strip).
    #[test]
    fn fresh_ids_produce_expected_names() {
        let mut st = Store::persistent();
        let mut gen = FVarIdGen::default();
        let mut lctx = LocalContext::default();
        let ty = st.expr_lit_nat(None, &Nat::from(0u64)).unwrap();

        let fvar0 = lctx
            .mk_local_decl(&mut st, None, &mut gen, None, ty, BinderInfo::Default)
            .unwrap();
        let fvar1 = lctx
            .mk_local_decl(&mut st, None, &mut gen, None, ty, BinderInfo::Default)
            .unwrap();

        let Node::FVar { id: id0 } = st.expr_node(None, fvar0) else {
            panic!("expected FVar row")
        };
        let Node::FVar { id: id1 } = st.expr_node(None, fvar1) else {
            panic!("expected FVar row")
        };
        let name0 = st.to_name(None, id0);
        let name1 = st.to_name(None, id1);

        // Direct pin: `_kernel_fresh.<n>`, matching the Arc doc comment.
        assert_eq!(name0.to_string(), "_kernel_fresh.0");
        assert_eq!(name1.to_string(), "_kernel_fresh.1");
    }

    #[test]
    fn fresh_ids_never_collide() {
        let mut st = Store::persistent();
        let mut gen = FVarIdGen::default();
        let mut lctx = LocalContext::default();
        let ty = st.expr_lit_nat(None, &Nat::from(0u64)).unwrap();

        let a = lctx
            .mk_local_decl(&mut st, None, &mut gen, None, ty, BinderInfo::Default)
            .unwrap();
        let b = lctx
            .mk_local_decl(&mut st, None, &mut gen, None, ty, BinderInfo::Default)
            .unwrap();

        let Node::FVar { id: ia } = st.expr_node(None, a) else {
            panic!()
        };
        let Node::FVar { id: ib } = st.expr_node(None, b) else {
            panic!()
        };
        assert_ne!(ia, ib);
        assert!(lctx.get(ia.unwrap()).is_some() && lctx.get(ib.unwrap()).is_some());
    }

    #[test]
    fn get_finds_a_pushed_decl_by_id() {
        let mut st = Store::persistent();
        let mut gen = FVarIdGen::default();
        let mut lctx = LocalContext::default();
        let name = st.intern_name(None, &nm("x")).unwrap();
        let ty = st.expr_lit_nat(None, &Nat::from(7u64)).unwrap();

        let fvar = lctx
            .mk_local_decl(&mut st, None, &mut gen, name, ty, BinderInfo::Implicit)
            .unwrap();
        let Node::FVar { id } = st.expr_node(None, fvar) else {
            panic!()
        };
        let decl = lctx.get(id.unwrap()).expect("decl should be found");
        assert_eq!(decl.id, id.unwrap());
        assert_eq!(decl.binder_name, name);
        assert_eq!(decl.ty, ty);
        assert_eq!(decl.binder_info, BinderInfo::Implicit);
        assert!(decl.value.is_none());

        // A never-pushed id is absent.
        let other_name = st.intern_name(None, &nm("y")).unwrap();
        assert!(lctx.get(other_name.unwrap()).is_none());
    }

    #[test]
    fn mk_local_decl_returns_an_fvar_node_wrapping_the_minted_id() {
        let mut st = Store::persistent();
        let mut gen = FVarIdGen::default();
        let mut lctx = LocalContext::default();
        let ty = st.expr_lit_nat(None, &Nat::from(0u64)).unwrap();

        let fvar = lctx
            .mk_local_decl(&mut st, None, &mut gen, None, ty, BinderInfo::Default)
            .unwrap();
        match st.expr_node(None, fvar) {
            Node::FVar { id } => {
                let decl = lctx.get(id.unwrap()).unwrap();
                assert_eq!(decl.id, id.unwrap());
            }
            other => panic!("expected FVar row, got {other:?}"),
        }
    }

    #[test]
    fn mk_let_decl_records_a_value_and_default_binder_info() {
        let mut st = Store::persistent();
        let mut gen = FVarIdGen::default();
        let mut lctx = LocalContext::default();
        let ty = st.expr_lit_nat(None, &Nat::from(1u64)).unwrap();
        let value = st.expr_lit_nat(None, &Nat::from(2u64)).unwrap();

        let fvar = lctx
            .mk_let_decl(&mut st, None, &mut gen, None, ty, value)
            .unwrap();
        let Node::FVar { id } = st.expr_node(None, fvar) else {
            panic!()
        };
        let decl = lctx.get(id.unwrap()).unwrap();
        assert_eq!(decl.value, Some(value));
        assert_eq!(decl.binder_info, BinderInfo::Default);
    }
}
