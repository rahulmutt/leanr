//! Id-twin of `crate::quot` (oracle: src/kernel/quot.cpp — `check_eq_type`
//! :19-45, `environment::add_quot` :47-79; reduction itself is
//! `quot.h:39-70`, already ported as `bank::quot_red`). Porting is
//! representation-only: `Arc<Name>`/`Arc<Expr>`/`Arc<Level>` become
//! `NameId`/`ExprId`/`LevelId` via the phase-1 bank (spec:
//! docs/superpowers/specs/2026-07-06-term-bank-kernel-migration-design.md).
//!
//! `add_quot` is the sole production entry point (mirroring the Arc
//! `add_quot(env: &mut Environment)`, dispatched from
//! `Environment::add_decl`'s `Declaration::Quot` arm): it requires the
//! environment to already contain a correctly-shaped `Eq`
//! (`check_eq_type`), then builds the four built-in quotient constants
//! with their hard-coded types. Unlike the Arc version, this function
//! does **not** mutate an environment (there is no id-native
//! `Environment` yet — that is Task 6): it returns the four
//! `ConstantInfo`s to admit, still scratch-region, and does **not**
//! itself flip `quot_initialized` (Task 6's `add_core`/env wiring does
//! that once it has actually admitted them, mirroring the Arc
//! `env.set_quot_initialized()` call at `add_quot`'s tail).
//!
//! Deviation from the brief's illustrative aside ("`check_eq_type` runs
//! a `TypeChecker`"): the actual Arc `quot.rs` source does not use a
//! `TypeChecker` anywhere — `check_eq_type` only builds expected types
//! via `LocalContext`/`FVarIdGen` and compares with `Expr::alpha_eq`.
//! This port follows the real Arc source, not the brief's aside.
//!
//! `Expr::alpha_eq` (binder-name/`BinderInfo`-insensitive structural
//! equality) has no id-native equivalent: the interning invariant makes
//! plain `ExprId` equality the analogue of `Expr::structural_eq` (which
//! IS binder-name/info sensitive — two differently-named-but-alpha-
//! equivalent trees intern to DIFFERENT ids), so `alpha_eq` itself must
//! still walk two full trees ignoring names/infos. Rather than
//! re-deriving that walk id-natively for two cold, once-per-quotient-
//! init call sites, this port bridges both operands out to `Arc<Expr>`
//! via `Store::to_expr` and calls the existing (already-proven)
//! `Expr::alpha_eq` — the same "non-structural operation stays on the
//! Arc side, bridged at the call site" precedent Task 4 used for
//! `Level::is_equivalent`/`mk_max_pair`/`mk_imax_pair`.

use super::decl::{ConstantInfo, ConstantVal, QuotVal};
use super::local_ctx::{FVarIdGen, LocalContext};
use super::tc::EnvView;
use super::{ExprId, NameId, Store};
use crate::{BinderInfo, Expr, KernelError, QuotKind, RecGuard};

fn mk_name1_id(st: &mut Store, base: Option<&Store>, part: &str) -> Result<NameId, KernelError> {
    let s = st.intern_str(base, part)?;
    st.name_str(base, None, s)
}

fn mk_name2_id(
    st: &mut Store,
    base: Option<&Store>,
    a: &str,
    b: &str,
) -> Result<NameId, KernelError> {
    let p = mk_name1_id(st, base, a)?;
    let s = st.intern_str(base, b)?;
    st.name_str(base, Some(p), s)
}

fn cval(name: NameId, level_params: Vec<NameId>, ty: ExprId) -> ConstantVal {
    ConstantVal {
        name,
        level_params,
        ty,
    }
}

/// oracle: `mk_arrow` (expr.cpp:181-183) — `Π (a : t), e` using the
/// oracle's own default binder name (`g_default_name = "a"`,
/// expr.cpp:180/507) and `binder_info::Default`. A "raw" Pi: it does NOT
/// go through a `LocalContext` and abstracts nothing.
fn arrow(
    st: &mut Store,
    base: Option<&Store>,
    dom: ExprId,
    body: ExprId,
) -> Result<ExprId, KernelError> {
    let a = mk_name1_id(st, base, "a")?;
    st.expr_forall(base, Some(a), dom, body, BinderInfo::Default)
}

/// Alpha-equivalence via the Arc bridge (see module doc comment).
fn alpha_eq(
    st: &Store,
    base: Option<&Store>,
    a: ExprId,
    b: ExprId,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    let arc_a = st.to_expr(base, a, g)?;
    let arc_b = st.to_expr(base, b, g)?;
    Expr::alpha_eq(&arc_a, &arc_b, g)
}

/// oracle: quot.cpp:19-45 (`check_eq_type`). Every failure path below
/// reports the same short reason tag, `InvalidQuot { what: "Eq" }` — see
/// the Arc `quot.rs::check_eq_type`'s doc comment for the full oracle
/// citation and the rationale for collapsing "Eq absent" and "Eq
/// mis-shaped" into one tag (no `KernelError` variant exists for
/// "unknown constant during quotient init" specifically).
fn check_eq_type(st: &mut Store, view: &EnvView, g: &mut RecGuard) -> Result<(), KernelError> {
    const WHAT: &str = "Eq";
    let fail = || KernelError::InvalidQuot { what: WHAT };
    let base = Some(view.store);

    let eq_name = mk_name1_id(st, base, "Eq")?;
    let eq_val = match view.get(eq_name) {
        Some(ConstantInfo::Induct(v)) => v,
        _ => return Err(fail()),
    };
    // quot.cpp:23-24: exactly one universe parameter.
    if eq_val.val.level_params.len() != 1 {
        return Err(fail());
    }
    // quot.cpp:25-26: exactly one constructor.
    if eq_val.ctors.len() != 1 {
        return Err(fail());
    }

    // quot.cpp:29-34: expected_eq_type = Π {α : Sort u}, α → α → Prop.
    let u = st.level_param(base, Some(eq_val.val.level_params[0]))?;
    let sort_u = st.expr_sort(base, u)?;
    let zero = st.level_zero(base)?;
    let prop = st.expr_sort(base, zero)?;
    let mut lctx = LocalContext::default();
    let mut gen = FVarIdGen::default();
    let alpha_name = mk_name1_id(st, base, "α")?;
    let alpha = lctx.mk_local_decl(
        st,
        base,
        &mut gen,
        Some(alpha_name),
        sort_u,
        BinderInfo::Implicit,
    )?;
    let arrow_body = {
        let a2 = arrow(st, base, alpha, prop)?;
        arrow(st, base, alpha, a2)?
    };
    let expected_eq_type = super::subst::mk_pi(st, base, &lctx, &[alpha], arrow_body, g)?;
    let eq_val_ty = eq_val.val.ty;
    if !alpha_eq(st, base, expected_eq_type, eq_val_ty, g)? {
        return Err(fail());
    }

    // quot.cpp:36-43: expected_eq_refl_type = Π {α : Sort u} (a : α), @Eq.{u} α a a.
    let refl_name = match view.get(eq_name) {
        Some(ConstantInfo::Induct(v)) => v.ctors[0],
        _ => return Err(fail()),
    };
    let refl_val = match view.get(refl_name) {
        Some(ConstantInfo::Ctor(v)) => v,
        _ => return Err(fail()),
    };
    let ru = match refl_val.val.level_params.first() {
        Some(&p) => st.level_param(base, Some(p))?,
        None => return Err(fail()),
    };
    let sort_ru = st.expr_sort(base, ru)?;
    let mut lctx2 = LocalContext::default();
    let mut gen2 = FVarIdGen::default();
    let alpha2_name = mk_name1_id(st, base, "α")?;
    let alpha2 = lctx2.mk_local_decl(
        st,
        base,
        &mut gen2,
        Some(alpha2_name),
        sort_ru,
        BinderInfo::Implicit,
    )?;
    let a_name = mk_name1_id(st, base, "a")?;
    let a2 = lctx2.mk_local_decl(
        st,
        base,
        &mut gen2,
        Some(a_name),
        alpha2,
        BinderInfo::Default,
    )?;
    let no_ru = st.intern_level_list(base, &[ru])?;
    let eq_const = st.expr_const(base, Some(eq_name), no_ru)?;
    let eq_app = {
        let t1 = st.expr_app(base, eq_const, alpha2)?;
        let t2 = st.expr_app(base, t1, a2)?;
        st.expr_app(base, t2, a2)?
    };
    let expected_refl_type = super::subst::mk_pi(st, base, &lctx2, &[alpha2, a2], eq_app, g)?;
    let refl_val_ty = refl_val.val.ty;
    if !alpha_eq(st, base, expected_refl_type, refl_val_ty, g)? {
        return Err(fail());
    }
    Ok(())
}

/// oracle: `environment::add_quot` (quot.cpp:47-79). Idempotent: if the
/// quotient is already initialized, this is a no-op success (quot.cpp:
/// 48-49) — nothing new to admit. Otherwise returns the four
/// `ConstantInfo::Quot(...)` values, still scratch-region, for the
/// caller (Task 6's `add_core`) to admit and to flip
/// `quot_initialized` afterward.
pub fn add_quot(scratch: &mut Store, view: &EnvView) -> Result<Vec<ConstantInfo>, KernelError> {
    if view.quot_initialized {
        return Ok(Vec::new());
    }
    let base = Some(view.store);
    check_eq_type(scratch, view, &mut RecGuard::new())?;
    let mut g = RecGuard::new();

    let mut out = Vec::with_capacity(4);

    let u_name = mk_name1_id(scratch, base, "u")?;
    let u = scratch.level_param(base, Some(u_name))?;
    let sort_u = scratch.expr_sort(base, u)?;
    let zero = scratch.level_zero(base)?;
    let prop = scratch.expr_sort(base, zero)?;
    let mut gen = FVarIdGen::default();

    // ---- Quot, Quot.mk: share one local context (quot.cpp:53-66) -----
    let mut lctx = LocalContext::default();
    let alpha_name = mk_name1_id(scratch, base, "α")?;
    let alpha = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(alpha_name),
        sort_u,
        BinderInfo::Implicit,
    )?;
    let r_dom = {
        let a2 = arrow(scratch, base, alpha, prop)?;
        arrow(scratch, base, alpha, a2)?
    };
    let r_name = mk_name1_id(scratch, base, "r")?;
    let r = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(r_name),
        r_dom,
        BinderInfo::Default,
    )?;

    // constant {u} Quot {α : Sort u} (r : α → α → Prop) : Sort u
    let quot_type = super::subst::mk_pi(scratch, base, &lctx, &[alpha, r], sort_u, &mut g)?;
    let quot_name = mk_name1_id(scratch, base, "Quot")?;
    out.push(ConstantInfo::Quot(QuotVal {
        val: cval(quot_name, vec![u_name], quot_type),
        kind: QuotKind::Type,
    }));

    let u_list = scratch.intern_level_list(base, &[u])?;
    let quot_const_u = scratch.expr_const(base, Some(quot_name), u_list)?;
    let quot_r = {
        let t1 = scratch.expr_app(base, quot_const_u, alpha)?;
        scratch.expr_app(base, t1, r)?
    };
    let a_name = mk_name1_id(scratch, base, "a")?;
    let a = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(a_name),
        alpha,
        BinderInfo::Default,
    )?;

    // constant {u} Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : @Quot.{u} α r
    let quot_mk_type = super::subst::mk_pi(scratch, base, &lctx, &[alpha, r, a], quot_r, &mut g)?;
    let quot_mk_name = mk_name2_id(scratch, base, "Quot", "mk")?;
    out.push(ConstantInfo::Quot(QuotVal {
        val: cval(quot_mk_name, vec![u_name], quot_mk_type),
        kind: QuotKind::Ctor,
    }));

    // ---- Quot.lift, Quot.ind: fresh local context; r/α re-declared ---
    // ---- (r is implicit here, unlike Quot/Quot.mk) (quot.cpp:67-96) --
    let mut lctx = LocalContext::default();
    let alpha_name = mk_name1_id(scratch, base, "α")?;
    let alpha = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(alpha_name),
        sort_u,
        BinderInfo::Implicit,
    )?;
    let r_dom = {
        let a2 = arrow(scratch, base, alpha, prop)?;
        arrow(scratch, base, alpha, a2)?
    };
    let r_name = mk_name1_id(scratch, base, "r")?;
    let r = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(r_name),
        r_dom,
        BinderInfo::Implicit,
    )?;
    let quot_r = {
        let t1 = scratch.expr_app(base, quot_const_u, alpha)?;
        scratch.expr_app(base, t1, r)?
    };
    let a_name = mk_name1_id(scratch, base, "a")?;
    let a = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(a_name),
        alpha,
        BinderInfo::Default,
    )?;

    let v_name = mk_name1_id(scratch, base, "v")?;
    let v = scratch.level_param(base, Some(v_name))?;
    let sort_v = scratch.expr_sort(base, v)?;
    let beta_name = mk_name1_id(scratch, base, "β")?;
    let beta = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(beta_name),
        sort_v,
        BinderInfo::Implicit,
    )?;
    let f_dom = arrow(scratch, base, alpha, beta)?;
    let f_name = mk_name1_id(scratch, base, "f")?;
    let f = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(f_name),
        f_dom,
        BinderInfo::Default,
    )?;
    let b_name = mk_name1_id(scratch, base, "b")?;
    let b = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(b_name),
        alpha,
        BinderInfo::Default,
    )?;

    let r_a_b = {
        let t1 = scratch.expr_app(base, r, a)?;
        scratch.expr_app(base, t1, b)?
    };
    let eq_name = mk_name1_id(scratch, base, "Eq")?;
    let v_list = scratch.intern_level_list(base, &[v])?;
    let eq_v = scratch.expr_const(base, Some(eq_name), v_list)?;
    let f_a = scratch.expr_app(base, f, a)?;
    let f_b = scratch.expr_app(base, f, b)?;
    // f a = f b
    let f_a_eq_f_b = {
        let t1 = scratch.expr_app(base, eq_v, beta)?;
        let t2 = scratch.expr_app(base, t1, f_a)?;
        scratch.expr_app(base, t2, f_b)?
    };
    // (∀ a b : α, r a b → f a = f b)
    let sanity = {
        let body = arrow(scratch, base, r_a_b, f_a_eq_f_b)?;
        super::subst::mk_pi(scratch, base, &lctx, &[a, b], body, &mut g)?
    };

    // constant {u v} Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
    //                          : (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β
    let lift_body = {
        let t1 = arrow(scratch, base, quot_r, beta)?;
        arrow(scratch, base, sanity, t1)?
    };
    let lift_type = super::subst::mk_pi(
        scratch,
        base,
        &lctx,
        &[alpha, r, beta, f],
        lift_body,
        &mut g,
    )?;
    let quot_lift_name = mk_name2_id(scratch, base, "Quot", "lift")?;
    out.push(ConstantInfo::Quot(QuotVal {
        val: cval(quot_lift_name, vec![u_name, v_name], lift_type),
        kind: QuotKind::Lift,
    }));

    // { β : @Quot.{u} α r → Prop } — Quot.ind's own β (re-declared).
    let beta_ind_dom = arrow(scratch, base, quot_r, prop)?;
    let beta_name = mk_name1_id(scratch, base, "β")?;
    let beta = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(beta_name),
        beta_ind_dom,
        BinderInfo::Implicit,
    )?;
    let quot_mk_const_u = scratch.expr_const(base, Some(quot_mk_name), u_list)?;
    let quot_mk_a = {
        let t1 = scratch.expr_app(base, quot_mk_const_u, alpha)?;
        let t2 = scratch.expr_app(base, t1, r)?;
        scratch.expr_app(base, t2, a)?
    };
    // (∀ a : α, β (@Quot.mk.{u} α r a))
    let all_quot = {
        let body = scratch.expr_app(base, beta, quot_mk_a)?;
        super::subst::mk_pi(scratch, base, &lctx, &[a], body, &mut g)?
    };
    let q_name = mk_name1_id(scratch, base, "q")?;
    let q = lctx.mk_local_decl(
        scratch,
        base,
        &mut gen,
        Some(q_name),
        quot_r,
        BinderInfo::Default,
    )?;
    // ∀ q : @Quot.{u} α r, β q
    let q_pi = {
        let body = scratch.expr_app(base, beta, q)?;
        super::subst::mk_pi(scratch, base, &lctx, &[q], body, &mut g)?
    };
    // (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q — a raw
    // "mk"-named Pi (oracle: `mk_pi("mk", all_quot, ...)`, quot.cpp:94),
    // NOT through `lctx`: both sides are already fully built.
    let mk_name = mk_name1_id(scratch, base, "mk")?;
    let mk_pi_node =
        scratch.expr_forall(base, Some(mk_name), all_quot, q_pi, BinderInfo::Default)?;

    // constant {u} Quot.ind {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop}
    //               : (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q
    let ind_type =
        super::subst::mk_pi(scratch, base, &lctx, &[alpha, r, beta], mk_pi_node, &mut g)?;
    let quot_ind_name = mk_name2_id(scratch, base, "Quot", "ind")?;
    out.push(ConstantInfo::Quot(QuotVal {
        val: cval(quot_ind_name, vec![u_name], ind_type),
        kind: QuotKind::Ind,
    }));

    Ok(out)
}

#[cfg(test)]
mod tests;
