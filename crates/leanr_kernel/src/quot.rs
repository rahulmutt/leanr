//! Quotient admission (oracle: src/kernel/quot.cpp — `check_eq_type`
//! :19-45, `environment::add_quot` :47-79; reduction itself is
//! `quot.h:39-70`, ported earlier as `quot_red.rs`).
//!
//! `add_quot` is the sole production entry point (dispatched from
//! `Environment::add_decl`'s `Declaration::Quot` arm): it requires the
//! environment to already contain a correctly-shaped `Eq`
//! (`check_eq_type`), then declares the four built-in quotient
//! constants with their hard-coded types and marks the environment
//! quotient-initialized (`Environment::set_quot_initialized`).
//!
//! Every type below is assembled via `LocalContext`/`FVarIdGen` (Task
//! 5), mirroring the oracle's own `local_ctx` usage line for line:
//! each parameter becomes a fresh free variable (so building
//! applications/arrows out of it needs no manual de Bruijn
//! bookkeeping — a fvar refers to its declaring site by a globally
//! unique id, unaffected by how many more binders are later wrapped
//! around it), and `LocalContext::mk_pi` abstracts a whole telescope
//! into bound variables in one pass at the very end, exactly like
//! `lctx.mk_pi(...)` in the oracle. This is what makes the four-line
//! doc-comment signatures in quot.cpp:59-78 transcribe directly into
//! the code below without hand-computed bvar indices anywhere.

use std::sync::Arc;

use crate::{
    BinderInfo, ConstantInfo, ConstantVal, Environment, Expr, FVarIdGen, KernelError, Level,
    LocalContext, Name, QuotKind, QuotVal, RecGuard,
};

fn nm(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

fn nm2(a: &str, b: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: nm(a),
        part: b.to_string(),
    })
}

fn cval(name: Arc<Name>, level_params: Vec<Arc<Name>>, ty: Arc<Expr>) -> ConstantVal {
    ConstantVal {
        name,
        level_params,
        ty,
    }
}

/// oracle: `mk_arrow` (expr.cpp:181-183) — `Π (a : t), e` using the
/// oracle's own default binder name (`g_default_name = "a"`,
/// expr.cpp:180/507) and `binder_info::Default`. A "raw" Pi: it does
/// NOT go through a `LocalContext` and abstracts nothing — `dom`/
/// `body` are used exactly as given (they may already reference outer
/// fvars, which this call leaves untouched; only a later
/// `LocalContext::mk_pi` call turns those into bound variables).
fn arrow(dom: Arc<Expr>, body: Arc<Expr>) -> Arc<Expr> {
    Expr::forall_e(nm("a"), dom, body, BinderInfo::Default)
}

/// oracle: quot.cpp:19-45 (`check_eq_type`). Every failure path below
/// reports the same short reason tag, `InvalidQuot { what: "Eq" }`:
/// `KernelError::InvalidQuot`'s `what` field is documented as a short
/// static reason (not a full message), and the brief's own
/// `add_quot_without_eq_fails` test pins exactly this payload for the
/// missing-constant case; every other check here belongs to the same
/// "Eq isn't shaped right for quotient init" family, so the tag is
/// reused rather than inventing one per branch.
///
/// Deviation from the oracle (documented): the oracle's `env.get("Eq")`
/// throws a DIFFERENT exception (`unknown_constant_exception`) when
/// "Eq" is entirely absent, distinct from the generic exception thrown
/// when "Eq" is present but mis-shaped. There is no `KernelError`
/// variant for "unknown constant during quotient init" specifically
/// (the variant list is frozen, Task 1), and from `add_quot`'s caller's
/// point of view both cases mean the same thing — quotient admission
/// cannot proceed — so both fold into `InvalidQuot { what: "Eq" }`.
///
/// The two shape checks below (`expected_eq_type`/`expected_refl_type`
/// against the environment's actual `Eq`/`Eq.refl` types) use
/// `Expr::alpha_eq`, not `Expr::structural_eq`: quot.cpp:33 and :42
/// compare with `expected != info.get_type()`, and `operator!=(expr)`
/// is `!is_equal(a, b)` = `!expr_eq_fn<false>()(a, b)`
/// (kernel/expr_eq_fn.cpp:140-142, kernel/expr.h). `expr_eq_fn<false>`
/// ignores binder name and `BinderInfo` on `Lam`/`Pi` nodes
/// (expr_eq_fn.cpp:113-119) — a real Lean-produced `Eq` may spell its
/// bound variables differently from the hard-coded names used to build
/// `expected_eq_type`/`expected_refl_type` above (`"α"`/`"a"`) and must
/// still be accepted. `Expr::structural_eq` is binder-name/info
/// sensitive (it is `expr_eq_fn<true>`/`is_bi_equal`, used elsewhere for
/// e.g. `ConstantInfo`'s derived-`BEq` mirror), so using it here would
/// reject correctly-shaped `Eq` declarations whose binder names differ
/// from ours — see `Expr::alpha_eq`'s doc comment in `expr.rs` for the
/// full oracle citation and the packed-data-word fast-reject soundness
/// argument.
fn check_eq_type(env: &Environment, g: &mut RecGuard) -> Result<(), KernelError> {
    const WHAT: &str = "Eq";
    let fail = || KernelError::InvalidQuot { what: WHAT };

    let eq_name = nm("Eq");
    let eq_val = match env.get(&eq_name) {
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
    let u = Arc::new(Level::Param(Arc::clone(&eq_val.val.level_params[0])));
    let sort_u = Expr::sort(u, g)?;
    let prop = Expr::sort(Arc::new(Level::Zero), g)?;
    let mut lctx = LocalContext::default();
    let mut gen = FVarIdGen::default();
    let alpha = lctx.mk_local_decl(&mut gen, &nm("α"), sort_u, BinderInfo::Implicit);
    let expected_eq_type = lctx.mk_pi(
        &[Arc::clone(&alpha)],
        &arrow(Arc::clone(&alpha), arrow(Arc::clone(&alpha), prop)),
        g,
    )?;
    if !Expr::alpha_eq(&expected_eq_type, &eq_val.val.ty, g)? {
        return Err(fail());
    }

    // quot.cpp:36-43: expected_eq_refl_type = Π {α : Sort u} (a : α), @Eq.{u} α a a.
    let refl_name = Arc::clone(&eq_val.ctors[0]);
    let refl_val = match env.get(&refl_name) {
        Some(ConstantInfo::Ctor(v)) => v,
        _ => return Err(fail()),
    };
    let ru = match refl_val.val.level_params.first() {
        Some(p) => Arc::new(Level::Param(Arc::clone(p))),
        None => return Err(fail()),
    };
    let sort_ru = Expr::sort(Arc::clone(&ru), g)?;
    let mut lctx2 = LocalContext::default();
    let mut gen2 = FVarIdGen::default();
    let alpha2 = lctx2.mk_local_decl(&mut gen2, &nm("α"), sort_ru, BinderInfo::Implicit);
    let a2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("a"),
        Arc::clone(&alpha2),
        BinderInfo::Default,
    );
    let eq_const = Expr::const_(Arc::clone(&eq_name), vec![ru], g)?;
    let eq_app = Expr::mk_app_spine(
        eq_const,
        &[Arc::clone(&alpha2), Arc::clone(&a2), Arc::clone(&a2)],
    );
    let expected_refl_type = lctx2.mk_pi(&[Arc::clone(&alpha2), Arc::clone(&a2)], &eq_app, g)?;
    if !Expr::alpha_eq(&expected_refl_type, &refl_val.val.ty, g)? {
        return Err(fail());
    }
    Ok(())
}

/// oracle: `environment::add_quot` (quot.cpp:47-79). Idempotent: if the
/// quotient is already initialized, this is a no-op success
/// (quot.cpp:48-49, `if (is_quot_initialized()) return *this;`).
pub(crate) fn add_quot(env: &mut Environment) -> Result<(), KernelError> {
    if env.quot_initialized() {
        return Ok(());
    }
    check_eq_type(&*env, &mut RecGuard::new())?;
    let mut g = RecGuard::new();

    let u_name = nm("u");
    let u = Arc::new(Level::Param(Arc::clone(&u_name)));
    let sort_u = Expr::sort(Arc::clone(&u), &mut g)?;
    let prop = Expr::sort(Arc::new(Level::Zero), &mut g)?;
    let mut gen = FVarIdGen::default();

    // ---- Quot, Quot.mk: share one local context (quot.cpp:53-66) -----
    let mut lctx = LocalContext::default();
    let alpha = lctx.mk_local_decl(
        &mut gen,
        &nm("α"),
        Arc::clone(&sort_u),
        BinderInfo::Implicit,
    );
    let r_dom = arrow(
        Arc::clone(&alpha),
        arrow(Arc::clone(&alpha), Arc::clone(&prop)),
    );
    let r = lctx.mk_local_decl(&mut gen, &nm("r"), r_dom, BinderInfo::Default);

    // constant {u} Quot {α : Sort u} (r : α → α → Prop) : Sort u
    let quot_type = lctx.mk_pi(&[Arc::clone(&alpha), Arc::clone(&r)], &sort_u, &mut g)?;
    env.add_core(ConstantInfo::Quot(QuotVal {
        val: cval(nm("Quot"), vec![Arc::clone(&u_name)], quot_type),
        kind: QuotKind::Type,
    }));

    let quot_const_u = Expr::const_(nm("Quot"), vec![Arc::clone(&u)], &mut g)?;
    let quot_r = Expr::mk_app_spine(
        Arc::clone(&quot_const_u),
        &[Arc::clone(&alpha), Arc::clone(&r)],
    );
    let a = lctx.mk_local_decl(&mut gen, &nm("a"), Arc::clone(&alpha), BinderInfo::Default);

    // constant {u} Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : @Quot.{u} α r
    let quot_mk_type = lctx.mk_pi(
        &[Arc::clone(&alpha), Arc::clone(&r), Arc::clone(&a)],
        &quot_r,
        &mut g,
    )?;
    env.add_core(ConstantInfo::Quot(QuotVal {
        val: cval(nm2("Quot", "mk"), vec![Arc::clone(&u_name)], quot_mk_type),
        kind: QuotKind::Ctor,
    }));

    // ---- Quot.lift, Quot.ind: fresh local context; r/α re-declared ---
    // ---- (r is implicit here, unlike Quot/Quot.mk) (quot.cpp:67-96) --
    let mut lctx = LocalContext::default();
    let alpha = lctx.mk_local_decl(
        &mut gen,
        &nm("α"),
        Arc::clone(&sort_u),
        BinderInfo::Implicit,
    );
    let r_dom = arrow(
        Arc::clone(&alpha),
        arrow(Arc::clone(&alpha), Arc::clone(&prop)),
    );
    let r = lctx.mk_local_decl(&mut gen, &nm("r"), r_dom, BinderInfo::Implicit);
    let quot_r = Expr::mk_app_spine(
        Arc::clone(&quot_const_u),
        &[Arc::clone(&alpha), Arc::clone(&r)],
    );
    let a = lctx.mk_local_decl(&mut gen, &nm("a"), Arc::clone(&alpha), BinderInfo::Default);

    let v_name = nm("v");
    let v = Arc::new(Level::Param(Arc::clone(&v_name)));
    let sort_v = Expr::sort(Arc::clone(&v), &mut g)?;
    let beta = lctx.mk_local_decl(&mut gen, &nm("β"), sort_v, BinderInfo::Implicit);
    let f_dom = arrow(Arc::clone(&alpha), Arc::clone(&beta));
    let f = lctx.mk_local_decl(&mut gen, &nm("f"), f_dom, BinderInfo::Default);
    let b = lctx.mk_local_decl(&mut gen, &nm("b"), Arc::clone(&alpha), BinderInfo::Default);

    let r_a_b = Expr::mk_app_spine(Arc::clone(&r), &[Arc::clone(&a), Arc::clone(&b)]);
    let eq_v = Expr::const_(nm("Eq"), vec![Arc::clone(&v)], &mut g)?;
    let f_a = Expr::app(Arc::clone(&f), Arc::clone(&a));
    let f_b = Expr::app(Arc::clone(&f), Arc::clone(&b));
    // f a = f b
    let f_a_eq_f_b = Expr::mk_app_spine(eq_v, &[Arc::clone(&beta), f_a, f_b]);
    // (∀ a b : α, r a b → f a = f b)
    let sanity = lctx.mk_pi(
        &[Arc::clone(&a), Arc::clone(&b)],
        &arrow(r_a_b, f_a_eq_f_b),
        &mut g,
    )?;

    // constant {u v} Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
    //                          : (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β
    let lift_body = arrow(sanity, arrow(Arc::clone(&quot_r), Arc::clone(&beta)));
    let lift_type = lctx.mk_pi(
        &[
            Arc::clone(&alpha),
            Arc::clone(&r),
            Arc::clone(&beta),
            Arc::clone(&f),
        ],
        &lift_body,
        &mut g,
    )?;
    env.add_core(ConstantInfo::Quot(QuotVal {
        val: cval(
            nm2("Quot", "lift"),
            vec![Arc::clone(&u_name), v_name],
            lift_type,
        ),
        kind: QuotKind::Lift,
    }));

    // { β : @Quot.{u} α r → Prop } — Quot.ind's own β (re-declared).
    let beta_ind_dom = arrow(Arc::clone(&quot_r), Arc::clone(&prop));
    let beta = lctx.mk_local_decl(&mut gen, &nm("β"), beta_ind_dom, BinderInfo::Implicit);
    let quot_mk_const_u = Expr::const_(nm2("Quot", "mk"), vec![Arc::clone(&u)], &mut g)?;
    let quot_mk_a = Expr::mk_app_spine(
        quot_mk_const_u,
        &[Arc::clone(&alpha), Arc::clone(&r), Arc::clone(&a)],
    );
    // (∀ a : α, β (@Quot.mk.{u} α r a))
    let all_quot = lctx.mk_pi(
        &[Arc::clone(&a)],
        &Expr::app(Arc::clone(&beta), quot_mk_a),
        &mut g,
    )?;
    let q = lctx.mk_local_decl(&mut gen, &nm("q"), Arc::clone(&quot_r), BinderInfo::Default);
    // ∀ q : @Quot.{u} α r, β q
    let q_pi = lctx.mk_pi(
        &[Arc::clone(&q)],
        &Expr::app(Arc::clone(&beta), Arc::clone(&q)),
        &mut g,
    )?;
    // (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q — a raw
    // "mk"-named Pi (oracle: `mk_pi("mk", all_quot, ...)`, quot.cpp:94),
    // NOT through `lctx`: both sides are already fully built (`all_quot`
    // still references α/r/β as fvars; `q_pi` is closed over `q` alone).
    let mk_pi_node = Expr::forall_e(nm("mk"), all_quot, q_pi, BinderInfo::Default);

    // constant {u} Quot.ind {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop}
    //               : (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q
    let ind_type = lctx.mk_pi(
        &[Arc::clone(&alpha), Arc::clone(&r), Arc::clone(&beta)],
        &mk_pi_node,
        &mut g,
    )?;
    env.add_core(ConstantInfo::Quot(QuotVal {
        val: cval(nm2("Quot", "ind"), vec![u_name], ind_type),
        kind: QuotKind::Ind,
    }));

    env.set_quot_initialized();
    Ok(())
}

#[cfg(test)]
mod tests;
