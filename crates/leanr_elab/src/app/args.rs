//! `ElabAppArgs.main` and the parameter-kind arms. Oracle:
//! `App.lean:730-951`.
//!
//! `kinds` is threaded as an explicit parameter down `main` ->
//! `process_explicit_arg` -> `elab_and_add_new_arg` rather than stored on
//! `AppElab`: the `KindInterner` is passed per call everywhere in this
//! crate (`elab.rs`'s own module doc — one `TermElabM` can elaborate
//! nodes drawn from different snapshots), and holding a `&KindInterner`
//! inside `AppElab` alongside the `&mut TermElabM` would add a lifetime
//! parameter that buys nothing.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_meta::{MVarId, MVarKind};
use leanr_syntax::kind::KindInterner;

use crate::app::expand::{Arg, NamedArg};
use crate::app::state::AppElab;
use crate::error::ElabError;
use crate::synthetic::PostponeBehavior;

/// oracle: `main` (`App.lean:926-951`).
pub fn main(app: &mut AppElab, kinds: &KindInterner) -> Result<ExprId, ElabError> {
    loop {
        if app.f_type_is_forall()? {
            let binder_name = app.get_param_name();
            // Rendering a `NameId` allocates (`AppElab::render_name`), so
            // render ONCE per iteration and reuse it for both the
            // `findNamedArg?` lookup and `pushFoundNamedArg` — a
            // `NamedArg::name` is the identifier's raw source text
            // (`expand::NamedArg`'s own doc), so every comparison against
            // a binder name goes through a rendering.
            let rendered = binder_name.map(|n| app.render_name(n));
            // oracle: `findNamedArg? s.namedArgs binderName`
            // (`App.lean:930-938`) — checked BEFORE the binder-info
            // dispatch, so a named argument fills its parameter no matter
            // what that parameter's binder info is.
            //
            // NAMED SEAM: the oracle's `findDeprecatedBinderName?`
            // fallback (`App.lean:85-115`, reached at `App.lean:932` when
            // the direct lookup misses) resolves a DEPRECATED ALIAS of the
            // binder name by reading the `deprecatedArgExt` environment
            // extension and the `linter.deprecated.arg` option. leanr
            // decodes neither, so the alias can never be found here; the
            // effect is that `f (oldName := v)` reports an unknown
            // argument where the oracle would accept it with a warning.
            // Not a silent divergence on any P1 corpus term (Elab0
            // declares no `@[deprecated]` argument aliases), and Task 9's
            // fixture-source audit is what keeps it that way.
            if let Some(na) = rendered.as_deref().and_then(|r| find_named_arg(app, r)) {
                crate::app::propagate::propagate_expected_type(app, kinds, &na.val)?;
                erase_named_arg(app, &na.name);
                elab_and_add_new_arg(app, kinds, binder_name, na.val)?;
                continue;
            }
            // oracle: `unless binderName.hasMacroScopes do
            // pushFoundNamedArg binderName` (`App.lean:940-941`).
            // leanr's binder names carry NO macro scopes — they come
            // either from an `.olean` declaration's own binder names or
            // from `builtin/binder.rs`'s surface-syntax identifiers,
            // neither of which goes through Lean's hygiene machinery — so
            // the guard is vacuously true here and scope stripping is
            // deliberately not implemented. An ANONYMOUS binder
            // (`binder_name == None`) is skipped instead of pushing a
            // rendered `[anonymous]`: `foundNamedArgs` exists solely to
            // list the VALID argument names in the oracle's "invalid
            // argument name" diagnostic (`App.lean:401`), which leanr does
            // not emit yet, and an anonymous parameter has no name a user
            // could have written.
            if let Some(r) = rendered {
                push_found_named_arg(app, r);
            }
            match app.get_param_info()? {
                BinderInfo::Default => {
                    if !process_explicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app, kinds);
                    }
                }
                BinderInfo::Implicit => {
                    if !process_implicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app, kinds);
                    }
                }
                BinderInfo::StrictImplicit => {
                    if !process_strict_implicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app, kinds);
                    }
                }
                BinderInfo::InstImplicit => {
                    if !process_inst_implicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app, kinds);
                    }
                }
            }
        } else if app.has_args_to_process() {
            synthesize_pending_and_normalize_fun_type(app, kinds)?;
        } else {
            return crate::app::finalize::finalize(app, kinds);
        }
    }
}

/// oracle: `synthesizePendingAndNormalizeFunType` (`App.lean:372-411`).
/// "fType may become a forallE after we synthesize pending metavariables."
fn synthesize_pending_and_normalize_fun_type(
    app: &mut AppElab,
    kinds: &KindInterner,
) -> Result<(), ElabError> {
    app.try_synthesize_app_inst_mvars()?;
    // oracle: `synthesizeSyntheticMVars` with its DEFAULT
    // `postpone := .yes` (:375) — this is a normalization attempt, not a
    // commitment point, so a still-stuck mvar must stay pending rather
    // than be reported.
    app.elab
        .synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds)?;
    if app.f_type_is_forall()? {
        return Ok(());
    }
    // oracle: `coerceToFunction? s.f` (:378) — M4b-3 P4.
    // The oracle's remaining arms are diagnostics: a deprecated-argument
    // linter, `throwInvalidNamedArg` (which needs `foundNamedArgs`
    // rendering leanr does not do), and the "Function expected" error.
    // Only the last changes control flow, so only it is ported.
    let f_type = app.st.f_type;
    if app.f_type_is_mvar_after_instantiation()? {
        return Err(ElabError::UnsupportedSyntax(
            "function type is still an unassigned metavariable after synthesis: needs \
             CoeFun (M4b-3 P4), or expected-type propagation into `fun` binder domains \
             (M4b-3 P5) for the M4b-2 `fun` shape"
                .to_string(),
        ));
    }
    Err(ElabError::FunctionExpected {
        f: app.st.f,
        f_type,
    })
}

/// oracle: `Term.findNamedArg?` (`App.lean:81-83`) — the entry for
/// `binder_name`, if `named_args` has one. Cloned rather than borrowed:
/// every caller goes on to mutate `app` (`propagate_expected_type`,
/// `erase_named_arg`) while still holding the result.
fn find_named_arg(app: &AppElab, binder_name: &str) -> Option<NamedArg> {
    app.st
        .named_args
        .iter()
        .find(|na| na.name == binder_name)
        .cloned()
}

/// oracle: `eraseNamedArg` (`App.lean:117-119` + its `M` wrapper at
/// `App.lean:305-307`) — drop EVERY entry for `binder_name`, not just
/// the first. `expand::expand_args` already rejects duplicates
/// (`addNamedArg`, `Arg.lean:55-59`), so at most one can match today;
/// the oracle filters anyway, and so does this.
fn erase_named_arg(app: &mut AppElab, binder_name: &str) {
    app.st.named_args.retain(|na| na.name != binder_name);
}

/// oracle: `pushFoundNamedArg` (`App.lean:309-311`) — record a VALID
/// named-argument name seen while walking the function's type. Pure
/// bookkeeping for the oracle's "invalid argument name" diagnostic
/// (`App.lean:401`); it never affects the emitted term.
fn push_found_named_arg(app: &mut AppElab, name: String) {
    app.st.found_named_args.push(name);
}

/// oracle: `findNamedArgDependsOnCurrent?` (`App.lean:337-346`) — is
/// there a remaining named argument whose parameter's type mentions the
/// parameter now being processed? If so, that parameter is DETERMINED by
/// the named argument and must become an implicit mvar rather than an
/// eta binder (`App.lean:860-864`). Returns the matching named
/// argument's name.
fn find_named_arg_depends_on_current(app: &mut AppElab) -> Result<Option<String>, ElabError> {
    if app.st.named_args.is_empty() {
        return Ok(None);
    }
    // oracle: `(← get).fType.isArrow` — the RAW `s.fType`, checked
    // before `getFType` is even called: nothing in a non-dependent
    // arrow's body can mention the current parameter, so no named
    // argument can depend on it.
    if app.is_arrow(app.st.f_type) {
        return Ok(None);
    }
    let f_type = app.get_f_type()?;
    let named: Vec<String> = app.st.named_args.iter().map(|na| na.name.clone()).collect();
    find_named_arg_depends_on(app, f_type, &named)
}

/// oracle: `findNamedArgDependsOn?` (`App.lean:320-335`). Walks
/// `f_type`'s telescope and returns the name of the first named argument
/// whose parameter's type depends on the telescope's FIRST binder.
///
/// Takes the candidate names rather than `NamedArg`s (and returns a
/// name rather than a `NamedArg`): the oracle's own two callers use the
/// result only for `.isSome` plus a trace of `.name`, and
/// `propagate.rs`'s `main'` simulation carries names alone — its
/// `namedArgs` is a progressively erased `Vec<String>`, not the state's
/// `named_args`.
pub(crate) fn find_named_arg_depends_on(
    app: &mut AppElab,
    f_type: ExprId,
    named: &[String],
) -> Result<Option<String>, ElabError> {
    if app.is_arrow(f_type) {
        return Ok(None);
    }
    let mut named: Vec<String> = named.to_vec();
    app.forall_telescope_reducing(f_type, move |app, xs| {
        // oracle: `let curr := xs[0]!`. Guarded rather than panicking:
        // both call sites reach here only with a non-arrow `f_type`,
        // which `forallTelescopeReducing` always opens into at least one
        // binder, but a partial function on a `pub(crate)` helper is a
        // worse contract than an early `None`.
        let Some(curr) = xs.first().map(|b| b.fvar) else {
            return Ok(None);
        };
        for b in xs.iter().skip(1) {
            let Some(name) = b.name else { continue };
            let rendered = app.render_name(name);
            if !named.contains(&rendered) {
                continue;
            }
            // oracle Remark (`App.lean:330`): "a default value at
            // `optParam` does not count as a dependency" — hence
            // `xDecl.type.cleanupAnnotations`. `cleanupAnnotations`
            // (`Expr.lean:1754-1756`) is `consumeMData` composed with
            // `consumeTypeAnnotations`, iterated to a fixed point;
            // `consume_type_annotations` is the FULL
            // `consumeTypeAnnotations` half (all four gadgets, since
            // I2), but the `consumeMData` half is still not modelled, so
            // an `MData`-wrapped `optParam` would keep its wrapper here
            // and its default value would count as a dependency. No
            // fixture parameter type carries either wrapper, let alone
            // under `MData`.
            let ty = app.consume_type_annotations(b.ty)?;
            if expr_depends_on(app, ty, curr) {
                return Ok(Some(rendered));
            }
            // oracle: "Erase, since `xDecl.userName` can be repeated, and
            // we can otherwise get false dependencies."
            named.retain(|n| *n != rendered);
        }
        Ok(None)
    })
}

/// oracle: `exprDependsOn e fvarId`
/// (`Lean/MetavarContext.lean:755`, worker `DependsOn.dep` at :690-720)
/// — does `e` mention the free variable `fvar`? A plain structural walk
/// is exact here: `ExprId`s are hash-consed, so identity IS structural
/// identity and the `visited` set makes a DAG-shaped term linear.
///
/// The oracle's walk does two extra things at a metavariable, and
/// NEITHER can change the answer at this call site, because `fvar` is
/// always a binder `forall_telescope_reducing` minted moments ago:
///   - an ASSIGNED `?m` is followed into its value. No assignment can
///     mention `fvar`: every assignment in the `mctx` predates the
///     telescope, and nothing assigns during the walk.
///   - an UNASSIGNED `?m` counts as a "may dependency" when `fvar` is in
///     `?m`'s own local context. Same argument, plus `mk_fresh_expr_mvar`
///     declares every P1 mvar with an EMPTY `LocalContext` (`elab.rs`),
///     so that test is `false` for any mvar this elaborator can produce.
fn expr_depends_on(app: &AppElab, e: ExprId, fvar: ExprId) -> bool {
    let mut stack = vec![e];
    let mut visited: std::collections::HashSet<ExprId> = std::collections::HashSet::new();
    while let Some(cur) = stack.pop() {
        if cur == fvar {
            return true;
        }
        if !visited.insert(cur) {
            continue;
        }
        match app.node(cur) {
            Node::App { f, arg } => {
                stack.push(f);
                stack.push(arg);
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            Node::LetE {
                ty, value, body, ..
            } => {
                stack.push(ty);
                stack.push(value);
                stack.push(body);
            }
            Node::MData { expr, .. } => stack.push(expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => stack.push(structure),
            // Leaves. `FVar` included: the `cur == fvar` test above is
            // the whole comparison — an fvar's identity is its `ExprId`
            // (hash-consed over its `NameId`).
            Node::BVar { .. }
            | Node::BVarBig { .. }
            | Node::FVar { .. }
            | Node::MVar { .. }
            | Node::Sort { .. }
            | Node::Const { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => {}
        }
    }
    false
}

/// oracle: `addEtaArg` (`App.lean:730-740`) — the missing explicit
/// parameter becomes a fresh local, is applied to `f` like any other
/// argument, and is recorded so `finalize` can `mkLambdaFVars` it back
/// out. This is what turns `pick (y := Nat.zero)` into
/// `fun x => pick x Nat.zero` (`App.lean:191-205`'s own worked example).
fn add_eta_arg(app: &mut AppElab, binder_name: Option<NameId>) -> Result<(), ElabError> {
    let ty = app.get_arg_expected_type()?;
    // oracle: `withLocalDeclD (← Core.mkFreshUserName argName) type` —
    // a FRESH name, not `argName`, "to ensure that the remaining
    // arguments can't capture this parameter's name". That matters in
    // leanr for the same reason: `builtin::ident` resolves a bare
    // identifier through `MetaCtx::lctx_lookup_by_name`, so pushing the
    // parameter's own name would let a LATER argument's `x` bind to this
    // eta fvar instead of to whatever `x` meant at the application site.
    // `TermElabM::mk_fresh_binder_name` is this crate's own
    // `_leanr_elab_*` prefix+counter fresh-name idiom (`elab.rs`), used
    // here in place of the oracle's macro-scope mechanism; `finalize`
    // restores the user-facing name on the emitted binder
    // (`Expr.updateBinderNames`, `App.lean:623`).
    let fresh = app.elab.mk_fresh_binder_name()?;
    // `withLocalDeclD` is `withLocalDecl` at `BinderInfo.default`.
    let fvar = app
        .elab
        .mctx
        .push_local_decl(Some(fresh), ty, BinderInfo::Default)
        .map_err(ElabError::from)?;
    // oracle: `etaArgs := s.etaArgs.push (argName, x)` — the pair keeps
    // the USER-facing name alongside the fresh fvar, which is exactly
    // what `finalize`'s `updateBinderNames` step consumes.
    app.st.eta_args.push((binder_name, fvar));
    add_new_arg(app, fvar)
}

/// oracle: `processExplicitArg` (`App.lean:765-877`). Returns `false`
/// when the oracle's own control flow reaches `finalize` (no argument
/// left to consume and no eta/optParam path applies), so `main` can
/// finalize rather than looping.
fn process_explicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.param_idx() < app.ctx.num_implicit_params {
        // Only reachable via structure-projection expansion (M4b-4),
        // which is the sole producer of `num_implicit_params > 0`.
        return Err(ElabError::UnsupportedSyntax(
            "numImplicitParams override (structure projection) — M4b-4".to_string(),
        ));
    }
    if let Some(arg) = app.st.args.first().cloned() {
        // oracle: `App.lean:803-806` — `propagateExpectedType arg` runs
        // BEFORE `modify fun s => { s with args }`, i.e. while the
        // argument about to be elaborated is still counted in
        // `s.args.length`. `get_resulting_type` walks that count, so
        // popping first would simulate one parameter too few. Hence the
        // clone-then-remove rather than `remove(0)` up front.
        crate::app::propagate::propagate_expected_type(app, kinds, &arg)?;
        app.st.args.remove(0);
        elab_and_add_new_arg(app, kinds, binder_name, arg)?;
        return Ok(true);
    }
    // No positional argument left. What follows is `App.lean:809-877`
    // IN THE ORACLE'S OWN ORDER, which is load-bearing: the current
    // parameter's optParam/autoParam DEFAULT is filled (827-855) BEFORE
    // the ellipsis/named/eta chain (855-877) ever runs.

    // oracle: `App.lean:810-825` — inside a PATTERN, `..` fills even an
    // optParam/autoParam parameter with an implicit mvar. `inPattern` is
    // `Term.Context`'s flag, set only by the match/pattern elaborator
    // (M4b-4); no P1 entry point can set it, so this arm is inert rather
    // than omitted, and the plain-ellipsis arm below is what `..` takes.

    // oracle: the `optParam`/`autoParam` default-filling arms
    // (`App.lean:827-854`), on the CURRENT parameter's type and gated on
    // `!explicit` exactly as the oracle's `match` scrutinee is.
    // `get_arg_expected_type` already STRIPS the wrapper (task 3), so an
    // explicitly-supplied argument to a wrapped parameter is handled
    // above; only the DEFAULT path is deferred. Detect it rather than
    // falling through to the eta chain and building a different term.
    if !app.ctx.explicit {
        let param_type = app.get_param_type()?;
        if app.consume_opt_auto_param(param_type)? != param_type {
            return Err(ElabError::UnsupportedSyntax(
                "optParam default / autoParam tactic argument — M4b-3 P5".to_string(),
            ));
        }
    }

    // oracle: `if (← read).ellipsis then addImplicitArg argName`
    // (`App.lean:856-857`) — with `..`, eta-expansion is DISABLED and
    // every missing argument is treated as `_` (`App.lean:202-204`).
    if app.ctx.ellipsis {
        add_implicit_arg(app)?;
        return Ok(true);
    }

    // oracle: `App.lean:858-869` — named arguments remain, so the
    // missing parameter is either DETERMINED by one of them (implicit)
    // or genuinely missing (eta).
    if !app.st.named_args.is_empty() {
        if find_named_arg_depends_on_current(app)?.is_some() {
            // "Dependencies of named arguments cannot be turned into eta
            // arguments since they are determined by the named
            // arguments. Instead we can turn them into implicit
            // arguments." (`App.lean:860-863`)
            add_implicit_arg(app)?;
        } else {
            add_eta_arg(app, binder_name)?;
        }
        return Ok(true);
    }

    // oracle: `else if !(← read).explicit then if (← hasOptAutoParams
    // (← getFType)) then addEtaArg` (`App.lean:870-873`) — a LATER
    // parameter in the remaining telescope carries a default, so the
    // application is eta-expanded up to it rather than left partial.
    // (The current parameter cannot be the one carrying it: that case
    // returned above.)
    if !app.ctx.explicit {
        let f_type = app.get_f_type()?;
        if has_opt_auto_params(app, f_type)? {
            add_eta_arg(app, binder_name)?;
            return Ok(true);
        }
    }

    // oracle: `finalize` (`App.lean:875`/`877`).
    Ok(false)
}

/// oracle: `hasOptAutoParams` (`App.lean:121-127`) — does ANY parameter
/// of the WHOLE remaining telescope carry an `optParam`/`autoParam`
/// wrapper? `App.lean:873`'s call site passes `(← getFType)`, the entire
/// remaining function type, not the current parameter's.
///
/// Task 4 first wrote this as a current-parameter-only test, which is a
/// named-seam hole rather than just an imprecision: for
/// `f : (a : Nat) → (b : Nat := 0) → Nat` applied with no positional
/// arguments, the oracle takes `addEtaArg` and builds `fun a => f a 0`,
/// while a test that finds no wrapper on `a` returns `false` and lets
/// `main` finalize the bare partial application `f` — a DIFFERENT term,
/// silently. Task 4 widened it to the whole telescope; Task 7 finishes
/// the job with the oracle's `forallTelescopeReducing`, so a telescope
/// that only reveals a further binder AFTER reduction is seen too. The
/// oracle's `xType ← inferType x` is `TelescopeBinder::ty` — the decl's
/// declared type — and `isOptParam || isAutoParam` is the "stripping the
/// annotations changed the term" test `consume_opt_auto_param` backs
/// (NOT the full `consume_type_annotations`, which also strips
/// `outParam`/`semiOutParam`: those carry no default value, so seeing
/// them here would answer a different question — see
/// `propagate::is_opt_or_auto_param`'s own note).
///
/// Takes the type to walk as a parameter (Task 6): `App.lean:873`'s call
/// site passes `(← getFType)`, but `getResultingTypeCore?`'s own call
/// (`App.lean:484`) passes the SIMULATED remaining type `fType'`, which
/// is not `s.fType`. One function, two call sites, exactly as the oracle
/// has it.
pub(crate) fn has_opt_auto_params(app: &mut AppElab, ty: ExprId) -> Result<bool, ElabError> {
    app.forall_telescope_reducing(ty, |app, xs| {
        for b in xs {
            if app.consume_opt_auto_param(b.ty)? != b.ty {
                return Ok(true);
            }
        }
        Ok(false)
    })
}

/// oracle: `addImplicitArg` (`App.lean:745-760`). Creates a fresh mvar
/// for the parameter — marking it as the application's
/// `resultTypeOutParam?` and disabling expected-type propagation when
/// `isNextOutParamOfLocalInstanceAndResult` says so (`:747-755`) —
/// records it in `toSetErrorCtx` for error attribution, and continues
/// the loop.
///
/// No `kinds` parameter: unlike `process_explicit_arg`'s eventual
/// `elab_and_add_new_arg` call, nothing here parses or elaborates
/// surface syntax — the argument is a freshly minted mvar, not an
/// `Arg::Stx` — so there is no `KindInterner` use to thread. The
/// brief's own signature carried it only for symmetry with the other
/// two arms and ended in `let _ = kinds;`; dropping the unused
/// parameter here rather than shipping a discard.
fn add_implicit_arg(app: &mut AppElab) -> Result<(), ElabError> {
    let arg_type = app.get_arg_expected_type()?;
    let arg = app.elab.mk_fresh_expr_mvar(arg_type)?;
    let Node::MVar { id: Some(n) } = app.node(arg) else {
        return Err(ElabError::UnsupportedSyntax(
            "internal invariant: mk_fresh_expr_mvar did not return an mvar node (app::args — \
             not a deferred construct)"
                .to_string(),
        ));
    };
    if is_next_out_param_of_local_instance_and_result(app, arg_type)? {
        // oracle (`App.lean:749-753`): "When the result type is an
        // output parameter, we don't want to propagate the expected
        // type. So, we just mark `propagateExpected := false` to disable
        // it. At `finalize`, we check whether `arg` is still unassigned,
        // if it is, we apply default instances, and try to synthesize
        // pending mvars."
        app.st.result_type_out_param = Some(MVarId(n));
        app.st.propagate_expected = false;
    }
    app.st.to_set_error_ctx.push(MVarId(n));
    add_new_arg(app, arg)
}

/// oracle: `isNextOutParamOfLocalInstanceAndResult` (`App.lean:681-727`)
/// — is the implicit parameter about to be inserted BOTH the result type
/// of the remaining function type AND an `outParam` of some
/// instance-implicit binder in it? The worked example (`App.lean:662-679`):
/// for `fType = {Elem : Type u_3} → [self : Get Cont Idx Elem] → Cont →
/// Idx → Elem` the answer is `true`; one binder earlier, for `Cont`, it
/// is `false`.
///
/// `arg_type` is the parameter's type with annotations consumed
/// (`get_arg_expected_type`), used only to type the probe fvar below.
///
/// The probe fvar (design spec § Amendment 4 item 3). The oracle mints a
/// DANGLING `mkFVar (← mkFreshFVarId)` (`:688`) — no local declaration,
/// purely a token to compare `d.getAppArgs` against by structural
/// equality. `leanr_meta` has no dangling-fvar constructor, so this
/// pushes a real `lctx` decl under the `lctx_checkpoint`/`lctx_restore`
/// bracket `AppElab::forall_telescope_reducing` already uses, and drops
/// it on every exit path. The two consumers cannot tell the difference:
/// `is_out_param_of` compares `ExprId`s (hash-consed, so the substituted
/// occurrence IS the probe), and the only `infer_type`/`whnf` in the
/// clauses run on the class CONSTANT and its type, which never mention
/// the probe.
fn is_next_out_param_of_local_instance_and_result(
    app: &mut AppElab,
    arg_type: ExprId,
) -> Result<bool, ElabError> {
    // oracle: `unless (← read).resultIsOutParamSupport && (← get).resultTypeOutParam?.isNone do return false`
    if !app.ctx.result_is_out_param_support || app.st.result_type_out_param.is_some() {
        return Ok(false);
    }
    // oracle: `let type := (← get).fType.bindingBody!` — `main` only
    // reaches this arm when `f_type_is_forall` answered true, so the
    // node is a `Forall`; anything else is the oracle's own `!` panic
    // domain, reported rather than unwrapped.
    let Node::Forall { body, .. } = app.node(app.st.f_type) else {
        return Err(ElabError::IllFormedSyntax(
            "isNextOutParamOfLocalInstanceAndResult on a non-forall fType".to_string(),
        ));
    };
    if !is_result_type(app, body, 0) {
        return Ok(false);
    }
    if !has_local_instance_with_out_params(app, body) {
        return Ok(false);
    }
    let checkpoint = app.elab.mctx.lctx_checkpoint();
    let result = (|| {
        let x = app
            .elab
            .mctx
            .push_local_decl(None, arg_type, BinderInfo::Default)
            .map_err(ElabError::from)?;
        // oracle: `type.instantiate1 x`.
        let body_x = app
            .elab
            .mctx
            .instantiate_beta_rev_range(body, std::slice::from_ref(&x))
            .map_err(ElabError::from)?;
        is_out_param_of_local_instance(app, x, body_x)
    })();
    app.elab.mctx.lctx_restore(checkpoint);
    result
}

/// oracle: `isResultType` (`App.lean:693-697`) — walk the remaining
/// binders counting depth, and answer whether the final body is the
/// bound variable `i` binders out, i.e. the parameter being inserted.
/// Pure de Bruijn arithmetic on an UNINSTANTIATED body: no `whnf`, no
/// telescope, exactly as the oracle has it. A `BVarBig` index can never
/// equal a `u32` depth reachable here and falls to the `false` arm.
fn is_result_type(app: &AppElab, ty: ExprId, i: u32) -> bool {
    match app.node(ty) {
        Node::Forall { body, .. } => is_result_type(app, body, i + 1),
        Node::BVar { idx } => idx == i,
        _ => false,
    }
}

/// oracle: `hasLocalInstanceWithOutParams` (`App.lean:700-706`) — the
/// QUICK FILTER: does any instance-implicit binder in `ty` have, at the
/// head of its domain, a class with output parameters? Reads the
/// `classExtension` through `MetaCtx::has_out_params` (`Class.lean:85-88`)
/// and inspects nothing else; the positional test is
/// `is_out_param_of_local_instance`'s.
fn has_local_instance_with_out_params(app: &AppElab, mut ty: ExprId) -> bool {
    loop {
        let Node::Forall {
            binder_type,
            body,
            binder_info,
            ..
        } = app.node(ty)
        else {
            return false;
        };
        if binder_info == BinderInfo::InstImplicit {
            if let Node::Const {
                name: Some(class), ..
            } = app.node(app.app_fn(binder_type))
            {
                if app.elab.mctx.has_out_params(class) {
                    return true;
                }
            }
        }
        ty = body;
    }
}

/// oracle: `isOutParamOfLocalInstance` (`App.lean:708-716`) — for each
/// instance-implicit binder `[C a₁ .. aₙ]` whose class has outParams,
/// infer `C`'s own type and ask `is_out_param_of` whether the probe `x`
/// sits at an `outParam` position. Later binders are walked WITHOUT
/// instantiating (the oracle recurses on the raw `b`), so their domains
/// may carry loose bvars — harmless, since only the spine's head
/// constant and the argument `ExprId`s are read.
fn is_out_param_of_local_instance(
    app: &mut AppElab,
    x: ExprId,
    mut ty: ExprId,
) -> Result<bool, ElabError> {
    loop {
        let Node::Forall {
            binder_type,
            body,
            binder_info,
            ..
        } = app.node(ty)
        else {
            return Ok(false);
        };
        if binder_info == BinderInfo::InstImplicit {
            let head = app.app_fn(binder_type);
            if let Node::Const {
                name: Some(class), ..
            } = app.node(head)
            {
                if app.elab.mctx.has_out_params(class) {
                    let c_type = app.elab.mctx.infer_type(head)?;
                    let args = app.app_args(binder_type);
                    if is_out_param_of(app, x, &args, c_type)? {
                        return Ok(true);
                    }
                }
            }
        }
        ty = body;
    }
}

/// oracle: `isOutParamOf` (`App.lean:718-727`) — walk the class type's
/// binders in step with the instance's arguments; `true` at the first
/// position where the argument IS the probe and the binder's domain is
/// `outParam _`. The test is on the class's own TYPE, syntactically
/// (`Expr.isOutParam`), not on `classExtension` positions — that is
/// how the oracle does it, and it is what makes `semiOutParam` a
/// non-match (design spec § Amendment 4 item 2).
///
/// The oracle `whnf`s the class type at every step. A step whose type
/// is already a `Forall` is reduced by nothing, so — as
/// `forall_telescope_reducing` does — reduction is skipped there; a
/// non-`Forall` node goes through `whnf_forall`, and if it is still not
/// a binder the walk ends `false` (`| _ => return false`).
fn is_out_param_of(
    app: &mut AppElab,
    x: ExprId,
    args: &[ExprId],
    mut c_type: ExprId,
) -> Result<bool, ElabError> {
    for &arg in args {
        let reduced = if matches!(app.node(c_type), Node::Forall { .. }) {
            c_type
        } else {
            app.whnf_forall(c_type)?
        };
        let Node::Forall {
            binder_type, body, ..
        } = app.node(reduced)
        else {
            return Ok(false);
        };
        if arg == x && app.is_out_param(binder_type) {
            return Ok(true);
        }
        c_type = body;
    }
    Ok(false)
}

/// oracle: `processImplicitArg` (`App.lean:879-885`) — under `@`, an
/// implicit parameter is filled from the positional arguments exactly
/// like an explicit one.
fn process_implicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.ctx.explicit {
        process_explicit_arg(app, kinds, binder_name)
    } else {
        add_implicit_arg(app)?;
        Ok(true)
    }
}

/// oracle: `processStrictImplicitArg` (`App.lean:887-895`) — a strict
/// implicit is inserted ONLY when there is still an argument to
/// process; otherwise the application finalizes here. This is the one
/// arm whose difference from `processImplicitArg` is invisible on
/// single-argument corpus terms, so `app_smoke.rs` gets a direct test.
fn process_strict_implicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.ctx.explicit {
        process_explicit_arg(app, kinds, binder_name)
    } else if app.has_args_to_process() {
        add_implicit_arg(app)?;
        Ok(true)
    } else {
        Ok(false)
    }
}

/// oracle: `processInstImplicitArg` (`App.lean:903-923`, confirmed
/// against the pinned source: `processInstImplicitArg` itself is
/// `903-917`, its `where mkInstMVar` clause `919-923` — the brief's
/// combined `903-923` citation is accurate).
///
/// Both halves, per the seam attribution P1 left here: under `@` an
/// instance-implicit parameter is filled POSITIONALLY, except that a
/// literal `_` is STILL synthesized (`nextArgHole?`, :905-911) — the
/// oracle's own comment: "We still use typeclass resolution for `_`
/// arguments."
fn process_inst_implicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.ctx.explicit {
        if next_arg_hole(app, kinds).is_some() {
            let ty = app.get_arg_expected_type()?;
            mk_inst_mvar(app, ty, binder_name)?;
            // oracle: `modify fun s => { s with args := s.args.tail! }`
            // (`App.lean:912`) — the hole is CONSUMED even though it was
            // not elaborated. `next_arg_hole` only PEEKED (see its own
            // doc); this is the oracle's own separate consume step, done
            // here rather than inside the peek.
            app.st.args.remove(0);
            return Ok(true);
        }
        return process_explicit_arg(app, kinds, binder_name);
    }
    let ty = app.get_arg_expected_type()?;
    mk_inst_mvar(app, ty, binder_name)?;
    Ok(true)
}

/// oracle: `nextArgHole?` (`App.lean:300-303`) — a PURE PEEK: `match
/// (← get).args with Arg.stx stx@(hole) :: _ => pure stx | _ => none`,
/// no `modify` anywhere in its body. The oracle's own consume step
/// (`s.args.tail!`) is a SEPARATE line inside `processInstImplicitArg`
/// (`App.lean:912`), run only on the branch that actually took the
/// hole — which is exactly why `process_inst_implicit_arg` above does
/// its own `app.st.args.remove(0)` rather than this function doing it:
/// consuming here would double-consume on that branch and wrongly
/// consume on the `else` branch (`processExplicitArg`), which must see
/// the argument still present.
fn next_arg_hole(app: &AppElab, kinds: &KindInterner) -> Option<()> {
    let Some(Arg::Stx(elem)) = app.st.args.first() else {
        return None;
    };
    (kinds.name(elem.kind()) == "Lean.Parser.Term.hole").then_some(())
}

/// oracle: `mkInstMVar` (`App.lean:919-923`).
///
/// `MVarKind::Synthetic`, NOT `SyntheticOpaque`: an instance mvar must
/// remain assignable by `isDefEq` (that is precisely what
/// `PostponeBehavior::Partial` relies on — "this kind of metavariable
/// are not synthetic opaque", `SyntheticMVars.lean:436-437`).
///
/// The oracle's `mkInstMVar` also calls `registerMVarArgName
/// arg.mvarId! argName` via `addNewArg` (`App.lean:428`) — pure
/// diagnostics (`TermElabM.lean:887`, the `mvarErrorInfos`-adjacent
/// "which parameter name does this mvar belong to" table this crate's
/// deferred prose layer would need, design spec § Amendment, item 2).
/// `add_new_arg` here, like `elab_and_add_new_arg`'s own
/// `_binder_name` before it, takes no name parameter at all — the same
/// established P1 precedent, not a new gap this task introduces — so
/// `binder_name` is discarded rather than threaded to nowhere.
fn mk_inst_mvar(
    app: &mut AppElab,
    ty: ExprId,
    binder_name: Option<NameId>,
) -> Result<ExprId, ElabError> {
    let (arg, mvar_id) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(ty, MVarKind::Synthetic)?;
    app.st.inst_mvars.push(mvar_id);
    let _ = binder_name;
    add_new_arg(app, arg)?;
    Ok(arg)
}

/// oracle: `addNewArg` (`App.lean:418-429`) — `f := f arg`, push onto
/// `fArgs`, and advance `fType` to its BINDING BODY (not a
/// re-instantiated type: the loose bvars are instantiated lazily by
/// `get_f_type`, which is what makes `paramIdx`/`fArgs` the single
/// source of truth).
pub fn add_new_arg(app: &mut AppElab, arg: ExprId) -> Result<(), ElabError> {
    let body = match app.node(app.st.f_type) {
        Node::Forall { body, .. } => body,
        _ => {
            return Err(ElabError::IllFormedSyntax(
                "add_new_arg on a non-forall fType".to_string(),
            ))
        }
    };
    // `base = Some(view.store)`, never `None`: both `app.st.f` (the head
    // constant, built by `head.rs` against the persistent store) and
    // `arg` can be PERSISTENT-region `ExprId`s, and `store_mut()` is the
    // SCRATCH store — routing a persistent id through it without a base
    // is `Store::store_for`'s own documented "silent wrong-row read"
    // (a `debug_assert!` in debug builds, nothing at all in release).
    let base = app.elab.view.store;
    let f = app
        .elab
        .mctx
        .store_mut()
        .expr_app(Some(base), app.st.f, arg)
        .map_err(leanr_meta::MetaError::from)?;
    app.st.f = f;
    app.st.f_args.push(arg);
    app.st.f_type = body;
    Ok(())
}

/// oracle: `elabAndAddNewArg` (`App.lean:431-441`) — elaborate the
/// argument against the parameter's expected type, `ensureArgType` it,
/// then `addNewArg`.
fn elab_and_add_new_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    _binder_name: Option<NameId>,
    arg: Arg,
) -> Result<(), ElabError> {
    let expected = app.get_arg_expected_type()?;
    let val = match arg {
        Arg::Expr(e) => e,
        Arg::Stx(elem) => app.elab.elab_term(&elem, kinds, Some(expected))?,
    };
    // oracle: `ensureArgType` = `ensureHasType expected val`
    // (coercion-inserting from P4 onward; here the M4b-1 behavior, which
    // ERRORS on a defeq mismatch).
    let inferred = app.elab.mctx.infer_type(val)?;
    if !app.elab.mctx.is_def_eq(inferred, expected)? {
        return Err(ElabError::TypeMismatch {
            expected,
            got: inferred,
        });
    }
    add_new_arg(app, val)
}
