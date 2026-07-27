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
use leanr_meta::MVarId;
use leanr_syntax::kind::KindInterner;

use crate::app::expand::{Arg, NamedArg};
use crate::app::state::AppElab;
use crate::error::ElabError;

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
                        return crate::app::finalize::finalize(app);
                    }
                }
                BinderInfo::Implicit => {
                    if !process_implicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app);
                    }
                }
                BinderInfo::StrictImplicit => {
                    if !process_strict_implicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app);
                    }
                }
                BinderInfo::InstImplicit => {
                    // oracle: `processInstImplicitArg` (`App.lean:903-923`)
                    // creates an instance mvar and pushes it onto
                    // `instMVars` for `synthesizeAppInstMVars`. Both need
                    // the synthesis client and the fixpoint.
                    //
                    // SEAM ATTRIBUTION (Task 9): this is the one place in
                    // `app/` where the oracle reads `explicit` and leanr
                    // does not. `processInstImplicitArg` is
                    // `if (← read).explicit then <hole?-or-processExplicitArg>
                    // else discard <| mkInstMVar ..` (`App.lean:904-917`),
                    // so under `@` an instance-implicit parameter is filled
                    // POSITIONALLY (or, for a literal `_`, still synthesized)
                    // and only the `else` half is P2's. Returning the P2 seam
                    // unconditionally therefore over-attributes the `@` slice
                    // to P2 — which is harmless today because it is
                    // UNREACHABLE: `Elab0.lean` declares no `class` and no
                    // `instance`, so no fixture constant has an
                    // `instImplicit` binder for either branch to reach.
                    // Splitting the arm would mean writing the explicit half
                    // with no way to test it; P2, which brings the fixture
                    // classes, owns both halves.
                    return Err(ElabError::UnsupportedSyntax(
                        "instance-implicit arguments require typeclass synthesis \
                         and the synthetic-mvar fixpoint — M4b-3 P2"
                            .to_string(),
                    ));
                }
            }
        } else if app.has_args_to_process() {
            // oracle: `synthesizePendingAndNormalizeFunType`
            // (`App.lean:372-404`) — synthesize pending instance mvars,
            // then re-WHNF; if `fType` is STILL not a forall it tries
            // `coerceToFunction?` and otherwise reports "function
            // expected". Both halves are later plans.
            return Err(ElabError::UnsupportedSyntax(
                "too many arguments: normalizing the function type needs pending-instance \
                 synthesis (M4b-3 P2) and CoeFun (M4b-3 P4)"
                    .to_string(),
            ));
        } else {
            return crate::app::finalize::finalize(app);
        }
    }
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
            // `xDecl.type.cleanupAnnotations`. `consume_type_annotations`
            // is the optParam/autoParam half of `cleanupAnnotations`;
            // the `consumeMData` half is not modelled, so an `MData`-
            // wrapped `optParam` would keep its wrapper here and its
            // default value would count as a dependency. No fixture
            // parameter type carries either wrapper, let alone under
            // `MData`.
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
        if app.consume_type_annotations(param_type)? != param_type {
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
/// annotations changed the term" test `consume_type_annotations` already
/// backs (see `propagate::is_opt_or_auto_param`'s own note).
///
/// Takes the type to walk as a parameter (Task 6): `App.lean:873`'s call
/// site passes `(← getFType)`, but `getResultingTypeCore?`'s own call
/// (`App.lean:484`) passes the SIMULATED remaining type `fType'`, which
/// is not `s.fType`. One function, two call sites, exactly as the oracle
/// has it.
pub(crate) fn has_opt_auto_params(app: &mut AppElab, ty: ExprId) -> Result<bool, ElabError> {
    app.forall_telescope_reducing(ty, |app, xs| {
        for b in xs {
            if app.consume_type_annotations(b.ty)? != b.ty {
                return Ok(true);
            }
        }
        Ok(false)
    })
}

/// oracle: `addImplicitArg` (`App.lean:747-760`). Creates a fresh mvar
/// for the parameter, records it in `toSetErrorCtx` for error
/// attribution, and continues the loop.
///
/// No `kinds` parameter: unlike `process_explicit_arg`'s eventual
/// `elab_and_add_new_arg` call, nothing here parses or elaborates
/// surface syntax — the argument is a freshly minted mvar, not a
/// `Arg::Stx` — so there is no `KindInterner` use to thread. The
/// brief's own signature carried it only for symmetry with the other
/// two arms and ended in `let _ = kinds;`; dropping the unused
/// parameter here rather than shipping a discard.
fn add_implicit_arg(app: &mut AppElab) -> Result<(), ElabError> {
    let arg_type = app.get_arg_expected_type()?;
    // oracle: the `isNextOutParamOfLocalInstanceAndResult` branch
    // (`App.lean:749-757`) sets `resultTypeOutParam?` and disables
    // propagation. It needs class outParam positions from the
    // `classExtension`, which leanr does not decode until P2; the
    // guarding flag (`result_is_out_param_support`) is false in the
    // fixture env, so the branch is inert here rather than skipped
    // silently. `finalize` re-checks `result_type_out_param` (task 4).
    if app.ctx.result_is_out_param_support {
        return Err(ElabError::UnsupportedSyntax(
            "local-instance outParam result type requires classExtension decode — M4b-3 P2"
                .to_string(),
        ));
    }
    let arg = app.elab.mk_fresh_expr_mvar(arg_type)?;
    if let Node::MVar { id: Some(n) } = app.node(arg) {
        app.st.to_set_error_ctx.push(MVarId(n));
    }
    add_new_arg(app, arg)
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
