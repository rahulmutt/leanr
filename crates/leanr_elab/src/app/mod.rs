//! M4b-3 P1: the application elaborator. Oracle: `Lean/Elab/App.lean`'s
//! `ElabAppArgs` namespace. See
//! docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
//! § P1 — the application machinery.
//!
//! NOT in this plan, each a named seam (never a silent fall-through):
//!   instance-implicit arguments + the synthetic-mvar fixpoint . P2
//!   num/char/scientific literals ......................... P3
//!   coercions (CoeT/CoeFun/CoeSort, mkCoe) ............... P4
//!   optParam defaults / autoParam / `..` ellipsis ........ P5
//!   implicit-lambda insertion ............................ P5
//!   overload resolution (candidates > 1) ................. resolve_global slice
//!   elabAsElim, dot notation, LVal machinery ............. M4b-4

pub mod args;
pub mod expand;
pub mod finalize;
pub mod head;
pub mod overload;
pub mod propagate;
pub mod state;

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::app::expand::{Arg, NamedArg};
use crate::app::state::{Context, State};
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `elabApp` (`App.lean:2238-2241`) — `universeConstraintsCheckpoint`
/// wraps the whole thing; that checkpoint maps onto leanr_meta's postponed
/// level-constraint queue and lands in P2 with `process_postponed`.
pub fn elab_app(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let (head, named_args, args, ellipsis) = expand::expand_app(node, kinds)?;
    elab_app_aux(
        elab, &head, kinds, named_args, args, ellipsis, false, expected,
    )
}

/// oracle: `elabAtom` (`App.lean:2243-2244`) — a zero-argument
/// application. This is what `ident`, `@`, `.{u}`, `choice`, `proj` and
/// `dotIdent` all reduce to in the oracle; P1 routes the first three.
pub fn elab_atom(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    elab_app_aux(
        elab,
        elem,
        kinds,
        Vec::new(),
        Vec::new(),
        false,
        false,
        expected,
    )
}

/// oracle: `elabAppAux` (`App.lean:2202-2217`) resolving the head, then
/// `elabAppArgs` (`App.lean:1351-1394`) building the `Context`/`State`
/// the loop runs over.
///
/// Task 8 peels `@` and `.{u, v}` HERE, not in `head.rs`: `@f a b` and
/// `f.{u} a` wrap the SAME head syntax the plain form has, so stripping
/// the wrapper (setting `explicit := true` / collecting the explicit
/// level list) before `elab_app_fn` keeps `head.rs` about NAMES only.
/// Until then `explicit` is always `false` and the explicit-level list
/// always empty; `elab_app_fn` names any non-`ident` head as an M4b-4
/// seam rather than mis-elaborating it.
#[allow(clippy::too_many_arguments)]
fn elab_app_aux(
    elab: &mut TermElabM,
    head: &SynElem,
    kinds: &KindInterner,
    named_args: Vec<NamedArg>,
    args: Vec<Arg>,
    ellipsis: bool,
    explicit: bool,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let candidates = head::elab_app_fn(elab, head, kinds, &[])?;
    let f = overload::expect_single(candidates)?;

    // oracle: `elabAppArgs`'s first two lines — `let fType ← inferType f;
    // let fType ← instantiateMVars fType`.
    let f_type = elab.mctx.infer_type(f)?;
    let f_type = elab.mctx.instantiate_mvars(f_type)?;

    // oracle: `App.lean:1374`'s `if (← isElabAsElim ..) then
    // elabAppArgsAux ..` branch reads the `@[elab_as_elim]` attribute —
    // an environment EXTENSION leanr does not decode, so there is no way
    // to consult it here and no way for it to be true. Task 9 records
    // this as a fixture-scoped seam and adds the fixture-source gate
    // (no `@[elab_as_elim]` declaration in `Elab0.lean`) that keeps the
    // branch inert rather than silently mis-taken.
    let ctx = Context {
        ellipsis,
        explicit,
        // oracle: `App.lean:1355`'s `env.contains ``Lean.Internal.coeM &&
        // resultIsOutParamSupport && !explicit`. Computed the same way,
        // not shortcut to `false`: it happens to be false throughout the
        // hermetic fixture env because prelude-mode `Elab0` declares no
        // `Lean.Internal.coeM`, and that must stay an OBSERVATION about
        // the env rather than an assumption baked into the code.
        result_is_out_param_support: env_contains_coe_m(elab)? && !explicit,
        // oracle: `Context.numImplicitParams` — the max over `namedArgs`.
        num_implicit_params: named_args
            .iter()
            .map(|n| n.num_implicit_params)
            .max()
            .unwrap_or(0),
    };
    let st = State {
        f,
        f_type,
        f_args: Vec::new(),
        args,
        named_args,
        expected_type: expected,
        eta_args: Vec::new(),
        to_set_error_ctx: Vec::new(),
        inst_mvars: Vec::new(),
        // oracle: `propagateExpectedTypeFor f` (`App.lean:1381`) consults
        // the `elab_without_expected_type` attribute — another extension
        // leanr does not decode, so this is `true` for every head, which
        // is the attribute's own default. Task 9 records the seam.
        propagate_expected: true,
        result_type_out_param: None,
        found_named_args: Vec::new(),
    };
    let mut app = state::AppElab { ctx, st, elab };
    // Bracket the whole loop (M4b-2's `binder.rs:217,226` idiom):
    // `args::add_eta_arg` pushes one fvar per eta-expanded parameter
    // into the ambient `lctx`, and `finalize`'s `mkLambdaFVars`
    // abstracts them back out — but only on the success path. Restoring
    // on EVERY exit is what keeps an eta fvar (or one left behind by a
    // failed argument elaboration) from leaking into the context a
    // caller goes on to elaborate in. The oracle gets this for free from
    // `withLocalDeclD`'s scoping in `addEtaArg`; leanr's
    // `push_local_decl` is unscoped, so the bracket is explicit.
    let checkpoint = app.elab.mctx.lctx_checkpoint();
    let result = args::main(&mut app, kinds);
    app.elab.mctx.lctx_restore(checkpoint);
    result
}

/// oracle: `env.contains ``Lean.Internal.coeM` (`App.lean:1355`). The
/// name has to be interned before it can be looked up — `EnvView` is
/// id-native and has no by-string entry point — which is exactly what
/// `head::intern_dotted` does, `base = Some(view.store)` so an already
/// declared constant's PERSISTENT `NameId` is found rather than shadowed
/// by a fresh scratch row `EnvView::get` would never resolve.
fn env_contains_coe_m(elab: &mut TermElabM) -> Result<bool, ElabError> {
    let name = head::intern_dotted(elab, "Lean.Internal.coeM")?;
    Ok(elab.view.get(name).is_some())
}
