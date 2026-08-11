//! `elabAppFn`: resolve the application head to a candidate list.
//! Oracle: `App.lean`'s `elabAppFn` ident case, which for a bare
//! identifier reduces to `resolveName`/`mkConsts`/`mkConst`
//! (`Lean/Elab/Term/TermElabM.lean:2117-2126`, `:2145`, `:2170`).
//!
//! This file is where M4b-1's `builtin/ident.rs` went. That module was
//! a SIMPLIFICATION, not a layer: `elabIdent := elabAtom`
//! (`App.lean:2246`), so a bare identifier is a zero-argument
//! application in the oracle and its implicit parameters are inserted
//! by `ElabAppArgs.main` like any other application's. Keeping a
//! separate leaf path would diverge on every polymorphic constant.
//!
//! Returns a Vec because the oracle's `elabAppFn` returns a candidate
//! ARRAY (overloaded names). Exactly-one is the only P1 shape; see
//! `overload.rs`.

use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_syntax::kind::KindInterner;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::resolve::resolve_global;

/// `heed_elab_as_elim` is the oracle's own two-line gate at the top of
/// `elabAsElim?` (`App.lean:1398-1399`): `unless (← read).heedElabAsElim
/// do return none` followed by `if explicit || ellipsis then return
/// none`. leanr never turns the reader field off (`withoutElabAsElim`,
/// `TermElabM.lean:733`, has no leanr counterpart — nothing in this
/// crate suppresses the branch), so the caller computes this as
/// `!explicit && !ellipsis`, which is exactly the second line. Threaded
/// rather than read off `AppElab` because `elab_app_fn` runs BEFORE the
/// `Context`/`State` exist — `elab_app_aux` needs the head's type to
/// build them.
pub fn elab_app_fn(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    explicit_levels: &[LevelId],
    heed_elab_as_elim: bool,
) -> Result<Vec<ExprId>, ElabError> {
    match (kinds.name(elem.kind()), elem) {
        ("<ident>", leanr_syntax::tree::NodeOrToken::Token(tok)) => Ok(vec![elab_ident_head(
            elab,
            tok.text(),
            explicit_levels,
            heed_elab_as_elim,
        )?]),
        // Task 9's seam audit split this from the catch-all below: the
        // two are DIFFERENT oracle arms with different owners, and one
        // message for both named the wrong one. `(f) a`, `(fun x => x) a`
        // and `(f : T) a` reach no LVal machinery at all in the oracle
        // (verified against the pinned oracle: `(Nat.succ) Nat.zero` and
        // `(fun (x : Nat) => x) Nat.zero` both elaborate cleanly there),
        // so calling them "dot notation" pointed a reader at M4b-4's
        // `resolveLValAux` for a construct that never touches it.
        (other, _) if is_lval_head(other) => Err(ElabError::UnsupportedSyntax(format!(
            "application head `{other}` needs the dot-notation / LVal machinery \
             (`elabAppFn`'s field/fieldIdx/dotIdent arms, App.lean:2067-2109, and its \
             `choiceKind` fan-out at :2062-2065) — M4b-4"
        ))),
        (other, _) => Err(ElabError::UnsupportedSyntax(format!(
            "application head `{other}` is a general term in function position — the \
             oracle takes `elabAppFn`'s generic branch (App.lean:2120-2138: `elabTerm f \
             none` then `elabAppLVals`), which succeeds; M4b-3 P1 scopes `elabAppFn` to \
             its ident case (design spec § P1), so the rest of `elabAppFn` is deferred \
             with the LVal machinery to M4b-4"
        ))),
    }
}

/// The application-head kinds whose oracle arm is the LVal / dot-notation
/// subsystem: `elabAppFn`'s `` `($(e).$field:ident) ``/`` `($e |>.$..) ``/
/// `` `($(e).$idx:fieldIdx) `` arms (`App.lean:2084-2097`), its
/// `` `(.$id:ident) `` arms (`:2106-2109`), the `namedPattern` arm
/// (`:2098-2100`, an outright error outside pattern position), and the
/// `choiceKind` fan-out (`:2062-2065`). None of them is routed by
/// `dispatch` either — see that module's deferral table.
fn is_lval_head(kind: &str) -> bool {
    matches!(
        kind,
        "Lean.Parser.Term.proj"
            | "Lean.Parser.Term.pipeProj"
            | "Lean.Parser.Term.dotIdent"
            | "Lean.Parser.Term.namedPattern"
            | "choice"
    )
}

/// oracle: `elabExplicitUnivs` (`App.lean:1899-1900`) —
/// `lvls.foldrM (init := []) fun stx lvls => return (← elabLevel stx)::lvls`,
/// i.e. elaborate every level of a `.{u, v}` suffix and keep them in
/// SOURCE ORDER (the `foldrM` builds the list right-to-left by consing,
/// which preserves order; it is not a reversal).
///
/// The level elaborator itself is `builtin::sort::elab_level`, the same
/// `Lean.Elab.Level.elabLevel` the `Sort u`/`Type u` path already calls
/// — reused, not re-implemented, so `max`/`imax`/`paren`/`addLit` stay
/// named seams in exactly one place.
pub(super) fn elab_explicit_univs(
    elab: &mut TermElabM,
    lvls: &[SynElem],
    kinds: &KindInterner,
) -> Result<Vec<LevelId>, ElabError> {
    lvls.iter()
        .map(|stx| crate::builtin::sort::elab_level(elab, stx, kinds))
        .collect()
}

/// The former `builtin::ident::elab_ident`, plus `explicit_levels`
/// (Task 8's `.{u}`): oracle `mkConst` creates fresh universe mvars only
/// for the levelParams NOT covered by explicit levels
/// (`TermElabM.lean:2117-2126`) — "Create an `Expr.const` using the
/// given name and explicit levels. Remark: fresh universe metavariables
/// are created if the constant has more universe parameters than
/// `explicitLevels`". Task 8's `.{u, v}` suffix (`app::mod`'s
/// `peel_head` -> `elab_explicit_univs`) is the only producer of a
/// non-empty `explicit_levels`; without one, every `levelParams` entry
/// gets its own fresh mvar, exactly as M4b-1's leaf elaborator did.
///
/// `raw` is the identifier's raw source text — a single lexer token that
/// already includes every `.`-separated component (`leanr_syntax::lex`'s
/// `hierarchical_idents_are_one_token`), so a dotted name like
/// `Nat.succ` arrives here as ONE string, split by `intern_dotted` below
/// exactly the way every other dotted-name builder in this workspace
/// does (`leanr_meta`'s own `intern_dotted`/`dotted_name` test helpers,
/// `pub(crate)`/test-only there and so not reusable from this crate).
fn elab_ident_head(
    elab: &mut TermElabM,
    raw: &str,
    explicit_levels: &[LevelId],
    heed_elab_as_elim: bool,
) -> Result<ExprId, ElabError> {
    let name = intern_dotted(elab, raw)?;
    // M4b-2 (binders): a local variable shadows a same-named global
    // constant, and must be checked FIRST — oracle: `elabIdent` consults
    // the local context before falling back to `resolveGlobalConst`.
    // `MetaCtx::lctx_lookup_by_name` (leanr_meta, additive/TCB-neutral,
    // mirroring the oracle's own `LocalContext.findFromUserName?`) is a
    // no-op (`None`) whenever `lctx` is empty — every query that never
    // enters a binder falls straight through to `resolve_global` exactly
    // as before this existed. Bypasses `resolve_global`/fresh-level-mvar
    // minting entirely on a hit: an fvar carries no separate
    // `levelParams` the way a global constant does.
    if let Some(fvar) = elab.mctx.lctx_lookup_by_name(name) {
        return Ok(fvar);
    }
    // `raw` (the identifier's own source text) doubles as `resolve_global`'s
    // error-message `display` — see that function's own doc comment for why
    // `name` itself (frequently a SCRATCH-region id here, minted by
    // `intern_dotted` just above for any identifier not already interned in
    // the persistent store) cannot safely be re-rendered through
    // `view.store` alone.
    let cname = resolve_global(&elab.view, name, raw)?;

    let info = elab
        .view
        .get(cname)
        .expect("resolve_global only returns names EnvView::get resolves");

    // oracle: `shouldElabAsElim` (`App.lean:1322-1328`) is
    //   `isRec declName || isCasesOnRecursor env declName
    //    || isBRecOnRecursor env declName || isRecOnRecursor env declName
    //    || elabAsElim.hasTag env declName`
    // and when it holds, `elabAppArgs` (`App.lean:1373`) diverts the
    // WHOLE application to `ElabElim.main` instead of `ElabAppArgs.main`
    // — a different elaborator producing a different term.
    //
    // P1 can decide only the FIRST of those five disjuncts. `isRec` is
    // `isRecCore` (`MonadEnv.lean:35-36`), a plain constant-kind test,
    // and leanr's environment carries `ConstantInfo::Rec(RecursorVal)`
    // already. The three `is*Recursor` predicates are
    // `isAuxRecursorWithSuffix` (`AuxRecursor.lean:39-51`), which reads
    // the `auxRecExt` tag extension, and the last is the `elabAsElim`
    // tag extension — neither is decoded anywhere in leanr. So this
    // guard is PARTIAL BY CONSTRUCTION, and deliberately so: seaming
    // what P1 can detect is strictly better than emitting a knowingly
    // different term for all five cases.
    //
    // STILL DIVERGENT, with no seam: `Nat.casesOn`, `Nat.recOn`,
    // `Nat.brecOn` (and every other aux recursor), plus anything
    // carrying `@[elab_as_elim]`. Those take the ordinary path here and
    // emit a term the oracle does not. `tests/seam_audit.rs`'s
    // `fixture_declares_no_undecoded_elab_attributes` is the backstop
    // that keeps such a query out of the committed corpus; M4b-4 owns
    // the `auxRecExt` decode and `ElabElim` itself.
    //
    // Measured, not assumed (Task 9, pinned oracle via `dump_elab.lean`'s
    // own entry point): `Nat.rec` elaborates to a bare `?m` there — the
    // branch postpones on the missing expected type — where leanr
    // emitted `const Nat.rec [?u]`.
    //
    // This guard is also an OVER-approximation in one direction the
    // oracle is finer about: `elabAsElim?` (`App.lean:1402-1420`) falls
    // back to the standard elaborator when the motive has ALREADY been
    // supplied, which needs `getElabElimInfo`'s `motivePos` — M4b-4
    // machinery. So `Nat.rec (motive := ..) ..` is seamed here where the
    // oracle would elaborate it normally. A named error is the safe
    // direction of that trade; a wrong `Expr` is not.
    if heed_elab_as_elim && matches!(info, leanr_kernel::ConstantInfo::Rec(_)) {
        return Err(ElabError::UnsupportedSyntax(format!(
            "`{raw}` is a recursor — the oracle elaborates eliminator-headed \
             applications with `ElabElim.main` (`shouldElabAsElim`, App.lean:1322-1328; \
             diverted at :1373), which needs `motivePos` — M4b-4"
        )));
    }

    let n_params = info.constant_val().level_params.len();
    // oracle: `mkConst` errors when the user wrote MORE explicit levels
    // than the constant has parameters, rather than truncating.
    if explicit_levels.len() > n_params {
        return Err(ElabError::TooManyUniverseLevels(raw.to_string()));
    }
    let mut levels = Vec::with_capacity(n_params);
    levels.extend_from_slice(explicit_levels);
    for _ in explicit_levels.len()..n_params {
        levels.push(elab.mk_fresh_level_mvar()?);
    }
    // `base = Some(elab.view.store)` from here on: `cname` is a
    // PERSISTENT-region `NameId` (`resolve_global` only ever returns a
    // name `EnvView::get` resolved, and every constant in `env.constants`
    // is persistent-region by construction — `Environment::admit_unchecked`
    // /decode never inserts a scratch id there). `Store::expr_const`'s
    // internal `name_hash_of` routes a persistent id through `base` when
    // `self` (the SCRATCH store `store_mut()` returns) isn't itself the
    // persistent store — passing `None` here trips `store_for`'s own
    // misrouting `debug_assert` (confirmed empirically: the gate panicked
    // on exactly this before the fix, and worse, would have silently
    // read the WRONG name row in a release build per that same method's
    // documented hazard).
    //
    // `intern_level_list` keeps `base = None`, and Task 8 RE-CHECKED
    // that now that `explicit_levels` has a producer and a
    // caller-supplied `LevelId` is no longer guaranteed to be
    // freshly-minted scratch data: `intern_level_list`'s `base` is a
    // DEDUP-ONLY parameter (`bank/mod.rs:564-584` — it consults
    // `b.level_lists` for an existing row and otherwise stores the
    // `LevelId`s VERBATIM), unlike every `store_for`-routing accessor.
    // It never resolves a child id, so no child's region can be
    // misrouted by it, whatever `base` is; the only effect of `None` is
    // skipping the persistent-side dedup lookup and minting a scratch
    // row. Each `LevelId` inside is re-routed by its OWN scratch bit at
    // every later read (`level_list_at` then `level_row`, both
    // `base`-taking), so mixing regions inside the list is safe.
    let base = elab.view.store;
    let levels_id = elab
        .mctx
        .store_mut()
        .intern_level_list(None, &levels)
        .map_err(leanr_meta::MetaError::from)?;
    let id = elab
        .mctx
        .store_mut()
        .expr_const(Some(base), Some(cname), levels_id)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(id)
}

/// Intern a (possibly dotted) identifier's raw source text as a
/// `NameId` — the store has no direct "parse a `&str` into a `Name`"
/// entry point (`Store::intern_name` only bridges FROM an already-built
/// `Arc<Name>`, `#[cfg(test)]`-only besides), so this builds the chain
/// component-by-component the same way `leanr_meta`'s own
/// `intern_dotted`/`dotted_name` (private test helpers there) do.
///
/// `base = Some(elab.view.store)`, not `None`: this has to find the
/// SAME `NameId` `resolve_global`/`EnvView::get` will look up against
/// the PERSISTENT store, not mint an unrelated fresh row in the
/// elaborator's own SCRATCH store (`elab.mctx.store_mut()`) — a global
/// like `Nat` is already interned in the persistent bank (every
/// declared constant's name lives there), so `base`'s dedup lookup
/// (`Store::name_str`'s own `if let Some(b) = base { .. }` branch)
/// finds and reuses the EXISTING persistent id instead of shadowing it
/// with a same-text-but-different-id scratch row that `EnvView::get`
/// would never resolve (confirmed empirically: omitting `base` here
/// made every query fail with `UnknownIdent`, and the resulting error
/// path — reading a scratch-region id back out of the persistent store
/// with `base = None` — is `EnvView::get_with`'s own documented
/// misrouting hazard, which is how the divergence surfaced as an
/// unrelated existing name (`Nat.brecOn.go`) rather than a clean miss).
pub(crate) fn intern_dotted(elab: &mut TermElabM, raw: &str) -> Result<NameId, ElabError> {
    let base = elab.view.store;
    let mut id: Option<NameId> = None;
    for part in raw.split('.') {
        let store = elab.mctx.store_mut();
        let s = store
            .intern_str(Some(base), part)
            .map_err(leanr_meta::MetaError::from)?;
        id = Some(
            store
                .name_str(Some(base), id, s)
                .map_err(leanr_meta::MetaError::from)?,
        );
    }
    Ok(id.expect("ident node's text is never empty (parser-validated token)"))
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::Store;
    use leanr_kernel::{AxiomVal, ConstantInfo, ConstantVal, Environment};
    use leanr_meta::{Config, EnvExtensions, MetaCtx};
    use leanr_syntax::{builtin, parse_term, tree::NodeOrToken};

    use crate::elab::TermElabM;

    /// A tiny persistent env declaring one axiom `Foo : Sort 0`, built
    /// directly against the public id-native API — same shape as
    /// `resolve::tests::env_with_foo` (duplicated rather than shared:
    /// the two `#[cfg(test)]` modules are compiled as entirely separate
    /// units with no path between them).
    fn env_with_foo() -> Environment {
        let mut env = Environment::default();
        let prop = {
            let store = env.store_mut();
            let zero = store.level_zero(None).unwrap();
            store.expr_sort(None, zero).unwrap()
        };
        let foo = {
            let store = env.store_mut();
            let s = store.intern_str(None, "Foo").unwrap();
            store.name_str(None, None, s).unwrap()
        };
        let ci = ConstantInfo::Axiom(AxiomVal {
            val: ConstantVal {
                name: foo,
                level_params: vec![],
                ty: prop,
            },
            is_unsafe: false,
        });
        env.admit_unchecked(ci).unwrap();
        env
    }

    /// The regression M4b-1's `builtin/ident.rs` carried, moved here
    /// with the code it guards (M4b-3 P1 task 4): `elab_ident_head`'s
    /// OWN pipeline (`intern_dotted` then `resolve_global`) on an
    /// identifier NOT declared in `env` — unlike `resolve::tests::
    /// unknown_ident_when_not_declared`, which mints the unknown name
    /// directly in the PERSISTENT store and so never reproduces the bug:
    /// `intern_dotted` mints a SCRATCH-region `NameId` for any name not
    /// already interned in the persistent store, which is exactly what
    /// happens for a genuinely unknown/typo'd identifier. Against the
    /// pre-fix `resolve_global` (which re-derived the error text via
    /// `view.store.to_name(None, Some(name))`, `view.store` being the
    /// PERSISTENT store, on a SCRATCH-region `name`) this test either
    /// panicked in `name_row`'s `.expect(..)` or — as observed then,
    /// since the persistent pool from `env_with_foo` is non-empty —
    /// silently returned the WRONG identifier text (a row from the
    /// persistent pool, not "Bar"). Post-fix, `resolve_global` takes the
    /// display text verbatim from the token's real source text, so this
    /// passes without touching the store at all for the error path.
    #[test]
    fn unknown_ident_via_real_scratch_pipeline() {
        let env = env_with_foo();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions::default(),
        );
        let mut elab = TermElabM::new(mctx, view);

        let snap = builtin::snapshot();
        let parsed = parse_term("Bar", &snap);
        assert!(
            parsed.errors.is_empty(),
            "parse errors: {:?}",
            parsed.errors
        );
        let root = parsed.tree.root();
        let tok = match root.first_child_or_token() {
            Some(NodeOrToken::Token(t)) => t,
            other => panic!("expected a bare ident token, got {other:?}"),
        };

        match super::elab_ident_head(&mut elab, tok.text(), &[], true) {
            Err(crate::ElabError::UnknownIdent(s)) => assert_eq!(s, "Bar"),
            other => panic!("expected UnknownIdent(\"Bar\"), got {other:?}"),
        }
    }
}
