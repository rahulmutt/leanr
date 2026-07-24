//! The identifier leaf: an identifier resolving to a global constant
//! elaborates to `Expr.const name levels`, with ONE FRESH universe
//! level metavariable per the constant's `levelParams` — oracle:
//! `Lean.Elab.Term.elabIdent` (`Lean/Elab/App.lean:2246`, `:= elabAtom`)
//! reduces, for a bare identifier with no application/explicit
//! universes/dot-notation (this slice's scope — see `resolve.rs`'s own
//! doc comment), to `Lean.Elab.Term.resolveName`/`resolveName'`
//! (`Lean/Elab/Term/TermElabM.lean:2170`, `:2201`) calling `mkConsts`
//! (`:2145`) calling `Lean.Elab.Term.mkConst`
//! (`Lean/Elab/Term/TermElabM.lean:2117-2126`): "Create an `Expr.const`
//! using the given name and explicit levels. Remark: fresh universe
//! metavariables are created if the constant has more universe
//! parameters than `explicitLevels`" — slice 1 has no `.{...}` explicit
//! universe syntax, so `explicitLevels` is always empty and EVERY
//! `levelParams` entry gets its own fresh mvar.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxToken;

use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::resolve::resolve_global;

/// `tok` is the `ident` syntax TOKEN itself — NOT a `SyntaxNode` (Task 5
/// reconciliation, see `dispatch.rs`'s own module doc: a bare identifier
/// is an unwrapped rowan leaf token, `Prim::Ident`'s `self.bump(t,
/// KIND_IDENT)`, never node-wrapped the way `str`/`num`/`char` are).
/// Its `.text()` is the identifier's raw source text — a single lexer
/// token that already includes every `.`-separated component
/// (`leanr_syntax::lex`'s `hierarchical_idents_are_one_token`), so a
/// dotted name like `Nat.succ` arrives here as ONE string, split below
/// exactly the way every other dotted-name builder in this workspace
/// does (`leanr_meta`'s own `intern_dotted`/`dotted_name` test helpers,
/// `pub(crate)`/test-only there and so not reusable from this crate).
pub fn elab_ident(
    elab: &mut TermElabM,
    tok: &SyntaxToken,
    _kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let raw = tok.text();
    let name = intern_dotted(elab, raw)?;
    // Task 3 (binders) addition: a local variable shadows a same-named
    // global constant, and must be checked FIRST — oracle: `elabIdent`
    // consults the local context before falling back to
    // `resolveGlobalConst`. `MetaCtx::lctx_lookup_by_name` (leanr_meta,
    // additive/TCB-neutral, mirroring the oracle's own
    // `LocalContext.findFromUserName?`) is a no-op (`None`) whenever
    // `lctx` is empty — every leaf query that never enters a binder falls
    // straight through to `resolve_global` exactly as before this
    // existed. Bypasses `resolve_global`/fresh-level-mvar minting
    // entirely on a hit: an fvar carries no separate `levelParams` the
    // way a global constant does.
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
    let n_params = info.constant_val().level_params.len();
    let mut levels = Vec::with_capacity(n_params);
    for _ in 0..n_params {
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
    // documented hazard). The freshly-minted `levels` are pure scratch
    // data with nothing to dedup against, so `intern_level_list` keeps
    // `base = None`.
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
fn intern_dotted(elab: &mut TermElabM, raw: &str) -> Result<leanr_kernel::bank::NameId, ElabError> {
    let base = elab.view.store;
    let mut id: Option<leanr_kernel::bank::NameId> = None;
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
    use leanr_meta::{Config, MetaCtx};
    use leanr_syntax::{builtin, parse_term, tree::NodeOrToken};

    use crate::elab::TermElabM;

    /// A tiny persistent env declaring one axiom `Foo : Sort 0`, built
    /// directly against the public id-native API — same shape as
    /// `resolve::tests::env_with_foo` (duplicated rather than shared:
    /// this task's scope is `resolve.rs`/`builtin/ident.rs`/
    /// `builtin/lit.rs` only, and the two `#[cfg(test)]` modules are
    /// compiled as entirely separate units with no path between them).
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

    /// The regression this task exists for: `elab_ident`'s OWN pipeline
    /// (`intern_dotted` then `resolve_global`) on an identifier NOT
    /// declared in `env` — unlike `resolve::tests::
    /// unknown_ident_when_not_declared`, which mints the unknown name
    /// directly in the PERSISTENT store and so never reproduces the bug:
    /// `intern_dotted` mints a SCRATCH-region `NameId` for any name not
    /// already interned in the persistent store, which is exactly what
    /// happens for a genuinely unknown/typo'd identifier. Against the
    /// pre-fix `resolve_global` (which re-derived the error text via
    /// `view.store.to_name(None, Some(name))`, `view.store` being the
    /// PERSISTENT store, on a SCRATCH-region `name`) this test either
    /// panicked in `name_row`'s `.expect(..)` or — as observed here,
    /// since the persistent pool from `env_with_foo` is non-empty —
    /// silently returned the WRONG identifier text (a row from the
    /// persistent pool, not "Bar"). Post-fix, `resolve_global` takes the
    /// display text verbatim from `elab_ident`'s own `raw` (the token's
    /// real source text), so this passes without touching the store at
    /// all for the error path.
    #[test]
    fn unknown_ident_via_real_scratch_pipeline() {
        let env = env_with_foo();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            &[],
            &[],
            &[],
            &[],
            &[],
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

        match super::elab_ident(&mut elab, &tok, &parsed.tree.kinds) {
            Err(crate::ElabError::UnknownIdent(s)) => assert_eq!(s, "Bar"),
            other => panic!("expected UnknownIdent(\"Bar\"), got {other:?}"),
        }
    }
}
