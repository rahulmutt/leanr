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
    let cname = resolve_global(&elab.view, name)?;

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
