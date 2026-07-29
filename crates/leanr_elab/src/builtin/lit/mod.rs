//! Literal term elaborators.
//!
//! Exactly one literal is a LEAF (design spec § Scope): a string
//! literal elaborates straight to `Expr.lit (.strVal _)`, no instance
//! search, no `OfNat`/`Char.ofNat` machinery. `num` is NOT a leaf — it
//! elaborates through an application (`@OfNat.ofNat.{u} ?α (rawNatLit
//! v) ?inst`) whose instance argument needs synthesis, and whose
//! carrier `?α` is fixed by the DEFAULT-INSTANCE rung of the
//! synthetic-mvar ladder when nothing else determines it. M4b-3 P3
//! task 6 lands it here alongside `elab_str`.
//!
//! `char` (`Char.ofNat (rawNatLit c)`) and `scientific`
//! (`OfScientific.ofScientific`) are M4b-3 P3 task 7's and are NOT
//! registered yet — they reach `dispatch`'s catch-all, named by kind.
//! The helpers below ([`mk_fresh_type_mvar_for`], [`const_with_level`],
//! [`mk_raw_nat_lit`], [`app_n`]) are shared with them by design.
//!
//! The token DECODERS (raw source text -> value) live in the sibling
//! `decode` module; this one holds only the elaborators and the
//! `Expr`-building helpers.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId};
use leanr_kernel::Nat;
use leanr_meta::{MVarId, MVarKind};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(crate) mod decode;

/// oracle: `Lean.Elab.Term.elabStrLit` (`Lean/Elab/BuiltinTerm.lean`) —
/// note the oracle itself never consults `expectedType?` for a string
/// literal (`fun stx _ => ...`); the value comes straight from the
/// syntax, independent of what the caller expects.
pub fn elab_str(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    _kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    // `node` is the `str` syntax node itself (a single atom child in
    // the oracle's own model, `Syntax.mkLit`); its `.text()` is exactly
    // that atom's raw source text — quotes and un-decoded escapes
    // included, no surrounding whitespace (confirmed empirically:
    // leanr's parser discovers trailing trivia lazily, only once the
    // Pratt loop peeks past the already-closed literal node, so it
    // never becomes a child of the literal node itself).
    let raw = node.text().to_string();
    let s = decode::decode_string_literal(&raw);
    let id = elab
        .mctx
        .store_mut()
        .expr_lit_str(None, &s)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(id)
}

/// oracle: `mkFreshTypeMVarFor` (`BuiltinTerm.lean:203-208`) — a fresh
/// SYNTHETIC type mvar, unified with the expected type if there is one.
///
/// `mkFreshTypeMVar kind` is itself `mkFreshLevelMVar` then
/// `mkFreshExprMVar (mkSort u) kind` (`Meta/Basic.lean`), which is why
/// the level mvar is minted here rather than by the caller.
///
/// The unification result is DELIBERATELY discarded (`discard <|
/// isDefEq expectedType typeMVar`): a numeral against an expected type
/// the instance cannot satisfy still elaborates, and the mismatch is
/// reported by `ensureHasType` with better context. A genuine
/// `MetaError` still propagates.
pub(crate) fn mk_fresh_type_mvar_for(
    elab: &mut TermElabM,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let u = elab.mk_fresh_level_mvar()?;
    let sort = elab
        .mctx
        .store_mut()
        .expr_sort(None, u)
        .map_err(leanr_meta::MetaError::from)?;
    let (ty_mvar, _) = elab.mk_fresh_expr_mvar_of_kind(sort, MVarKind::Synthetic)?;
    if let Some(e) = expected {
        let _ = elab.mctx.is_def_eq(e, ty_mvar)?;
    }
    Ok(ty_mvar)
}

/// A fixture constant applied to exactly one universe level:
/// `OfNat.{u}`, `OfNat.ofNat.{u}`, `OfScientific.{u}`.
///
/// `base = Some(view.store)` for the const row (matching
/// `app::head::elab_ident_head`, which is the only other site that
/// builds a constant), `None` for the level list (matching that same
/// site: `intern_level_list`'s `base` is dedup-only and never routes a
/// child id, so `None` merely skips the persistent-side dedup lookup).
pub(crate) fn const_with_level(
    elab: &mut TermElabM,
    name: &str,
    u: LevelId,
) -> Result<ExprId, ElabError> {
    let cname = crate::app::head::intern_dotted(elab, name)?;
    let resolved = crate::resolve::resolve_global(&elab.view, cname, name)?;
    let base = elab.view.store;
    let levels = elab
        .mctx
        .store_mut()
        .intern_level_list(None, &[u])
        .map_err(leanr_meta::MetaError::from)?;
    elab.mctx
        .store_mut()
        .expr_const(Some(base), Some(resolved), levels)
        .map_err(|e| ElabError::from(leanr_meta::MetaError::from(e)))
}

/// A raw `Nat` literal — oracle: `mkRawNatLit` (`Expr.lean`), i.e.
/// `mkLit (.natVal v)` with no `OfNat` wrapper. Takes leanr's
/// arbitrary-precision `Nat` (which is what `Store::expr_lit_nat`
/// stores), so there is no width limit on a numeric literal.
///
/// `base = Some(view.store)` — NOT `elab_str`'s `None`. A string
/// literal is the whole term and never unifies against a
/// persistent-region literal; a numeral's `Expr.lit` becomes an
/// ARGUMENT of `OfNat ?α (lit v)`, which is unified against
/// `instOfNatNat`'s own type from the persistent store, and every
/// application row this crate builds around it uses `Some(base)`
/// (`app/args.rs::add_new_arg`'s own convention and its stated reason).
pub(crate) fn mk_raw_nat_lit(elab: &mut TermElabM, v: &Nat) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    elab.mctx
        .store_mut()
        .expr_lit_nat(Some(base), v)
        .map_err(|e| ElabError::from(leanr_meta::MetaError::from(e)))
}

/// Left-associated application, `base = Some(view.store)` throughout —
/// the oracle's `mkApp2`/`mkApp3`/`mkApp5`.
pub(crate) fn app_n(elab: &mut TermElabM, f: ExprId, args: &[ExprId]) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    let mut cur = f;
    for a in args {
        cur = elab
            .mctx
            .store_mut()
            .expr_app(Some(base), cur, *a)
            .map_err(leanr_meta::MetaError::from)?;
    }
    Ok(cur)
}

/// The `MVarId` behind an `Expr.mvar` node `TermElabM::mk_inst_mvar`
/// just returned.
///
/// oracle: `mvar.mvarId!` (`BuiltinTerm.lean:228`), a partial function
/// that PANICS on anything else. Unreachable by contract here too —
/// `mk_inst_mvar` returns exactly what `mk_fresh_expr_mvar_of_kind`
/// minted — but LOUD rather than silent all the same, the same shape
/// `synthetic::default_inst`'s own `mvar_id_of` uses: skipping the
/// registration silently would drop the numeral's
/// `registerMVarErrorImplicitArgInfo`, which is a wrong (missing)
/// side effect rather than an error.
fn inst_mvar_id(elab: &TermElabM, e: ExprId) -> Result<MVarId, ElabError> {
    let base = elab.view.store;
    let node = elab.mctx.store().expr_node(Some(base), e);
    if let Node::MVar { id: Some(n) } = node {
        return Ok(MVarId(n));
    }
    debug_assert!(false, "mkInstMVar returned a non-metavariable: {node:?}");
    Err(ElabError::UnsupportedSyntax(
        "mkInstMVar returned a non-metavariable — M4b-3 P3 invariant".to_string(),
    ))
}

/// oracle: `elabNumLit` (`BuiltinTerm.lean:210-229`).
///
/// `@OfNat.ofNat.{u} ?α (rawNatLit v) ?inst`, where `?α` is a fresh
/// synthetic type mvar unified with the expected type, `u` is
/// `getDecLevel ?α`, and `?inst` is a `Term.mkInstMVar` for
/// `OfNat.{u} ?α (rawNatLit v)` — so it is synthesized eagerly and
/// registered `.typeClass` only if that is not yet possible.
///
/// With NO expected type nothing determines `?α`, the eager attempt
/// comes back not-ready, and the ladder's default-instance rung is what
/// finally closes the goal — the first construct in leanr's grammar for
/// which that rung does real work.
///
/// The oracle's `extraErrorMsg` ("numerals are polymorphic in Lean…",
/// `:225`) is prose and is not carried (design spec § Amendment,
/// item 2).
pub fn elab_num(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    _kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    // oracle: `stx.isNatLit?` (`:211-213`), which is `isLit? numLitKind`
    // followed by `decodeNatLitVal?` — the node's single atom child's
    // raw text, decoded. `node.text()` is exactly that atom's text
    // (`elab_str`'s own measured note on trivia applies verbatim).
    let raw = node.text().to_string();
    let Some(val) = decode::decode_nat_literal(&raw) else {
        // oracle: `throwIllFormedSyntax`. The decoder is
        // arbitrary-precision, so this means exactly one thing: the
        // token is not a Nat literal.
        return Err(ElabError::IllFormedLiteral(format!(
            "numeric literal `{raw}` is not a Nat literal"
        )));
    };
    let type_mvar = mk_fresh_type_mvar_for(elab, expected)?;
    // oracle: `try getDecLevel typeMVar catch ex => ...` (`:215-224`) —
    // the two failure branches are DISTINCT oracle errors and stay
    // distinct: expected type is a `Prop` (`:221`), versus expected type
    // is universe-polymorphic and MAY be a proposition (`:223`). With no
    // expected type at all the oracle rethrows the original level error
    // (`:224`).
    let u = match elab.mctx.get_dec_level(type_mvar) {
        Ok(u) => u,
        Err(e) => {
            return match expected {
                Some(t) => {
                    let is_prop = elab.mctx.is_prop(t)?;
                    Err(ElabError::NumeralIsNotData {
                        expected: t,
                        is_prop,
                    })
                }
                None => Err(ElabError::from(e)),
            }
        }
    };
    let lit = mk_raw_nat_lit(elab, &val)?;
    // oracle: `mkInstMVar (mkApp2 (mkConst ``OfNat [u]) typeMVar
    // (mkRawNatLit val)) extraMsg` (`:226`).
    let of_nat = const_with_level(elab, "OfNat", u)?;
    let goal = app_n(elab, of_nat, &[type_mvar, lit])?;
    let inst = elab.mk_inst_mvar(goal, SynElem::Node(node.clone()))?;
    // oracle: `mkApp3 (mkConst ``OfNat.ofNat [u]) typeMVar
    // (mkRawNatLit val) mvar` (`:227`) — the SAME `mkRawNatLit val`
    // built twice in the oracle, one hash-consed row here.
    let of_nat_of_nat = const_with_level(elab, "OfNat.ofNat", u)?;
    let r = app_n(elab, of_nat_of_nat, &[type_mvar, lit, inst])?;
    // oracle: `registerMVarErrorImplicitArgInfo mvar.mvarId! stx r`
    // (`:228`) — attribute a later "cannot synthesize" report to this
    // literal rather than to whatever enclosing term holds it.
    let inst_id = inst_mvar_id(elab, inst)?;
    elab.register_mvar_error_implicit_arg_info(inst_id, SynElem::Node(node.clone()), r);
    Ok(r)
}
