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
//! `char` and `scientific` land here too (task 7), and neither is a leaf
//! either: `char` emits `Char.ofNat (rawNatLit c)` — an application, but
//! a monomorphic one with no instance, no expected type and no universe
//! level — while `scientific` emits `@OfScientific.ofScientific.{u} ?α
//! ?inst (rawNatLit m) sign (rawNatLit e)`, structurally `num`'s shape
//! with the instance argument SECOND. The helpers below
//! ([`mk_fresh_type_mvar_for`], [`const_with_level`], [`const_no_levels`],
//! [`mk_raw_nat_lit`], [`app_n`]) are shared across all three.
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
///
/// **LATENT NAME-RESOLUTION TRAP — read before implementing `open`.**
/// This helper (and its sibling [`const_no_levels`]) routes a
/// HARD-CODED name — `"OfNat"`, `"OfNat.ofNat"`, `"OfScientific"`,
/// `"OfScientific.ofScientific"`, `"Char.ofNat"`, `"Bool.true"`,
/// `"Bool.false"` — through `resolve::resolve_global`, i.e. through
/// USER-VISIBLE name resolution. The oracle does not: `elabNumLit`
/// (`BuiltinTerm.lean:226`) writes
///
/// ```text
/// mkConst ``OfNat [u]
/// ```
///
/// and that double-backtick name literal is resolved and checked when
/// `BuiltinTerm.lean` itself is compiled, so the elaborator holds an
/// ABSOLUTE `Name` that no user syntax can redirect.
///
/// The two agree today only because `resolve_global` performs no
/// namespace, `open`, alias or `_root_` search — its candidate set is
/// `{name}` or `{}` (its own doc). When that search lands — deferred as
/// a later slice at `lib.rs`'s deferral ledger, the
/// "`open`/alias/`export`/`_root_` resolution" row — a user-`open`ed
/// namespace containing its own `OfNat` could shadow the elaborator's
/// constant and silently retarget a numeral's `OfNat` application.
/// That slice must decide the strategy (most likely: bypass
/// `resolve_global` here in favour of an absolute lookup, matching the
/// oracle's compile-time-resolved name); this comment is the record
/// that the decision is owed, not the decision.
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

/// A fixture constant with an EMPTY universe-level list: `Char.ofNat`,
/// `Bool.true`, `Bool.false`. Oracle: a bare `Lean.mkConst ``C` with no
/// level argument (`BuiltinTerm.lean:250`, and `toExpr` for a `Bool`).
/// Same `base` convention as [`const_with_level`], which this is
/// otherwise identical to.
pub(crate) fn const_no_levels(elab: &mut TermElabM, name: &str) -> Result<ExprId, ElabError> {
    let cname = crate::app::head::intern_dotted(elab, name)?;
    let resolved = crate::resolve::resolve_global(&elab.view, cname, name)?;
    let base = elab.view.store;
    let levels = elab
        .mctx
        .store_mut()
        .intern_level_list(None, &[])
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
///
/// The message names an INTERNAL INVARIANT, not a slice. It carried
/// "M4b-3 P3 invariant" until task 8's seam audit: under this crate's
/// named-seam discipline an `UnsupportedSyntax` naming a slice reads as
/// "that slice owes an implementation", and no slice owes one here —
/// the construct is implemented, and this arm is a broken postcondition
/// of a function three lines up. Retargeting it at a LATER slice would
/// have been a second false claim, so the label was dropped instead.
/// `tests/seam_audit.rs`'s `no_seam_message_names_the_completed_p3_slice`
/// is the gate.
fn inst_mvar_id(elab: &TermElabM, e: ExprId) -> Result<MVarId, ElabError> {
    let base = elab.view.store;
    let node = elab.mctx.store().expr_node(Some(base), e);
    if let Node::MVar { id: Some(n) } = node {
        return Ok(MVarId(n));
    }
    debug_assert!(false, "mkInstMVar returned a non-metavariable: {node:?}");
    Err(ElabError::UnsupportedSyntax(
        "internal invariant: mkInstMVar returned a non-metavariable \
         (builtin::lit — not a deferred construct)"
            .to_string(),
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
    //
    // The `is_prop == true` arm is pinned by
    // `synthetic_smoke.rs`'s `a_numeral_ascribed_to_a_prop_is_not_data`
    // — on the POLARITY of the field, since keeping the oracle's two
    // errors apart is the only reason the field exists. That test's doc
    // also records why the `is_prop == false` arm is unreachable from
    // any `Elab0` term (it needs a universe PARAMETER in scope; a level
    // MVAR is assigned by `dec_level` instead of failing) and so is
    // deliberately not asserted.
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

/// oracle: `elabCharLit` (`BuiltinTerm.lean:248-251`) —
/// `mkApp (mkConst ``Char.ofNat) (mkRawNatLit val.toNat)`.
///
/// The simplest non-leaf literal in the grammar: no instance, no
/// expected type (`fun stx _ => ...`, like `elabStrLit`), and no
/// universe level — `Char.ofNat` is monomorphic, so the constant carries
/// an EMPTY level list rather than a fresh level mvar. `Char`'s own
/// shape is never consulted, which is why the fixture may carry an
/// opaque carrier for it (design spec § P3; plan § Measured facts,
/// item 8) and still be byte-identical.
pub fn elab_char(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    _kinds: &KindInterner,
    _expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    // oracle: `stx.isCharLit?` (`:249`) — `isLit? charLitKind` followed
    // by `decodeCharLit`, i.e. the node's single atom child's raw text
    // (`elab_str`'s own measured note on trivia applies verbatim).
    let raw = node.text().to_string();
    let Some(c) = decode::decode_char_literal(&raw) else {
        // oracle: `throwIllFormedSyntax` (`:251`).
        return Err(ElabError::IllFormedLiteral(format!(
            "character literal `{raw}` is not a Char literal"
        )));
    };
    // oracle: `val.toNat` — the Unicode scalar value.
    let lit = mk_raw_nat_lit(elab, &Nat::from(u64::from(c as u32)))?;
    let f = const_no_levels(elab, "Char.ofNat")?;
    app_n(elab, f, &[lit])
}

/// oracle: `elabScientificLit` (`BuiltinTerm.lean:236-246`) —
/// `@OfScientific.ofScientific.{u} ?α ?inst (rawNatLit m) sign
/// (rawNatLit e)`.
///
/// Structurally `elab_num`'s shape, with two deliberate differences,
/// both transcribed as the oracle has them rather than harmonized:
///
///  * the ARGUMENT ORDER — the instance comes SECOND, right after the
///    carrier type, not last (`:244`, `mkApp5 .. typeMVar mvar
///    (mkRawNatLit m) (toExpr sign) (mkRawNatLit e)`);
///  * NO `getDecLevel` failure recovery — `:242` is a bare `getDecLevel`
///    with no `try`, so the level error propagates instead of becoming
///    the "numerals are data in Lean" pair of messages `elabNumLit`
///    raises. `mkInstMVar` here also takes no `extraErrorMsg`.
///
/// There is no default instance for `OfScientific` in the fixture, so an
/// unascribed scientific literal is a stuck typeclass goal — the corpus
/// ascribes every record.
pub fn elab_scientific(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    _kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    // oracle: `stx.isScientificLit?` (`:238`) — `isLit?
    // scientificLitKind` followed by `decodeScientificLitVal?`.
    let raw = node.text().to_string();
    let Some((m, sign, e)) = decode::decode_scientific_literal(&raw) else {
        // oracle: `throwIllFormedSyntax` (`:239`). The decoder is
        // arbitrary-precision, so this means exactly one thing: the
        // token is not a scientific literal.
        return Err(ElabError::IllFormedLiteral(format!(
            "scientific literal `{raw}` is not a scientific literal"
        )));
    };
    let type_mvar = mk_fresh_type_mvar_for(elab, expected)?;
    // oracle: `let u ← getDecLevel typeMVar` (`:242`) — NO `try`.
    let u = elab.mctx.get_dec_level(type_mvar)?;
    // oracle: `mkInstMVar (mkApp (mkConst ``OfScientific [u]) typeMVar)`
    // (`:243`) — the goal is the CLASS applied to the carrier alone; the
    // mantissa/sign/exponent are not part of it, unlike `OfNat`'s.
    let of_sci = const_with_level(elab, "OfScientific", u)?;
    let goal = app_n(elab, of_sci, &[type_mvar])?;
    let inst = elab.mk_inst_mvar(goal, SynElem::Node(node.clone()))?;
    let m_lit = mk_raw_nat_lit(elab, &m)?;
    let e_lit = mk_raw_nat_lit(elab, &e)?;
    // oracle: `toExpr sign` — `Bool.true` / `Bool.false`, a
    // zero-universe constant either way.
    let sign_expr = const_no_levels(elab, if sign { "Bool.true" } else { "Bool.false" })?;
    let f = const_with_level(elab, "OfScientific.ofScientific", u)?;
    let r = app_n(elab, f, &[type_mvar, inst, m_lit, sign_expr, e_lit])?;
    // oracle: `registerMVarErrorImplicitArgInfo mvar.mvarId! stx r`
    // (`:245`).
    let inst_id = inst_mvar_id(elab, inst)?;
    elab.register_mvar_error_implicit_arg_info(inst_id, SynElem::Node(node.clone()), r);
    Ok(r)
}
