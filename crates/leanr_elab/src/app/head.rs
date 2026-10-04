//! `elabAppFn`: resolve the application head to a candidate list.
//! Oracle: `App.lean`'s `elabAppFn` ident case, which for a bare
//! identifier reduces to `resolveName`/`mkConsts`/`mkConst`
//! (`Lean/Elab/Term/TermElabM.lean:2128-2136`, `:2145`, `:2170`).
//!
//! This file is where M4b-1's `builtin/ident.rs` went. That module was
//! a SIMPLIFICATION, not a layer: `elabIdent := elabAtom`
//! (`App.lean:2246`), so a bare identifier is a zero-argument
//! application in the oracle and its implicit parameters are inserted
//! by `ElabAppArgs.main` like any other application's. Keeping a
//! separate leaf path would diverge on every polymorphic constant.
//!
//! `elab_app_fn` returns FINISHED candidates, as the oracle's
//! `elabAppFn` does: it owns the call into `elabAppArgs` (via
//! `lval::elab_app_lvals`) and threads the pending LVal list. An
//! overloaded identifier yields several, each under `observing`
//! ([`AppFn::Candidates`]); `overload.rs` selects among them.

use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_syntax::kind::KindInterner;

use crate::app::lval::LVal;
use crate::app::AppCall;
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::resolve::resolve_local_name;
use crate::synthetic::TermElabResult;

/// What `elabAppFn` (`App.lean:2060-2138`) produced.
///
/// The oracle always returns a `TermElabResult` array and `elabAppAux`
/// `applyResult`s a lone candidate (`:2204-2206`). leanr returns one
/// resolution as `Done` and never brackets it: with a single candidate,
/// observing and then applying is the identity. It also skips a state
/// snapshot on every application.
pub(crate) enum AppFn {
    Done(ExprId),
    /// Two or more resolutions, each under `observing`.
    /// `app::overload::select` picks.
    Candidates(Vec<TermElabResult>),
}

/// One entry of `resolveName'`'s output (`TermElabM.lean:2201-2208`): the
/// head, plus the `LVal`s its split-off field components become.
pub(crate) struct Resolution {
    pub f: ExprId,
    pub fields: Vec<LVal>,
}

/// Oracle `elabAppFn` (`App.lean:2060-2138`): returns FINISHED
/// candidates (the oracle's `TermElabResult` array), because it threads
/// `lvals` and itself calls `elabAppLVals`, which calls `elabAppArgs`
/// (`lval::elab_app_lvals` -> `elab_app_args`).
///
/// No eliminator gate lives here any more (M4b-4c P2). The oracle's
/// `elabAsElim?` (`App.lean:1397-1431`) runs inside `elabAppArgs` on the
/// FINAL head, after any LVals are resolved, so its port is
/// `app/elim.rs`'s `elab_as_elim_info`, called from `elab_app_args`.
pub(crate) fn elab_app_fn(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    explicit_levels: &[LevelId],
    lvals: Vec<LVal>,
    call: AppCall,
) -> Result<AppFn, ElabError> {
    let kind = kinds.name(elem.kind());
    // The oracle's parser admits `.{us}` only after an identifier, a
    // `dotIdent` or a `proj` (`explicitUniv`'s `checkStackTop
    // isIdentOrDotIdentOrProj`, `Parser/Term.lean:938-950`). leanr_syntax
    // skips that check (`builtin/term.rs`'s `explicitUniv` registration),
    // so `(f).{0} a`, `(fun x => x).{0} a` and `List.{0}.{1}` reach here
    // with levels on a head that has no arm to take them. The oracle
    // rejects all three at parse time ("unexpected token '.{'"). Every arm
    // but those three would DROP the levels (or, for a nested
    // `explicitUniv`, overwrite them), elaborating a term the oracle never
    // sees. So: a tree the oracle's grammar cannot produce is
    // `IllFormedSyntax`, the variant leanr uses for shapes the grammar
    // rules out.
    if !explicit_levels.is_empty()
        && !matches!(
            kind,
            "<ident>" | "Lean.Parser.Term.proj" | "Lean.Parser.Term.dotIdent"
        )
    {
        return Err(ElabError::IllFormedSyntax(format!(
            "explicit universes `.{{..}}` after `{kind}`: the oracle's parser accepts them only \
             after an identifier, `dotIdent` or `proj` (`explicitUniv`'s `checkStackTop \
             isIdentOrDotIdentOrProj`, Parser/Term.lean:938-950)"
        )));
    }
    match (kind, elem) {
        ("<ident>", leanr_syntax::tree::NodeOrToken::Token(tok)) => {
            elab_app_fn_id(elab, elem, tok.text(), explicit_levels, lvals, call, kinds)
        }
        // oracle: `` `($(e).$idx:fieldIdx) `` / `` `($(e).$field:ident) ``
        // and their `.{us}` forms (`App.lean:2084-2097`). The explicit levels
        // peeled off a `.{us}` wrapper belong to the FIELD (the last
        // component), never to `e`.
        ("Lean.Parser.Term.proj", _) => {
            let (base, field) = proj_parts(elem)?;
            let mut new = field_lvals(&field, kinds, explicit_levels)?;
            new.extend(lvals);
            elab_app_fn(elab, &base, kinds, &[], new, call)
        }
        // oracle: `` `($e |>.$idx:fieldIdx) `` / `` `($e |>.$field:ident) ``
        // and their `.{us}` forms (`App.lean:2085-2097`), the same
        // `elabFieldIdx` / `elabFieldName` as a projection.
        //
        // These patterns have no `$args*`, so they match only a pipeProj
        // with NO trailing arguments. `elabPipeProj` (`App.lean:2250-2258`)
        // rebuilds the node it was handed without its arguments before
        // calling `elabAppAux`, so the outermost pipeProj always matches;
        // leanr instead leaves the node intact and `app::elab_pipe_proj`
        // passes it as `call.stx`, so `elem == call.stx` identifies it and
        // its arguments are already in `call`. Any OTHER pipeProj that
        // still carries arguments, e.g. the inner `s |>.addTo Nat.zero` that
        // is the base of `s |>.addTo Nat.zero |>.succ`, matches none of the
        // patterns and falls to the generic arm (`:2120-2138`): it is
        // elaborated whole, through `elabPipeProj` again, and the pending
        // lvals are applied to the result.
        //
        // `explicit_levels` is always empty here: the check at the top of
        // this function rejects `.{us}` peeled off any head but an
        // identifier, `proj` or `dotIdent`. A pipeProj's own `.{us}` is
        // its child [3], read below.
        ("Lean.Parser.Term.pipeProj", _) => {
            let (base, field, lvls, has_args) = pipe_proj_parts(elem)?;
            if has_args && *elem != call.stx {
                return elab_app_fn_generic(elab, elem, kinds, lvals, call);
            }
            let levels = elab_explicit_univs(elab, &lvls, kinds)?;
            let mut new = field_lvals(&field, kinds, &levels)?;
            new.extend(lvals);
            elab_app_fn(elab, &base, kinds, &[], new, call)
        }
        // oracle: `` `($_:ident@$_:term) `` (`App.lean:2098-2100`).
        ("Lean.Parser.Term.namedPattern", _) => {
            Err(ElabError::NamedPatternOutsidePattern { as_function: true })
        }
        // oracle: `` `(.$id:ident) `` / `` `(.$id:ident.{$us,*}) ``
        // (`App.lean:2106-2109`) → `elabDottedIdent` (`:2079-2082`):
        // `resolveDottedIdentFn`, then `elabAppFnResolutions` with no
        // fields. `.{us}` arrive as `explicit_levels` (`app::peel_head`).
        ("Lean.Parser.Term.dotIdent", _) => {
            let raw = dot_ident_text(elem)?;
            let fs = crate::app::dot_ident::resolve_dotted_ident_fn(
                elab,
                &raw,
                explicit_levels,
                call.expected,
            )?;
            let fns = fs
                .into_iter()
                .map(|f| Resolution {
                    f,
                    fields: Vec::new(),
                })
                .collect();
            elab_app_fn_resolutions(elab, fns, lvals, call, kinds)
        }
        // oracle: `` `($id:ident.{$us,*}) `` (`App.lean:2103-2105`) and the
        // proj `.{us}` arms (`:2087-2090`, `:2094-2097`), reached by
        // recursion — a `.{us}` on a proj's own base, e.g. `o.1.{0}.2`.
        // `app::peel_head` strips a top-level wrapper before this runs.
        ("Lean.Parser.Term.explicitUniv", _) => {
            let (inner, lvls) = crate::app::explicit_univ_parts(elem)?;
            let levels = elab_explicit_univs(elab, &lvls, kinds)?;
            elab_app_fn(elab, &inner, kinds, &levels, lvals, call)
        }
        // oracle: `` `(_) `` (`App.lean:2119`).
        ("Lean.Parser.Term.hole", _) => Err(ElabError::PlaceholderAsFunction),
        ("choice", _) => Err(ElabError::UnsupportedSyntax(
            "application head `choice` needs `elabAppFn`'s `choiceKind` fan-out \
             (App.lean:2062-2065); leanr's parser never builds `choice` \
             (longestMatch ties are first-wins) — choice-node parsing"
                .to_string(),
        )),
        // oracle: `elabAppFn`'s generic arm (`App.lean:2120-2138`). With
        // nothing to apply, the term is elaborated against the expected
        // type and returned AS IS — not re-applied through `elabAppArgs`.
        // Otherwise it is elaborated with no expected type and handed to
        // `elabAppLVals`. `catchPostpone := !overloaded` (`:2121`) is
        // always `true` here, since `overloaded` is false until `choice`
        // is routed (choice-node parsing), so `elab_term`'s catch applies.
        // `observing`'s restore-and-rethrow of a postponement
        // (`TermElabM.lean:586-589`) is subsumed by the enclosing
        // `elab_term`'s own restore, which rolls back to an earlier state.
        _ => elab_app_fn_generic(elab, elem, kinds, lvals, call),
    }
}

/// `elabAppFn`'s generic arm (`App.lean:2120-2138`); see the `_` arm of
/// `elab_app_fn`, which documents it.
fn elab_app_fn_generic(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    lvals: Vec<LVal>,
    call: AppCall,
) -> Result<AppFn, ElabError> {
    if lvals.is_empty() && call.named_args.is_empty() && call.args.is_empty() {
        Ok(AppFn::Done(elab.elab_term(elem, kinds, call.expected)?))
    } else {
        let f = elab.elab_term(elem, kinds, None)?;
        Ok(AppFn::Done(crate::app::lval::elab_app_lvals(
            elab, f, lvals, call, kinds,
        )?))
    }
}

/// oracle: `elabFieldIdx` / `elabFieldName` (`App.lean:2067-2078`): the
/// LVals a `.field` suffix contributes. Shared by `Term.proj` and
/// `Term.pipeProj`. `levels` go to the LAST component; `suffix? := none`,
/// since a projection's field "can't be part of a composite name" (`:2072`).
fn field_lvals(
    field: &SynElem,
    kinds: &KindInterner,
    levels: &[LevelId],
) -> Result<Vec<LVal>, ElabError> {
    Ok(match kinds.name(field.kind()) {
        // `elabFieldIdx` (`:2075-2078`).
        "fieldIdx" => {
            let text = field.to_string();
            let idx = text
                .trim()
                .parse::<usize>()
                .map_err(|_| ElabError::IllFormedSyntax(format!("fieldIdx `{text}`")))?;
            vec![LVal::FieldIdx {
                r#ref: field.clone(),
                idx,
                levels: levels.to_vec(),
            }]
        }
        // `elabFieldName` (`:2067-2074`): `field.identComponents` —
        // ONE token, one LVal per component (M4b-4a P1 plan § Review
        // Focus 5), each component unescaped (`«a»` is the field `a`).
        _ => {
            let text = field.to_string();
            let comps = ident_components(text.trim())?;
            let last = comps.len() - 1;
            comps
                .into_iter()
                .enumerate()
                .map(|(i, c)| LVal::FieldName {
                    r#ref: field.clone(),
                    name: c,
                    levels: if i == last {
                        levels.to_vec()
                    } else {
                        Vec::new()
                    },
                    suffix: None,
                })
                .collect()
        }
    })
}

/// `Term.pipeProj`'s children (`term_app.rs`'s `register_pipe_proj`;
/// confirmed with `leanr parse --dump` while planning):
///
/// ```text
///   [0] e   [1] "|>."   [2] field: fieldIdx node | <ident> token
///   [3] null: `optional explicitUnivSuffix`, empty or [".{", levels, "}"]
///   [4] null: `many argument` (`app::elab_pipe_proj` takes it apart)
/// ```
///
/// Returns `e`, the field, the level syntax (separators dropped, as
/// `app::explicit_univ_parts` does) and whether [4] holds any argument.
fn pipe_proj_parts(elem: &SynElem) -> Result<(SynElem, SynElem, Vec<SynElem>, bool), ElabError> {
    let bad = |what: &str| ElabError::IllFormedSyntax(format!("pipeProj: {what}"));
    let node = elem.as_node().ok_or_else(|| bad("not a node"))?;
    let ch = non_trivia_children(node);
    if ch.len() != 5 {
        return Err(bad("expected `[e, \"|>.\", field, univs, args]`"));
    }
    let suffix = ch[3]
        .as_node()
        .ok_or_else(|| bad("univ suffix is not a node"))?;
    let sch = non_trivia_children(suffix);
    let lvls = match sch.get(1).and_then(|el| el.as_node()) {
        Some(list) => non_trivia_children(list).into_iter().step_by(2).collect(),
        None if sch.is_empty() => Vec::new(),
        None => return Err(bad("malformed `.{..}` suffix")),
    };
    let args = ch[4]
        .as_node()
        .ok_or_else(|| bad("argument list is not a node"))?;
    let has_args = !non_trivia_children(args).is_empty();
    Ok((ch[0].clone(), ch[2].clone(), lvls, has_args))
}

/// `(base, field)` of a `Lean.Parser.Term.proj` node. Layout (confirmed
/// by a throwaway parse probe, never landed — same precedent as
/// `expand.rs`'s recorded shapes):
///
/// ```text
/// (Nat.zero).1:                 (s).toS2.toS1:
///   [0] Term.paren "(Nat.zero)"   [0] Term.paren "(s)"
///   [1] <atom> "."                [1] <atom> "."
///   [2] fieldIdx "1"              [2] <ident> "toS2.toS1"   <- ONE token
///         [0] <atom> "1"
/// ```
///
/// A `.{us}` suffix wraps the whole proj (`o.1.{0}` is
/// `explicitUniv(proj(o, 1), ..)`), so it never appears here.
pub(crate) fn proj_parts(elem: &SynElem) -> Result<(SynElem, SynElem), ElabError> {
    let node = elem
        .as_node()
        .ok_or_else(|| ElabError::IllFormedSyntax("proj: Term.proj is not a node".to_string()))?;
    let ch = non_trivia_children(node);
    match (ch.first(), ch.get(2)) {
        (Some(base), Some(field)) if ch.len() == 3 => Ok((base.clone(), field.clone())),
        _ => Err(ElabError::IllFormedSyntax(
            "proj: expected `[base, \".\", field]`".to_string(),
        )),
    }
}

/// `Term.dotIdent`'s identifier: children `[".", <ident>]`
/// (`term_app.rs`'s `register_dot_ident`).
fn dot_ident_text(elem: &SynElem) -> Result<String, ElabError> {
    let bad = || ElabError::IllFormedSyntax("dotIdent: expected `[\".\", ident]`".to_string());
    let node = elem.as_node().ok_or_else(bad)?;
    match non_trivia_children(node).get(1) {
        Some(leanr_syntax::tree::NodeOrToken::Token(t)) => Ok(t.text().to_string()),
        _ => Err(bad()),
    }
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

/// oracle: `elabAppFnId` (`App.lean:1952-1958`): `resolveName'`
/// (`TermElabM.lean:2201-2208`) over `resolveName` (`:2170-2192`), then
/// `elabAppFnResolutions` (`App.lean:1926-1950`), which turns the
/// split-off field components into `LVal`s in front of the pending ones.
///
/// The former `builtin::ident::elab_ident`, plus `explicit_levels`
/// (Task 8's `.{u}`): oracle `mkConst` creates fresh universe mvars only
/// for the levelParams NOT covered by explicit levels
/// (`TermElabM.lean:2128-2136`, docstring `:2121-2127`) — "Create an
/// `Expr.const` using the given name and explicit levels. Remark: fresh universe metavariables
/// are created if the constant has more universe parameters than
/// `explicitLevels`". Task 8's `.{u, v}` suffix (`app::mod`'s
/// `peel_head` -> `elab_explicit_univs`) is the only producer of a
/// non-empty `explicit_levels`; without one, every `levelParams` entry
/// gets its own fresh mvar, exactly as M4b-1's leaf elaborator did.
///
/// `raw` is the identifier's raw source text — a single lexer token that
/// already includes every `.`-separated component (`leanr_syntax::lex`'s
/// `hierarchical_idents_are_one_token`), so a dotted name like
/// `Nat.succ` arrives here as ONE string, decoded below by
/// `ident_prefixes` (`«»` escapes stripped, as `ident.getId` does).
fn elab_app_fn_id(
    elab: &mut TermElabM,
    elem: &SynElem,
    raw: &str,
    explicit_levels: &[LevelId],
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<AppFn, ElabError> {
    // The decoded name (`ident_prefixes`), so a single-component prefix is
    // the same `NameId` a binder of that name has (`intern_binder_name`).
    let (comps, prefixes) = ident_prefixes(elab, raw)?;
    let parts: Vec<&str> = comps.iter().map(String::as_str).collect();
    // `resolveName`: every local prefix before any global (`:2180-2181`).
    //
    // M4b-2 (binders): a local variable shadows a same-named global
    // constant, and must be checked FIRST. `MetaCtx::lctx_lookup_by_name`
    // (leanr_meta, additive/TCB-neutral, mirroring the oracle's own
    // `LocalContext.findFromUserName?`) is a no-op (`None`) whenever
    // `lctx` is empty — every query that never enters a binder falls
    // straight through to `resolve_global_name`. A local hit bypasses
    // fresh-level-mvar minting entirely: an fvar carries no separate
    // `levelParams` the way a global constant does.
    let fns = if let Some((fvar, n_fields)) = resolve_local_name(elab, &prefixes)? {
        // `processLocal` (`:2172-2179`).
        if n_fields == 0 && !explicit_levels.is_empty() {
            return Err(ElabError::InvalidExplicitUniversesForLocal(fvar));
        }
        let fields = field_name_lvals(elem, &parts, n_fields, explicit_levels);
        vec![Resolution { f: fvar, fields }]
    } else {
        let cands = elab.resolve_global(&prefixes)?;
        if cands.is_empty() {
            // `elabAppFnId`'s `throwUnknownIdWithSuggestions` (`App.lean:1957`).
            return Err(ElabError::UnknownIdent(raw.to_string()));
        }
        // `mkConsts` (`:2145-2158`) builds EVERY candidate's constant before
        // `elabAppFnResolutions` tries any. Its fresh level mvars live
        // outside the `observing` brackets, and a `mkConst` error is thrown
        // before any candidate runs (row `overload/explicitUniv`). With
        // fields, the explicit levels belong to the last field and the
        // constant gets fresh ones.
        let mut fns = Vec::with_capacity(cands.len());
        for (cname, n_fields) in cands {
            let (const_levels, proj_levels): (&[LevelId], &[LevelId]) = if n_fields == 0 {
                (explicit_levels, &[])
            } else {
                (&[], explicit_levels)
            };
            let f = mk_const(elab, cname, const_levels)?;
            let fields = field_name_lvals(elem, &parts, n_fields, proj_levels);
            fns.push(Resolution { f, fields });
        }
        // `mkConsts` is `candidates.foldlM (init := []) … return (const, …)
        // :: result` (`TermElabM.lean:2146-2158`): it calls `mkConst` in
        // `resolveGlobalName` order (so a `mkConst` error fires in that
        // order, above) but returns the list REVERSED, and
        // `elabAppFnResolutions` folds over that. With `open A B` the
        // candidates run B before A (test
        // `overloaded_candidates_run_in_mk_consts_order`).
        fns.reverse();
        fns
    };
    elab_app_fn_resolutions(elab, fns, lvals, call, kinds)
}

/// `elabAppFnResolutions`' field `LVal`s (`App.lean:1934-1938`): the last
/// `n_fields` components of the identifier. `levels` go to the last one,
/// and the first carries the composite `suffix?`.
fn field_name_lvals(
    elem: &SynElem,
    parts: &[&str],
    n_fields: usize,
    levels: &[LevelId],
) -> Vec<LVal> {
    let fields = &parts[parts.len() - n_fields..];
    let suffix = (!fields.is_empty()).then(|| fields.join("."));
    fields
        .iter()
        .enumerate()
        .map(|(i, c)| LVal::FieldName {
            r#ref: elem.clone(),
            name: (*c).to_string(),
            levels: if i + 1 == n_fields {
                levels.to_vec()
            } else {
                Vec::new()
            },
            suffix: if i == 0 { suffix.clone() } else { None },
        })
        .collect()
}

/// oracle: `elabAppFnResolutions` (`App.lean:1926-1950`). With more than
/// one resolution the application is `overloaded` (`:1930`): each
/// resolution is elaborated under `observing`, and its result must have
/// the expected type (`ensureHasType`, `:1943`), since the expected type
/// is what tells the candidates apart (row `overload/expectedType`).
///
/// The oracle's incoming `overloaded` flag is only ever `true` under a
/// `choice` node (`:2062-2065`), which is out of scope (`elab_app_fn`'s
/// `choice` arm). So here `overloaded` is exactly `fns.len() > 1`.
/// `errToSorry := false` (`:1932`) is leanr's only mode: it stops at
/// the first error.
pub(crate) fn elab_app_fn_resolutions(
    elab: &mut TermElabM,
    fns: Vec<Resolution>,
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<AppFn, ElabError> {
    if fns.len() == 1 {
        let Resolution { f, mut fields } = fns.into_iter().next().expect("len == 1");
        fields.extend(lvals);
        return Ok(AppFn::Done(crate::app::lval::elab_app_lvals(
            elab, f, fields, call, kinds,
        )?));
    }
    let mut out = Vec::with_capacity(fns.len());
    for Resolution { f, mut fields } in fns {
        fields.extend(lvals.iter().cloned());
        let call = call.clone();
        out.push(elab.observing(|elab| {
            let (stx, expected) = (call.stx.clone(), call.expected);
            let e = crate::app::lval::elab_app_lvals(elab, f, fields, call, kinds)?;
            elab.ensure_has_type(&stx, expected, e)
        })?);
    }
    Ok(AppFn::Candidates(out))
}

/// oracle: `mkConst` (`TermElabM.lean:2128-2136`).
///
/// An undeclared `cname` is `UnknownConstant` (the full name), as the
/// oracle's `getConstInfo` throws. `resolve_global_name` can return one:
/// alias targets and an explicit `open`'s declaration are not checked
/// against the environment (`ResolveName.lean:85-92`, `:175-176`).
pub(crate) fn mk_const(
    elab: &mut TermElabM,
    cname: NameId,
    explicit_levels: &[LevelId],
) -> Result<ExprId, ElabError> {
    let render = |elab: &TermElabM| {
        crate::names::render(elab.mctx.store(), Some(elab.view.store), Some(cname))
    };
    let Some(info) = elab.view.get(cname) else {
        return Err(ElabError::UnknownConstant(render(elab)));
    };
    let n_params = info.constant_val().level_params.len();
    // oracle: `mkConst` errors when the user wrote MORE explicit levels
    // than the constant has parameters (``too many explicit universe levels
    // for `{constName}` ``, `:2132`: the RESOLVED name, row
    // `overload/explicitUniv`), rather than truncating.
    if explicit_levels.len() > n_params {
        return Err(ElabError::TooManyUniverseLevels(render(elab)));
    }
    let mut levels = Vec::with_capacity(n_params);
    levels.extend_from_slice(explicit_levels);
    for _ in explicit_levels.len()..n_params {
        levels.push(elab.mk_fresh_level_mvar()?);
    }
    // `base = Some(elab.view.store)` from here on: `cname` is a
    // PERSISTENT-region `NameId` (`EnvView::get` just resolved it, and
    // every constant in `env.constants` is persistent-region by
    // construction — `Environment::admit_unchecked`
    // /decode never inserts a scratch id there). `Store::expr_const`'s
    // internal `name_hash_of` routes a persistent id through `base` when
    // `self` (the SCRATCH store `store_mut()` returns) isn't itself the
    // persistent store — passing `None` here trips `store_for`'s own
    // misrouting `debug_assert` (confirmed empirically: the gate panicked
    // on exactly this before the fix, and worse, would have silently
    // read the WRONG name row in a release build per that same method's
    // documented hazard).
    //
    // `intern_level_list` takes `base = Some(..)` too (M4c-2a): its `base`
    // is a DEDUP-ONLY parameter (`bank/mod.rs:564-584`: it consults
    // `b.level_lists` for an existing row and otherwise stores the
    // `LevelId`s verbatim, never resolving a child), so passing it is safe
    // whatever regions the ids are in. With `None` an empty list minted a
    // scratch row beside the persistent one, so `Nat` was a scratch `Const`
    // id distinct from the environment's, and ExprId equality stopped being
    // structural: the env-wide aux-lemma cache (`AuxLemmaCache`, keyed by
    // type id) then missed a type its own earlier declaration had cached.
    let base = elab.view.store;
    let levels_id = elab
        .mctx
        .store_mut()
        .intern_level_list(Some(base), &levels)
        .map_err(leanr_meta::MetaError::from)?;
    let id = elab
        .mctx
        .store_mut()
        .expr_const(Some(base), Some(cname), levels_id)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(id)
}

/// The components of an identifier token's raw source text, with
/// `«»` escapes stripped: `a.«b.c».d` is `["a", "b.c", "d"]`. The
/// oracle's `Name` never carries the guillemets; they are syntax
/// (`identFnAux`, `Parser/Basic.lean`; leanr_syntax's `ident_len` is the
/// lexer side). The token was lexer-validated, but it is still parsed
/// totally: an unterminated escape or an empty component is
/// `IllFormedSyntax`, never a panic.
pub(crate) fn ident_components(raw: &str) -> Result<Vec<String>, ElabError> {
    let bad = || ElabError::IllFormedSyntax(format!("identifier `{raw}`"));
    let mut comps = Vec::new();
    let mut rest = raw;
    loop {
        let (comp, after) = if let Some(esc) = rest.strip_prefix('«') {
            let end = esc.find('»').ok_or_else(bad)?;
            (&esc[..end], &esc[end + '»'.len_utf8()..])
        } else {
            let end = rest.find('.').unwrap_or(rest.len());
            if end == 0 {
                return Err(bad());
            }
            (&rest[..end], &rest[end..])
        };
        comps.push(comp.to_string());
        match after.strip_prefix('.') {
            Some(next) => rest = next,
            None if after.is_empty() => return Ok(comps),
            None => return Err(bad()),
        }
    }
}

/// `ident_components` then `intern_prefixes`: every prefix of an
/// identifier token's DECODED name (`ident.getId`). The name every
/// source-identifier lookup uses, so `«x»` and `x` find the same binder
/// and `a.«b.c»` has the two components `a`, `b.c`.
pub(crate) fn ident_prefixes(
    elab: &mut TermElabM,
    raw: &str,
) -> Result<(Vec<String>, Vec<NameId>), ElabError> {
    let comps = ident_components(raw)?;
    let parts: Vec<&str> = comps.iter().map(String::as_str).collect();
    let prefixes = intern_prefixes(elab, &parts)?;
    Ok((comps, prefixes))
}

/// Intern every prefix of a dotted name: `prefixes[k]` is the name of
/// `parts[..=k]`. Same store discipline as `intern_components` (below),
/// which is the last element. `resolve::resolve_local_name` /
/// `resolve_global_name` need every prefix, and chaining `name_str`
/// mints them all anyway.
pub(crate) fn intern_prefixes(
    elab: &mut TermElabM,
    parts: &[&str],
) -> Result<Vec<NameId>, ElabError> {
    let base = elab.view.store;
    let mut prefixes = Vec::with_capacity(parts.len());
    let mut id: Option<NameId> = None;
    for part in parts {
        let store = elab.mctx.store_mut();
        let s = store
            .intern_str(Some(base), part)
            .map_err(leanr_meta::MetaError::from)?;
        let n = store
            .name_str(Some(base), id, s)
            .map_err(leanr_meta::MetaError::from)?;
        prefixes.push(n);
        id = Some(n);
    }
    Ok(prefixes)
}

/// Intern `parts` as the hierarchical name `parts[0].parts[1]...`, each
/// part ONE component whatever it contains (so an unescaped `«a.b»`
/// stays a single component). Same store discipline as `intern_dotted`.
pub(crate) fn intern_components(elab: &mut TermElabM, parts: &[&str]) -> Result<NameId, ElabError> {
    intern_prefixes(elab, parts)?
        .last()
        .copied()
        .ok_or_else(|| ElabError::IllFormedSyntax("empty name".to_string()))
}

/// Intern a (possibly dotted) identifier's raw source text as a
/// `NameId` — the store has no direct "parse a `&str` into a `Name`"
/// entry point (`Store::intern_name` only bridges FROM an already-built
/// `Arc<Name>`, `#[cfg(test)]`-only besides), so this builds the chain
/// component-by-component the same way `leanr_meta`'s own
/// `intern_dotted`/`dotted_name` (private test helpers there) do.
///
/// `base = Some(elab.view.store)`, not `None`: this has to find the
/// SAME `NameId` `resolve_global_name`/`EnvView::get` will look up against
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
///
/// Splits on every `.` and keeps `«»` verbatim: for the elaborator's own
/// built-in names only. A SOURCE identifier goes through
/// `ident_components` / `ident_prefixes`, which decode `«»`.
pub(crate) fn intern_dotted(elab: &mut TermElabM, raw: &str) -> Result<NameId, ElabError> {
    let parts: Vec<&str> = raw.split('.').collect();
    intern_components(elab, &parts)
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

    /// `«»` escapes are stripped and an escaped component keeps its
    /// dots; malformed text is an error, never a panic.
    #[test]
    fn ident_components_respects_guillemets() {
        use super::ident_components;
        assert_eq!(ident_components("a").unwrap(), ["a"]);
        assert_eq!(ident_components("«a»").unwrap(), ["a"]);
        assert_eq!(
            ident_components("toS2.«b.c».d").unwrap(),
            ["toS2", "b.c", "d"]
        );
        for bad in ["«a", "a..b", "a.", ".a", "«a»b"] {
            assert!(ident_components(bad).is_err(), "{bad}");
        }
    }

    /// The regression M4b-1's `builtin/ident.rs` carried, moved here
    /// with the code it guards (M4b-3 P1 task 4): `elab_app_fn_id`'s
    /// OWN pipeline (`intern_prefixes` then `resolve_global_name`) on an
    /// identifier NOT declared in `env` — unlike `resolve::tests::
    /// unknown_ident_when_not_declared`, which mints the unknown name
    /// directly in the PERSISTENT store and so never reproduces the bug:
    /// `intern_prefixes` mints a SCRATCH-region `NameId` for any name not
    /// already interned in the persistent store, which is exactly what
    /// happens for a genuinely unknown/typo'd identifier. Against the
    /// pre-fix `resolve_global` (M4b-1; P4 replaced it with
    /// `resolve_global_name`), which re-derived the error text via
    /// `view.store.to_name(None, Some(name))`, `view.store` being the
    /// PERSISTENT store, on a SCRATCH-region `name`, this test either
    /// panicked in `name_row`'s `.expect(..)` or — as observed then,
    /// since the persistent pool from `env_with_foo` is non-empty —
    /// silently returned the WRONG identifier text (a row from the
    /// persistent pool, not "Bar"). Post-fix, the resolver (today
    /// `resolve_global_name`) takes the display text verbatim from the
    /// token's real source text, so this passes without touching the store
    /// at all for the error path.
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
        let elem = parsed.tree.root().first_child_or_token().expect("a term");
        assert!(
            matches!(elem, NodeOrToken::Token(_)),
            "expected a bare ident token"
        );
        let call = crate::app::AppCall {
            named_args: Vec::new(),
            args: Vec::new(),
            expected: None,
            explicit: false,
            ellipsis: false,
            stx: elem.clone(),
            result_is_out_param_support: true,
        };
        match super::elab_app_fn(&mut elab, &elem, &parsed.tree.kinds, &[], Vec::new(), call)
            .map(|_| ())
        {
            Err(crate::ElabError::UnknownIdent(s)) => assert_eq!(s, "Bar"),
            other => panic!("expected UnknownIdent(\"Bar\"), got {other:?}"),
        }
    }

    /// oracle: `mkConst` → `getConstInfo` throws ``Unknown constant `B.ex` ``
    /// (`TermElabM.lean:2128-2136`). `resolveGlobalName` returns alias
    /// targets without an environment check (`getAliases`,
    /// `ResolveName.lean:85-92`), so an alias to an undeclared target (a
    /// malformed .olean) reaches `mk_const`: an error, never a panic.
    #[test]
    fn alias_to_undeclared_target_is_unknown_constant() {
        let mut env = env_with_foo();
        let (ex, b_ex) = {
            let store = env.store_mut();
            let s_ex = store.intern_str(None, "ex").unwrap();
            let s_b = store.intern_str(None, "B").unwrap();
            let ex = store.name_str(None, None, s_ex).unwrap();
            let b = store.name_str(None, None, s_b).unwrap();
            (ex, store.name_str(None, Some(b), s_ex).unwrap())
        };
        let tables = crate::names::NameTables::new(&[], &[], &[(ex, b_ex)]);
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions::default(),
        );
        let mut elab = TermElabM::new(mctx, view);
        elab.resolve = crate::resolve::ResolveCtx {
            ns: None,
            open_decls: &[],
            tables: &tables,
            aux_decl: None,
        };

        let snap = builtin::snapshot();
        let parsed = parse_term("ex", &snap);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let elem = parsed.tree.root().first_child_or_token().expect("a term");
        let call = crate::app::AppCall {
            named_args: Vec::new(),
            args: Vec::new(),
            expected: None,
            explicit: false,
            ellipsis: false,
            stx: elem.clone(),
            result_is_out_param_support: true,
        };
        match super::elab_app_fn(&mut elab, &elem, &parsed.tree.kinds, &[], Vec::new(), call)
            .map(|_| ())
        {
            Err(crate::ElabError::UnknownConstant(s)) => assert_eq!(s, "B.ex"),
            other => panic!("expected UnknownConstant(\"B.ex\"), got {other:?}"),
        }
    }
}
