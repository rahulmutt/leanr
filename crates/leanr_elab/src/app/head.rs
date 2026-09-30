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
//! `elab_app_fn` now returns FINISHED candidates, as the oracle's
//! `elabAppFn` does: it owns the call into `elabAppArgs` (via
//! `lval::elab_app_lvals`) and threads the pending LVal list. A Vec
//! because the oracle returns a candidate ARRAY (overloaded names).
//! Exactly-one is the only P1 shape; see `overload.rs`.

use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_syntax::kind::KindInterner;

use crate::app::lval::LVal;
use crate::app::AppCall;
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::resolve::{resolve_global_name, resolve_local_name};

/// Oracle `elabAppFn` (`App.lean:2060-2138`): returns FINISHED
/// candidates (the oracle's `TermElabResult` array), because it threads
/// `lvals` and itself calls `elabAppLVals`, which calls `elabAppArgs`
/// (`lval::elab_app_lvals` -> `elab_app_args`).
///
/// The recursor guard (`heed` in `elab_app_fn_id`) is the oracle's own
/// two-line gate at the top of `elabAsElim?` (`App.lean:1398-1399`):
/// `unless (← read).heedElabAsElim do return none` followed by `if
/// explicit || ellipsis then return none`. leanr never turns the reader
/// field off (`withoutElabAsElim`, `TermElabM.lean:733`, has no leanr
/// counterpart — nothing in this crate suppresses the branch), so it is
/// `!explicit && !ellipsis`, which is exactly the second line, and
/// additionally off while LVals are pending or fields were split off the
/// identifier. Computed in `elab_app_fn_id` rather than
/// read off `AppElab` because `elab_app_fn` runs BEFORE the
/// `Context`/`State` exist — `elab_app_args` needs the head's type to
/// build them.
pub fn elab_app_fn(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    explicit_levels: &[LevelId],
    lvals: Vec<LVal>,
    call: AppCall,
) -> Result<Vec<ExprId>, ElabError> {
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
        ("<ident>", leanr_syntax::tree::NodeOrToken::Token(tok)) => Ok(vec![elab_app_fn_id(
            elab,
            elem,
            tok.text(),
            explicit_levels,
            lvals,
            call,
            kinds,
        )?]),
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
        // `elabFieldIdx` / `elabFieldName` as a projection. The trailing
        // arguments were taken off by `app::elab_pipe_proj`.
        ("Lean.Parser.Term.pipeProj", _) => {
            let (base, field, lvls) = pipe_proj_parts(elem)?;
            let levels = elab_explicit_univs(elab, &lvls, kinds)?;
            let mut new = field_lvals(&field, kinds, &levels)?;
            new.extend(lvals);
            elab_app_fn(elab, &base, kinds, &[], new, call)
        }
        // oracle: `` `($_:ident@$_:term) `` (`App.lean:2098-2100`).
        ("Lean.Parser.Term.namedPattern", _) => {
            Err(ElabError::NamedPatternOutsidePattern { as_function: true })
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
             (App.lean:2062-2065) — the overloading slice (resolve_global_name)"
                .to_string(),
        )),
        (other, _) if is_lval_head(other) => Err(ElabError::UnsupportedSyntax(format!(
            "application head `{other}` needs `elabAppFn`'s dotIdent arm \
             (App.lean:2106-2109) — M4b-4a P4"
        ))),
        // oracle: `elabAppFn`'s generic arm (`App.lean:2120-2138`). With
        // nothing to apply, the term is elaborated against the expected
        // type and returned AS IS — not re-applied through `elabAppArgs`.
        // Otherwise it is elaborated with no expected type and handed to
        // `elabAppLVals`. `catchPostpone := !overloaded` (`:2121`) is
        // always `true` here, since `overloaded` is false until `choice`
        // is routed (overloading slice), so `elab_term`'s catch applies.
        // `observing`'s restore-and-rethrow of a postponement
        // (`TermElabM.lean:586-589`) is subsumed by the enclosing
        // `elab_term`'s own restore, which rolls back to an earlier state.
        _ => {
            if lvals.is_empty() && call.named_args.is_empty() && call.args.is_empty() {
                Ok(vec![elab.elab_term(elem, kinds, call.expected)?])
            } else {
                let f = elab.elab_term(elem, kinds, None)?;
                Ok(vec![crate::app::lval::elab_app_lvals(
                    elab, f, lvals, call, kinds,
                )?])
            }
        }
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
/// Returns `e`, the field and the level syntax (separators dropped, as
/// `app::explicit_univ_parts` does).
fn pipe_proj_parts(elem: &SynElem) -> Result<(SynElem, SynElem, Vec<SynElem>), ElabError> {
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
    Ok((ch[0].clone(), ch[2].clone(), lvls))
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

/// The application-head kind whose oracle arm is still unported:
/// `elabAppFn`'s `` `(.$id:ident) `` arms (`App.lean:2106-2109`).
/// `choice` has its own arm above; `proj`, `pipeProj` and `namedPattern`
/// are ported.
fn is_lval_head(kind: &str) -> bool {
    matches!(kind, "Lean.Parser.Term.dotIdent")
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
/// `Nat.succ` arrives here as ONE string, split below exactly the way
/// `intern_dotted` and every other dotted-name builder in this workspace
/// does (`leanr_meta`'s own `intern_dotted`/`dotted_name` test helpers,
/// `pub(crate)`/test-only there and so not reusable from this crate).
fn elab_app_fn_id(
    elab: &mut TermElabM,
    elem: &SynElem,
    raw: &str,
    explicit_levels: &[LevelId],
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    // `intern_dotted`'s convention (split on every `.`, `«»` kept), so a
    // single-component prefix is the same `NameId` a binder of that text
    // has (plan § Decisions).
    let parts: Vec<&str> = raw.split('.').collect();
    let prefixes = intern_prefixes(elab, &parts)?;
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
    let (f, n_fields, proj_levels) =
        if let Some((fvar, n_fields)) = resolve_local_name(&elab.mctx, &prefixes) {
            // `processLocal` (`:2172-2179`).
            if n_fields == 0 && !explicit_levels.is_empty() {
                return Err(ElabError::InvalidExplicitUniversesForLocal(fvar));
            }
            (fvar, n_fields, explicit_levels.to_vec())
        } else {
            // `raw` (the identifier's own source text) doubles as the
            // error-message `display` — see `resolve_global_name`'s doc
            // for why a prefix (frequently a SCRATCH-region id, minted by
            // `intern_prefixes` just above for any name not already
            // interned in the persistent store) cannot safely be
            // re-rendered through `view.store` alone.
            let (cname, n_fields) = resolve_global_name(&elab.view, &prefixes, raw)?;
            // `mkConsts` (`:2145-2158`): with fields, the explicit levels
            // belong to the last field and the constant gets fresh ones.
            let (const_levels, proj_levels): (&[LevelId], &[LevelId]) = if n_fields == 0 {
                (explicit_levels, &[])
            } else {
                (&[], explicit_levels)
            };
            // `elabAsElim?` runs inside `elabAppArgs` on the FINAL head
            // (`App.lean:1373`). With LVals pending, or fields split off,
            // the constant is not that head — `resolveLVal` consumes it
            // first — so the recursor guard must not fire (M4b-4a P1 plan
            // § Review Focus 1). Otherwise the guard is the oracle's own
            // two-line gate at the top of `elabAsElim?` (see
            // `elab_app_fn`'s doc).
            let heed = !call.explicit && !call.ellipsis && lvals.is_empty() && n_fields == 0;
            let info = elab
                .view
                .get(cname)
                .expect("resolve_global_name only returns names EnvView::get resolves");
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
            // that keeps such a query out of the committed corpus; M4b-4c owns
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
            // supplied, which needs `getElabElimInfo`'s `motivePos` — M4b-4c
            // machinery. So `Nat.rec (motive := ..) ..` is seamed here where the
            // oracle would elaborate it normally. A named error is the safe
            // direction of that trade; a wrong `Expr` is not.
            if heed && matches!(info, leanr_kernel::ConstantInfo::Rec(_)) {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "`{raw}` is a recursor — the oracle elaborates eliminator-headed \
                     applications with `ElabElim.main` (`shouldElabAsElim`, App.lean:1322-1328; \
                     diverted at :1373), which needs `motivePos` — M4b-4c"
                )));
            }
            let display = parts[..parts.len() - n_fields].join(".");
            (
                mk_const(elab, cname, const_levels, &display)?,
                n_fields,
                proj_levels.to_vec(),
            )
        };
    // `elabAppFnResolutions` (`:1933-1938`).
    let fields = &parts[parts.len() - n_fields..];
    let suffix = (!fields.is_empty()).then(|| fields.join("."));
    let mut all: Vec<LVal> = fields
        .iter()
        .enumerate()
        .map(|(i, c)| LVal::FieldName {
            r#ref: elem.clone(),
            name: (*c).to_string(),
            levels: if i + 1 == n_fields {
                proj_levels.clone()
            } else {
                Vec::new()
            },
            suffix: if i == 0 { suffix.clone() } else { None },
        })
        .collect();
    all.extend(lvals);
    crate::app::lval::elab_app_lvals(elab, f, all, call, kinds)
}

/// oracle: `mkConst` (`TermElabM.lean:2128-2136`). `display` is the
/// identifier's source text, used only in the `TooManyUniverseLevels` error.
///
/// Precondition: `cname` is declared. Both callers establish it —
/// `elab_app_fn_id` via `resolve_global_name`, `lval::elab_app_lvals` by
/// checking the `structureExt`-decoded `projFn` against the environment.
pub(crate) fn mk_const(
    elab: &mut TermElabM,
    cname: NameId,
    explicit_levels: &[LevelId],
    display: &str,
) -> Result<ExprId, ElabError> {
    let info = elab
        .view
        .get(cname)
        .expect("mk_const callers pass only declared names (resolve_global_name / checked projFn)");
    let n_params = info.constant_val().level_params.len();
    // oracle: `mkConst` errors when the user wrote MORE explicit levels
    // than the constant has parameters, rather than truncating.
    if explicit_levels.len() > n_params {
        return Err(ElabError::TooManyUniverseLevels(display.to_string()));
    }
    let mut levels = Vec::with_capacity(n_params);
    levels.extend_from_slice(explicit_levels);
    for _ in explicit_levels.len()..n_params {
        levels.push(elab.mk_fresh_level_mvar()?);
    }
    // `base = Some(elab.view.store)` from here on: `cname` is a
    // PERSISTENT-region `NameId` (`resolve_global_name` only ever returns a
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
/// Splits on every `.` and keeps `«»` verbatim; `ident_components` is
/// the escape-aware splitter (used for field names).
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
    /// pre-fix `resolve_global_name` (which re-derived the error text via
    /// `view.store.to_name(None, Some(name))`, `view.store` being the
    /// PERSISTENT store, on a SCRATCH-region `name`) this test either
    /// panicked in `name_row`'s `.expect(..)` or — as observed then,
    /// since the persistent pool from `env_with_foo` is non-empty —
    /// silently returned the WRONG identifier text (a row from the
    /// persistent pool, not "Bar"). Post-fix, `resolve_global_name` takes the
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
        };
        match super::elab_app_fn(&mut elab, &elem, &parsed.tree.kinds, &[], Vec::new(), call) {
            Err(crate::ElabError::UnknownIdent(s)) => assert_eq!(s, "Bar"),
            other => panic!("expected UnknownIdent(\"Bar\"), got {other:?}"),
        }
    }
}
