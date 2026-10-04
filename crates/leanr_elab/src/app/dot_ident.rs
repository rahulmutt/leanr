//! M4b-4a P4: `.c` dot identifiers. Oracle: `resolveDottedIdentFn`
//! (`Lean/Elab/App.lean:1985-2058`, pinned v4.33.0-rc1). Design:
//! docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md § P4.
//!
//! Not ported:
//! - overloaded candidates (`:2032`, two or more `C ++ id` under the
//!   `open` declarations): a named M4c-2b-ii seam;
//! - the logged earlier failures (`:2056`), because leanr has no message
//!   log (spec § Seams after P4);
//! - `addCompletionInfo` and the `reverseFieldLookup` hint, which are
//!   UI only.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_meta::MetaError;

use crate::app::head::{ident_components, intern_components, mk_const};
use crate::app::lval::{app_fn, node, render};
use crate::elab::TermElabM;
use crate::error::{ElabError, InvalidDottedIdentReason};

fn dotted_err(id: &str, reason: InvalidDottedIdentReason) -> ElabError {
    ElabError::InvalidDottedIdent {
        id: id.to_string(),
        reason,
    }
}

/// oracle: `resolveDottedIdentFn` (`App.lean:1985-2058`). Returns the one
/// resolution; two or more candidates are seamed (module doc).
pub(crate) fn resolve_dotted_ident_fn(
    elab: &mut TermElabM,
    raw: &str,
    explicit_levels: &[LevelId],
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    // `id.getId.eraseMacroScopes` (`App.lean:2080`), escape-aware: `.«a.b»`
    // is atomic. This name is only ever appended to a constant's
    // namespace, never matched against a binder, so the escape convention
    // of plan § Decisions does not apply.
    let comps = ident_components(raw)?;
    // `:1986-1987`.
    if comps.len() != 1 {
        return Err(dotted_err(raw, InvalidDottedIdentReason::NotAtomic));
    }
    let id = comps[0].as_str();
    // `:1988`.
    elab.try_postpone_if_none_or_mvar(expected)?;
    // `:1989-1990`.
    let Some(expected) = expected else {
        return Err(dotted_err(id, InvalidDottedIdentReason::NoExpectedType));
    };
    // `:1994-1995`.
    with_forall_body(elab, expected, |elab, result_type| {
        go(elab, id, explicit_levels, result_type, expected)
    })
}

/// `withForallBody` (`App.lean:2009-2015`): `whnfCoreUnfoldingAnnotations`,
/// then, while the result is a pi, enter every syntactic binder
/// (`forallTelescope`, non-reducing) and repeat on the body. The
/// telescope's locals are dropped on EVERY exit path (Review Focus 4). A
/// resolution is a closed constant, so it never refers to them.
fn with_forall_body<R>(
    elab: &mut TermElabM,
    ty: ExprId,
    k: impl FnOnce(&mut TermElabM, ExprId) -> Result<R, ElabError>,
) -> Result<R, ElabError> {
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let mut cur = whnf_core_unfolding_annotations(elab, ty)?;
        while matches!(node(elab, cur), Node::Forall { .. }) {
            while let Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = node(elab, cur)
            {
                let fvar = elab
                    .mctx
                    .push_local_decl(binder_name, binder_type, binder_info)?;
                cur = elab.mctx.instantiate1(body, fvar)?;
            }
            cur = whnf_core_unfolding_annotations(elab, cur)?;
        }
        k(elab, cur)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}

/// oracle: `whnfCoreUnfoldingAnnotations` (`Meta/WHNF.lean:980-981`) —
/// `whnfHeadPred` (`:962-970`) with `isTypeAnnotation` (`Expr.lean:1725-1729`):
/// `whnfCore`, and while the head is `outParam` / `semiOutParam` /
/// `optParam` / `autoParam`, unfold it and repeat. Not observable in
/// accepted terms (plan § Spec deviations 6).
fn whnf_core_unfolding_annotations(elab: &mut TermElabM, e: ExprId) -> Result<ExprId, ElabError> {
    let mut e = e;
    loop {
        e = elab.mctx.whnf_core(e)?;
        if !is_type_annotation(elab, e)? {
            return Ok(e);
        }
        match elab.mctx.unfold_definition_pub(e)? {
            Some(u) => e = u,
            None => return Ok(e),
        }
    }
}

/// oracle: `Expr.isTypeAnnotation` (`Expr.lean:1725-1729`).
fn is_type_annotation(elab: &mut TermElabM, e: ExprId) -> Result<bool, ElabError> {
    let Node::Const { name: Some(c), .. } = node(elab, app_fn(elab, e)) else {
        return Ok(false);
    };
    for n in ["outParam", "semiOutParam", "optParam", "autoParam"] {
        if c == intern_components(elab, &[n])? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// `go` (`App.lean:2016-2058`): resolve against `result_type`'s head;
/// on an oracle error, unfold `result_type` and retry. Postponement,
/// seams and `Meta` / `Internal` failures pass through
/// (`ElabError::is_oracle_error`, the `.internal` rethrow at `:2058`).
fn go(
    elab: &mut TermElabM,
    id: &str,
    explicit_levels: &[LevelId],
    result_type: ExprId,
    expected: ExprId,
) -> Result<ExprId, ElabError> {
    let result_type = elab.mctx.instantiate_mvars(result_type)?;
    match resolve_against(elab, id, explicit_levels, result_type, expected) {
        Ok(e) => Ok(e),
        Err(err) if err.is_oracle_error() => match elab.mctx.unfold_definition_pub(result_type)? {
            Some(t) => with_forall_body(elab, t, |elab, t| {
                go(elab, id, explicit_levels, t, expected)
            }),
            // `:2055-2057`: the oracle logs the earlier failures, then
            // throws this one.
            None => Err(err),
        },
        Err(err) => Err(err),
    }
}

/// The `try` body of `go` (`App.lean:2019-2048`).
fn resolve_against(
    elab: &mut TermElabM,
    id: &str,
    explicit_levels: &[LevelId],
    result_type: ExprId,
    expected: ExprId,
) -> Result<ExprId, ElabError> {
    let head = app_fn(elab, result_type);
    // `:2020`.
    elab.try_postpone_if_mvar(head)?;
    match node(elab, head) {
        Node::Const {
            name: Some(decl), ..
        } => {
            let decl_str = render(elab, decl);
            // `isInaccessiblePrivateName` / `privateToUserName`
            // (`:2024-2027`): leanr models no private names.
            if decl_str.starts_with("_private.") {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "`.{id}` against the private type `{decl_str}` (`isInaccessiblePrivateName`, \
                     App.lean:2024) — the slice that models private names"
                )));
            }
            // `fullName := declName ++ id` (`:2027`), one string
            // component under `decl`'s own `NameId`.
            let full = child_name(elab, decl, id)?;
            // `resolveGlobalName Name.anonymous (← getOpenDecls) fullName
            // |>.filter (·.2.isEmpty)` (`:2029-2031`), then `mkConst` each
            // (`:2032-2033`).
            match crate::resolve::resolve_global_name_at_root(elab, full)?.as_slice() {
                [] => {}
                [c] => return mk_const(elab, *c, explicit_levels),
                cs => {
                    return Err(ElabError::UnsupportedSyntax(format!(
                        "overloaded identifier `.{id}` ({} candidates) — M4c-2b-ii",
                        cs.len()
                    )))
                }
            }
            // `resolveLocalName fullName` with no fields (`:2034-2037`):
            // a dotted `let` name, or the declaration's own aux local
            // (`resolve_local_name`'s recursion seam).
            let prefixes = name_prefixes(elab, full);
            if let Some((fvar, 0)) = crate::resolve::resolve_local_name(elab, &prefixes)? {
                if !explicit_levels.is_empty() {
                    return Err(ElabError::InvalidExplicitUniversesForLocal(fvar));
                }
                return Ok(fvar);
            }
            // `:2038-2040`.
            Err(dotted_err(
                id,
                InvalidDottedIdentReason::UnknownConstant {
                    full_name: format!("{decl_str}.{id}"),
                },
            ))
        }
        // `:2041-2042`.
        Node::Sort { .. } => Err(dotted_err(id, InvalidDottedIdentReason::Sort)),
        // `:2043-2048`: syntactic `getAppFn.isMVar` on the ORIGINAL
        // expected type, not instantiated.
        _ => {
            if matches!(node(elab, app_fn(elab, expected)), Node::MVar { .. }) {
                Err(dotted_err(id, InvalidDottedIdentReason::NoExpectedType))
            } else {
                Err(dotted_err(id, InvalidDottedIdentReason::NotConstApp))
            }
        }
    }
}

/// `n` and every proper non-anonymous prefix of it, shortest first:
/// `resolve_local_name`'s `prefixes[k]` = the first `k + 1` components.
fn name_prefixes(elab: &TermElabM, n: NameId) -> Vec<NameId> {
    let base = Some(elab.view.store);
    let mut out = vec![n];
    while let Some(p) = crate::names::parent(elab.mctx.store(), base, *out.last().unwrap()) {
        out.push(p);
    }
    out.reverse();
    out
}

/// `parent ++ s` for an atomic `s`: one string component under
/// `parent`'s own `NameId`, no render/parse round trip. `base = Some(view
/// store)`, so a declared name dedups to its persistent id
/// (`head::intern_components`).
pub(crate) fn child_name(
    elab: &mut TermElabM,
    parent: NameId,
    s: &str,
) -> Result<NameId, ElabError> {
    let base = elab.view.store;
    let store = elab.mctx.store_mut();
    let sid = store.intern_str(Some(base), s).map_err(MetaError::from)?;
    let n = store
        .name_str(Some(base), Some(parent), sid)
        .map_err(MetaError::from)?;
    Ok(n)
}
