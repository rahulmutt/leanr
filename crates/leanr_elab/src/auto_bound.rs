//! Auto-bound implicits: oracle `Elab/AutoBound.lean` and
//! `withAutoBoundImplicit` / `withoutAutoBoundImplicit` /
//! `withAutoBoundImplicitForbiddenPred`
//! (`Elab/Term/TermElabM.lean:1959-1986`).
//!
//! An unknown identifier inside a [`TermElabM::with_auto_bound_implicit`]
//! scope throws the internal [`ElabError::AutoBoundImplicitLocal`]
//! ([`unknown_ident`]); the loop catches it, rewinds the attempt, declares
//! the name as an implicit local of a fresh type, and runs the attempt
//! again.

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_meta::{MVarId, MetaError};

use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `AutoBoundImplicitContext` (`AutoBound.lean:77-89`).
#[derive(Clone, Debug)]
pub(crate) struct AutoBoundCtx {
    /// `autoImplicitEnabled`: the `autoImplicit` option at entry.
    pub enabled: bool,
    /// `boundVariables`: the auto-bound fvars, in discovery order.
    pub bound: Vec<ExprId>,
}

/// The two options this slice ports (`AutoBound.lean:17-25`'s
/// `register_builtin_option`s, both default `true`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ElabOptions {
    pub auto_implicit: bool,
    pub relaxed_auto_implicit: bool,
}

impl Default for ElabOptions {
    fn default() -> Self {
        ElabOptions {
            auto_implicit: true,
            relaxed_auto_implicit: true,
        }
    }
}

/// oracle `isSubScriptAlnum` (`Init/Meta/Defs.lean:111-118`): numeric
/// subscripts `₀`-`₉`, subscript letters `ₐ`-`ₜ`, `ᵢ`-`ᵪ`, and `ⱼ`.
fn is_sub_script_alnum(c: char) -> bool {
    ('\u{2080}'..='\u{2089}').contains(&c)
        || ('\u{2090}'..='\u{209c}').contains(&c)
        || ('\u{1d62}'..='\u{1d6a}').contains(&c)
        || c == '\u{2c7c}'
}

/// `isValidAutoBoundSuffix` (`AutoBound.lean:35-36`): every char after
/// the first is an ASCII digit (`Char.isDigit`), a subscript, `_` or `'`.
fn is_valid_suffix(s: &str) -> bool {
    s.chars()
        .skip(1)
        .all(|c| c.is_ascii_digit() || is_sub_script_alnum(c) || c == '_' || c == '\'')
}

/// `checkValidAutoBoundImplicitName` (`AutoBound.lean:56-67`), `.ok true`
/// only; its `.error` (note) arm is `false` here — the note is not
/// modelled (spec Amendment 1, item 3). `comps` are the identifier's
/// components: only an atomic name (`.str .anonymous s`) qualifies. A
/// `_leanr_` head is leanr's macro-scope stand-in, which the oracle
/// rejects by the same atomicity test (a macro-scoped name is not
/// `.str .anonymous`; `AutoBound.lean:38-49`).
pub(crate) fn check_valid_auto_bound_implicit_name(
    comps: &[String],
    allowed: bool,
    relaxed: bool,
) -> bool {
    match comps {
        [s] if !s.is_empty() && !s.starts_with("_leanr_") => {
            allowed && (relaxed || is_valid_suffix(s))
        }
        _ => false,
    }
}

/// `isValidAutoBoundLevelName` (`AutoBound.lean:69-72`). `String.front`'s
/// `Char.isLower` is ASCII `a`-`z` only.
pub(crate) fn is_valid_auto_bound_level_name(s: &str, relaxed: bool) -> bool {
    !s.is_empty()
        && (relaxed
            || (s.chars().next().is_some_and(|c| c.is_ascii_lowercase()) && is_valid_suffix(s)))
}

/// oracle: `elabAppFnId`'s `throwUnknownIdWithSuggestions`
/// (`App.lean:1960-1974`). The `isExporting` private-name hint is not
/// modelled (no private names — later M4). `allowed` reads
/// `options.auto_implicit`, as the oracle reads `autoImplicit.get`; inside
/// a context that equals its `enabled`.
///
/// The forbidden test is `NameId` equality with `.str .anonymous comps[0]`
/// without interning it: hash-consing makes that NameId equal exactly the
/// atomic names whose one component is `comps[0]`, so the test compares
/// the decoded component (never the `«»`-escaped rendering).
pub(crate) fn unknown_ident(elab: &TermElabM, comps: &[String], raw: &str) -> ElabError {
    let forbidden = match comps {
        [s] => {
            let base = Some(elab.view.store);
            let st = elab.mctx.store();
            elab.auto_bound_forbidden.iter().any(|&n| {
                crate::names::is_atomic(st, base, Some(n))
                    && crate::names::last_str(st, base, n) == Some(s.as_str())
            })
        }
        _ => false,
    };
    if !forbidden && elab.auto_bound.is_some() {
        let o = elab.options;
        if check_valid_auto_bound_implicit_name(comps, o.auto_implicit, o.relaxed_auto_implicit) {
            return ElabError::AutoBoundImplicitLocal(comps[0].clone());
        }
    }
    ElabError::UnknownIdent(raw.to_string())
}

impl TermElabM<'_> {
    /// `n` rendered (`Name.toString`).
    pub(crate) fn name_str(&self, n: NameId) -> String {
        self.mctx
            .store()
            .to_name(Some(self.view.store), Some(n))
            .to_string()
    }

    /// oracle: `withAutoBoundImplicit` (`TermElabM.lean:1959-1980`).
    /// Iterative where the oracle recurses (`loop`): one pass per
    /// discovered name, so 30 autos are 31 attempts on a flat stack.
    ///
    /// The autos' local decls live in the lctx the CALLER brackets; each
    /// attempt's lctx checkpoint is taken AFTER the autos pushed so far,
    /// so rewinding a failed attempt keeps them (the oracle's nested
    /// `withLocalDecl … fun x => loop …`). Each retry counts as one
    /// `withIncRecDepth` level (`:1963`) against
    /// [`crate::error::MAX_REC_DEPTH`], as `app/lval.rs`'s `addLValArg.go`
    /// does; `checkSystem` is not modelled.
    pub(crate) fn with_auto_bound_implicit<R>(
        &mut self,
        mut k: impl FnMut(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let outer = self.auto_bound.take();
        let enabled = self.options.auto_implicit;
        self.auto_bound = Some(AutoBoundCtx {
            enabled,
            bound: Vec::new(),
        });
        let out = if !enabled {
            // `:1976-1979`: the context is set (it shapes the error
            // message) but nothing is caught.
            k(self)
        } else {
            self.auto_bound_retry_loop(&mut k)
        };
        self.auto_bound = outer;
        out
    }

    fn auto_bound_retry_loop<R>(
        &mut self,
        k: &mut impl FnMut(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        // `withIncRecDepth` (`TermElabM.lean:1963`) around every attempt:
        // the oracle's `loop` recurses once per retry, so the retries
        // count against `defaultMaxRecDepth`; see `ElabError::MaxRecDepth`.
        use crate::error::MAX_REC_DEPTH;
        let mut depth: usize = 0;
        loop {
            // `saveState`: `Term.State` (incl. `levelNames`) + the lctx,
            // which the oracle scopes by the reader.
            let saved = self.save_term_state();
            let level_names = self.level_names.clone();
            let lctx = self.mctx.lctx_checkpoint();
            match k(self) {
                Err(ElabError::AutoBoundImplicitLocal(n)) => {
                    // `s.restore (restoreInfo := true)`
                    self.restore_term_state(saved);
                    self.level_names = level_names;
                    self.mctx.lctx_restore(lctx);
                    let name = crate::command::header::intern_atomic(self, &n)?;
                    // Not the oracle's fast-fail ahead of the depth cap
                    // below: a name thrown again after it was bound can
                    // only repeat until maxRecDepth (the bound local is in
                    // scope for every later attempt), so a regressed throw
                    // site fails at once with a precise message.
                    if self.auto_bound_has_name(name) {
                        return Err(ElabError::Internal(format!(
                            "auto-bound retry made no progress: `{n}` was thrown again after \
                             it was bound"
                        )));
                    }
                    // The retry's `withIncRecDepth` (`:1963`).
                    if depth + 1 >= MAX_REC_DEPTH {
                        return Err(ElabError::MaxRecDepth);
                    }
                    depth += 1;
                    // `withLocalDecl n .implicit (← mkFreshTypeMVar)`
                    let ty = self.mk_fresh_type_mvar()?;
                    let x = self
                        .mctx
                        .push_local_decl(Some(name), ty, BinderInfo::Implicit)?;
                    self.auto_bound
                        .as_mut()
                        .expect("with_auto_bound_implicit sets the context")
                        .bound
                        .push(x);
                }
                other => return other,
            }
        }
    }

    /// Some auto bound so far is named `name`.
    fn auto_bound_has_name(&mut self, name: NameId) -> bool {
        let bound = match &self.auto_bound {
            Some(c) => c.bound.clone(),
            None => return false,
        };
        bound.into_iter().any(|x| {
            self.fvar_decl(x)
                .is_some_and(|d| d.binder_name == Some(name))
        })
    }

    /// The current local context's declaration of fvar `x`, if any.
    fn fvar_decl(&mut self, x: ExprId) -> Option<leanr_kernel::LocalDecl> {
        let Node::FVar { id: Some(id) } = self.mctx.store().expr_node(Some(self.view.store), x)
        else {
            return None;
        };
        self.mctx.current_lctx().lctx().get(id).cloned()
    }

    /// oracle: `addAutoBoundImplicits xs none` (`TermElabM.lean:2071-2089`)
    /// with `collectUnassignedMVars` (`:1991-2015`): each auto, in
    /// discovery order, preceded by the unassigned mvars of its type not
    /// collected yet. Returns `autos ++ xs`. No inlay hint (no info tree).
    pub(crate) fn add_auto_bound_implicits(
        &mut self,
        xs: &[ExprId],
    ) -> Result<Vec<ExprId>, ElabError> {
        let todo = self
            .auto_bound
            .as_ref()
            .map(|c| c.bound.clone())
            .unwrap_or_default();
        let mut autos: Vec<ExprId> = Vec::new();
        for auto in todo {
            let ty = self.mctx.infer_type(auto)?;
            self.collect_unassigned_mvars(ty, &mut autos)?;
            autos.push(auto);
        }
        // `:2080-2085`
        for &auto in &autos {
            let Some(decl) = self.fvar_decl(auto) else {
                continue; // `auto.isFVar` (an fvar always has a decl here)
            };
            for &x in xs {
                if self.local_decl_depends_on_fvar(decl.ty, x)? {
                    return Err(ElabError::AutoImplicitDependsOnExplicit {
                        auto: self.fvar_user_name(auto),
                        x: self.fvar_user_name(x),
                    });
                }
            }
        }
        autos.extend_from_slice(xs);
        Ok(autos)
    }

    fn fvar_user_name(&mut self, x: ExprId) -> String {
        match self.fvar_decl(x).and_then(|d| d.binder_name) {
            Some(n) => self.name_str(n),
            None => "_".to_string(),
        }
    }

    /// Approximates `localDeclDependsOn localDecl x` (`:2084`): `x` occurs
    /// in the instantiated decl type. The oracle also follows the lctxs of
    /// the type's unassigned mvars; reachable only by the unit test (spec
    /// Amendment 1: the error is unreachable from source).
    fn local_decl_depends_on_fvar(&mut self, ty: ExprId, x: ExprId) -> Result<bool, ElabError> {
        let ty = self.mctx.instantiate_mvars(ty)?;
        let mut fvars = HashSet::new();
        crate::app::elim_info::collect_fvars(self, ty, &mut fvars);
        Ok(fvars.contains(&x))
    }

    /// `collectUnassignedMVars type init` (`:1991-2015`) with `init` =
    /// `result`: dependency-first, each mvar once, skipping assigned ones
    /// and ones already in `result`. Mvars are compared by `MVarId` (the
    /// oracle's `mkMVar` equality).
    fn collect_unassigned_mvars(
        &mut self,
        ty: ExprId,
        result: &mut Vec<ExprId>,
    ) -> Result<(), ElabError> {
        let mut todo: std::collections::VecDeque<MVarId> = self.get_mvars(ty)?.into();
        if todo.is_empty() {
            return Ok(());
        }
        let base = Some(self.view.store);
        let mvar_of = |elab: &Self, e: ExprId| match elab.mctx.store().expr_node(base, e) {
            Node::MVar { id: Some(n) } => Some(MVarId(n)),
            _ => None,
        };
        // `go mvarIds.toList init init`: `visited` starts as `init`.
        let mut in_result: Vec<MVarId> = result.iter().filter_map(|&e| mvar_of(self, e)).collect();
        let mut visited: Vec<MVarId> = in_result.clone();
        while let Some(m) = todo.pop_front() {
            // pushed BEFORE the assigned/contained checks (`:2003`).
            visited.push(m);
            if self.mctx.mctx().is_assigned(m) || in_result.contains(&m) {
                continue;
            }
            let mty = self
                .mctx
                .mctx()
                .decl(m)
                .ok_or_else(|| ElabError::Internal("undeclared mvar".into()))?
                .ty;
            let fresh: Vec<MVarId> = self
                .get_mvars(mty)?
                .into_iter()
                .filter(|n| !visited.contains(n))
                .collect();
            if fresh.is_empty() {
                let e = self
                    .mctx
                    .store_mut()
                    .expr_mvar(base, Some(m.0))
                    .map_err(MetaError::from)?;
                result.push(e);
                in_result.push(m);
            } else {
                // `go (mvarIdsNew.toList ++ mvarId :: mvarIds)`
                todo.push_front(m);
                for n in fresh.into_iter().rev() {
                    todo.push_front(n);
                }
            }
        }
        Ok(())
    }

    /// oracle: `withoutAutoBoundImplicit` (`TermElabM.lean:1982-1983`).
    #[allow(dead_code)] // P2: `runTermElabM`'s `elabFn` (`Command.lean:791`, `:798`)
    pub(crate) fn without_auto_bound_implicit<R>(
        &mut self,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let outer = self.auto_bound.take();
        let out = k(self);
        self.auto_bound = outer;
        out
    }

    /// oracle: `withAutoBoundImplicitForbiddenPred`
    /// (`TermElabM.lean:1985-1986`), with the predicate a name list: the
    /// new names are OR-ed onto the enclosing ones.
    pub(crate) fn with_auto_bound_forbidden<R>(
        &mut self,
        names: &[NameId],
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let n = self.auto_bound_forbidden.len();
        self.auto_bound_forbidden.extend_from_slice(names);
        let out = k(self);
        self.auto_bound_forbidden.truncate(n);
        out
    }
}

#[cfg(test)]
mod tests {
    use leanr_kernel::BinderInfo;

    use super::*;
    use crate::error::ElabError;
    use crate::test_support::{local_decl_of, parse_term, with_elab0};

    #[test]
    fn name_checks_follow_auto_bound_lean() {
        // AutoBound.lean: checkValidAutoBoundImplicitName / isValidAutoBoundSuffix
        let c = |s: &str| vec![s.to_string()];
        assert!(check_valid_auto_bound_implicit_name(&c("α"), true, true));
        assert!(check_valid_auto_bound_implicit_name(&c("foo"), true, true));
        assert!(!check_valid_auto_bound_implicit_name(
            &c("foo"),
            true,
            false
        ));
        for ok in ["α₁", "X12", "β'", "α_1", "αᵢ"] {
            assert!(
                check_valid_auto_bound_implicit_name(&c(ok), true, false),
                "{ok}"
            );
        }
        assert!(!check_valid_auto_bound_implicit_name(&c("α"), false, true));
        assert!(!check_valid_auto_bound_implicit_name(
            &["A".into(), "b".into()],
            true,
            true
        ));
        assert!(!check_valid_auto_bound_implicit_name(&c(""), true, true));
        // isValidAutoBoundLevelName: strict = lowercase head + valid suffix
        assert!(is_valid_auto_bound_level_name("u", false));
        assert!(is_valid_auto_bound_level_name("u1", false));
        assert!(!is_valid_auto_bound_level_name("U", false));
        assert!(!is_valid_auto_bound_level_name("uv", false));
        assert!(is_valid_auto_bound_level_name("uv", true));
        // `Char.isLower` is ASCII-only: a Greek head is not strict-valid.
        assert!(!is_valid_auto_bound_level_name("α", false));
        assert!(is_valid_auto_bound_level_name("α", true));
    }

    #[test]
    fn the_loop_binds_an_unknown_identifier_and_retries() {
        with_elab0(|elab, kinds| {
            let stx = parse_term(kinds, "List α");
            let entry = elab.mctx.lctx_checkpoint();
            let (ty, autos) = elab
                .with_auto_bound_implicit(|elab| {
                    let t = crate::builtin::binder::elab_type(elab, &stx, kinds)?;
                    Ok((t, elab.auto_bound.as_ref().unwrap().bound.clone()))
                })
                .expect("auto-bound");
            assert_eq!(autos.len(), 1, "exactly one auto: α");
            let d = local_decl_of(elab, autos[0]).expect("declared"); // fvar's decl
            assert_eq!(d.binder_info, BinderInfo::Implicit);
            let base = Some(elab.view.store);
            assert!(
                elab.mctx.store().expr_data(base, ty).has_fvar(),
                "List α mentions the auto"
            );
            assert_eq!(
                elab.mctx.lctx_checkpoint(),
                entry + 1,
                "only the auto survives the retries"
            );
            assert!(elab.auto_bound.is_none(), "the context is scoped");
        });
    }

    /// An auto found under an open binder (`∀ (y : Nat), List α`) is
    /// declared at the OUTER level: the binder elaborators bracket their
    /// own telescope on every exit path, so nothing of the failed attempt
    /// is left behind (spec Review Focus 1, term level).
    #[test]
    fn the_retry_drops_the_failed_attempts_binders() {
        with_elab0(|elab, kinds| {
            let stx = parse_term(kinds, "∀ (y : Nat), List α");
            let entry = elab.mctx.lctx_checkpoint();
            let autos = elab
                .with_auto_bound_implicit(|elab| {
                    crate::builtin::binder::elab_type(elab, &stx, kinds)?;
                    Ok(elab.auto_bound.as_ref().unwrap().bound.clone())
                })
                .expect("auto-bound");
            assert_eq!(autos.len(), 1, "exactly one auto: α");
            assert_eq!(
                elab.mctx.lctx_checkpoint(),
                entry + 1,
                "the failed attempt's `y` was dropped"
            );
            let d = local_decl_of(elab, autos[0]).expect("declared");
            assert_eq!(elab.name_str(d.binder_name.unwrap()), "α");
        });
    }

    /// A `k` that leaves its own locals open across the failing
    /// elaboration (the header shape: binders stay in the lctx while the
    /// type is elaborated) leaks them into the next attempt unless the
    /// loop rewinds the lctx itself — the oracle's `withLocalDecl` scoping.
    #[test]
    fn the_retry_drops_the_failed_attempts_locals() {
        with_elab0(|elab, kinds| {
            let stx = parse_term(kinds, "List α");
            let entry = elab.mctx.lctx_checkpoint();
            let x_name = crate::command::header::intern_atomic(elab, "x").unwrap();
            let autos = elab
                .with_auto_bound_implicit(|elab| {
                    let ty = elab.mk_fresh_type_mvar()?;
                    elab.mctx
                        .push_local_decl(Some(x_name), ty, BinderInfo::Default)?;
                    crate::builtin::binder::elab_type(elab, &stx, kinds)?;
                    Ok(elab.auto_bound.as_ref().unwrap().bound.clone())
                })
                .expect("auto-bound");
            assert_eq!(autos.len(), 1, "exactly one auto: α");
            assert_eq!(
                elab.mctx.lctx_checkpoint(),
                entry + 2,
                "α and the retry's `x`; the failed attempt's `x` was dropped"
            );
        });
    }

    /// oracle: `levelNames` is `Term.State`, so the retry's `s.restore`
    /// rewinds a universe the failed attempt auto-bound (`Level.lean:82`).
    /// On every source path this is unobservable (each failed attempt's
    /// universes are a prefix of the next attempt's, and `elab_level`
    /// skips a name already present; the header's own `with_level_names`
    /// inside the loop also rewinds), so `k` pushes unconditionally here.
    #[test]
    fn the_retry_rewinds_level_names() {
        with_elab0(|elab, kinds| {
            let stx = parse_term(kinds, "List α");
            let v = crate::command::header::intern_atomic(elab, "v").unwrap();
            let names = elab
                .with_auto_bound_implicit(|elab| {
                    elab.level_names.insert(0, v);
                    crate::builtin::binder::elab_type(elab, &stx, kinds)?;
                    Ok(elab.level_names.clone())
                })
                .expect("auto-bound");
            assert_eq!(names, vec![v], "pushed once per surviving attempt");
        });
    }

    /// An unknown universe binds in place, newest first (`Level.lean:82`'s
    /// `paramName :: s.levelNames`) — no retry — and only in an enabled
    /// context; outside one it is "unknown universe level".
    #[test]
    fn an_unknown_universe_binds_in_place_newest_first() {
        with_elab0(|elab, kinds| {
            let stx = parse_term(kinds, "Sort v → Sort u → Sort v");
            let attempts = std::cell::Cell::new(0);
            let names = elab
                .with_auto_bound_implicit(|elab| {
                    attempts.set(attempts.get() + 1);
                    crate::builtin::binder::elab_type(elab, &stx, kinds)?;
                    Ok(elab.level_names.clone())
                })
                .expect("auto-bound");
            let names: Vec<String> = names.into_iter().map(|n| elab.name_str(n)).collect();
            assert_eq!(names, ["u", "v"]);
            assert_eq!(attempts.get(), 1, "a universe never retries");
            elab.level_names.clear();
            let e = crate::builtin::binder::elab_type(elab, &stx, kinds).unwrap_err();
            assert_eq!(
                e.oracle_first_line().as_deref(),
                Some("unknown universe level `v`")
            );
            elab.options.auto_implicit = false;
            let e = elab
                .with_auto_bound_implicit(|elab| {
                    crate::builtin::binder::elab_type(elab, &stx, kinds)
                })
                .unwrap_err();
            assert!(
                matches!(e, ElabError::UnknownUniverseLevel(ref s) if s == "v"),
                "a disabled context: {e:?}"
            );
            // `isValidAutoBoundLevelName`: atomic only; strict (`relaxed`
            // off) wants a lowercase head.
            elab.options.auto_implicit = true;
            for (src, opts_relaxed, bad) in [("Sort a.b", true, "a.b"), ("Sort U", false, "U")] {
                elab.options.relaxed_auto_implicit = opts_relaxed;
                let stx = parse_term(kinds, src);
                let e = elab
                    .with_auto_bound_implicit(|elab| {
                        crate::builtin::binder::elab_type(elab, &stx, kinds)
                    })
                    .unwrap_err();
                assert!(
                    matches!(e, ElabError::UnknownUniverseLevel(ref s) if s == bad),
                    "{src}: {e:?}"
                );
            }
        });
    }

    #[test]
    fn without_a_context_it_is_a_plain_unknown_identifier() {
        with_elab0(|elab, kinds| {
            let stx = parse_term(kinds, "List α");
            let e = crate::builtin::binder::elab_type(elab, &stx, kinds).unwrap_err();
            assert!(
                matches!(e, ElabError::UnknownIdent(ref s) if s == "α"),
                "{e:?}"
            );
        });
    }

    #[test]
    fn a_disabled_context_reports_unknown_identifier() {
        with_elab0(|elab, kinds| {
            elab.options.auto_implicit = false;
            let stx = parse_term(kinds, "List α");
            let e = elab
                .with_auto_bound_implicit(|elab| {
                    crate::builtin::binder::elab_type(elab, &stx, kinds)
                })
                .unwrap_err();
            assert!(
                matches!(e, ElabError::UnknownIdent(ref s) if s == "α"),
                "{e:?}"
            );
        });
    }

    #[test]
    fn a_forbidden_name_is_not_auto_bound() {
        with_elab0(|elab, kinds| {
            let f = crate::command::header::intern_atomic(elab, "self_name").unwrap();
            let stx = parse_term(kinds, "List self_name");
            let e = elab
                .with_auto_bound_forbidden(&[f], |elab| {
                    elab.with_auto_bound_implicit(|elab| {
                        crate::builtin::binder::elab_type(elab, &stx, kinds)
                    })
                })
                .unwrap_err();
            assert!(
                matches!(e, ElabError::UnknownIdent(ref s) if s == "self_name"),
                "{e:?}"
            );
            assert!(elab.auto_bound_forbidden.is_empty(), "forbidden is scoped");
        });
    }

    #[test]
    fn the_internal_error_escapes_observing() {
        // oracle `Term.observing` catches `.error` and postpone only.
        with_elab0(|elab, _| {
            let r = elab.observing(|_| Err(ElabError::AutoBoundImplicitLocal("x".into())));
            assert!(matches!(r, Err(ElabError::AutoBoundImplicitLocal(_))));
            assert!(!ElabError::AutoBoundImplicitLocal("x".into()).is_oracle_error());
        });
    }

    /// A table expansion's head (`app::elab_app_expanded`) is a quotation
    /// identifier: macro-scoped, so the oracle's
    /// `checkValidAutoBoundImplicitName` (`.str .anonymous s` only) never
    /// accepts it. `Elab0` has no `Or`, so the expansion of `a ∨ b` fails
    /// on its head with a plain unknown identifier even inside the loop.
    /// Auto-binding it instead would retry forever, as the expanded head
    /// is looked up in the environment only.
    #[test]
    fn a_macro_head_is_never_auto_bound() {
        with_elab0(|elab, kinds| {
            let a = parse_term(kinds, "a");
            let e = elab
                .with_auto_bound_implicit(|elab| {
                    let args = [a.clone(), a.clone()];
                    crate::app::elab_app_expanded(elab, "Or", &args, &a, kinds, None)
                })
                .unwrap_err();
            assert!(
                matches!(e, ElabError::UnknownIdent(ref s) if s == "Or"),
                "{e:?}"
            );
            assert!(elab.auto_bound.is_none());
        });
    }

    #[test]
    fn an_auto_depending_on_an_explicit_binder_is_rejected() {
        // Unreachable from source (spec Amendment 1); constructed directly.
        with_elab0(|elab, _| {
            let nat = crate::builtin::op::mk_const_named(elab, "Nat").unwrap();
            let eq = crate::builtin::op::mk_const_named(elab, "Eq").unwrap();
            let xn = crate::command::header::intern_atomic(elab, "x").unwrap();
            let an = crate::command::header::intern_atomic(elab, "a").unwrap();
            let x = elab
                .mctx
                .push_local_decl(Some(xn), nat, BinderInfo::Default)
                .unwrap();
            let base = Some(elab.view.store);
            let st = elab.mctx.store_mut();
            let ty = st.expr_app(base, eq, nat).unwrap();
            let ty = st.expr_app(base, ty, x).unwrap();
            let ty = st.expr_app(base, ty, x).unwrap(); // Eq Nat x x
            let a = elab
                .mctx
                .push_local_decl(Some(an), ty, BinderInfo::Implicit)
                .unwrap();
            elab.auto_bound = Some(AutoBoundCtx {
                enabled: true,
                bound: vec![a],
            });
            let e = elab.add_auto_bound_implicits(&[x]).unwrap_err();
            assert_eq!(
                e.oracle_first_line().as_deref(),
                Some(
                    "invalid auto implicit argument `a`, it depends on explicitly provided \
                     argument `x`"
                ),
                "{e:?}"
            );
            // An explicit binder the auto does not mention is fine.
            let y = elab
                .mctx
                .push_local_decl(Some(xn), nat, BinderInfo::Default)
                .unwrap();
            assert_eq!(elab.add_auto_bound_implicits(&[y]).unwrap(), vec![a, y]);
        });
    }

    /// `collectUnassignedMVars`: an auto's type mvar precedes it, and a
    /// mvar in that mvar's type precedes both (dependency-first); each
    /// mvar is collected once across autos.
    #[test]
    fn add_auto_bound_implicits_puts_type_mvars_first() {
        with_elab0(|elab, _| {
            // ?t : Sort ?u, ?m : ?t, a : C ?m ?t (as an app of fresh mvars)
            let t = elab.mk_fresh_type_mvar().unwrap();
            let m = elab.mk_fresh_expr_mvar(t).unwrap();
            let c = elab.mk_fresh_type_mvar().unwrap();
            let base = Some(elab.view.store);
            let ty = elab.mctx.store_mut().expr_app(base, c, m).unwrap();
            let an = crate::command::header::intern_atomic(elab, "a").unwrap();
            let bn = crate::command::header::intern_atomic(elab, "b").unwrap();
            let a = elab
                .mctx
                .push_local_decl(Some(an), ty, BinderInfo::Implicit)
                .unwrap();
            let b = elab
                .mctx
                .push_local_decl(Some(bn), t, BinderInfo::Implicit)
                .unwrap();
            elab.auto_bound = Some(AutoBoundCtx {
                enabled: true,
                bound: vec![a, b],
            });
            let out = elab.add_auto_bound_implicits(&[]).unwrap();
            // `c`'s own type `Sort ?v` has no expr mvar; `?m : ?t` pulls `?t`
            // in first; `b : ?t` adds nothing new.
            assert_eq!(out, vec![c, t, m, a, b]);
        });
    }

    /// Not the oracle's (which caps the loop at maxRecDepth): a name thrown
    /// again after it was bound fails fast instead of retrying to the cap.
    #[test]
    fn a_name_thrown_after_it_was_bound_stops_the_loop() {
        with_elab0(|elab, _| {
            let mut attempts = 0;
            let e = elab
                .with_auto_bound_implicit(|_| -> Result<(), ElabError> {
                    attempts += 1;
                    Err(ElabError::AutoBoundImplicitLocal("x".into()))
                })
                .unwrap_err();
            assert!(
                matches!(e, ElabError::Internal(ref m) if m.contains("no progress")),
                "{e:?}"
            );
            assert_eq!(attempts, 2, "bound once, then the repeat is refused");
            assert!(elab.auto_bound.is_none());
        });
    }

    /// oracle: every retry runs under `withIncRecDepth`
    /// (`TermElabM.lean:1963`). A throw site that names a fresh, distinct
    /// local every attempt slips past the no-progress guard; the depth cap
    /// still ends the loop (so a regressed guard can never hang or OOM).
    #[test]
    fn endless_fresh_names_hit_the_rec_depth_cap() {
        with_elab0(|elab, _| {
            let entry = elab.mctx.lctx_checkpoint();
            let mut attempts = 0usize;
            let e = elab
                .with_auto_bound_implicit(|_| -> Result<(), ElabError> {
                    attempts += 1;
                    Err(ElabError::AutoBoundImplicitLocal(format!("x{attempts}")))
                })
                .unwrap_err();
            assert!(matches!(e, ElabError::MaxRecDepth), "{e:?}");
            assert!(!e.is_oracle_error(), "a runtime exception: never caught");
            assert_eq!(
                attempts,
                crate::error::MAX_REC_DEPTH,
                "depths 0..MAX_REC_DEPTH, as `addLValArg.go`'s count"
            );
            assert!(elab.auto_bound.is_none(), "the context is scoped");
            // The caller brackets the autos' lctx (`elab_header`); the loop
            // itself pushed exactly one local per retry.
            assert_eq!(
                elab.mctx.lctx_checkpoint(),
                entry + crate::error::MAX_REC_DEPTH - 1
            );
        });
    }

    /// The forbidden test compares the decoded component, not the
    /// `«»`-escaped rendering of the forbidden name.
    #[test]
    fn a_forbidden_name_needing_escapes_is_not_auto_bound() {
        with_elab0(|elab, kinds| {
            let f = crate::command::header::intern_atomic(elab, "a b").unwrap();
            let stx = parse_term(kinds, "List «a b»");
            let e = elab
                .with_auto_bound_forbidden(&[f], |elab| {
                    elab.with_auto_bound_implicit(|elab| {
                        crate::builtin::binder::elab_type(elab, &stx, kinds)
                    })
                })
                .unwrap_err();
            assert!(matches!(e, ElabError::UnknownIdent(_)), "{e:?}");
        });
    }
}
