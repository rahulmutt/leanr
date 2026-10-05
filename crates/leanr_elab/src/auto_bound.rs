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

// Nothing calls the loop until M4c-2c-ii P1 Task 4 (headers) and Task 5
// (level names) wire it in; remove this then.
#![allow(dead_code)]

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;

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
/// (`App.lean:1960-1975`). The `isExporting` private-name hint is not
/// modelled (no private names — later M4). `allowed` reads
/// `options.auto_implicit`, as the oracle reads `autoImplicit.get`; inside
/// a context that equals its `enabled`.
pub(crate) fn unknown_ident(elab: &TermElabM, comps: &[String], raw: &str) -> ElabError {
    let forbidden = match comps {
        [s] => elab
            .auto_bound_forbidden
            .iter()
            .any(|&n| elab.name_str(n) == *s),
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
    /// `withLocalDecl … fun x => loop …`). The oracle's
    /// `withIncRecDepth`/`checkSystem` per retry are not modelled.
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
                    // `withLocalDecl n .implicit (← mkFreshTypeMVar)`
                    let ty = self.mk_fresh_type_mvar()?;
                    let name = crate::command::header::intern_atomic(self, &n)?;
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

    /// oracle: `withoutAutoBoundImplicit` (`TermElabM.lean:1982-1983`).
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
}
