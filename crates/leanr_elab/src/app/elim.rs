//! M4b-4c P2: eliminator elaboration. Oracle: `Lean/Elab/App.lean`,
//! `shouldElabAsElim` (`:1322-1328`), `elabAppArgs.elabAsElim?`
//! (`:1397-1431`) and the `ElabElim` namespace (`:1140-1319`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_meta::{MVarId, MVarKind};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;

use crate::app::args::ensure_arg_type;
use crate::app::elim_info::{get_elab_elim_info, ElabElimInfo};
use crate::app::expand::{Arg, NamedArg};
use crate::app::lval;
use crate::app::state::{open_forall_telescope, open_forall_telescope_reducing, whnf_forall};
use crate::dispatch::SynElem;
use crate::elab::{TermElabM, TermTarget};
use crate::error::{ElabError, EliminatorErrorReason as R};

/// oracle: `shouldElabAsElim` (`App.lean:1322-1328`). `isRec` is the
/// constant-kind test (`ConstantInfo::Rec`); the other four read P1's
/// decoded `auxRecExt` / `elabAsElim` sets.
pub fn should_elab_as_elim(elab: &TermElabM<'_>, name: NameId) -> bool {
    matches!(
        elab.view.get(name),
        Some(leanr_kernel::ConstantInfo::Rec(_))
    ) || elab.mctx.is_cases_on_recursor(name)
        || elab.mctx.is_brec_on_recursor(name)
        || elab.mctx.is_rec_on_recursor(name)
        || elab.mctx.has_elab_as_elim_tag(name)
}

/// oracle: `elabAppArgs.elabAsElim?` (`App.lean:1397-1431`). `Some` means
/// divert to `ElabElim`. `heedElabAsElim` is not modelled: only the
/// `induction` tactic clears it (`Tactic/Induction.lean:806`), so in
/// term elaboration it is always `true`.
pub fn elab_as_elim_info(
    elab: &mut TermElabM<'_>,
    f: ExprId,
    named_args: &[NamedArg],
    args: &[Arg],
    explicit: bool,
    ellipsis: bool,
    kinds: &KindInterner,
) -> Result<Option<ElabElimInfo>, ElabError> {
    if explicit || ellipsis {
        return Ok(None);
    }
    let Node::Const {
        name: Some(name), ..
    } = lval::node(elab, f)
    else {
        return Ok(None);
    };
    if !should_elab_as_elim(elab, name) {
        return Ok(None);
    }
    let info = get_elab_elim_info(elab, name)?;
    let f_type = elab.mctx.infer_type(f)?;
    let cp = elab.mctx.lctx_checkpoint();
    let r = motive_supplied(elab, f_type, &info, named_args, args, kinds);
    elab.mctx.lctx_restore(cp);
    Ok(if r? { None } else { Some(info) })
}

/// The `forallTelescopeReducing` body of `elabAsElim?`
/// (`App.lean:1403-1431`): simulate argument consumption up to the
/// motive, then decide whether the caller already supplied it.
fn motive_supplied(
    elab: &mut TermElabM<'_>,
    f_type: ExprId,
    info: &ElabElimInfo,
    named_args: &[NamedArg],
    args: &[Arg],
    kinds: &KindInterner,
) -> Result<bool, ElabError> {
    let (xs, _) = open_forall_telescope_reducing(elab, f_type)?;
    let mut named: Vec<&str> = named_args.iter().map(|n| n.name.as_str()).collect();
    let mut args = args;
    // oracle: `let some x := xs[elimInfo.motivePos]? | unreachable!` (`:1415`);
    // `.olean` input is untrusted, so this is an error, not a panic.
    let Some(x) = xs.get(info.motive_pos) else {
        return Err(ElabError::Internal(
            "elabAsElim?: motivePos past the telescope".into(),
        ));
    };
    for p in &xs[..info.motive_pos] {
        let user = binder_user_name(elab, p.name);
        if named.contains(&user.as_str()) {
            named.retain(|n| *n != user);
        } else if p.bi == BinderInfo::Default {
            args = args.get(1..).unwrap_or(&[]);
        }
    }
    let user = binder_user_name(elab, x.name);
    if named.contains(&user.as_str()) {
        return Ok(true);
    }
    Ok(match (x.bi == BinderInfo::Default, args.first()) {
        (true, Some(Arg::Expr(_))) => true,
        (true, Some(Arg::Stx(stx))) => kinds.name(stx.kind()) != "Lean.Parser.Term.hole",
        (true, Some(Arg::AnonCtorTail { .. })) => true,
        _ => false,
    })
}

/// A binder's user name rendered the way `NamedArg::name` is stored
/// (source text). `.anonymous` renders as `[anonymous]`, which no
/// named argument can spell.
pub(crate) fn binder_user_name(elab: &TermElabM<'_>, n: Option<NameId>) -> String {
    let base = elab.view.store;
    elab.mctx.store().to_name(Some(base), n).to_string()
}

/// oracle: `ElabElim.Context` + `ElabElim.State` (`App.lean:1142-1162`),
/// one struct, the same way `AppElab` folds `ElabAppArgs.M`
/// (`state.rs`'s module doc). Deliberately not an `AppElab`: the oracle's
/// `ElabElim.M` has its own state, and its `fType` is kept INSTANTIATED
/// after every argument (`addArgAndContinue`), unlike `AppElab`'s lazy
/// `fArgs` scheme.
pub(crate) struct ElimElab<'a, 'e> {
    pub(crate) elab: &'a mut TermElabM<'e>,
    // Context
    pub(crate) info: ElabElimInfo,
    pub(crate) expected: ExprId,
    /// The application's syntax: the oracle's ambient `getRef`
    /// (`state::Context::stx`'s doc). Used for `.expr` arguments'
    /// `ensureArgType` and for `synthesizeAppInstMVars`.
    pub(crate) stx: SynElem,
    // State
    pub(crate) f: ExprId,
    pub(crate) f_type: ExprId,
    pub(crate) named_args: Vec<NamedArg>,
    pub(crate) args: Vec<Arg>,
    pub(crate) inst_mvars: Vec<MVarId>,
    pub(crate) idx: usize,
    pub(crate) motive: Option<ExprId>,
}

/// oracle: `LOption Arg`, as returned by `getNextArg?`.
enum NextArg {
    Some(Arg),
    None,
    Undef,
}

impl ElimElab<'_, '_> {
    /// oracle: `ElabElim.main` (`App.lean:1286-1317`). The oracle
    /// recurses through `addArgAndContinue`; this loops.
    pub(crate) fn main(mut self, kinds: &KindInterner) -> Result<ExprId, ElabError> {
        loop {
            let ft = whnf_forall(self.elab, self.f_type)?;
            let Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = lval::node(self.elab, ft)
            else {
                return self.finalize(kinds);
            };
            let arg = if self.idx == self.info.motive_pos {
                let m = match self.get_next_arg(binder_name, binder_info) {
                    // `elabAsElim?` guarantees this is a positional `_`.
                    NextArg::Some(a) => self.elab_arg(a, binder_type, kinds)?,
                    // `.undef`: the explicit motive is missing; treated as
                    // implicit so `h.rec` works (`App.lean:1301-1305`).
                    NextArg::None | NextArg::Undef => {
                        self.mk_implicit_arg(binder_type, binder_info)?
                    }
                };
                self.motive = Some(m);
                m
            } else if self.info.majors_pos.contains(&self.idx) {
                match self.get_next_arg(binder_name, binder_info) {
                    NextArg::Some(a) => self.elab_arg(a, binder_type, kinds)?,
                    NextArg::Undef => return self.finalize(kinds),
                    NextArg::None => self.mk_implicit_arg(binder_type, binder_info)?,
                }
            } else {
                match self.get_next_arg(binder_name, binder_info) {
                    NextArg::Some(Arg::Stx(stx)) => {
                        self.elab.postpone_elab_term(&stx, Some(binder_type))?
                    }
                    NextArg::Some(Arg::AnonCtorTail { node, from }) => {
                        self.elab.postpone_elab_target(
                            &TermTarget::AnonCtorTail { node, from },
                            Some(binder_type),
                        )?
                    }
                    // oracle: `ensureArgType (← get).f val binderType` (`:1315`).
                    NextArg::Some(Arg::Expr(v)) => {
                        let stx = self.stx.clone();
                        ensure_arg_type(self.elab, &stx, self.f, v, binder_type)?
                    }
                    NextArg::Undef => return self.finalize(kinds),
                    NextArg::None => self.mk_implicit_arg(binder_type, binder_info)?,
                }
            };
            // oracle: `addArgAndContinue` → `saveArgInfo arg binderName`
            // (`App.lean:1275-1277`).
            if let (Node::MVar { id: Some(m) }, Some(bn)) = (
                self.elab
                    .mctx
                    .store()
                    .expr_node(Some(self.elab.view.store), arg),
                binder_name,
            ) {
                self.elab.register_mvar_arg_name(leanr_meta::MVarId(m), bn);
            }
            self.idx += 1;
            let base = self.elab.view.store;
            self.f = self
                .elab
                .mctx
                .store_mut()
                .expr_app(Some(base), self.f, arg)
                .map_err(leanr_meta::MetaError::from)?;
            self.f_type = self.elab.mctx.instantiate_beta_rev_range(body, &[arg])?;
        }
    }

    /// oracle: `getNextArg?` (`App.lean:1247-1260`).
    fn get_next_arg(&mut self, binder_name: Option<NameId>, bi: BinderInfo) -> NextArg {
        let user = binder_user_name(self.elab, binder_name);
        if let Some(na) = self.named_args.iter().find(|n| n.name == user).cloned() {
            self.named_args.retain(|n| n.name != user);
            return NextArg::Some(na.val);
        }
        if bi == BinderInfo::Default {
            if self.args.is_empty() {
                NextArg::Undef
            } else {
                NextArg::Some(self.args.remove(0))
            }
        } else {
            NextArg::None
        }
    }

    /// oracle: `elabArg` (`App.lean:1267-1272`): the RAW binder type, no
    /// `consumeTypeAnnotations` (unlike `AppElab::get_arg_expected_type`).
    fn elab_arg(
        &mut self,
        arg: Arg,
        expected: ExprId,
        kinds: &KindInterner,
    ) -> Result<ExprId, ElabError> {
        match arg {
            Arg::Expr(v) => {
                let stx = self.stx.clone();
                ensure_arg_type(self.elab, &stx, self.f, v, expected)
            }
            Arg::Stx(stx) => {
                let v = self.elab.elab_term(&stx, kinds, Some(expected))?;
                ensure_arg_type(self.elab, &stx, self.f, v, expected)
            }
            Arg::AnonCtorTail { node, from } => {
                let r = NodeOrToken::Node(node.clone());
                let v = self.elab.elab_target(
                    &TermTarget::AnonCtorTail { node, from },
                    kinds,
                    Some(expected),
                )?;
                ensure_arg_type(self.elab, &r, self.f, v, expected)
            }
        }
    }

    /// oracle: `mkImplicitArg` (`App.lean:1280-1284`).
    fn mk_implicit_arg(&mut self, ty: ExprId, bi: BinderInfo) -> Result<ExprId, ElabError> {
        let inst = bi == BinderInfo::InstImplicit;
        let kind = if inst {
            MVarKind::Synthetic
        } else {
            MVarKind::Natural
        };
        let (e, id) = self.elab.mk_fresh_expr_mvar_of_kind(ty, kind)?;
        if inst {
            self.inst_mvars.push(id);
        }
        Ok(e)
    }
}

impl ElimElab<'_, '_> {
    /// oracle: `finalize` (`App.lean:1196-1240`).
    fn finalize(mut self, kinds: &KindInterner) -> Result<ExprId, ElabError> {
        if !self.named_args.is_empty() {
            let names = self.named_args.iter().map(|n| n.name.clone()).collect();
            return Err(ElabError::Eliminator {
                reason: R::UnusedNamedArgs(names),
            });
        }
        let Some(motive) = self.motive else {
            return Err(ElabError::Eliminator {
                reason: R::InsufficientArgs,
            });
        };
        // oracle: `forallTelescope`. The fvars are scoped to it.
        let cp = self.elab.mctx.lctx_checkpoint();
        let r = self.finalize_in_telescope(motive, kinds);
        self.elab.mctx.lctx_restore(cp);
        r
    }

    fn finalize_in_telescope(
        &mut self,
        motive: ExprId,
        kinds: &KindInterner,
    ) -> Result<ExprId, ElabError> {
        let (binders, f_type) = open_forall_telescope(self.elab, self.f_type)?;
        let xs: Vec<ExprId> = binders.iter().map(|b| b.fvar).collect();
        let insufficient = || ElabError::Eliminator {
            reason: R::InsufficientArgsExpectedType,
        };
        let mut expected = self.expected;
        let mut f = self.f;
        if !xs.is_empty() {
            // Under-application: specialize the expected type by `xs`.
            for &x in &xs {
                let w = self.elab.mctx.whnf(expected)?;
                let Node::Forall {
                    binder_type: t,
                    body: b,
                    ..
                } = lval::node(self.elab, w)
                else {
                    return Err(insufficient());
                };
                let x_ty = self.elab.mctx.infer_type(x)?;
                if !self
                    .elab
                    .mctx
                    .with_full_approx_def_eq(|m| m.is_def_eq(t, x_ty))?
                {
                    return Err(insufficient());
                }
                expected = self.elab.mctx.instantiate1(b, x)?;
            }
        } else {
            // Over-application (or exact): "revert" the remaining arguments.
            (f, expected) = self.revert_args(f, expected, kinds)?;
            if !self.elab.mctx.is_type_correct(expected)? {
                return Err(ElabError::Eliminator {
                    reason: R::OverAppTypeIncorrect,
                });
            }
        }
        let result = mk_app_n(self.elab, f, &xs)?;
        if lval::app_fn(self.elab, f_type) != motive {
            return Err(ElabError::Eliminator {
                reason: R::MotiveNotHead,
            });
        }
        let discrs = lval::app_args(self.elab, f_type);
        let motive_val = self.mk_motive(&discrs, expected)?;
        if !self.elab.mctx.is_type_correct(motive_val)? {
            return Err(ElabError::Eliminator {
                reason: R::MotiveNotTypeCorrect,
            });
        }
        if !self.elab.mctx.is_def_eq(motive, motive_val)? {
            return Err(ElabError::Eliminator {
                reason: R::InvalidMotive,
            });
        }
        let inst = std::mem::take(&mut self.inst_mvars);
        let stx = self.stx.clone();
        self.elab.synthesize_app_inst_mvars_of(inst, result, &stx)?;
        let result = self.elab.mctx.instantiate_mvars(result)?;
        Ok(self.elab.mctx.mk_lambda(&xs, result)?)
    }

    /// oracle: `revertArgs` (`App.lean:1179-1190`). `foldrM`: the
    /// arguments are ELABORATED right to left.
    fn revert_args(
        &mut self,
        f: ExprId,
        expected: ExprId,
        kinds: &KindInterner,
    ) -> Result<(ExprId, ExprId), ElabError> {
        let args = std::mem::take(&mut self.args);
        let mut vals = Vec::with_capacity(args.len());
        let mut expected = expected;
        for arg in args.into_iter().rev() {
            let val = match arg {
                Arg::Expr(v) => v,
                Arg::Stx(stx) => self.elab.elab_term(&stx, kinds, None)?,
                Arg::AnonCtorTail { node, from } => {
                    self.elab
                        .elab_target(&TermTarget::AnonCtorTail { node, from }, kinds, None)?
                }
            };
            let val = self.elab.mctx.instantiate_mvars(val)?;
            let body = self.elab.mctx.kabstract(expected, val)?;
            let ty = self.elab.mctx.infer_type(val)?;
            let ty = self.elab.mctx.instantiate_mvars(ty)?;
            let ty = self.elab.mctx.transform_used_let_only(ty)?;
            let name = self.elab.mk_fresh_binder_name()?;
            let base = self.elab.view.store;
            expected = self
                .elab
                .mctx
                .store_mut()
                .expr_forall(Some(base), Some(name), ty, body, BinderInfo::Default)
                .map_err(leanr_meta::MetaError::from)?;
            vals.push(val);
        }
        vals.reverse();
        Ok((mk_app_n(self.elab, f, &vals)?, expected))
    }

    /// oracle: `mkMotive` (`App.lean:1167-1173`), `foldrM` from the right.
    fn mk_motive(&mut self, discrs: &[ExprId], expected: ExprId) -> Result<ExprId, ElabError> {
        let mut motive = expected;
        for &discr in discrs.iter().rev() {
            let discr = self.elab.mctx.instantiate_mvars(discr)?;
            let body = self.elab.mctx.kabstract(motive, discr)?;
            let ty = self.elab.mctx.infer_type(discr)?;
            let ty = self.elab.mctx.instantiate_mvars(ty)?;
            let ty = self.elab.mctx.transform_used_let_only(ty)?;
            let name = self.elab.mk_fresh_binder_name()?;
            let base = self.elab.view.store;
            motive = self
                .elab
                .mctx
                .store_mut()
                .expr_lam(Some(base), Some(name), ty, body, BinderInfo::Default)
                .map_err(leanr_meta::MetaError::from)?;
        }
        Ok(motive)
    }
}

/// `mkAppN f args`.
fn mk_app_n(elab: &mut TermElabM<'_>, f: ExprId, args: &[ExprId]) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    let mut r = f;
    for &a in args {
        r = elab
            .mctx
            .store_mut()
            .expr_app(Some(base), r, a)
            .map_err(leanr_meta::MetaError::from)?;
    }
    Ok(r)
}
