//! M4b-4c P2: eliminator elaboration. Oracle: `Lean/Elab/App.lean`,
//! `shouldElabAsElim` (`:1322-1328`), `elabAppArgs.elabAsElim?`
//! (`:1397-1431`) and the `ElabElim` namespace (`:1140-1319`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;

use crate::app::elim_info::{get_elab_elim_info, ElabElimInfo};
use crate::app::expand::{Arg, NamedArg};
use crate::app::lval;
use crate::app::state::open_forall_telescope_reducing;
use crate::elab::TermElabM;
use crate::error::ElabError;

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
    let Some(pre) = xs.get(..info.motive_pos) else {
        // oracle: `unreachable!` (`:1415`); `.olean` input is untrusted.
        return Err(ElabError::Internal(
            "elabAsElim?: motivePos past the telescope".into(),
        ));
    };
    for x in pre {
        let user = binder_user_name(elab, x.name);
        if named.contains(&user.as_str()) {
            named.retain(|n| *n != user);
        } else if x.bi == BinderInfo::Default {
            args = args.get(1..).unwrap_or(&[]);
        }
    }
    let x = &xs[info.motive_pos];
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
