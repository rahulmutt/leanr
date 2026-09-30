//! The anonymous constructor `⟨…⟩`. Oracle: `elabAnonymousCtor`
//! (`Lean/Elab/BuiltinNotation.lean:43-102`). Design spec:
//! `docs/superpowers/specs/2026-09-30-m4b4b-anonymous-constructor-design.md`.
//!
//! The oracle builds new syntax — `$(mkCIdentFrom stx ctor (canonical :=
//! true)) $(args)*` — and elaborates it. leanr calls the application
//! elaborator on the constructor directly: `mkCIdentFrom` carries a
//! reserved macro scope and `[.decl ctor []]` (`Init/Meta/Defs.lean:736-739`),
//! so `resolveName`'s `resolveLocalName` (`TermElabM.lean:2180`) can never
//! capture it and the preresolved decl becomes `mkConst` with fresh level
//! mvars — `mk_const(ctor, &[])`. `withMacroExpansion` (`:97`) has no
//! counterpart: leanr has no macro stack.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{BinderInfo, ConstantInfo};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::app::expand::Arg;
use crate::app::head::mk_const;
use crate::app::lval::{app_fn, node as expr_node, render};
use crate::app::AppCall;
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::{AnonCtorError, ElabError};

/// The term arguments of an `anonymousCtor` node, `,` separators
/// dropped. Shape: `⟨` atom, a `null` node holding `arg (, arg)*`, `⟩`
/// atom (confirmed by `anon_ctor_smoke.rs`'s shape probe).
pub(crate) fn anon_ctor_args(
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<Vec<SynElem>, ElabError> {
    let children = non_trivia_children(node);
    let list = match children.as_slice() {
        [_, NodeOrToken::Node(list), _] => list.clone(),
        _ => {
            return Err(ElabError::IllFormedSyntax(format!(
                "anonymousCtor: expected `⟨`, an argument list and `⟩`, got {} children",
                children.len()
            )))
        }
    };
    Ok(non_trivia_children(&list)
        .into_iter()
        .filter(|el| {
            !(kinds.name(el.kind()) == "<atom>" && el.as_token().is_some_and(|t| t.text() == ","))
        })
        .collect())
}

/// oracle: `elabAnonymousCtor` (`BuiltinNotation.lean:43-102`), over
/// `args[from..]` of `node`. `from` is 0 for a real `⟨…⟩`; the flatten
/// tail (Task 2) re-enters with a later start on the SAME node, which is
/// the oracle's recursion through its synthesized `⟨$[$extra],*⟩`.
pub(crate) fn elab_anon_ctor(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    from: usize,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let all = anon_ctor_args(node, kinds)?;
    let Some(args) = all.get(from..) else {
        return Err(ElabError::Internal(format!(
            "anonymousCtor tail starts at {from}, past its {} arguments",
            all.len()
        )));
    };
    let unknown = || ElabError::InvalidAnonymousCtor(AnonCtorError::ExpectedTypeUnknown);
    // `:46`.
    elab.try_postpone_if_none_or_mvar(expected)?;
    // `:101`.
    let Some(expected) = expected else {
        return Err(unknown());
    };
    // `:53-54`: default-transparency `whnf`; an mvar head is a hard
    // error here, not a second postponement.
    let ty = elab.mctx.whnf(expected)?;
    let head = expr_node(elab, app_fn(elab, ty));
    if matches!(head, Node::MVar { .. }) {
        return Err(unknown());
    }
    // `:55-57`: `matchConstInduct`.
    let ctors = match head {
        Node::Const { name: Some(c), .. } => match elab.view.get(c) {
            Some(ConstantInfo::Induct(ind)) => Some(ind.ctors.clone()),
            _ => None,
        },
        _ => None,
    };
    let Some(ctors) = ctors else {
        return Err(ElabError::InvalidAnonymousCtor(
            AnonCtorError::NotInductive { ty },
        ));
    };
    // `:59`, `:98-99`.
    let ctor = match ctors.as_slice() {
        [c] => *c,
        [] => {
            return Err(ElabError::InvalidAnonymousCtor(AnonCtorError::NoCtors {
                ty,
            }))
        }
        _ => {
            return Err(ElabError::InvalidAnonymousCtor(
                AnonCtorError::MultipleCtors { ty },
            ))
        }
    };
    let ctor_name = render(elab, ctor);
    // `:61-62` `isInaccessiblePrivateName`: leanr models no private
    // names (the same seam as `app/lval.rs` and `app/dot_ident.rs`).
    if ctor_name.starts_with("_private.") {
        return Err(ElabError::UnsupportedSyntax(format!(
            "`⟨…⟩` with the private constructor `{ctor_name}` (`isInaccessiblePrivateName`, \
             BuiltinNotation.lean:61) — the slice that models private names"
        )));
    }
    // `:63` `getConstInfoCtor`.
    let ctor_info = match elab.view.get(ctor) {
        Some(ConstantInfo::Ctor(c)) => c.num_params.to_usize().map(|p| (c.val.ty, p)),
        _ => None,
    };
    let Some((ctor_ty, num_params)) = ctor_info else {
        return Err(ElabError::Internal(format!(
            "`{ctor_name}` is not a constructor with a machine-sized `numParams` \
             (getConstInfoCtor, BuiltinNotation.lean:63)"
        )));
    };
    // `:64-69`.
    let k = num_explicit_fields(elab, ctor_ty, num_params)?;
    let n = args.len();
    // `:71-96`, in the oracle's order.
    let app_args: Vec<Arg> = if n < k {
        return Err(ElabError::InvalidAnonymousCtor(
            AnonCtorError::InsufficientFields {
                ctor: ctor_name,
                explicit: k,
                provided: n,
            },
        ));
    } else if n == k {
        args.iter().cloned().map(Arg::Stx).collect()
    } else if k == 0 {
        return Err(ElabError::InvalidAnonymousCtor(
            AnonCtorError::NoExplicitFields {
                ctor: ctor_name,
                provided: n,
            },
        ));
    } else {
        return Err(ElabError::UnsupportedSyntax(
            "`⟨…⟩` with more arguments than explicit fields (flattening) — M4b-4b task 2"
                .to_string(),
        ));
    };
    // `:97`: `elabTerm newStx expectedType?` — the ORIGINAL expected
    // type, not its `whnf`.
    let f = mk_const(elab, ctor, &[], &ctor_name)?;
    crate::app::elab_app_args(
        elab,
        f,
        AppCall {
            named_args: Vec::new(),
            args: app_args,
            expected: Some(expected),
            explicit: false,
            ellipsis: false,
            stx: NodeOrToken::Node(node.clone()),
        },
        kinds,
    )
}

/// oracle: `:64-69` — `forallTelescopeReducing cinfo.type`, counting the
/// explicit (`BinderInfo::Default`) binders at positions
/// `numParams..`. The walk is `AppElab::forall_telescope_reducing`'s
/// (`app/state.rs`), inlined because there is no `AppElab` here; the
/// ambient `lctx` is restored on every exit path.
fn num_explicit_fields(
    elab: &mut TermElabM,
    ctor_ty: ExprId,
    num_params: usize,
) -> Result<usize, ElabError> {
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let mut count = 0;
        let mut i = 0;
        let mut cur = ctor_ty;
        loop {
            let reduced = if matches!(expr_node(elab, cur), Node::Forall { .. }) {
                cur
            } else {
                elab.mctx.whnf(cur)?
            };
            let Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = expr_node(elab, reduced)
            else {
                break;
            };
            if i >= num_params && binder_info == BinderInfo::Default {
                count += 1;
            }
            let fvar = elab
                .mctx
                .push_local_decl(binder_name, binder_type, binder_info)?;
            cur = elab.mctx.instantiate_beta_rev_range(body, &[fvar])?;
            i += 1;
        }
        Ok(count)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}
