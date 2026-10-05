//! `#[cfg(test)]` helpers for `src/` unit tests that need a real
//! environment: the committed `Elab0.olean`, replayed through
//! `leanr_meta`'s canonical test support (ONE source of truth, the same
//! file `tests/support/mod.rs` includes), plus the builtin-grammar term
//! parser.

use std::ops::Deref;
use std::sync::Arc;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, Store};
use leanr_kernel::EnvView;
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::kind::KindInterner;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;

#[path = "../../leanr_meta/tests/support/mod.rs"]
mod meta_support;

/// The builtin grammar and its kind table. Derefs to the
/// [`KindInterner`] the elaborator takes, so `kinds` passes straight to
/// `elab_term`/`elab_type`.
pub(crate) struct Kinds {
    snap: GrammarSnapshot,
    kinds: Arc<KindInterner>,
}

impl Deref for Kinds {
    type Target = KindInterner;
    fn deref(&self) -> &KindInterner {
        &self.kinds
    }
}

/// Replay `Elab0` and hand `k` a fresh `TermElabM` over it plus the
/// builtin grammar's kinds (`tests/support`'s `with_elab_env`, in-crate).
pub(crate) fn with_elab0<R>(k: impl FnOnce(&mut TermElabM, &Kinds) -> R) -> R {
    let meta_support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
        aux_recs,
        elab_as_elim,
        structures,
        ..
    } = meta_support::replay_fixture_in("elab", "Elab0.olean");
    let view: EnvView = env.view();
    let mut scratch = Store::scratch();
    let mctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            reducibility: &reducibility,
            matchers: &matchers,
            instances: &instances,
            default_instances: &default_instances,
            projection_fns: &projection_fns,
            classes: &classes,
            coe_decls: &coe_decls,
            aux_recs: &aux_recs,
            elab_as_elim: &elab_as_elim,
            structures: &structures,
        },
    );
    let mut elab = TermElabM::new(mctx, view);
    let snap = leanr_syntax::builtin::snapshot();
    let kinds = Kinds {
        kinds: snap.kinds(),
        snap,
    };
    k(&mut elab, &kinds)
}

/// Parse `src` as a term with the builtin grammar; its syntax element.
/// Panics on a parse error, or if the parse needed kinds outside the
/// grammar's own table (then `kinds` could not elaborate it).
pub(crate) fn parse_term(kinds: &Kinds, src: &str) -> SynElem {
    let parsed = leanr_syntax::parse_term(src, &kinds.snap);
    assert!(
        parsed.errors.is_empty(),
        "parse_term: {src:?}: {:?}",
        parsed.errors
    );
    assert!(
        Arc::ptr_eq(&parsed.tree.kinds, &kinds.kinds),
        "parse_term: {src:?} grew the kind table"
    );
    parsed
        .tree
        .root()
        .first_child_or_token()
        .unwrap_or_else(|| panic!("parse_term: no term child for {src:?}"))
}

/// The current local context's declaration of fvar `x`, if any.
pub(crate) fn local_decl_of(elab: &mut TermElabM, x: ExprId) -> Option<leanr_kernel::LocalDecl> {
    let Node::FVar { id: Some(id) } = elab.mctx.store().expr_node(Some(elab.view.store), x) else {
        return None;
    };
    elab.mctx.current_lctx().lctx().get(id).cloned()
}
