//! One attribute row per local declaration.
//!
//! `MetaCtx::local_names` has always been exactly one entry per
//! `push_local_decl`/`push_let_decl` call, asserted in lockstep with
//! `lctx.decls` at every push, checkpoint, restore and install. This is
//! that row, widened to carry what leanr's `LocalDecl` cannot.
//!
//! **Why not on `LocalDecl`.** `leanr_kernel::local_ctx` ports the C++
//! kernel's `local_ctx.h`, which has neither bit — `nondep` and
//! `LocalDeclKind` are `Lean.LocalDecl` (elaborator) concepts
//! (`Lean/LocalContext.lean:23`, `:55-86`). The kernel does read let
//! values during whnf (`tc.rs:1385`, `:1544`), so fields there would be
//! inert, and an inert TCB field invites a future kernel reader.
//!
//! **Why not a second sparse table.** `local_instance.rs` is sparse
//! because only class-typed declarations produce an entry; its
//! truncate-by-recorded-depth rule is the subtlety that file exists to
//! contain. These bits are dense: every declaration has a kind, every
//! ldecl a `nondep`. Dense data belongs in the row that is already
//! dense and already positional.

use leanr_kernel::bank::{ExprId, NameId};

use crate::LocalDeclKind;

/// The attributes of one local declaration, positionally parallel to
/// `LocalContext`'s own decl list.
///
/// `nondep` readers: against the AMBIENT context, through
/// `MetaCtx::local_entry`, `whnf`'s zeta-delta, `assign.rs`'s
/// `simp_assignment_arg_aux` and `mk_lambda_fvars_with_let_deps`, and
/// `check_assignment.rs`'s `check_assignment_scope_body` and
/// `ca_check_fvar`; against a metavariable's OWN context,
/// through `LocalCtxSnapshot::entry`, `collect_forward_deps`,
/// `mk_mvar_app` and `mk_aux_mvar_type_with` (`mk_binding.rs`).
#[derive(Clone)]
pub(crate) struct LocalEntry {
    /// The `Expr::fvar` `push_local_decl` returned.
    pub fvar: ExprId,
    /// The user-facing binder name, `None` for an anonymous binder.
    /// Read by `lctx_lookup_by_name`.
    pub name: Option<NameId>,
    /// The declaration's fvar id. Stored so a lookup compares by
    /// `NameId` — the basis `LocalCtxSnapshot::reduced` already argues
    /// for over `ExprId` — without a `Store` decode per read.
    pub id: NameId,
    /// oracle: `LocalDecl.ldecl (nondep := …)`. `true` for a `have`,
    /// `false` for a `let` and for every cdecl. A nondep ldecl is
    /// "locally a cdecl": its value is invisible to zeta-delta
    /// (`WHNF.lean:397-409`), to `getValue?` (`Meta/Basic.lean:1044`,
    /// `allowNondep := false`) and to `isLet`
    /// (`LocalContext.lean:106-109`).
    pub nondep: bool,
    /// oracle: `LocalDecl`'s `kind` field. Consumed by
    /// `install_local_instance_for`, and by `withLocalInstances` when
    /// the match slice ports it.
    pub kind: LocalDeclKind,
}
