//! `TermElabM`: the leaf-term elaborator's own state, layered directly
//! over `leanr_meta::MetaCtx`. Independent of any single parse — the
//! `KindInterner` is passed to `elab_term`, never stored, so one
//! `TermElabM` can elaborate nodes drawn from different snapshots.

use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::{EnvView, Nat};
use leanr_meta::{LMVarId, MetaCtx};
use leanr_syntax::kind::KindInterner;

use crate::dispatch::{self, SynElem};
use crate::error::ElabError;

pub struct TermElabM<'e> {
    pub mctx: MetaCtx<'e>,
    /// The environment view `mctx` was itself built over, held a second
    /// time here: `MetaCtx::view` is `pub(crate)` to `leanr_meta` (no
    /// accessor — `grep -rn "pub fn " crates/leanr_meta/src/metactx.rs`
    /// confirms it), so `resolve_global` (design spec's named-seam
    /// global-constant resolution, `resolve.rs`) has no way to reach a
    /// `&EnvView` through `mctx` at all. `EnvView<'e>` is `Copy`
    /// (`tc.rs`'s own derive), so the caller's `view` local — already
    /// constructed one line before `MetaCtx::new(view, ..)` in every
    /// call site (`oracle_elab.rs`'s own shape) — is still valid to pass
    /// here too; storing an independent copy costs nothing and needs no
    /// `leanr_meta` change (the "do not modify leanr_meta/src" scope
    /// boundary this task was given).
    pub view: EnvView<'e>,
    /// Universe parameters in scope, for `Sort u`. Empty for closed leaf
    /// terms; the field exists because `sort` reads it.
    pub level_names: Vec<NameId>,
    /// Monotone counter backing `mk_fresh_level_mvar`, this crate's own
    /// "fixed prefix + counter" name generator (mirroring
    /// `leanr_meta::MetaCtx`'s own `level_mvar_gen`, which this crate
    /// cannot reach — it is `pub(crate)` to `leanr_meta`). A distinct
    /// prefix (`_leanr_elab_lvl_fresh`, below) keeps this counter's
    /// names from ever colliding with `leanr_meta`'s internal fresh
    /// mvars, even though both mint into the same scratch `Store`.
    level_mvar_gen: u64,
}

impl<'e> TermElabM<'e> {
    pub fn new(mctx: MetaCtx<'e>, view: EnvView<'e>) -> Self {
        TermElabM {
            mctx,
            view,
            level_names: Vec::new(),
            level_mvar_gen: 0,
        }
    }

    /// oracle: `mkFreshLevelMVar` (`Lean/Meta/Basic.lean:861-863`) —
    /// mints a globally-fresh `LMVarId`, declares it in the `mctx`, and
    /// returns the `LevelId` of `Level.mvar` referencing it. One fresh
    /// mvar per universe parameter is exactly what `elab_ident` needs
    /// for `mkConst` (design spec's "Universe metavariables in the
    /// output"). Reachable capability surface is entirely public
    /// (`MetaCtx::store_mut`/`mctx_mut`, `MetavarContext::declare_level`,
    /// `Store::level_mvar`) — no `leanr_meta` change needed; this is a
    /// standalone transcription of `leanr_meta::level::fresh_level_mvar`
    /// (which is `pub(crate)` there, so unreachable from here), not a
    /// call to it.
    pub fn mk_fresh_level_mvar(&mut self) -> Result<LevelId, ElabError> {
        let idx = self.level_mvar_gen;
        self.level_mvar_gen += 1;
        // `Store`'s own methods return `KernelError`, which has no
        // direct `ElabError` conversion (only `MetaError` does, via
        // `ElabError::from(MetaError)`) — route each through
        // `MetaError::from` so `?` reuses that existing impl rather
        // than adding a second `From<KernelError>` to `error.rs`
        // (outside this task's file scope).
        let store = self.mctx.store_mut();
        let prefix_str = store
            .intern_str(None, "_leanr_elab_lvl_fresh")
            .map_err(leanr_meta::MetaError::from)?;
        let prefix = store
            .name_str(None, None, prefix_str)
            .map_err(leanr_meta::MetaError::from)?;
        let idx_id = store
            .intern_nat(None, &Nat::from(idx))
            .map_err(leanr_meta::MetaError::from)?;
        let name = store
            .name_num(None, Some(prefix), idx_id)
            .map_err(leanr_meta::MetaError::from)?;
        let id = LMVarId(name);
        self.mctx.mctx_mut().declare_level(id);
        let level_id = self
            .mctx
            .store_mut()
            .level_mvar(None, Some(name))
            .map_err(leanr_meta::MetaError::from)?;
        Ok(level_id)
    }

    pub fn elab_term(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        dispatch::dispatch(self, elem, kinds, expected)
    }

    pub fn elab_term_ensuring_type(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        let e = self.elab_term(elem, kinds, expected)?;
        if let Some(t) = expected {
            let inferred = self.mctx.infer_type(e)?;
            if !self.mctx.is_def_eq(inferred, t)? {
                return Err(ElabError::TypeMismatch {
                    expected: t,
                    got: inferred,
                });
            }
        }
        Ok(e)
    }
}
