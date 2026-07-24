//! `TermElabM`: the leaf-term elaborator's own state, layered directly
//! over `leanr_meta::MetaCtx`. Independent of any single parse — the
//! `KindInterner` is passed to `elab_term`, never stored, so one
//! `TermElabM` can elaborate nodes drawn from different snapshots.

use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::{EnvView, LocalContext, Nat};
use leanr_meta::{LMVarId, MVarDecl, MVarId, MVarKind, MetaCtx};
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
    /// Monotone counter backing `mk_fresh_expr_mvar` (Task 6) — the
    /// same "fixed prefix + counter" idiom as `level_mvar_gen`, but a
    /// SEPARATE counter and a DISTINCT prefix
    /// (`_leanr_elab_expr_fresh`, below) so an expr-mvar name can never
    /// collide with a level-mvar name even at the same counter value.
    expr_mvar_gen: u64,
}

impl<'e> TermElabM<'e> {
    pub fn new(mctx: MetaCtx<'e>, view: EnvView<'e>) -> Self {
        TermElabM {
            mctx,
            view,
            level_names: Vec::new(),
            level_mvar_gen: 0,
            expr_mvar_gen: 0,
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
    ///
    /// `base = Some(self.view.store)` throughout (M4b-2 task 2 fix,
    /// bound before `store_mut()` — the same disjoint-field-borrow
    /// convention `ident.rs` uses): NOT the self-contained-scratch
    /// `base = None` `mk_fresh_expr_mvar` uses below. A fresh level
    /// mvar's `Sort ?u` is fed into `elab_term_ensuring_type`
    /// (`binder::elab_type`, M4b-2), whose `is_def_eq` — on a Sort-vs-Sort
    /// compare — round-trips the mvar's `LevelId` through
    /// `level.rs::level_normalize` (`to_level` then `intern_level`),
    /// ALWAYS with `base = Some(view.store)` (that module's own fixed
    /// convention, never `None`). `intern_nat`'s `base`-first dedup
    /// lookup means interning the SAME small index (e.g. `0`) once
    /// under `base = None` and once under `base = Some(persistent)` can
    /// resolve to two DIFFERENT `NatId`s — the persistent store already
    /// has small `Nat`s interned, so the `base = Some` call finds
    /// persistent's row while a `base = None` call would have kept the
    /// original scratch row — which in turn mints a genuinely different
    /// `NameId` for the "same" mvar name on the round trip, so the
    /// later `assign_level` targets an id that was never `declare_level`-d
    /// (confirmed empirically: this was `elab_arrow`'s exact RED-phase
    /// failure, `assign_level: level metavariable .. was never
    /// declared`, traced to this mismatch, not to `binder.rs` itself).
    /// Minting under `base = Some(view.store)` from the start — matching
    /// `level.rs::fresh_level_mvar`'s own convention exactly — makes the
    /// mint and every later re-intern agree on the same persistent-backed
    /// ids, closing the gap.
    pub fn mk_fresh_level_mvar(&mut self) -> Result<LevelId, ElabError> {
        let idx = self.level_mvar_gen;
        self.level_mvar_gen += 1;
        // `Store`'s own methods return `KernelError`, which has no
        // direct `ElabError` conversion (only `MetaError` does, via
        // `ElabError::from(MetaError)`) — route each through
        // `MetaError::from` so `?` reuses that existing impl rather
        // than adding a second `From<KernelError>` to `error.rs`
        // (outside this task's file scope).
        let base = self.view.store;
        let store = self.mctx.store_mut();
        let prefix_str = store
            .intern_str(Some(base), "_leanr_elab_lvl_fresh")
            .map_err(leanr_meta::MetaError::from)?;
        let prefix = store
            .name_str(Some(base), None, prefix_str)
            .map_err(leanr_meta::MetaError::from)?;
        let idx_id = store
            .intern_nat(Some(base), &Nat::from(idx))
            .map_err(leanr_meta::MetaError::from)?;
        let name = store
            .name_num(Some(base), Some(prefix), idx_id)
            .map_err(leanr_meta::MetaError::from)?;
        let id = LMVarId(name);
        self.mctx.mctx_mut().declare_level(id);
        let level_id = self
            .mctx
            .store_mut()
            .level_mvar(Some(base), Some(name))
            .map_err(leanr_meta::MetaError::from)?;
        Ok(level_id)
    }

    /// oracle: `mkFreshExprMVarCore`/`mkFreshMVarId`
    /// (`Lean/Meta/Basic.lean:864-877`) — mints a globally-fresh
    /// `MVarId` (own `expr_mvar_gen` counter, mirroring
    /// `mk_fresh_level_mvar`'s `level_mvar_gen` exactly), `declare`s it
    /// in `mctx` with an EMPTY `LocalContext` — slice 1 elaborates no
    /// binder/lambda/pi, so no leaf elaborator ever runs under a
    /// nonempty local context; `LocalContext::default()` is the correct
    /// context here, not a placeholder — and `MVarKind::Natural` (see
    /// `builtin::hole`'s own doc for why every hole is minted `Natural`
    /// rather than replicating `elabHole`'s `Natural`/`SyntheticOpaque`
    /// branch), and returns the `ExprId` of `Expr.mvar` referencing it.
    /// `base = None` throughout — unlike `mk_fresh_level_mvar` (M4b-2
    /// task 2 fix, see its own doc comment for why THAT one now needs
    /// `base = Some(view.store)`): every id minted here (prefix string,
    /// the mvar's own synthetic name, the `Expr.mvar` row) is
    /// self-contained fresh scratch data with nothing in the PERSISTENT
    /// store to dedup against, and — the part that actually matters —
    /// nothing in this crate re-interns an expr mvar's own synthetic
    /// name through a `base = Some(persistent)` path the way
    /// `level.rs::level_normalize` does for level mvars, so there is no
    /// analogous round-trip mismatch to guard against here. `ty` itself
    /// (the caller-supplied type, possibly persistent-region) is stored
    /// VERBATIM in `MVarDecl::ty`, never re-interned, so it needs no
    /// `base` here either.
    pub fn mk_fresh_expr_mvar(&mut self, ty: ExprId) -> Result<ExprId, ElabError> {
        let idx = self.expr_mvar_gen;
        self.expr_mvar_gen += 1;
        let store = self.mctx.store_mut();
        let prefix_str = store
            .intern_str(None, "_leanr_elab_expr_fresh")
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
        let id = MVarId(name);
        self.mctx.mctx_mut().declare(
            id,
            MVarDecl {
                user_name: None,
                ty,
                lctx: LocalContext::default(),
                kind: MVarKind::Natural,
            },
        );
        let mvar_id = self
            .mctx
            .store_mut()
            .expr_mvar(None, Some(name))
            .map_err(leanr_meta::MetaError::from)?;
        Ok(mvar_id)
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
