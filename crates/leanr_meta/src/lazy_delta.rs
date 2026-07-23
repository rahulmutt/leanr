//! Lazy delta reduction (`isDefEqDelta` + `tryHeuristic`) and the rest
//! of the expensive `is_def_eq` ladder that needs reduction: eta,
//! structure eta, projection (+ its own lazy-delta variant), proof
//! irrelevance, unit-like structures, and the `Nat`/`String` literal
//! channels.
//!
//! oracle: `Lean/Meta/ExprDefEq.lean`, toolchain
//! leanprover/lean4:v4.33.0-rc1. Every function cites its exact region.
//!
//! # `ReducibilityHints` vs `ReducibilityStatus` — DO NOT CROSS THEM
//!
//! This module reads `ReducibilityHints` (`ConstantInfo::Defn(_).hints`,
//! the kernel's own unfolding-COST metric — `Opaque`/`Abbrev`/
//! `Regular(height)` — already decoded, never gated by transparency) to
//! decide WHICH side of a same-shape pair to unfold first
//! (`hints_lt`/`hints_cmp` below, mirroring `Declaration.lean`'s
//! `ReducibilityHints.lt`/`.compare`, :65-77). `transparency.rs`'s
//! `can_unfold`/`ReducibilityStatus` (`Reducible`/`Semireducible`/
//! `Irreducible`/...) decides WHETHER a constant may unfold AT ALL at
//! the current transparency — a completely different axis. Both are
//! consulted here (`is_delta_candidate` for the latter,
//! `unfold_reducible_def_eq`'s `isReducible` check too), never
//! conflated.
//!
//! # Scope cuts, all named
//!
//! - `tryHeuristic`'s real gate (`isNonTrivialRegular`, :1405-1461, plus
//!   an `isMatcherCore`/has-mvar escape) is NARROWED to "both heads are
//!   the same `Defn` constant with `Regular` hints" — see
//!   [`MetaCtx::try_heuristic`]'s own doc for why this is a sound
//!   superset, never a wrong verdict.
//! - `isDefEqDelta`'s class-projection layer (`unfoldNonProjFnDefEq`,
//!   :1642-1657, needing `getProjectionFnInfo?`) collapses to
//!   `unfoldReducibleDefEq` exactly, because this crate's projection-
//!   function registry is ALWAYS absent (`whnf.rs`'s own
//!   `unfold_proj_inst_when_instances`/`get_stuck_mvar` seams) — see
//!   [`MetaCtx::is_def_eq_delta`]'s doc.
//! - `isDefEqEtaStruct`/`isDefEqUnitLike`'s `useEtaStruct` config gate
//!   (`Config.etaStruct`, unmodeled — `config.rs`'s own doc on why
//!   fields arrive with the feature that consults them) is elided,
//!   always taking the oracle's own default-on branch, matching
//!   `whnf.rs::to_ctor_when_structure`'s established precedent.
//! - `isDefEqProofIrrel`/`isProp`'s `isProofQuick`/`isPropQuick`
//!   approximate fast paths (InferType.lean:315-441) are skipped:
//!   always compute `infer_type` + the full check. Semantically
//!   equivalent (see [`MetaCtx::is_def_eq_proof_irrel`]'s doc), just
//!   without their extra speed.
//! - `isDefEqStringLit`'s only productive direction depends on
//!   `to_ctor_if_lit`'s pre-existing `LitStr` seam (task 5, `whnf.rs`) —
//!   the dispatch below is a complete, correct transcription, but
//!   converges only once that seam's own citation is filled in.
//!
//! # Named seams (never silent `false`)
//!
//! - [`MetaCtx::is_def_eq_offset`] — `isDefEqOffset` (Meta/Offset.lean:
//!   118-144), gated on `Config.offsetCnstrs` (unmodeled). Task 7+.
//! - [`MetaCtx::is_def_eq_native`] — `isDefEqNative` (ExprDefEq.lean:
//!   186-193), compiled-eval support. Permanently out of scope (no
//!   native evaluator in a pure-Rust toolchain).
//! - `isDefEqProjInst`/`isDefEqOnFailure` are cited, not ported, at
//!   their call site in `defeq.rs::is_def_eq_expensive`.

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::{ConstantInfo, DefinitionVal, Nat, ReducibilityHints};
use leanr_olean::ReducibilityStatus;

use crate::{MVarId, MVarKind, MetaCtx, MetaError, TransparencyMode};

/// oracle: `ReducibilityHints.lt` (Declaration.lean:65-71): "if `lt h1
/// h2`, we want to reduce the declaration associated with `h1`" —
/// larger `Regular` depth (further from the primitives) unfolds first.
fn hints_lt(h1: ReducibilityHints, h2: ReducibilityHints) -> bool {
    use ReducibilityHints::{Abbrev, Opaque, Regular};
    match (h1, h2) {
        (Abbrev, Abbrev) => false,
        (Abbrev, _) => true,
        (Regular(d1), Regular(d2)) => d1 > d2,
        (Regular(_), Opaque) => true,
        _ => false,
    }
}

/// oracle: `ReducibilityHints.compare` (Declaration.lean:72-80) — the
/// `Ord` instance `isDefEqDeltaStep` (:2049-2051) and `isDefEqDeltaStep`
/// (proj-delta variant) both switch on.
fn hints_cmp(h1: ReducibilityHints, h2: ReducibilityHints) -> std::cmp::Ordering {
    use std::cmp::Ordering::{Equal, Greater, Less};
    use ReducibilityHints::{Abbrev, Opaque, Regular};
    match (h1, h2) {
        (Abbrev, Abbrev) => Equal,
        (Abbrev, _) => Less,
        (Regular(_), Abbrev) => Greater,
        (Regular(d1), Regular(d2)) => d2.cmp(&d1),
        (Regular(_), Opaque) => Less,
        (Opaque, Opaque) => Equal,
        (Opaque, _) => Greater,
    }
}

/// Result of one `isDefEqDeltaStep` (ExprDefEq.lean:2037-2064, the
/// `DeltaStepResult` inductive at :2030-2034).
enum DeltaStepResult {
    Eq,
    Unknown,
    Cont(ExprId, ExprId),
    Diff(ExprId, ExprId),
}

impl<'e> MetaCtx<'e> {
    // =======================================================================
    // isDefEqProofIrrel
    // =======================================================================

    /// oracle: `isDefEqProofIrrel` (ExprDefEq.lean:1766-1780). The
    /// `isProofQuick`-driven fast path is skipped (module doc): always
    /// compute `infer_type(t)` and test `is_prop` directly, which is
    /// exactly the case `isProofQuick`'s `.undef` arm already falls
    /// through to, so the final verdict is unchanged, only slower —
    /// `isProofQuick t == .true` implies `is_prop(inferType t)` would
    /// also answer `true` (a term can only BE a proof if its inferred
    /// type really is a `Prop`), and `isProofQuick t == .false` implies
    /// `t`'s SHAPE (`Sort`/`Lam`/`Lit`/`Forall`, `isProofQuick`'s own
    /// `false`-shape leaves) can never itself be a proof term either,
    /// so `is_prop(inferType t)` cannot spuriously say `true` for it.
    pub(crate) fn is_def_eq_proof_irrel(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        if !self.cfg.proof_irrelevance {
            return Ok(None);
        }
        let t_ty = self.infer_type(t)?;
        if !self.is_prop(t_ty)? {
            return Ok(None);
        }
        let s_ty = self.infer_type(s)?;
        // oracle: `withProofIrrelTransparency` (:1760-1764), gated on
        // `backward.isDefEq.respectTransparency` (default `true` — no
        // bump). No options table (module doc, `config.rs`'s own
        // posture on unmodeled option-gated behavior): always take the
        // default branch, plain `is_def_eq_core`.
        Ok(Some(self.is_def_eq_core(t_ty, s_ty)?))
    }

    /// oracle: `isProp` (InferType.lean:315-330). `isPropQuick`'s fast
    /// path is skipped for the reason [`MetaCtx::is_def_eq_proof_irrel`]
    /// gives for `isProofQuick`. `isAlwaysZero` (`Level.lean`, over
    /// `max`/`imax`-normalized universe expressions) is narrowed to the
    /// literal `Level::Zero` case only — never wrong (a Prop whose
    /// universe is a non-normalized-but-provably-zero `max`/`imax` is
    /// reported "not Prop" instead, incompleteness only, no fixture
    /// this task commits needs the general case).
    ///
    /// `pub(crate)` (task B2): `discr_path.rs`'s `ignoreArg` transcription
    /// (`isProof e = isProp (inferType e)`, InferType.lean:448-451) reuses
    /// this exact primitive rather than a second copy — same
    /// `whnf_default`-sharing precedent this method's own doc cites.
    pub(crate) fn is_prop(&mut self, e: ExprId) -> Result<bool, MetaError> {
        let ty = self.infer_type(e)?;
        let ty = self.whnf_default(ty)?;
        match self.node(ty) {
            Node::Sort { level } => Ok(self.is_level_literal_zero(level)),
            _ => Ok(false),
        }
    }

    fn is_level_literal_zero(&self, level: LevelId) -> bool {
        matches!(
            *self.scratch.level_row(Some(self.view.store), level),
            LevelRow::Zero
        )
    }

    // =======================================================================
    // isDefEqEta / isDefEqEtaStruct
    // =======================================================================

    /// oracle: `isDefEqEta` (ExprDefEq.lean:161-181). Eta-expands `b`
    /// into `fun (x : d) => b x` when `a` is a lambda and `b` is not,
    /// then recurses. `b` is guaranteed loose-bvar-free at this point
    /// (every binder this crate's ladder ever opens is immediately
    /// substituted by a real fvar — `defeq.rs`'s own module doc), so
    /// `App(b, BVar 0)` needs no index shift.
    pub(crate) fn is_def_eq_eta(
        &mut self,
        a: ExprId,
        b: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        let a_is_lam = matches!(self.node(a), Node::Lam { .. });
        let b_is_lam = matches!(self.node(b), Node::Lam { .. });
        if !a_is_lam || b_is_lam {
            return Ok(None);
        }
        let b_ty = self.infer_type(b)?;
        let b_ty = self.whnf_default(b_ty)?;
        let (binder_name, binder_type, binder_info) = match self.node(b_ty) {
            Node::Forall {
                binder_name,
                binder_type,
                binder_info,
                ..
            } => (binder_name, binder_type, binder_info),
            _ => return Ok(None),
        };
        let bvar0 = self
            .scratch
            .expr_bvar(Some(self.view.store), &Nat::from(0u64))?;
        let applied = self.scratch.expr_app(Some(self.view.store), b, bvar0)?;
        let eta_b = self.scratch.expr_lam(
            Some(self.view.store),
            binder_name,
            binder_type,
            applied,
            binder_info,
        )?;
        Ok(Some(self.is_def_eq_core(a, eta_b)?))
    }

    /// oracle: `isDefEqEtaStruct` (ExprDefEq.lean:129-163). `useEtaStruct`
    /// (:131) elided (module doc, always on). The `isProof`/
    /// `isAbstractedUnassignedMVar` skip inside the field loop (:141-148)
    /// is a pure performance optimization — omitted: every field
    /// compared via `is_def_eq_core` unconditionally, same verdict.
    pub(crate) fn is_def_eq_eta_struct(&mut self, a: ExprId, b: ExprId) -> Result<bool, MetaError> {
        let b_fn = self.get_app_fn(b);
        let ctor_name = match self.node(b_fn) {
            Node::Const { name: Some(n), .. } => n,
            _ => return Ok(false),
        };
        let ctor_val = match self.view.get(ctor_name) {
            Some(ConstantInfo::Ctor(v)) => v,
            _ => return Ok(false),
        };
        // matchConstCtor a.getAppFn (fun _ => go ..) fun _ _ => false —
        // `a` already being a ctor app takes the FAILURE verdict here.
        if self.is_constructor_app(a) {
            return Ok(false);
        }
        let nparams = match ctor_val.num_params.to_usize() {
            Some(v) => v,
            None => return Ok(false),
        };
        let nfields = match ctor_val.num_fields.to_usize() {
            Some(v) => v,
            None => return Ok(false),
        };
        let b_args = self.get_app_args(b);
        if nparams + nfields != b_args.len() {
            return Ok(false);
        }
        if !self.view.is_structure_like(ctor_val.induct) {
            return Ok(false);
        }
        let a_ty = self.infer_type(a)?;
        let b_ty = self.infer_type(b)?;
        // oracle calls the checkpointing top-level `isDefEq` here; this
        // crate's convention (see `defeq.rs::is_def_eq_core`'s own doc
        // on `assign.rs::check_types_and_assign`) is `is_def_eq_core`
        // from a nested position, avoiding a double checkpoint.
        if !self.is_def_eq_core(a_ty, b_ty)? {
            return Ok(false);
        }
        let induct = ctor_val.induct;
        let snap = self.checkpoint();
        for j in 0..nfields {
            let proj = self.scratch.expr_proj(
                Some(self.view.store),
                Some(induct),
                &Nat::from(j as u64),
                a,
            )?;
            if !self.is_def_eq_core(proj, b_args[nparams + j])? {
                self.rollback(snap);
                return Ok(false);
            }
        }
        Ok(true)
    }

    // =======================================================================
    // isDefEqUnitLike
    // =======================================================================

    /// oracle: `isDefEqUnitLike` (ExprDefEq.lean:2181-2189). `useEtaStruct`
    /// elided as above.
    pub(crate) fn is_def_eq_unit_like(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        let t_ty = self.infer_type(t)?;
        let t_ty = self.whnf(t_ty)?;
        let name = match self.node(self.get_app_fn(t_ty)) {
            Node::Const { name: Some(n), .. } => n,
            _ => return Ok(false),
        };
        if !self.view.is_structure_like(name) {
            return Ok(false);
        }
        let ctor_name = match self.get_first_ctor(name) {
            Some(c) => c,
            None => return Ok(false),
        };
        let ctor_val = match self.view.get(ctor_name) {
            Some(ConstantInfo::Ctor(v)) => v,
            _ => return Ok(false),
        };
        if ctor_val.num_fields.to_usize() != Some(0) {
            return Ok(false);
        }
        let s_ty = self.infer_type(s)?;
        self.is_def_eq_core(t_ty, s_ty)
    }

    // =======================================================================
    // isDefEqProj / isDefEqProjDelta / isDefEqSingleton
    // =======================================================================

    /// `type_name`/`idx`/`structure` of a `Proj`/`ProjBig` node,
    /// normalizing the `u32`-vs-pooled-`Nat` index representation
    /// (`whnf_core_proj`'s own idiom).
    fn proj_parts(&self, e: ExprId) -> Option<(Option<NameId>, Nat, ExprId)> {
        match self.node(e) {
            Node::Proj {
                type_name,
                idx,
                structure,
            } => Some((type_name, Nat::from(idx as u64), structure)),
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => Some((
                type_name,
                self.scratch.nat_at(Some(self.view.store), idx).clone(),
                structure,
            )),
            _ => None,
        }
    }

    /// oracle: `isDefEqProj` (ExprDefEq.lean:2099-2130). The
    /// class-projection transparency bump (`isDefEqStructArgs`,
    /// `fromClass`-gated) is elided: `fromClass` is always `false` here
    /// (no class-projection registry, matching `whnf.rs`'s own
    /// `unfold_proj_inst_when_instances`/`get_stuck_mvar` posture), so
    /// `isDefEqStructArgs` degenerates to the identity. The
    /// `inTypeClassResolution` branch (:2112-2114) never applies either
    /// (no elaborator-context reader modeling that flag). `backward.
    /// isDefEq.lazyProjDelta` (default `true`, no options table) always
    /// takes the `isDefEqProjDelta` branch.
    pub(crate) fn is_def_eq_proj(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        match (self.proj_parts(t), self.proj_parts(s)) {
            (Some((tn, ti, tt)), Some((sn, si, ss))) => {
                if tn != sn || ti != si {
                    return Ok(false);
                }
                match ti.to_usize() {
                    Some(idx) => self.is_def_eq_proj_delta(tt, ss, idx),
                    // Index too large to index a slice with (never
                    // exercised by any real structure — field counts
                    // are always tiny): fall back to comparing the
                    // whole structures, a sound under-approximation
                    // (structure defeq implies projection defeq by
                    // congruence; incompleteness only).
                    None => self.is_def_eq_core(tt, ss),
                }
            }
            (Some((Some(struct_name), idx, structure)), None) if idx.is_zero() => {
                self.is_def_eq_singleton(struct_name, structure, s)
            }
            (None, Some((Some(struct_name), idx, structure))) if idx.is_zero() => {
                self.is_def_eq_singleton(struct_name, structure, t)
            }
            _ => Ok(false),
        }
    }

    /// oracle: `isDefEqProjDelta` (ExprDefEq.lean:2072-2098): solve
    /// `t.i =?= s.i` (already peeled to their `structure` arguments) by
    /// lazy-delta-stepping the structures until they visibly agree or
    /// diverge, falling back to comparing the projected fields directly.
    fn is_def_eq_proj_delta(
        &mut self,
        t0: ExprId,
        s0: ExprId,
        idx: usize,
    ) -> Result<bool, MetaError> {
        let t = self.whnf_core(t0)?;
        let s = self.whnf_core(s0)?;
        if let Some(true) = self.is_def_eq_quick(t, s)? {
            return Ok(true);
        }
        self.is_def_eq_proj_delta_loop(t, s, idx)
    }

    fn is_def_eq_proj_delta_loop(
        &mut self,
        mut t: ExprId,
        mut s: ExprId,
        idx: usize,
    ) -> Result<bool, MetaError> {
        loop {
            self.step()?;
            match self.is_def_eq_delta_step(t, s)? {
                DeltaStepResult::Cont(t2, s2) => {
                    t = t2;
                    s = s2;
                }
                DeltaStepResult::Eq => return Ok(true),
                DeltaStepResult::Unknown => return self.try_reduce_projs(t, s, idx),
                DeltaStepResult::Diff(t2, s2) => return self.try_reduce_projs(t2, s2, idx),
            }
        }
    }

    /// oracle: `isDefEqProjDelta.tryReduceProjs` (:2091-2094).
    fn try_reduce_projs(&mut self, t: ExprId, s: ExprId, idx: usize) -> Result<bool, MetaError> {
        let pt = self.project_core(t, idx)?;
        let ps = self.project_core(s, idx)?;
        match (pt, ps) {
            (Some(a), Some(b)) => self.is_def_eq_core(a, b),
            _ => self.is_def_eq_core(t, s),
        }
    }

    /// oracle: `isDefEqSingleton` (ExprDefEq.lean:2135-2162), the
    /// `isDefEqProj` `where`-clause helper: solve `(?m ..).1 =?= v` (or
    /// the symmetric `v =?= (?m ..).1`) by assigning `?m` to
    /// `⟨.., v⟩` when `structName` is a single-field non-recursive
    /// structure. `isClass` elided (always `false` — no class registry,
    /// same posture as `is_def_eq_proj`'s own doc).
    fn is_def_eq_singleton(
        &mut self,
        struct_name: NameId,
        structure: ExprId,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.view.is_structure_like(struct_name) {
            return Ok(false);
        }
        let ctor_name = match self.get_first_ctor(struct_name) {
            Some(c) => c,
            None => return Ok(false),
        };
        let ctor_val = match self.view.get(ctor_name) {
            Some(ConstantInfo::Ctor(cv)) => cv,
            _ => return Ok(false),
        };
        if ctor_val.num_fields.to_usize() != Some(1) {
            return Ok(false);
        }
        let s_ty = self.infer_type(structure)?;
        let s_ty = self.whnf(s_ty)?;
        let (s_ty_name, s_ty_levels) = match self.node(self.get_app_fn(s_ty)) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, levels),
            _ => return Ok(false),
        };
        if s_ty_name != struct_name {
            return Ok(false);
        }
        let s_w = self.whnf(structure)?;
        let mvar_id = match self.node(self.get_app_fn(s_w)) {
            Node::MVar { id: Some(id) } => MVarId(id),
            _ => return Ok(false),
        };
        // oracle: `isAssignable` (ExprDefEq.lean:1731-1734), narrowed to
        // the one real (non-seamed) exclusion this crate tracks —
        // `assign.rs::unassigned_mvar_id`'s own doc makes the identical
        // point.
        let assignable = matches!(
            self.mctx.decl(mvar_id),
            Some(d) if d.kind != MVarKind::SyntheticOpaque
        );
        if !assignable {
            return Ok(false);
        }
        let ctor_const =
            self.scratch
                .expr_const(Some(self.view.store), Some(ctor_name), s_ty_levels)?;
        let s_ty_args = self.get_app_args(s_ty);
        let ctor_partial = self.mk_app_spine(ctor_const, &s_ty_args)?;
        let ctor_app = self
            .scratch
            .expr_app(Some(self.view.store), ctor_partial, v)?;
        self.process_assignment_prime(s_w, ctor_app)
    }

    // =======================================================================
    // isDefEqDelta / isDefEqDeltaStep + tryHeuristic
    // =======================================================================

    /// oracle: `isDeltaCandidate?` (ExprDefEq.lean:1380-1383) via
    /// `getUnfoldableConst?` (`GetUnfoldableConst.lean:44-50`): head is a
    /// `Const` naming a `Defn` (never a `Thm`/`Axiom`/...) that passes
    /// the transparency gate. The `ctx.canUnfold?` override
    /// (`canUnfold`, `GetUnfoldableConst.lean:30-35`) is not consulted:
    /// this crate's own override channel (`can_unfold_override`) is
    /// scoped ONLY to `whnf_matcher`'s dynamic extent (`whnf.rs`'s own
    /// doc), which `is_def_eq_delta` never runs inside — plain
    /// `crate::can_unfold` is exactly equivalent here.
    fn is_delta_candidate(&self, e: ExprId) -> Option<&'e DefinitionVal> {
        let f = self.get_app_fn(e);
        let name = match self.node(f) {
            Node::Const { name: Some(n), .. } => n,
            _ => return None,
        };
        match self.view.get(name) {
            Some(ConstantInfo::Defn(v))
                if crate::can_unfold(self.cfg.transparency, self.status_of(name)) =>
            {
                Some(v)
            }
            _ => None,
        }
    }

    /// oracle: `tryHeuristic` (ExprDefEq.lean:1468-1508). NARROWED per
    /// this task's brief: the real gate (`isNonTrivialRegular`,
    /// :1405-1461, plus an `isMatcherCore`/has-mvar escape) additionally
    /// needs an AST-shape/matcher classifier this crate does not build.
    /// This port applies the heuristic whenever both heads are the SAME
    /// `Defn` constant with `Regular` hints — a strict SUPERSET of when
    /// the oracle applies it. Soundness is unaffected: a `true` here is
    /// always a valid witness (pointwise arg/level congruence under the
    /// SAME function is definitionally sound regardless of why the
    /// heuristic was tried — this is just ordinary congruence), and a
    /// `false` here only sends the caller to `unfoldBoth`/
    /// `unfoldComparingHeadsDefEq`, exactly what happens when the
    /// oracle's own (narrower) gate declines to try the heuristic at
    /// all. Incompleteness (this rung tries, and fails, MORE often than
    /// the oracle would) only — never a wrong verdict.
    fn try_heuristic(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        let t_fn = self.get_app_fn(t);
        let s_fn = self.get_app_fn(s);
        let (t_name, t_levels) = match self.node(t_fn) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, levels),
            _ => return Ok(false),
        };
        let s_levels = match self.node(s_fn) {
            Node::Const { levels, .. } => levels,
            _ => return Ok(false),
        };
        match self.view.get(t_name) {
            Some(ConstantInfo::Defn(v)) if matches!(v.hints, ReducibilityHints::Regular(_)) => {}
            _ => return Ok(false),
        }
        let t_args = self.get_app_args(t);
        let s_args = self.get_app_args(s);
        // oracle processes args BEFORE levels (its own comment,
        // :1487-1503, on avoiding a spurious "stuck" interruption).
        let us = self
            .scratch
            .level_list_at(Some(self.view.store), t_levels)
            .to_vec();
        let vs = self
            .scratch
            .level_list_at(Some(self.view.store), s_levels)
            .to_vec();
        // oracle: `checkpointDefEq` (:1503-1508). Bare checkpoint/
        // rollback, not the full `is_def_eq` entry (same nested-
        // checkpoint avoidance `assign.rs::is_def_eq_mvar_mvar` already
        // establishes as this crate's convention).
        let snap = self.checkpoint();
        let ok = self.is_def_eq_args(t_fn, &t_args, &s_args)? && self.is_def_eq_levels(&us, &vs)?;
        if !ok {
            self.rollback(snap);
        }
        Ok(ok)
    }

    /// oracle: `isDefEqDelta` (ExprDefEq.lean:1685-1710). The
    /// class-projection layer (`unfoldNonProjFnDefEq`, :1642-1657) is
    /// elided for the differing-name case: it degenerates EXACTLY to
    /// `unfoldReducibleDefEq` in this crate, because `getProjectionFnInfo?`
    /// (its `tProjInfo?`/`sProjInfo?` reads) is always `None` here (module
    /// doc) — every one of `unfoldNonProjFnDefEq`'s branches that would
    /// fire on a `some` result is dead, and its final `_, _ =>` arm is
    /// exactly `unfoldReducibleDefEq tInfo sInfo t s`.
    pub(crate) fn is_def_eq_delta(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        let t_cand = self.is_delta_candidate(t);
        let s_cand = self.is_delta_candidate(s);
        match (t_cand, s_cand) {
            (None, None) => Ok(None),
            (Some(_), None) => match self.unfold_definition(t)? {
                Some(t2) => Ok(Some(self.is_def_eq_core(t2, s)?)),
                None => Ok(None),
            },
            (None, Some(_)) => match self.unfold_definition(s)? {
                Some(s2) => Ok(Some(self.is_def_eq_core(t, s2)?)),
                None => Ok(None),
            },
            (Some(tinfo), Some(sinfo)) => {
                if tinfo.val.name == sinfo.val.name {
                    self.unfold_both_def_eq(t, s)
                } else {
                    self.unfold_reducible_def_eq(tinfo, sinfo, t, s)
                }
            }
        }
    }

    /// oracle: `unfoldBothDefEq` (ExprDefEq.lean:1611-1626), the
    /// same-declared-name case.
    fn unfold_both_def_eq(&mut self, t: ExprId, s: ExprId) -> Result<Option<bool>, MetaError> {
        match (self.node(t), self.node(s)) {
            (Node::Const { levels: ls1, .. }, Node::Const { levels: ls2, .. }) => {
                let us = self
                    .scratch
                    .level_list_at(Some(self.view.store), ls1)
                    .to_vec();
                let vs = self
                    .scratch
                    .level_list_at(Some(self.view.store), ls2)
                    .to_vec();
                if self.is_def_eq_levels(&us, &vs)? {
                    return Ok(Some(true));
                }
                match self.unfold_definition(t)? {
                    Some(t2) => match self.unfold_definition(s)? {
                        Some(s2) => Ok(Some(self.is_def_eq_core(t2, s2)?)),
                        None => Ok(None),
                    },
                    None => Ok(None),
                }
            }
            (Node::App { .. }, Node::App { .. }) => {
                if self.try_heuristic(t, s)? {
                    return Ok(Some(true));
                }
                match self.unfold_definition(t)? {
                    None => match self.unfold_definition(s)? {
                        None => Ok(None),
                        Some(s2) => Ok(Some(self.is_def_eq_core(t, s2)?)),
                    },
                    Some(t2) => match self.unfold_definition(s)? {
                        Some(s2) => Ok(Some(self.is_def_eq_core(t2, s2)?)),
                        None => Ok(Some(self.is_def_eq_core(t2, s)?)),
                    },
                }
            }
            _ => Ok(Some(false)),
        }
    }

    /// oracle: `sameHeadSymbol` (ExprDefEq.lean:1628-1630).
    fn same_head_symbol(&self, t: ExprId, s: ExprId) -> bool {
        matches!(
            (self.node(self.get_app_fn(t)), self.node(self.get_app_fn(s))),
            (Node::Const { name: Some(a), .. }, Node::Const { name: Some(b), .. }) if a == b
        )
    }

    /// oracle: `unfoldComparingHeadsDefEq` (ExprDefEq.lean:1632-1649).
    /// Both `tInfo`/`sInfo` params are unused in the oracle itself
    /// beyond their `.name` field (fed only to the tracing wrappers
    /// `isDefEqLeft`/`isDefEqRight`, which this crate's `is_def_eq_core`
    /// calls carry no trace payload for), so they are dropped entirely.
    fn unfold_comparing_heads_def_eq(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        match self.unfold_definition(t)? {
            None => match self.unfold_definition(s)? {
                None => Ok(None),
                Some(s2) => Ok(Some(self.is_def_eq_core(t, s2)?)),
            },
            Some(t2) => {
                if self.same_head_symbol(t2, s) {
                    Ok(Some(self.is_def_eq_core(t2, s)?))
                } else {
                    match self.unfold_definition(s)? {
                        None => Ok(Some(self.is_def_eq_core(t2, s)?)),
                        Some(s2) => {
                            if self.same_head_symbol(t, s2) {
                                Ok(Some(self.is_def_eq_core(t, s2)?))
                            } else {
                                Ok(Some(self.is_def_eq_core(t2, s2)?))
                            }
                        }
                    }
                }
            }
        }
    }

    /// oracle: `unfoldDefEq` (ExprDefEq.lean:1651-1662) — the
    /// kernel-simulated heuristic when neither side carries an
    /// expr-mvar.
    fn unfold_def_eq(
        &mut self,
        t_hints: ReducibilityHints,
        s_hints: ReducibilityHints,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        let has_mvar = self.data(t).has_expr_mvar() || self.data(s).has_expr_mvar();
        if !has_mvar {
            if hints_lt(t_hints, s_hints) {
                return match self.unfold_definition(t)? {
                    Some(t2) => Ok(Some(self.is_def_eq_core(t2, s)?)),
                    None => self.unfold_comparing_heads_def_eq(t, s),
                };
            }
            if hints_lt(s_hints, t_hints) {
                return match self.unfold_definition(s)? {
                    Some(s2) => Ok(Some(self.is_def_eq_core(t, s2)?)),
                    None => self.unfold_comparing_heads_def_eq(t, s),
                };
            }
        }
        self.unfold_comparing_heads_def_eq(t, s)
    }

    /// oracle: `unfoldReducibleDefEq` (ExprDefEq.lean:1664-1675).
    fn unfold_reducible_def_eq(
        &mut self,
        tinfo: &'e DefinitionVal,
        sinfo: &'e DefinitionVal,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        if self.cfg.transparency == TransparencyMode::Reducible {
            return self.unfold_def_eq(tinfo.hints, sinfo.hints, t, s);
        }
        let t_reducible = self.status_of(tinfo.val.name) == ReducibilityStatus::Reducible;
        let s_reducible = self.status_of(sinfo.val.name) == ReducibilityStatus::Reducible;
        if t_reducible && !s_reducible {
            return match self.unfold_definition(t)? {
                Some(t2) => Ok(Some(self.is_def_eq_core(t2, s)?)),
                None => self.unfold_def_eq(tinfo.hints, sinfo.hints, t, s),
            };
        }
        if !t_reducible && s_reducible {
            return match self.unfold_definition(s)? {
                Some(s2) => Ok(Some(self.is_def_eq_core(t, s2)?)),
                None => self.unfold_def_eq(tinfo.hints, sinfo.hints, t, s),
            };
        }
        self.unfold_def_eq(tinfo.hints, sinfo.hints, t, s)
    }

    /// oracle: `isDefEqDeltaStep` (ExprDefEq.lean:2037-2064). Used only
    /// by `isDefEqProjDelta`'s loop.
    fn is_def_eq_delta_step(&mut self, t: ExprId, s: ExprId) -> Result<DeltaStepResult, MetaError> {
        let t_cand = self.is_delta_candidate(t);
        let s_cand = self.is_delta_candidate(s);
        match (t_cand, s_cand) {
            (None, None) => Ok(DeltaStepResult::Unknown),
            (Some(_), None) => match self.unfold_definition(t)? {
                Some(t2) => self.delta_step_k(t2, s),
                None => Ok(DeltaStepResult::Unknown),
            },
            (None, Some(_)) => match self.unfold_definition(s)? {
                Some(s2) => self.delta_step_k(t, s2),
                None => Ok(DeltaStepResult::Unknown),
            },
            (Some(tinfo), Some(sinfo)) => match hints_cmp(tinfo.hints, sinfo.hints) {
                std::cmp::Ordering::Less => match self.unfold_definition(t)? {
                    Some(t2) => self.delta_step_k(t2, s),
                    None => Ok(DeltaStepResult::Unknown),
                },
                std::cmp::Ordering::Greater => match self.unfold_definition(s)? {
                    Some(s2) => self.delta_step_k(t, s2),
                    None => Ok(DeltaStepResult::Unknown),
                },
                std::cmp::Ordering::Equal => {
                    let same_name = tinfo.val.name == sinfo.val.name;
                    let both_app = matches!(self.node(t), Node::App { .. })
                        && matches!(self.node(s), Node::App { .. });
                    if same_name && both_app && self.try_heuristic(t, s)? {
                        return Ok(DeltaStepResult::Eq);
                    }
                    self.delta_step_unfold_both(t, s)
                }
            },
        }
    }

    fn delta_step_unfold_both(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<DeltaStepResult, MetaError> {
        match self.unfold_definition(t)? {
            None => match self.unfold_definition(s)? {
                None => Ok(DeltaStepResult::Unknown),
                Some(s2) => self.delta_step_k(t, s2),
            },
            Some(t2) => match self.unfold_definition(s)? {
                Some(s2) => self.delta_step_k(t2, s2),
                None => self.delta_step_k(t2, s),
            },
        }
    }

    /// oracle: `isDefEqDeltaStep.k` (:2059-2064).
    fn delta_step_k(&mut self, t: ExprId, s: ExprId) -> Result<DeltaStepResult, MetaError> {
        let t2 = self.whnf_core(t)?;
        let s2 = self.whnf_core(s)?;
        match self.is_def_eq_quick(t2, s2)? {
            Some(true) => Ok(DeltaStepResult::Eq),
            Some(false) => Ok(DeltaStepResult::Diff(t2, s2)),
            None => Ok(DeltaStepResult::Cont(t2, s2)),
        }
    }

    // =======================================================================
    // isDefEqNat / isDefEqStringLit
    // =======================================================================

    /// oracle: `isDefEqNat` (ExprDefEq.lean:189-200). `reduceNat?`
    /// (`whnf.rs::reduce_nat`, task 5, widened to `pub(crate)` here)
    /// already implements the literal-folding logic; this adds the
    /// has-fvar/has-mvar guard and "reduce whichever side can, then
    /// compare" dispatch.
    pub(crate) fn is_def_eq_nat(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        if self.data(t).has_fvar()
            || self.data(t).has_expr_mvar()
            || self.data(s).has_fvar()
            || self.data(s).has_expr_mvar()
        {
            return Ok(None);
        }
        let t2 = self.reduce_nat(t)?;
        let s2 = self.reduce_nat(s)?;
        match (t2, s2) {
            (None, None) => Ok(None),
            (Some(tv), Some(sv)) => Ok(Some(self.is_def_eq_core(tv, sv)?)),
            (Some(tv), None) => Ok(Some(self.is_def_eq_core(tv, s)?)),
            (None, Some(sv)) => Ok(Some(self.is_def_eq_core(t, sv)?)),
        }
    }

    /// oracle: `isDefEqStringLit` (ExprDefEq.lean:202-209). See the
    /// module doc's scope-cut note: the productive (`LitStr` vs
    /// `String.ofList`) direction is gated by `to_ctor_if_lit`'s own
    /// pre-existing `LitStr` seam.
    pub(crate) fn is_def_eq_string_lit(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        let string_of_list = self.dotted(&["String", "ofList"])?;
        let t_is_lit = matches!(self.node(t), Node::LitStr { .. });
        let s_is_lit = matches!(self.node(s), Node::LitStr { .. });
        let t_is_of_list = matches!(
            self.node(self.get_app_fn(t)),
            Node::Const { name: Some(n), .. } if n == string_of_list
        );
        let s_is_of_list = matches!(
            self.node(self.get_app_fn(s)),
            Node::Const { name: Some(n), .. } if n == string_of_list
        );
        if t_is_lit && s_is_of_list {
            let t2 = self.to_ctor_if_lit(t)?;
            Ok(Some(self.is_def_eq_core(t2, s)?))
        } else if t_is_of_list && s_is_lit {
            let s2 = self.to_ctor_if_lit(s)?;
            Ok(Some(self.is_def_eq_core(t, s2)?))
        } else {
            Ok(None)
        }
    }

    /// Intern a dotted name (`["String", "ofList"]` -> `String.ofList`)
    /// against the current store — the same idiom `whnf.rs::intern_dotted`
    /// uses, restated locally (that helper is module-private and tied to
    /// the matcher-unfold allowlist's own concerns).
    fn dotted(&mut self, parts: &[&str]) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let mut name = None;
        for part in parts {
            let s = self.scratch.intern_str(base, part)?;
            name = Some(self.scratch.name_str(base, name, s)?);
        }
        Ok(name.expect("dotted: parts must be non-empty"))
    }

    // =======================================================================
    // Named seams: isDefEqOffset / isDefEqNative
    // =======================================================================

    /// SEAM: oracle `isDefEqOffset` (Meta/Offset.lean:118-144, `?x + k
    /// =?= n` on `Nat`). Gated on `Config.offsetCnstrs`, a field this
    /// plan's `Config` does not carry (`config.rs`'s own doc: fields
    /// arrive with the feature that consults them). Always `Ok(None)`.
    pub(crate) fn is_def_eq_offset(
        &mut self,
        _t: ExprId,
        _s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        Ok(None)
    }

    /// SEAM: oracle `isDefEqNative` (ExprDefEq.lean:186-193, compiled
    /// `Lean.reduceBool`/`Lean.reduceNat` support via `reduceNative?`).
    /// Permanently out of scope: no native-code evaluator in a
    /// pure-Rust toolchain (same posture as `whnf.rs`'s own
    /// `reduceNative?` stub and `leanr_kernel::tc::TypeChecker::
    /// reduce_native`'s kernel-side twin). Always `Ok(None)`.
    pub(crate) fn is_def_eq_native(
        &mut self,
        _t: ExprId,
        _s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::{NameId, Store};
    use leanr_kernel::{
        BinderInfo, ConstSource, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal,
        EnvView, Nat, ReducibilityHints,
    };

    use crate::test_support::{fresh_fvar, with_ctx};

    /// Brief's step-1 test, corrected per AGENTS.md's "source wins"
    /// rule: the brief's literal construction (`h1 h2 : Sort 0`
    /// directly) does NOT exercise proof irrelevance — verified against
    /// the pinned oracle itself (`example (h1 h2 : Prop) : h1 = h2 :=
    /// rfl` FAILS to typecheck: `h1`/`h2` there are two arbitrary
    /// PROPOSITIONS, i.e. elements of `Prop` = `Sort 0`, not proofs of
    /// one — `isProofQuick`'s `.sort ..` arm returns `LBool.false`
    /// unconditionally, `InferType.lean:333`, so `isDefEqProofIrrel`
    /// never even reaches its `isProp` check for such a pair). The
    /// oracle-confirmed shape (`example (P : Prop) (h1 h2 : P) : h1 =
    /// h2 := rfl` DOES typecheck) needs an intermediate opaque `P :
    /// Prop` fvar, with `h1`/`h2` typed AT `P` (not at `Sort 0`
    /// directly) — `isProp(inferType h1) = isProp(P)` then holds
    /// because `P`'s OWN declared type (via `fresh_fvar`) is literally
    /// `Sort 0`.
    #[test]
    fn proof_irrelevance_equates_two_proofs_of_one_prop() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let prop = ctx.scratch.expr_sort(None, z).unwrap(); // Sort 0, i.e. `Prop`.
            let big_p = fresh_fvar(ctx, prop, "P"); // P : Prop (an opaque proposition).
            let h1 = fresh_fvar(ctx, big_p, "h1"); // h1 : P
            let h2 = fresh_fvar(ctx, big_p, "h2"); // h2 : P
            assert!(ctx.is_def_eq(h1, h2).unwrap());
            ctx.cfg.proof_irrelevance = false;
            assert!(
                !ctx.is_def_eq(h1, h2).unwrap(),
                "off ⇒ distinct fvars are not eq"
            );
        });
    }

    /// `tryHeuristic`'s same-head-no-unfold path (ExprDefEq.lean:
    /// 1468-1508, wired via `unfold_both_def_eq`'s App/App arm): `f a
    /// =?= f b` for a same-name `Regular`-hint `f`, where establishing
    /// `a =?= b` costs a handful of steps and `f`'s OWN body duplicates
    /// its argument thousands of times. If `is_def_eq_delta` unfolded
    /// `f` on both sides BEFORE trying the heuristic, comparing the two
    /// unfolded (thousands-of-arguments) spines would cost thousands of
    /// steps (`a =?= b` re-derived once per duplicate, this crate
    /// having no transient defeq cache yet — task 8). Trying the
    /// heuristic FIRST costs O(1) (`a =?= b` derived exactly once, for
    /// `f`'s own single argument) — so a small step budget distinguishes
    /// the two: this test's budget is comfortably above the heuristic's
    /// real cost and comfortably below the unfold-first cost.
    #[test]
    fn try_heuristic_same_head_avoids_unfolding_via_arg_congruence() {
        const N: usize = 5000;

        let mut base = Store::persistent();
        let z = base.level_zero(None).unwrap();
        let sort0 = base.expr_sort(None, z).unwrap();
        let no_levels = base.intern_level_list(None, &[]).unwrap();

        // f : Sort 0 -> Sort 0.
        let f_ty = base
            .expr_forall(None, None, sort0, sort0, BinderInfo::Default)
            .unwrap();

        // g, an opaque fvar `f`'s value applies to its own bound
        // variable N times: `fun x => g x x .. x` (N copies).
        let g_str = base.intern_str(None, "g").unwrap();
        let g_name = base.name_str(None, None, g_str).unwrap();
        let g = base.expr_fvar(None, Some(g_name)).unwrap();
        let bvar0 = base.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let mut spine = g;
        for _ in 0..N {
            spine = base.expr_app(None, spine, bvar0).unwrap();
        }
        let value = base
            .expr_lam(None, None, sort0, spine, BinderInfo::Default)
            .unwrap();

        let f_str = base.intern_str(None, "f").unwrap();
        let f_name: NameId = base.name_str(None, None, f_str).unwrap();
        let f_const = base.expr_const(None, Some(f_name), no_levels).unwrap();

        let mut extra = std::collections::HashMap::new();
        extra.insert(
            f_name,
            ConstantInfo::Defn(DefinitionVal {
                val: ConstantVal {
                    name: f_name,
                    level_params: vec![],
                    ty: f_ty,
                },
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all: vec![f_name],
            }),
        );

        // `a` needs one beta step to reduce to `b`'s own normal form —
        // real (if cheap) work every one of the `N` duplicated
        // occurrences would have to redo under a naive unfold-first
        // strategy.
        let const_lam = base
            .expr_lam(None, None, sort0, sort0, BinderInfo::Default)
            .unwrap(); // fun _ => Sort 0
        let a = base.expr_app(None, const_lam, sort0).unwrap(); // (fun _ => Sort 0) Sort 0
        let b = sort0;

        let t = base.expr_app(None, f_const, a).unwrap();
        let s = base.expr_app(None, f_const, b).unwrap();

        let empty_consts = leanr_kernel::CheckedConstants::new(std::collections::HashMap::new());
        let view = EnvView {
            consts: ConstSource::Gated(&empty_consts),
            extra: Some(&extra),
            quot_initialized: false,
            store: &base,
        };
        let mut scratch = Store::scratch();
        let mut ctx = crate::MetaCtx::new(
            view,
            &mut scratch,
            crate::Config::default(),
            &[],
            &[],
            &[],
            &[],
            &[],
        );
        ctx.set_step_budget(300);

        assert_eq!(
            ctx.is_def_eq(t, s),
            Ok(true),
            "tryHeuristic should settle `f a =?= f b` in O(1) steps via \
             argument congruence, never unfolding `f`'s {N}-deep body"
        );
    }
}
