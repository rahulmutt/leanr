//! oracle: `Lean.Meta.abstractNestedProofs`
//! (`Lean/Meta/AbstractNestedProofs.lean:17-116`) with `cache := true`,
//! plus the helpers it reaches: `mkAuxTheorem` (`Meta/Closure.lean:457-460`),
//! `mkAuxLemma` (`Meta/Tactic/AuxLemma.lean:43-79`) and `mkAuxDeclName` /
//! `DeclNameGenerator.mkUniqueName` (`CoreM.lean:149-153`, `:102-125`).
//!
//! The oracle `addDecl`s each aux theorem as soon as it is minted. leanr's
//! `MetaCtx` reads a fixed `EnvView`, so the theorems collect in
//! [`AuxLemmas::pending`] instead, and the caller commits them in order
//! before the main declaration. Wherever the oracle asks "is this name in
//! the env?", this port asks "is it in the env OR pending?".
//!
//! Seams (each returns `MetaError::Unsupported`):
//! - a `letE` reached by the walk (the oracle's `lambdaLetTelescope` arm,
//!   `:101`): P2 rejects `let` before this runs;
//! - an aux whose type or value mentions an unsafe constant (the oracle's
//!   unsafe opaque `defnDecl`, `AuxLemma.lean:51-58`): `add_decl_in`
//!   rejects unsafe definitions;
//! - a lookup of a PENDING aux constant (`pending_lookup_seam`). The spec
//!   assumed none happens inside `abstractNestedProofs`, but one does: once
//!   a binder type is rewritten to mention `foo._proof_k`, a later
//!   `is_proof` on the body can `infer_type` through it (e.g. whnf's
//!   `Eq.rec` iota, `to_ctor_when_k`, infers the major premise
//!   `foo._proof_k n`). The oracle has already `addDecl`ed the aux, so it
//!   succeeds; here the unknown-constant error naming a pending aux is
//!   mapped to a named `Unsupported` until a pending-constant overlay
//!   lands.
//!
//! Not modeled: private names. `mkUniqueName`'s `isConflict` also checks the
//! private/public twin of each candidate (`CoreM.lean:117-120`), and `curr`
//! privatizes the candidate in a module (`:121-125`). leanr has no private
//! names, and Elab0 is not a module.

use std::collections::HashMap;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::{
    abstract_fvars, instantiate_rev, BinderInfo, ConstantInfo, ConstantVal, Declaration,
    DefinitionSafety, KernelError, Nat, TheoremVal,
};

use crate::level_params::append_index_after;
use crate::{MetaCtx, MetaError};

/// The `auxLemmasExt` state (`Meta/Tactic/AuxLemma.lean:25-30`): aux-lemma
/// type → (name, levelParams). The oracle's key `AuxLemmaKey` (`:16-23`)
/// also holds `isPrivate := !env.isExporting` and `defeq`. Without a
/// `module` header `isExporting` is false, and `abstractNestedProofs`
/// passes `defeq := false`, so both are constant and the key is the type
/// alone, up to `BEq Expr` = `Expr.eqv`, which ignores binder names and
/// binder info. Hash-consing makes `ExprId` equality structural but NOT
/// alpha-equivalent, so keys are [`aux_lemma_key`]-canonical types.
pub type AuxLemmaCache = HashMap<ExprId, (NameId, Vec<NameId>)>;

/// The cache key of an aux-lemma type `e`: `e` with every binder name
/// erased and every binder info reset to default, so two types that are
/// equal under `Expr.eqv` (`Expr.lean`, "alpha equivalence", binder
/// annotations ignored) intern to the same `ExprId`. Interned in `st`
/// (through `base`, which dedups against the persistent store).
pub fn aux_lemma_key(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
) -> Result<ExprId, KernelError> {
    fn go(
        st: &mut Store,
        base: Option<&Store>,
        e: ExprId,
        memo: &mut HashMap<ExprId, ExprId>,
        depth: u32,
    ) -> Result<ExprId, KernelError> {
        if depth > 4096 {
            return Err(KernelError::DeepRecursion);
        }
        if let Some(&r) = memo.get(&e) {
            return Ok(r);
        }
        let r = match st.expr_node(base, e) {
            Node::App { f, arg } => {
                let f = go(st, base, f, memo, depth + 1)?;
                let a = go(st, base, arg, memo, depth + 1)?;
                st.expr_app(base, f, a)?
            }
            Node::Lam {
                binder_type, body, ..
            } => {
                let t = go(st, base, binder_type, memo, depth + 1)?;
                let b = go(st, base, body, memo, depth + 1)?;
                st.expr_lam(base, None, t, b, BinderInfo::Default)?
            }
            Node::Forall {
                binder_type, body, ..
            } => {
                let t = go(st, base, binder_type, memo, depth + 1)?;
                let b = go(st, base, body, memo, depth + 1)?;
                st.expr_forall(base, None, t, b, BinderInfo::Default)?
            }
            Node::LetE {
                ty,
                value,
                body,
                non_dep,
                ..
            } => {
                let t = go(st, base, ty, memo, depth + 1)?;
                let v = go(st, base, value, memo, depth + 1)?;
                let b = go(st, base, body, memo, depth + 1)?;
                st.expr_let(base, None, t, v, b, non_dep)?
            }
            Node::MData { data, expr } => {
                let c = go(st, base, expr, memo, depth + 1)?;
                st.expr_mdata(base, data, c)?
            }
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s = go(st, base, structure, memo, depth + 1)?;
                st.expr_proj(base, type_name, &Nat::from(idx as u64), s)?
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let n = st.nat_at(base, idx).clone();
                let s = go(st, base, structure, memo, depth + 1)?;
                st.expr_proj(base, type_name, &n, s)?
            }
            _ => e,
        };
        memo.insert(e, r);
        Ok(r)
    }
    go(st, base, e, &mut HashMap::new(), 0)
}

/// Aux theorems minted while abstracting one declaration's value, in
/// creation order — the caller commits them, in order, BEFORE the main
/// declaration (`Environment::add_decl_in`).
pub struct AuxLemmas {
    decl_name: NameId,
    /// `DeclNameGenerator.idx` for the `_proof` infix (starts at 1,
    /// `CoreM.lean:79`).
    next_idx: u64,
    /// Seeded from the caller's environment-wide cache (`with_cache`);
    /// `mk_aux_lemma` reads it and inserts what it mints.
    cache: AuxLemmaCache,
    pending: Vec<Declaration>,
}

impl AuxLemmas {
    /// `withDeclNameForAuxNaming decl_name` (`CoreM.lean:158-169`, entered at
    /// `PreDefinition/Basic.lean:125`): a fresh generator, prefix
    /// `decl_name`, index 1, and an empty aux-lemma cache.
    pub fn new(decl_name: NameId) -> Self {
        Self::with_cache(decl_name, AuxLemmaCache::new())
    }

    /// `new`, seeded with the environment's `auxLemmasExt` state, so a
    /// nested proof whose type an earlier declaration's aux lemma already
    /// has reuses that constant (`AuxLemma.lean:70-73`). `cache`'s ids must
    /// be resolvable from the caller's store: environment-store ids are.
    pub fn with_cache(decl_name: NameId, cache: AuxLemmaCache) -> Self {
        AuxLemmas {
            decl_name,
            next_idx: 1,
            cache,
            pending: Vec::new(),
        }
    }

    pub fn pending(&self) -> &[Declaration] {
        &self.pending
    }

    pub fn into_pending(self) -> Vec<Declaration> {
        self.pending
    }

    /// Whether `n` names a pending aux theorem (only `Thm`s are pushed).
    pub(crate) fn is_pending(&self, n: NameId) -> bool {
        self.pending
            .iter()
            .any(|d| matches!(d, Declaration::Thm(t) if t.val.name == n))
    }
}

/// oracle: `Expr.isAtomic` (`Expr.lean:1516-1523`).
fn is_atomic(node: &Node) -> bool {
    matches!(
        node,
        Node::Const { .. }
            | Node::Sort { .. }
            | Node::BVar { .. }
            | Node::BVarBig { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. }
            | Node::MVar { .. }
            | Node::FVar { .. }
    )
}

/// `visit`'s `MonadCacheT ExprStructEq Expr` (`AbstractNestedProofs.lean:70`):
/// one map per `abstract_nested_proofs` call. Hash-consing makes `ExprId`
/// equality structural, as `ExprStructEq` is. `log` records keys in
/// insertion order so `anp_visit_binders` can find the entries made while
/// visiting a telescope's binder types. It also carries the two constant
/// names the walk compares against, interned once per call.
struct VisitCache {
    map: HashMap<ExprId, ExprId>,
    log: Vec<ExprId>,
    /// `sorryAx` (`Expr.hasSorry`, `Util/Sorry.lean:28-29`).
    sorry_ax: NameId,
    /// `Lean.Grind.nestedProof` (`isNonTrivialProof`, `:52`).
    nested_proof: NameId,
}

impl VisitCache {
    fn get(&self, e: &ExprId) -> Option<&ExprId> {
        self.map.get(e)
    }

    fn insert(&mut self, k: ExprId, v: ExprId) {
        if self.map.insert(k, v).is_none() {
            self.log.push(k);
        }
    }
}

impl MetaCtx<'_> {
    /// oracle: `Meta.abstractNestedProofs` (`AbstractNestedProofs.lean:111-116`), `cache := true`.
    pub fn abstract_nested_proofs(
        &mut self,
        aux: &mut AuxLemmas,
        e: ExprId,
    ) -> Result<ExprId, MetaError> {
        if self.is_proof(e)? {
            return Ok(e);
        }
        let mut cache = self.anp_visit_cache()?;
        self.anp_visit(aux, &mut cache, e)
            .map_err(|err| self.pending_lookup_seam(aux, err))
    }

    /// A fresh per-call `VisitCache`, with its two names interned once
    /// (an intern error propagates rather than reading as "no match").
    fn anp_visit_cache(&mut self) -> Result<VisitCache, MetaError> {
        Ok(VisitCache {
            map: HashMap::new(),
            log: Vec::new(),
            sorry_ax: self.anp_name(&["sorryAx"])?,
            nested_proof: self.anp_name(&["Lean", "Grind", "nestedProof"])?,
        })
    }

    /// The pending-aux lookup seam (module doc): an unknown-constant
    /// error naming a PENDING aux theorem becomes a named `Unsupported`.
    /// Every other error passes through unchanged.
    fn pending_lookup_seam(&self, aux: &AuxLemmas, err: MetaError) -> MetaError {
        let msg = match &err {
            MetaError::Infer(m) => m.clone(),
            MetaError::Kernel(k @ leanr_kernel::KernelError::UnknownConstant(_)) => k.to_string(),
            _ => return err,
        };
        let base = Some(self.view.store);
        for d in &aux.pending {
            let Declaration::Thm(t) = d else { continue };
            let nm = self.scratch.to_name(base, Some(t.val.name));
            if msg == format!("unknown constant '{nm}'") {
                return MetaError::Unsupported(format!(
                    "abstractNestedProofs: lookup of pending aux lemma {nm} — M4c-1 seam \
                     (needs pending-constant overlay)"
                ));
            }
        }
        err
    }

    /// oracle: `AbstractNestedProofs.visit` (`AbstractNestedProofs.lean:72-106`).
    /// Every recursive call goes through `guarded`, the leanr stand-in for
    /// `checkSystem` (`:73`): a deep term ends in `DepthBudgetExhausted`,
    /// not a stack overflow.
    fn anp_visit(
        &mut self,
        aux: &mut AuxLemmas,
        cache: &mut VisitCache,
        e: ExprId,
    ) -> Result<ExprId, MetaError> {
        let node = self.node(e);
        if is_atomic(&node) {
            return Ok(e);
        }
        if let Some(&r) = cache.get(&e) {
            return Ok(r);
        }
        self.step()?;
        let base = Some(self.view.store);
        let r = if self.is_non_trivial_proof(aux, cache, e)? && !self.has_sorry(cache, e) {
            self.abstract_proof(aux, cache, e)?
        } else {
            match node {
                Node::Lam { .. } | Node::Forall { .. } => {
                    let cp = self.lctx_checkpoint();
                    let r = self.anp_visit_binders(aux, cache, e);
                    self.lctx_restore(cp);
                    r?
                }
                Node::LetE { .. } => {
                    return Err(MetaError::Unsupported(
                        "abstractNestedProofs under let — letToHave follow-up (M4c-1 seam)".into(),
                    ))
                }
                Node::MData { data, expr } => {
                    let b = self.guarded(|c| c.anp_visit(aux, cache, expr))?;
                    self.scratch.expr_mdata(base, data, b)?
                }
                Node::Proj {
                    type_name,
                    idx,
                    structure,
                } => {
                    let b = self.guarded(|c| c.anp_visit(aux, cache, structure))?;
                    self.scratch
                        .expr_proj(base, type_name, &Nat::from(idx as u64), b)?
                }
                Node::ProjBig {
                    type_name,
                    idx,
                    structure,
                } => {
                    let n = self.scratch.nat_at(base, idx).clone();
                    let b = self.guarded(|c| c.anp_visit(aux, cache, structure))?;
                    self.scratch.expr_proj(base, type_name, &n, b)?
                }
                Node::App { .. } => {
                    let f = self.get_app_fn(e);
                    let args = self.get_app_args(e);
                    let mut r = self.guarded(|c| c.anp_visit(aux, cache, f))?;
                    for a in args {
                        let a2 = self.guarded(|c| c.anp_visit(aux, cache, a))?;
                        r = self.scratch.expr_app(base, r, a2)?;
                    }
                    r
                }
                _ => e,
            }
        };
        cache.insert(e, r);
        Ok(r)
    }

    /// oracle: the `lam` / `forallE` arms of `visit`
    /// (`AbstractNestedProofs.lean:100-102`) with `visitBinders` (`:77-89`).
    ///
    /// The oracle opens the whole telescope with the ORIGINAL binder
    /// types (`lambdaLetTelescope` / `forallTelescope`), visits every
    /// binder type under that context (`:83`, in the ambient lctx), and
    /// only then runs the body continuation under `withLCtx lctx` (`:89`),
    /// where `lctx` has each decl's type replaced by its visited version
    /// (`:84,88`, `modifyLocalDecl`). So a later binder's proof that
    /// closes over an earlier binder sees that binder's RAW type, and the
    /// aux theorem's binder domain keeps the raw proof.
    ///
    /// Phase 1 here pushes every binder with its original type and visits
    /// each type. leanr's `LocalContext` has no `modifyLocalDecl` (it is
    /// kernel-owned and keeps fvar ids fresh), so phase 2 restores and
    /// re-pushes the telescope with the visited types under NEW fvars,
    /// substituting old → new in each visited type. The oracle keeps the
    /// fvar ids, so its `visit` cache entries made while visiting the types
    /// still hit inside the body; to keep that, every entry phase 1 added
    /// is copied with old → new substituted in key and value.
    ///
    /// Rebuild: `mkLambdaFVars (usedLetOnly := false) (generalizeNondepLet
    /// := false)` / `mkForallFVars` at its defaults. `generalizeNondepLet`
    /// only matters for a `have` in the telescope, which cannot occur here:
    /// the walk stops at a `lam`/`forallE` boundary, and `letE` is a seam.
    /// The caller checkpoints/restores the lctx.
    fn anp_visit_binders(
        &mut self,
        aux: &mut AuxLemmas,
        cache: &mut VisitCache,
        e: ExprId,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let is_lambda = matches!(self.node(e), Node::Lam { .. });
        let cp = self.lctx_checkpoint();
        // Phase 1: open the telescope with the original binder types.
        let mut xs: Vec<ExprId> = Vec::new();
        let mut binders = Vec::new();
        let mut cur = e;
        loop {
            let (binder_name, binder_type, body, binder_info) = match self.node(cur) {
                Node::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } if is_lambda => (binder_name, binder_type, body, binder_info),
                Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } if !is_lambda => (binder_name, binder_type, body, binder_info),
                _ => break,
            };
            let d = instantiate_rev(self.scratch, base, binder_type, &xs, &mut self.guard)?;
            let x = self.push_local_decl(binder_name, d, binder_info)?;
            xs.push(x);
            binders.push((binder_name, d, binder_info));
            cur = body;
        }
        // `:80-88`: visit every binder type under the original telescope.
        let log_start = cache.log.len();
        let mut types = Vec::with_capacity(binders.len());
        for &(_, d, _) in &binders {
            types.push(self.guarded(|c| c.anp_visit(aux, cache, d))?);
        }
        // `:89` `withLCtx lctx`: re-open with the visited types.
        self.lctx_restore(cp);
        let mut ys: Vec<ExprId> = Vec::with_capacity(xs.len());
        for (i, &(binder_name, _, binder_info)) in binders.iter().enumerate() {
            let t = self.anp_replace_fvars(types[i], &xs[..i], &ys)?;
            let y = self.push_local_decl(binder_name, t, binder_info)?;
            ys.push(y);
        }
        // Entries the copy itself appends (past `log_end`) are not revisited.
        let log_end = cache.log.len();
        for i in log_start..log_end {
            let k = cache.log[i];
            if !self.data(k).has_fvar() {
                continue;
            }
            let k2 = self.anp_replace_fvars(k, &xs, &ys)?;
            if k2 != k {
                let v2 = self.anp_replace_fvars(cache.map[&k], &xs, &ys)?;
                cache.insert(k2, v2);
            }
        }
        let b = instantiate_rev(self.scratch, base, cur, &ys, &mut self.guard)?;
        let b = self.guarded(|c| c.anp_visit(aux, cache, b))?;
        if is_lambda {
            self.mk_lambda(&ys, b)
        } else {
            self.mk_forall(&ys, b)
        }
    }

    /// `e[xs := ys]` for closed `e` (no loose bvars): abstract `xs`, then
    /// instantiate with `ys`.
    fn anp_replace_fvars(
        &mut self,
        e: ExprId,
        xs: &[ExprId],
        ys: &[ExprId],
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let a = abstract_fvars(self.scratch, base, e, xs, &mut self.guard)?;
        Ok(instantiate_rev(self.scratch, base, a, ys, &mut self.guard)?)
    }

    /// oracle: `AbstractNestedProofs.isNonTrivialProof`
    /// (`AbstractNestedProofs.lean:40-65`). "In the env" (`origEnv.contains`,
    /// `:64`) also counts pending aux theorems, which the oracle has
    /// already added to the env at this point.
    fn is_non_trivial_proof(
        &mut self,
        aux: &AuxLemmas,
        cache: &VisitCache,
        e: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.is_proof(e)? {
            return Ok(false);
        }
        // `e.isAppOf ``Grind.nestedProof` (`:52`): inside `namespace
        // Lean.Meta` the double-backtick name resolves to
        // `Lean.Grind.nestedProof` (`Init/Grind/Util.lean:13,16`).
        let head = self.get_app_fn(e);
        if let Node::Const { name: Some(n), .. } = self.node(head) {
            if n == cache.nested_proof {
                return Ok(false);
            }
        }
        // `getLambdaBody` (`:35-38`) strips `lam` only; the body may keep
        // loose bvars, and `withApp` is syntactic.
        let mut body = e;
        while let Node::Lam { body: b, .. } = self.node(body) {
            body = b;
        }
        let f = self.get_app_fn(body);
        let f_node = self.node(f);
        if !is_atomic(&f_node) {
            return Ok(true);
        }
        if let Node::Const { name, .. } = f_node {
            let in_env = name.is_some_and(|n| self.view.get(n).is_some() || aux.is_pending(n));
            if !in_env {
                return Ok(true);
            }
        }
        for a in self.get_app_args(body) {
            if !is_atomic(&self.node(a)) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// oracle: `Meta.abstractProof` (`AbstractNestedProofs.lean:18-31`) with
    /// `postprocessType := visit` (`:98`), sharing `visit`'s cache.
    fn abstract_proof(
        &mut self,
        aux: &mut AuxLemmas,
        cache: &mut VisitCache,
        proof: ExprId,
    ) -> Result<ExprId, MetaError> {
        let ty = self.infer_type(proof)?;
        let ty = self.beta_reduce(ty)?;
        let ty = self.zeta_reduce(ty)?;
        let ty = self.guarded(|c| c.anp_visit(aux, cache, ty))?;
        // `:27`: `visit` only abstracts sorry-free proofs (`:91`), so this
        // is always `true` here; kept for parity.
        let use_cache = !self.has_sorry(cache, proof);
        self.mk_aux_theorem(aux, ty, proof, use_cache)
    }

    /// oracle: `mkAuxTheorem` (`Meta/Closure.lean:457-460`) with
    /// `zetaDelta := true` and `kind? := none` (so `_proof`).
    fn mk_aux_theorem(
        &mut self,
        aux: &mut AuxLemmas,
        ty: ExprId,
        value: ExprId,
        use_cache: bool,
    ) -> Result<ExprId, MetaError> {
        let r = self.mk_value_type_closure(ty, value)?;
        let name = self.mk_aux_lemma(aux, r.level_params, r.ty, r.value, use_cache)?;
        let base = Some(self.view.store);
        let ls = self.scratch.intern_level_list(base, &r.level_args)?;
        let c = self.scratch.expr_const(base, Some(name), ls)?;
        self.mk_app_spine(c, &r.expr_args)
    }

    /// oracle: `mkAuxLemma` (`Meta/Tactic/AuxLemma.lean:43-79`) with
    /// `kind? := none`, `inferRfl := false`, `forceExpose := false`,
    /// `defeq := false`.
    ///
    /// The oracle key is `{type, isPrivate := !env.isExporting, defeq}`
    /// (`:47`). `isExporting` is `false` outside a module
    /// (`Environment.lean:614,652-654`), so every key in a non-module
    /// file has `isPrivate := true` and the private retry (`:75-78`) looks
    /// up keys nobody inserts. The cache is therefore keyed on `type`
    /// alone. As in the oracle, a miss inserts even when `use_cache` is
    /// `false` (`:68`).
    fn mk_aux_lemma(
        &mut self,
        aux: &mut AuxLemmas,
        level_params: Vec<NameId>,
        ty: ExprId,
        value: ExprId,
        use_cache: bool,
    ) -> Result<NameId, MetaError> {
        let key = aux_lemma_key(self.scratch, Some(self.view.store), ty)?;
        if use_cache {
            if let Some((name, lps)) = aux.cache.get(&key) {
                if *lps == level_params {
                    return Ok(*name);
                }
            }
        }
        let name = self.mk_aux_decl_name(aux)?;
        if self.has_unsafe(ty) || self.has_unsafe(value) {
            return Err(MetaError::Unsupported(
                "abstractNestedProofs: aux lemma over an unsafe constant \
                 (unsafe opaque defnDecl, AuxLemma.lean:51-58) — M4c-1 seam"
                    .into(),
            ));
        }
        // `TheoremVal.all` defaults to `[name]` (`Declaration.lean:147`).
        aux.pending.push(Declaration::Thm(TheoremVal {
            val: ConstantVal {
                name,
                level_params: level_params.clone(),
                ty,
            },
            value,
            all: vec![name],
        }));
        aux.cache.insert(key, (name, level_params));
        Ok(name)
    }

    /// oracle: `mkAuxDeclName (kind := `_proof)` (`CoreM.lean:149-153`) over
    /// `DeclNameGenerator.mkUniqueName` (`:102-125`). `base := namePrefix ++
    /// _proof`; while `appendIndexAfter base idx` conflicts, `idx += 1`.
    /// The generator is stored at the FOUND index, not past it (`:111`
    /// returns `(curr g base, g)`), so the next call starts there, sees the
    /// now-pending name, and moves on.
    fn mk_aux_decl_name(&mut self, aux: &mut AuxLemmas) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let infix = self.scratch.intern_str(base, "_proof")?;
        let base_name = self.scratch.name_str(base, Some(aux.decl_name), infix)?;
        let mut idx = aux.next_idx;
        loop {
            let cand = append_index_after(self.scratch, base, base_name, idx)?;
            if self.view.get(cand).is_none() && !aux.is_pending(cand) {
                aux.next_idx = idx;
                return Ok(cand);
            }
            idx += 1;
        }
    }

    /// The hierarchical name `parts` (e.g. `["Lean", "Grind",
    /// "nestedProof"]`), interned (hash-consed, so `NameId` equality is
    /// name equality).
    fn anp_name(&mut self, parts: &[&str]) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let mut acc = None;
        for p in parts {
            let s = self.scratch.intern_str(base, p)?;
            acc = Some(self.scratch.name_str(base, acc, s)?);
        }
        acc.ok_or_else(|| MetaError::Infer("anp_name: empty name".into()))
    }

    /// Whether some `Const` in `e` satisfies `pred` (an `Expr.find?` over
    /// constants). Explicit stack plus a visited set: the term bank is a
    /// DAG.
    fn find_const(&self, e: ExprId, mut pred: impl FnMut(&Self, Option<NameId>) -> bool) -> bool {
        let mut stack = vec![e];
        let mut seen = std::collections::HashSet::new();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            match self.node(x) {
                Node::Const { name, .. } => {
                    if pred(self, name) {
                        return true;
                    }
                }
                Node::App { f, arg } => stack.extend([f, arg]),
                Node::Lam {
                    binder_type, body, ..
                }
                | Node::Forall {
                    binder_type, body, ..
                } => stack.extend([binder_type, body]),
                Node::LetE {
                    ty, value, body, ..
                } => stack.extend([ty, value, body]),
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                    stack.push(structure)
                }
                _ => {}
            }
        }
        false
    }

    /// oracle: `Expr.hasSorry` (`Util/Sorry.lean:28-29`): some `Const`
    /// named `sorryAx`.
    fn has_sorry(&self, cache: &VisitCache, e: ExprId) -> bool {
        let sorry = cache.sorry_ax;
        self.find_const(e, |_, n| n == Some(sorry))
    }

    /// oracle: `Environment.hasUnsafe` (`Environment.lean:2629-2638`): some
    /// `Const` whose env entry is unsafe; a name not in the env is safe.
    /// Pending aux theorems are never unsafe (they are `thmDecl`s).
    fn has_unsafe(&self, e: ExprId) -> bool {
        self.find_const(e, |ctx, n| {
            let Some(n) = n else { return false };
            match ctx.view.get(n) {
                Some(ConstantInfo::Defn(v)) => v.safety == DefinitionSafety::Unsafe,
                Some(ConstantInfo::Axiom(v)) => v.is_unsafe,
                Some(ConstantInfo::Opaque(v)) => v.is_unsafe,
                Some(ConstantInfo::Induct(v)) => v.is_unsafe,
                Some(ConstantInfo::Ctor(v)) => v.is_unsafe,
                Some(ConstantInfo::Rec(v)) => v.is_unsafe,
                Some(ConstantInfo::Thm(_)) | Some(ConstantInfo::Quot(_)) | None => false,
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{app, c, cu, lit_level, render_name, with_meta0_ctx};
    use leanr_kernel::{BinderInfo, Declaration};

    fn name(ctx: &mut MetaCtx, s: &str) -> NameId {
        let base = Some(ctx.view.store);
        let mut n = None;
        for part in s.split('.') {
            let id = ctx.scratch.intern_str(base, part).unwrap();
            n = Some(ctx.scratch.name_str(base, n, id).unwrap());
        }
        n.unwrap()
    }

    /// `fun (n : N) => @PProd.mk.{l1,l2} A B a b` with `n` bound; the closure
    /// receives the opened `n` and returns (A, B, a, b).
    fn lam_n_pprod(
        ctx: &mut MetaCtx,
        levels: (u32, u32),
        parts: impl FnOnce(&mut MetaCtx, ExprId) -> (ExprId, ExprId, ExprId, ExprId),
    ) -> ExprId {
        let n_ty = c(ctx, "N");
        let n_name = name(ctx, "n");
        let cp = ctx.lctx_checkpoint();
        let n = ctx
            .push_local_decl(Some(n_name), n_ty, BinderInfo::Default)
            .unwrap();
        let (ta, tb, a, b) = parts(ctx, n);
        let (l1, l2) = (lit_level(ctx, levels.0), lit_level(ctx, levels.1));
        let mk = cu(ctx, "PProd.mk", &[l1, l2]);
        let body = ctx.mk_app_spine(mk, &[ta, tb, a, b]).unwrap();
        let r = ctx.mk_lambda(&[n], body).unwrap();
        ctx.lctx_restore(cp);
        r
    }

    /// `@Eq.{1} N x x` and `@rfl.{1} N x`.
    fn eq_rfl(ctx: &mut MetaCtx, x: ExprId) -> (ExprId, ExprId) {
        let one = lit_level(ctx, 1);
        let n_ty = c(ctx, "N");
        let eq = cu(ctx, "Eq", &[one]);
        let rfl = cu(ctx, "rfl", &[one]);
        (
            ctx.mk_app_spine(eq, &[n_ty, x, x]).unwrap(),
            ctx.mk_app_spine(rfl, &[n_ty, x]).unwrap(),
        )
    }

    fn pending_names(ctx: &MetaCtx, aux: &AuxLemmas) -> Vec<String> {
        aux.pending()
            .iter()
            .map(|d| match d {
                Declaration::Thm(t) => render_name(ctx, t.val.name),
                _ => panic!("thmDecl expected"),
            })
            .collect()
    }

    /// probe foo1: `⟨n, rfl⟩ : PProd N (N.succ n = N.succ n)` →
    /// `foo1._proof_1 n`, one pending theorem.
    #[test]
    fn nested_proof_becomes_proof_1_applied_to_its_closure() {
        with_meta0_ctx(|ctx| {
            let foo1 = name(ctx, "foo1");
            let succ = c(ctx, "N.succ");
            let n_ty = c(ctx, "N");
            let e = lam_n_pprod(ctx, (1, 0), |ctx, n| {
                let sn = app(ctx, succ, n);
                let (ty, pf) = eq_rfl(ctx, sn);
                (n_ty, ty, n, pf)
            });
            let mut aux = AuxLemmas::new(foo1);
            let out = ctx.abstract_nested_proofs(&mut aux, e).unwrap();
            assert_eq!(aux.pending().len(), 1);
            let Declaration::Thm(t) = &aux.pending()[0] else {
                panic!("thmDecl expected")
            };
            assert_eq!(render_name(ctx, t.val.name), "foo1._proof_1");
            assert!(t.val.level_params.is_empty());
            // `TheoremVal.all` default `[name]` (Declaration.lean:147).
            assert_eq!(t.all, vec![t.val.name]);
            // out = fun n => @PProd.mk.{1,0} N (Eq ..) n (foo1._proof_1 n)
            let p1 = cu(ctx, "foo1._proof_1", &[]);
            let want = lam_n_pprod(ctx, (1, 0), |ctx, n| {
                let sn = app(ctx, succ, n);
                let (ty, _) = eq_rfl(ctx, sn);
                let call = app(ctx, p1, n);
                (n_ty, ty, n, call)
            });
            assert_eq!(out, want);
        });
    }

    /// Review Focus 4 / probe foo5: `@rfl.{1} N n` has atomic args → kept.
    #[test]
    fn atomic_arg_proof_is_not_abstracted() {
        with_meta0_ctx(|ctx| {
            let foo5 = name(ctx, "foo5");
            let n_ty = c(ctx, "N");
            let e = lam_n_pprod(ctx, (1, 0), |ctx, n| {
                let (ty, pf) = eq_rfl(ctx, n);
                (n_ty, ty, n, pf)
            });
            let mut aux = AuxLemmas::new(foo5);
            assert_eq!(ctx.abstract_nested_proofs(&mut aux, e).unwrap(), e);
            assert!(aux.pending().is_empty());
        });
    }

    /// Two identical proofs in one declaration share one aux. The two
    /// occurrences are one `ExprId`, so `visit`'s own cache dedups them
    /// before `mkAuxLemma` is reached (see the next test for the
    /// `mkAuxLemma` cache).
    #[test]
    fn identical_proofs_share_one_aux() {
        with_meta0_ctx(|ctx| {
            let foo3 = name(ctx, "foo3");
            let succ = c(ctx, "N.succ");
            let e = lam_n_pprod(ctx, (0, 0), |ctx, n| {
                let sn = app(ctx, succ, n);
                let (ty, pf) = eq_rfl(ctx, sn);
                (ty, ty, pf, pf)
            });
            let mut aux = AuxLemmas::new(foo3);
            ctx.abstract_nested_proofs(&mut aux, e).unwrap();
            assert_eq!(aux.pending().len(), 1);
        });
    }

    /// Ruling R3: two DIFFERENT proof terms (`@rfl.{1} N (N.succ n)` and
    /// `@Eq.refl.{1} N (N.succ n)`, distinct `ExprId`s) of the same
    /// type share one aux through `mkAuxLemma`'s type-keyed cache
    /// (`AuxLemma.lean:70-73`), not `visit`'s.
    #[test]
    fn different_proofs_of_one_type_share_one_aux() {
        with_meta0_ctx(|ctx| {
            let foo6 = name(ctx, "foo6");
            let succ = c(ctx, "N.succ");
            let one = lit_level(ctx, 1);
            let n_ty = c(ctx, "N");
            let eq_refl = cu(ctx, "Eq.refl", &[one]);
            let e = lam_n_pprod(ctx, (0, 0), |ctx, n| {
                let sn = app(ctx, succ, n);
                let (ty, p1) = eq_rfl(ctx, sn);
                let p2 = ctx.mk_app_spine(eq_refl, &[n_ty, sn]).unwrap();
                assert_ne!(p1, p2, "the two proofs must be distinct ExprIds");
                // Both inferred types reach the same ExprId after
                // betaReduce/zetaReduce (`AbstractNestedProofs.lean:20-22`).
                for p in [p1, p2] {
                    let t = ctx.infer_type(p).unwrap();
                    let t = ctx.beta_reduce(t).unwrap();
                    let t = ctx.zeta_reduce(t).unwrap();
                    assert_eq!(t, ty);
                }
                (ty, ty, p1, p2)
            });
            let mut aux = AuxLemmas::new(foo6);
            ctx.abstract_nested_proofs(&mut aux, e).unwrap();
            assert_eq!(pending_names(ctx, &aux), vec!["foo6._proof_1"]);
        });
    }

    /// Review Focus 2: two DISTINCT proofs → `_proof_1`, `_proof_2`, though
    /// neither is in the env yet.
    #[test]
    fn distinct_proofs_get_distinct_indices() {
        with_meta0_ctx(|ctx| {
            let foo4 = name(ctx, "foo4");
            let succ = c(ctx, "N.succ");
            let e = lam_n_pprod(ctx, (0, 0), |ctx, n| {
                let sn = app(ctx, succ, n);
                let ssn = app(ctx, succ, sn);
                let (t1, p1) = eq_rfl(ctx, sn);
                let (t2, p2) = eq_rfl(ctx, ssn);
                (t1, t2, p1, p2)
            });
            let mut aux = AuxLemmas::new(foo4);
            ctx.abstract_nested_proofs(&mut aux, e).unwrap();
            assert_eq!(
                pending_names(ctx, &aux),
                vec!["foo4._proof_1", "foo4._proof_2"]
            );
        });
    }

    /// `@Eq.rec.{2,1} N x (fun (b : N) (h : @Eq.{1} N x b) => Type) N x pf`,
    /// a type that reduces to `N` by `Eq.rec` iota when `pf` is `rfl`.
    fn eq_rec_n(ctx: &mut MetaCtx, x: ExprId, pf: ExprId) -> ExprId {
        let base = Some(ctx.view.store);
        let n_ty = c(ctx, "N");
        let one = lit_level(ctx, 1);
        let two = lit_level(ctx, 2);
        let b_name = name(ctx, "b");
        let h_name = name(ctx, "h");
        let eq = cu(ctx, "Eq", &[one]);
        let b0 = crate::test_support::bvar(ctx, 0);
        let h_ty = ctx.mk_app_spine(eq, &[n_ty, x, b0]).unwrap();
        let type0 = ctx.scratch.expr_sort(base, one).unwrap();
        let inner = ctx
            .scratch
            .expr_lam(base, Some(h_name), h_ty, type0, BinderInfo::Default)
            .unwrap();
        let motive = ctx
            .scratch
            .expr_lam(base, Some(b_name), n_ty, inner, BinderInfo::Default)
            .unwrap();
        let rec = cu(ctx, "Eq.rec", &[two, one]);
        ctx.mk_app_spine(rec, &[n_ty, x, motive, n_ty, x, pf])
            .unwrap()
    }

    /// Final review Important #1: every binder TYPE is visited under the
    /// telescope's ORIGINAL local context; only the body sees the visited
    /// types (`visitBinders`, `AbstractNestedProofs.lean:77-89`: `visit
    /// localDecl.type` runs in the ambient context, and `withLCtx lctx`
    /// wraps only `k`). Oracle probe (v4.33.0-rc1, `Nat` for `N`):
    ///
    /// ```text
    /// def fooP (a : @Eq.rec Nat (Nat.succ Nat.zero) (fun _ _ => Type) Nat
    ///                 (Nat.succ Nat.zero) (@rfl Nat (Nat.succ Nat.zero)))
    ///          (b : @Eq.rec Nat (Nat.succ a) (fun _ _ => Type) Nat
    ///                 (Nat.succ a) (@rfl Nat (Nat.succ a))) : … := b
    /// theorem fooP._proof_2 : ∀ (a : @Eq.rec Nat Nat.zero.succ (fun x x_1 => Type)
    ///     Nat Nat.zero.succ (@rfl Nat Nat.zero.succ)), @Eq Nat (Nat.succ a) (Nat.succ a)
    /// value: fun (a : @Eq.rec … fooP._proof_1) (b : @Eq.rec … (fooP._proof_2 a)) => b
    /// ```
    ///
    /// `_proof_2`'s binder domain keeps the RAW `rfl`, not `fooP._proof_1`.
    #[test]
    fn binder_types_are_visited_under_the_original_lctx() {
        with_meta0_ctx(|ctx| {
            let foo_p = name(ctx, "fooP");
            let succ = c(ctx, "N.succ");
            let zero = c(ctx, "N.zero");
            let a_name = name(ctx, "a");
            let b_name = name(ctx, "b");
            let sz = app(ctx, succ, zero);
            let (eq_sz, pf1) = eq_rfl(ctx, sz);
            let a_ty = eq_rec_n(ctx, sz, pf1);
            let cp = ctx.lctx_checkpoint();
            let a = ctx
                .push_local_decl(Some(a_name), a_ty, BinderInfo::Default)
                .unwrap();
            let sa = app(ctx, succ, a);
            let (eq_sa, pf2) = eq_rfl(ctx, sa);
            let b_ty = eq_rec_n(ctx, sa, pf2);
            let b = ctx
                .push_local_decl(Some(b_name), b_ty, BinderInfo::Default)
                .unwrap();
            let e = ctx.mk_lambda(&[a, b], b).unwrap();
            // The aux theorem's statement, as the oracle prints it.
            let want_p2_ty = ctx.mk_forall(&[a], eq_sa).unwrap();
            ctx.lctx_restore(cp);
            ctx.infer_type(e).expect("the probe term is well typed");

            let mut aux = AuxLemmas::new(foo_p);
            let out = ctx.abstract_nested_proofs(&mut aux, e).unwrap();
            assert_eq!(
                pending_names(ctx, &aux),
                vec!["fooP._proof_1", "fooP._proof_2"]
            );
            let Declaration::Thm(t1) = &aux.pending()[0] else {
                panic!("thmDecl expected")
            };
            assert_eq!(t1.val.ty, eq_sz);
            let Declaration::Thm(t2) = &aux.pending()[1] else {
                panic!("thmDecl expected")
            };
            let Node::Forall { binder_type, .. } = ctx.node(t2.val.ty) else {
                panic!("fooP._proof_2 must be a ∀")
            };
            assert_eq!(
                binder_type, a_ty,
                "fooP._proof_2's binder domain must keep the RAW proof"
            );
            assert_eq!(t2.val.ty, want_p2_ty);

            // out = fun (a : E(succ zero)[_proof_1]) (b : E(succ a)[_proof_2 a]) => b
            let p1 = cu(ctx, "fooP._proof_1", &[]);
            let p2 = cu(ctx, "fooP._proof_2", &[]);
            let a_ty2 = eq_rec_n(ctx, sz, p1);
            let cp = ctx.lctx_checkpoint();
            let a = ctx
                .push_local_decl(Some(a_name), a_ty2, BinderInfo::Default)
                .unwrap();
            let sa = app(ctx, succ, a);
            let p2a = app(ctx, p2, a);
            let b_ty2 = eq_rec_n(ctx, sa, p2a);
            let b = ctx
                .push_local_decl(Some(b_name), b_ty2, BinderInfo::Default)
                .unwrap();
            let want = ctx.mk_lambda(&[a, b], b).unwrap();
            ctx.lctx_restore(cp);
            assert_eq!(out, want);
        });
    }

    /// The oracle keeps the binder fvars when it swaps in the visited
    /// types, so a proof cached while visiting a binder type still hits
    /// in the body. Oracle probe (v4.33.0-rc1): `fooQ` = `fooP` with body
    /// `@PProd.mk Nat (@Eq Nat (Nat.succ a) (Nat.succ a)) a (@rfl Nat
    /// (Nat.succ a))` has exactly `_proof_1`, `_proof_2` (`#print
    /// fooQ._proof_3` → unknown constant) and the body becomes
    /// `@PProd.mk … a (fooQ._proof_2 a)`. leanr re-pushes under new fvars,
    /// so this pins the cache copy in `anp_visit_binders`.
    #[test]
    fn binder_type_cache_entries_still_hit_in_the_body() {
        with_meta0_ctx(|ctx| {
            let foo_q = name(ctx, "fooQ");
            let succ = c(ctx, "N.succ");
            let zero = c(ctx, "N.zero");
            let n_ty = c(ctx, "N");
            let one = lit_level(ctx, 1);
            let zero_l = lit_level(ctx, 0);
            let mk = cu(ctx, "PProd.mk", &[one, zero_l]);
            let a_name = name(ctx, "a");
            let b_name = name(ctx, "b");
            let sz = app(ctx, succ, zero);
            let (_, pf1) = eq_rfl(ctx, sz);
            let a_ty = eq_rec_n(ctx, sz, pf1);
            let cp = ctx.lctx_checkpoint();
            let a = ctx
                .push_local_decl(Some(a_name), a_ty, BinderInfo::Default)
                .unwrap();
            let sa = app(ctx, succ, a);
            let (eq_sa, pf2) = eq_rfl(ctx, sa);
            let b_ty = eq_rec_n(ctx, sa, pf2);
            let b = ctx
                .push_local_decl(Some(b_name), b_ty, BinderInfo::Default)
                .unwrap();
            let body = ctx.mk_app_spine(mk, &[n_ty, eq_sa, a, pf2]).unwrap();
            let e = ctx.mk_lambda(&[a, b], body).unwrap();
            ctx.lctx_restore(cp);
            ctx.infer_type(e).expect("the probe term is well typed");

            let mut aux = AuxLemmas::new(foo_q);
            let out = ctx.abstract_nested_proofs(&mut aux, e).unwrap();
            assert_eq!(
                pending_names(ctx, &aux),
                vec!["fooQ._proof_1", "fooQ._proof_2"]
            );
            let p1 = cu(ctx, "fooQ._proof_1", &[]);
            let p2 = cu(ctx, "fooQ._proof_2", &[]);
            let a_ty2 = eq_rec_n(ctx, sz, p1);
            let cp = ctx.lctx_checkpoint();
            let a = ctx
                .push_local_decl(Some(a_name), a_ty2, BinderInfo::Default)
                .unwrap();
            let sa = app(ctx, succ, a);
            let (eq_sa, _) = eq_rfl(ctx, sa);
            let p2a = app(ctx, p2, a);
            let b_ty2 = eq_rec_n(ctx, sa, p2a);
            let b = ctx
                .push_local_decl(Some(b_name), b_ty2, BinderInfo::Default)
                .unwrap();
            let body = ctx.mk_app_spine(mk, &[n_ty, eq_sa, a, p2a]).unwrap();
            let want = ctx.mk_lambda(&[a, b], body).unwrap();
            ctx.lctx_restore(cp);
            assert_eq!(out, want);
        });
    }

    /// Ruling R4 pin: the pending-aux lookup seam. Probe term
    /// `fun (n : N) (x : @Eq.rec.{2,1} N (N.succ n) (fun b h => Type)
    /// (N → N) (N.succ n) (@rfl.{1} N (N.succ n))) => x N.zero`:
    /// visiting `x`'s domain abstracts the `rfl`, then the body's
    /// `is_proof` infers through `Eq.rec` iota and looks up
    /// `fooP._proof_1`, which is only pending.
    #[test]
    fn pending_aux_lookup_is_a_named_seam() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let foo_p = name(ctx, "fooP");
            let n_ty = c(ctx, "N");
            let succ = c(ctx, "N.succ");
            let zero = c(ctx, "N.zero");
            let one = lit_level(ctx, 1);
            let two = lit_level(ctx, 2);
            let n_name = name(ctx, "n");
            let x_name = name(ctx, "x");
            let b_name = name(ctx, "b");
            let h_name = name(ctx, "h");
            let cp = ctx.lctx_checkpoint();
            let n = ctx
                .push_local_decl(Some(n_name), n_ty, BinderInfo::Default)
                .unwrap();
            let sn = app(ctx, succ, n);
            let (_, pf) = eq_rfl(ctx, sn);
            // motive := fun (b : N) (h : @Eq.{1} N (N.succ n) b) => Type
            let eq = cu(ctx, "Eq", &[one]);
            let b0 = crate::test_support::bvar(ctx, 0);
            let h_ty = ctx.mk_app_spine(eq, &[n_ty, sn, b0]).unwrap();
            let type0 = ctx.scratch.expr_sort(base, one).unwrap();
            let inner = ctx
                .scratch
                .expr_lam(base, Some(h_name), h_ty, type0, BinderInfo::Default)
                .unwrap();
            let motive = ctx
                .scratch
                .expr_lam(base, Some(b_name), n_ty, inner, BinderInfo::Default)
                .unwrap();
            let arrow = ctx
                .scratch
                .expr_forall(base, None, n_ty, n_ty, BinderInfo::Default)
                .unwrap();
            let rec = cu(ctx, "Eq.rec", &[two, one]);
            let x_ty = ctx
                .mk_app_spine(rec, &[n_ty, sn, motive, arrow, sn, pf])
                .unwrap();
            let x = ctx
                .push_local_decl(Some(x_name), x_ty, BinderInfo::Default)
                .unwrap();
            let body = app(ctx, x, zero);
            let e = ctx.mk_lambda(&[n, x], body).unwrap();
            ctx.lctx_restore(cp);
            ctx.infer_type(e).expect("the probe term is well typed");
            let mut aux = AuxLemmas::new(foo_p);
            match ctx.abstract_nested_proofs(&mut aux, e) {
                Err(MetaError::Unsupported(m)) => assert_eq!(
                    m,
                    "abstractNestedProofs: lookup of pending aux lemma fooP._proof_1 — \
                     M4c-1 seam (needs pending-constant overlay)"
                ),
                other => panic!("expected the pending-aux seam, got {other:?}"),
            }
        });
    }

    /// A value that is itself a proof is returned unchanged
    /// (`AbstractNestedProofs.lean:112-114`).
    #[test]
    fn a_proof_value_is_not_abstracted_at_the_root() {
        with_meta0_ctx(|ctx| {
            let succ = c(ctx, "N.succ");
            let zero = c(ctx, "N.zero");
            let sz = app(ctx, succ, zero);
            let (_, pf) = eq_rfl(ctx, sz);
            let thm = name(ctx, "thm");
            let mut aux = AuxLemmas::new(thm);
            assert_eq!(ctx.abstract_nested_proofs(&mut aux, pf).unwrap(), pf);
            assert!(aux.pending().is_empty());
        });
    }

    /// Final review Important #2: `anp_visit` recurses through `guarded`,
    /// so a deep term ends in `Ok` or `DepthBudgetExhausted`, never a
    /// stack-overflow abort.
    #[test]
    fn deep_term_does_not_overflow_the_stack() {
        crate::test_support::on_8mib_stack(|| {
            with_meta0_ctx(|ctx| {
                let e = crate::test_support::deep_succ_lambda(ctx, 100_000);
                let deep = name(ctx, "deep");
                let mut aux = AuxLemmas::new(deep);
                match ctx.abstract_nested_proofs(&mut aux, e) {
                    Ok(r) => assert_eq!(r, e),
                    Err(MetaError::DepthBudgetExhausted) => {}
                    Err(other) => panic!("expected Ok or DepthBudgetExhausted, got {other:?}"),
                }
                assert!(aux.pending().is_empty());
            })
        });
    }

    /// `has_sorry` matches a `sorryAx` constant anywhere in the term
    /// (`Util/Sorry.lean:28-29`), through the name interned once in
    /// `anp_visit_cache`. Meta0 has no `sorryAx`, so this checks the
    /// syntactic scan only.
    #[test]
    fn has_sorry_finds_sorry_ax_through_the_interned_name() {
        with_meta0_ctx(|ctx| {
            let cache = ctx.anp_visit_cache().unwrap();
            let n_ty = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let sorry = cu(ctx, "sorryAx", &[]);
            let s = app(ctx, sorry, n_ty);
            let succ = c(ctx, "N.succ");
            let e = app(ctx, succ, s);
            assert!(ctx.has_sorry(&cache, e));
            let e2 = app(ctx, succ, zero);
            assert!(!ctx.has_sorry(&cache, e2));
        });
    }
}
