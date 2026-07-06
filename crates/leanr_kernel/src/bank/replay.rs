//! Oracle-faithful replay of decoded modules — id-native port of
//! `crate::replay` (Task 12; oracle: src/Lean/Replay.lean). `replay`
//! takes the union of one or more decoded modules' `ConstantInfo`s
//! (already bridged into id form via `Environment::intern_module`, so
//! every `NameId`/`ExprId` reaching this module is already
//! persistent-region) and sends each declaration through the kernel's
//! admission pipeline (`Environment::add_decl`) in dependency order.
//!
//! What replay does NOT send to the kernel: constructors and recursors.
//! Those are *regenerated* by the kernel when their inductive block is
//! admitted, and replay instead checks that each decoded ctor/recursor
//! is structurally identical (`bank::decl::constant_info_eq`, Task 1) to
//! the regenerated one — id/scalar comparisons only, no guard needed (the
//! interning invariant already makes id equality exactly structural).
//!
//! **Deleted relative to the Arc port**: the pre-intern block (Arc
//! `replay.rs:89-107`, which re-interned the whole input map through the
//! env's structural interner before admission). Interning AT INPUT —
//! `Environment::intern_module`, called once per decoded module before
//! its output is folded into the `constants` map this function
//! receives — already puts every id in the shared persistent `Store`;
//! there is nothing left to intern here, and the Arc interner concept
//! itself has no id equivalent (see `bank::env::Environment::add_core`'s
//! doc comment).
//!
//! Everything here still runs on UNTRUSTED input: the constants map, all
//! cross-references inside it, and the dependency chains between decls
//! are attacker-controlled. Nothing may panic. The oracle uses
//! `unreachable!`/`[n]!` at points a well-formed module can never reach;
//! each becomes a real error for us (`MissingConstant`, `InvalidInductive`).
//! The recursion that follows dependency chains is bounded and
//! stack-safe via `RecGuard` (guard.rs).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::decl::{constant_info_eq, ConstantInfo, Declaration, InductiveType};
use super::env::Environment;
use super::{ExprId, NameId};
use crate::{DefinitionSafety, KernelError, Name, RecGuard};

/// `KernelError` plus the declaration being replayed when it fired,
/// mirroring Replay.lean:135's `while replaying declaration '<name>'`
/// wrapping (id-twin of `crate::replay::ReplayError`). `decl` is built
/// via `to_name` (cold path, error construction only) — no scratch id
/// ever reaches a `KernelError`/`ReplayError`, and every `NameId` this
/// module handles is persistent-region anyway (see module doc).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayError {
    pub decl: Arc<Name>,
    pub error: KernelError,
}

impl std::fmt::Display for ReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "while replaying declaration '{}': {}",
            self.decl, self.error
        )
    }
}

impl std::error::Error for ReplayError {}

/// Result of a successful replay, for CLI reporting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplayStats {
    /// Declarations sent to the kernel (`add_decl` calls: axioms, defs,
    /// theorems, opaques, one per inductive block, and quotient init).
    /// Constructors/recursors are checked structurally, not sent, so
    /// they are not counted here.
    pub checked: usize,
    /// Constants skipped because they are `unsafe` or `partial`
    /// (Replay.lean:176-181): neither checked nor added.
    pub skipped_unsafe: usize,
}

/// Port of `Lean.Environment.replay`. `constants` is the union of the
/// modules-to-check's id-form `ConstantInfo`s (decode order irrelevant,
/// already bridged via `Environment::intern_module`); `env` starts as
/// the already-trusted base (empty for fresh checking) and is extended
/// in place with every admitted declaration.
pub fn replay(
    env: &mut Environment,
    constants: HashMap<NameId, ConstantInfo>,
) -> Result<ReplayStats, ReplayError> {
    // Replay.lean:177-182 — seed `remaining` with every safe, non-partial
    // constant; count the rest as skipped without ever checking them.
    let mut remaining: HashSet<NameId> = HashSet::new();
    let mut skipped_unsafe = 0usize;
    for (&n, ci) in &constants {
        if is_unsafe(ci) || is_partial(ci) {
            skipped_unsafe += 1;
        } else {
            remaining.insert(n);
        }
    }

    let mut g = RecGuard::new();

    let mut st = Replayer {
        constants,
        env,
        remaining,
        pending: HashSet::new(),
        postponed_constructors: HashSet::new(),
        postponed_recursors: HashSet::new(),
        checked: 0,
        failing_decl: None,
    };

    // Replay.lean:185-186 — iterate the initial `remaining` snapshot.
    // Each `replay_constant` moves names out of `remaining`; a name a
    // dependency already handled is a no-op (`is_todo` returns false).
    let names: Vec<NameId> = st.remaining.iter().copied().collect();
    for n in names {
        st.replay_constant(n, &mut g).map_err(|e| st.wrap(e))?;
    }

    // Replay.lean:187-188 — the postponed structural checks.
    st.check_postponed_constructors()?;
    st.check_postponed_recursors()?;

    Ok(ReplayStats {
        checked: st.checked,
        skipped_unsafe,
    })
}

fn is_unsafe(ci: &ConstantInfo) -> bool {
    match ci {
        ConstantInfo::Defn(v) => v.safety == DefinitionSafety::Unsafe,
        ConstantInfo::Axiom(v) => v.is_unsafe,
        ConstantInfo::Opaque(v) => v.is_unsafe,
        ConstantInfo::Induct(v) => v.is_unsafe,
        ConstantInfo::Ctor(v) => v.is_unsafe,
        ConstantInfo::Rec(v) => v.is_unsafe,
        ConstantInfo::Thm(_) | ConstantInfo::Quot(_) => false,
    }
}

fn is_partial(ci: &ConstantInfo) -> bool {
    matches!(
        ci,
        ConstantInfo::Defn(v) if v.safety == DefinitionSafety::Partial
    )
}

struct Replayer<'a> {
    /// The working map (Replay.lean's `newConstants`). Owned so that each
    /// constant can be released once it has been successfully admitted
    /// into `env` (mirrors the Arc port's Change 2 / M1b Task 16 memory
    /// fix): as `env` grows the map shrinks. Constructors/recursors are
    /// never removed — they are re-read here for the postponed
    /// structural checks.
    constants: HashMap<NameId, ConstantInfo>,
    env: &'a mut Environment,
    remaining: HashSet<NameId>,
    pending: HashSet<NameId>,
    postponed_constructors: HashSet<NameId>,
    postponed_recursors: HashSet<NameId>,
    checked: usize,
    /// The declaration being processed when the first `KernelError` fired
    /// during the recursive descent (id-twin of the Arc `failing_decl`:
    /// `NameId` is `Copy`, so this needs no `Arc::clone` at each write).
    failing_decl: Option<NameId>,
}

impl Replayer<'_> {
    /// Bridge a (persistent-region, per module doc) `NameId` to `Arc<Name>`
    /// — cold path, error construction only.
    fn to_name(&self, n: NameId) -> Arc<Name> {
        self.env.view().store.to_name(None, Some(n))
    }

    /// Build a `ReplayError` from a bare kernel error plus the recorded
    /// failing declaration.
    fn wrap(&self, error: KernelError) -> ReplayError {
        let decl = match self.failing_decl {
            Some(n) => self.to_name(n),
            None => Arc::new(Name::Anonymous),
        };
        ReplayError { decl, error }
    }

    /// Record `name` as the failing declaration if none recorded yet, and
    /// return the error unchanged.
    fn blame(&mut self, name: NameId, error: KernelError) -> KernelError {
        if self.failing_decl.is_none() {
            self.failing_decl = Some(name);
        }
        error
    }

    /// Replay.lean:46-52 — if `name` still needs processing, move it from
    /// `remaining` to `pending` and return true.
    fn is_todo(&mut self, name: NameId) -> bool {
        if self.remaining.remove(&name) {
            self.pending.insert(name);
            true
        } else {
            false
        }
    }

    /// Replay.lean:74-136 — `replayConstant`, threaded through `RecGuard`
    /// because dependency chains are attacker-controlled.
    fn replay_constant(&mut self, name: NameId, g: &mut RecGuard) -> Result<(), KernelError> {
        g.enter(|g| self.replay_constant_inner(name, g))
    }

    fn replay_constant_inner(&mut self, name: NameId, g: &mut RecGuard) -> Result<(), KernelError> {
        if !self.is_todo(name) {
            return Ok(());
        }
        // Replay.lean:76 — `newConstants[name]? | unreachable!`. `name`
        // came from `remaining`, which only holds keys of `constants`, so
        // this lookup always succeeds; the fallback is defence in depth.
        let ci = match self.constants.get(&name) {
            Some(ci) => ci.clone(),
            None => {
                let dn = self.to_name(name);
                return Err(self.blame(name, KernelError::MissingConstant(dn)));
            }
        };

        // Replay.lean:77 — replay dependencies first. `used_constants`
        // returns an owned `Vec<NameId>` (no borrow of `self.env` outlives
        // the call), so the loop below is free to mutate `self` per
        // iteration.
        let deps = crate::bank::used_consts::used_constants(self.env.view().store, None, &ci);
        for dep in deps {
            self.replay_constant(dep, g)?;
        }

        // Replay.lean:79 — a mutual (inductive) block may already have
        // cleared this name; only act if it is still pending.
        if !self.pending.contains(&name) {
            return Ok(());
        }

        match &ci {
            ConstantInfo::Defn(v) => {
                self.add_decl(name, Declaration::Defn(v.clone()))?;
            }
            ConstantInfo::Axiom(v) => {
                self.add_decl(name, Declaration::Axiom(v.clone()))?;
            }
            ConstantInfo::Opaque(v) => {
                self.add_decl(name, Declaration::Opaque(v.clone()))?;
            }
            ConstantInfo::Thm(v) => {
                // Replay.lean:84-97 — tolerate a duplicate theorem iff an
                // existing entry is a theorem with identical name, type,
                // level params, and `all`. `Expr::structural_eq(a,b,g)?`
                // and `Name` list equality become plain `==` on
                // `ExprId`/`Vec<NameId>` (no guard) — the interning
                // invariant already makes id equality exactly structural
                // (same porting rule Task 3/4 applied to `is_equiv_core`).
                if let Some(ConstantInfo::Thm(existing)) = self.env.get(name) {
                    if existing.val.name == v.val.name
                        && existing.val.ty == v.val.ty
                        && existing.val.level_params == v.val.level_params
                        && existing.all == v.all
                    {
                        self.pending.remove(&name);
                        self.constants.remove(&name);
                        return Ok(());
                    }
                }
                self.add_decl(name, Declaration::Thm(v.clone()))?;
            }
            ConstantInfo::Induct(_) => {
                self.replay_inductive(name, &ci, g)?;
            }
            // Replay.lean:124-128 — postpone; checked structurally at the
            // end against the kernel's regenerated version.
            ConstantInfo::Ctor(_) => {
                self.postponed_constructors.insert(name);
            }
            ConstantInfo::Rec(_) => {
                self.postponed_recursors.insert(name);
            }
            ConstantInfo::Quot(_) => {
                // Replay.lean:129-133 — `Quot.lift`/`Quot.ind` types
                // reference `Eq`, so replay `Eq` first, then admit the
                // single quotient declaration. Subsequent quot infos find
                // the env already quot-initialized and their `add_decl`
                // is a no-op re-init guarded inside `add_quot`.
                let eq_id = intern_eq_name(self.env)?;
                self.replay_constant(eq_id, g)?;
                self.add_decl(name, Declaration::Quot)?;
            }
        }

        self.pending.remove(&name);
        // This constant is now in `env`; release the working copy so only
        // `env` retains it. Constructors and recursors are the exception —
        // never admitted here (only postponed), re-read from `constants` at
        // the end by `check_postponed_{constructors,recursors}`. `is_todo`
        // guarantees an already-admitted (hence removed) name is never read
        // from `constants` again.
        if !matches!(ci, ConstantInfo::Ctor(_) | ConstantInfo::Rec(_)) {
            self.constants.remove(&name);
        }
        Ok(())
    }

    /// Replay.lean:102-120 — rebuild and admit a whole inductive block.
    fn replay_inductive(
        &mut self,
        name: NameId,
        ci: &ConstantInfo,
        g: &mut RecGuard,
    ) -> Result<(), KernelError> {
        let ConstantInfo::Induct(info) = ci else {
            unreachable!("replay_inductive called on non-inductive");
        };
        let lparams = info.val.level_params.clone();
        let nparams = info.num_params.clone();

        // Replay.lean:105-108 — gather every block member's info and drop
        // ALL of them from `remaining`/`pending` at once (the mutual
        // block is admitted as a unit). A missing member is untrusted-
        // input malformation, so `MissingConstant`.
        let mut members: Vec<ConstantInfo> = Vec::with_capacity(info.all.len());
        for &n in &info.all {
            let member = match self.constants.get(&n).cloned() {
                Some(m) => m,
                None => {
                    let dn = self.to_name(n);
                    return Err(self.blame(name, KernelError::MissingConstant(dn)));
                }
            };
            members.push(member);
        }
        for m in &members {
            let mn = m.name();
            self.remaining.remove(&mn);
            self.pending.remove(&mn);
        }

        // Replay.lean:109-119 — per member, gather its constructor infos
        // (in declared order) and build the `InductiveType`.
        let mut types: Vec<InductiveType> = Vec::with_capacity(members.len());
        let mut all_ctor_infos: Vec<ConstantInfo> = Vec::new();
        for member in &members {
            // Replay.lean:110 `ci.inductiveVal!` — a non-inductive member
            // is malformed; reject rather than panic.
            let miv = match member {
                ConstantInfo::Induct(miv) => miv,
                _ => {
                    let dn = self.to_name(member.name());
                    return Err(self.blame(
                        name,
                        KernelError::InvalidInductive {
                            name: dn,
                            what: "mutual block member is not an inductive",
                        },
                    ));
                }
            };
            let mut ctor_pairs: Vec<(NameId, ExprId)> = Vec::with_capacity(miv.ctors.len());
            for &cn in &miv.ctors {
                let cinfo = match self.constants.get(&cn).cloned() {
                    Some(c) => c,
                    None => {
                        let dn = self.to_name(cn);
                        return Err(self.blame(name, KernelError::MissingConstant(dn)));
                    }
                };
                ctor_pairs.push((cinfo.name(), cinfo.constant_val().ty));
                all_ctor_infos.push(cinfo);
            }
            types.push(InductiveType {
                name: miv.val.name,
                ty: miv.val.ty,
                ctors: ctor_pairs,
            });
        }

        // Replay.lean:112-115 — make sure the constructors' own
        // dependencies are replayed before we admit the block.
        for cinfo in &all_ctor_infos {
            let deps = crate::bank::used_consts::used_constants(self.env.view().store, None, cinfo);
            for dep in deps {
                self.replay_constant(dep, g)?;
            }
        }

        // Replay.lean:120 — admit the block; `is_unsafe := false` always
        // (unsafe inductives never reach `remaining`). `add_inductive`
        // recomputes `num_nested` itself, so we pass none.
        self.add_decl(
            name,
            Declaration::Inductive {
                lparams,
                nparams,
                types,
                is_unsafe: false,
            },
        )?;
        // The whole block's inductive infos are now in `env`; drop them
        // from the working map. Their members were already removed from
        // `remaining`/`pending` above, so no later `is_todo` will read
        // them back. Constructors are NOT removed here — they remain in
        // `remaining` (processed later, then postponed) and the postponed
        // structural check re-reads them from `constants`.
        for m in &members {
            self.constants.remove(&m.name());
        }
        Ok(())
    }

    /// `add_decl` wrapper that blames `name` on failure and counts the
    /// successful kernel admission.
    fn add_decl(&mut self, name: NameId, d: Declaration) -> Result<(), KernelError> {
        match self.env.add_decl(d) {
            Ok(()) => {
                self.checked += 1;
                Ok(())
            }
            Err(e) => Err(self.blame(name, e)),
        }
    }

    /// Replay.lean:148-153 — every postponed constructor must exist in
    /// the env (as a ctor, regenerated by its inductive) and be
    /// structurally identical to the decoded one.
    fn check_postponed_constructors(&mut self) -> Result<(), ReplayError> {
        for &ctor in &self.postponed_constructors {
            let ok = match (self.env.get(ctor), self.constants.get(&ctor)) {
                (
                    Some(regenerated @ ConstantInfo::Ctor(_)),
                    Some(decoded @ ConstantInfo::Ctor(_)),
                ) => constant_info_eq(decoded, regenerated),
                _ => false,
            };
            if !ok {
                return Err(ReplayError {
                    decl: self.to_name(ctor),
                    error: KernelError::ConstructorMismatch(self.to_name(ctor)),
                });
            }
        }
        Ok(())
    }

    /// Replay.lean:159-164 — same, for recursors.
    fn check_postponed_recursors(&mut self) -> Result<(), ReplayError> {
        for &rec in &self.postponed_recursors {
            let ok = match (self.env.get(rec), self.constants.get(&rec)) {
                (
                    Some(regenerated @ ConstantInfo::Rec(_)),
                    Some(decoded @ ConstantInfo::Rec(_)),
                ) => constant_info_eq(decoded, regenerated),
                _ => false,
            };
            if !ok {
                return Err(ReplayError {
                    decl: self.to_name(rec),
                    error: KernelError::RecursorMismatch(self.to_name(rec)),
                });
            }
        }
        Ok(())
    }
}

fn eq_name() -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: "Eq".to_string(),
    })
}

/// Resolve `Eq`'s persistent `NameId` (idempotent: interning an
/// already-present name returns its existing id, never a duplicate row).
/// The id-native environment has no direct `Arc<Name>`-keyed lookup the
/// way Arc `Environment::get` does, so `Eq` must be resolved to an id
/// before it can be looked up in `self.constants`/`self.env`.
fn intern_eq_name(env: &mut Environment) -> Result<NameId, KernelError> {
    env.intern_name(&eq_name())?
        .ok_or(KernelError::BankExhausted)
}

#[cfg(test)]
mod tests;
