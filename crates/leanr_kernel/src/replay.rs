//! Oracle-faithful replay of decoded modules (port of
//! src/Lean/Replay.lean). `replay` takes the union of one or more
//! decoded modules' `ConstantInfo`s and sends each declaration through
//! the kernel's admission pipeline (`Environment::add_decl`) in
//! dependency order, so an `Environment` built from untrusted `.olean`
//! bytes is checked from scratch rather than trusted.
//!
//! What replay does NOT send to the kernel: constructors and recursors.
//! Those are *regenerated* by the kernel when their inductive block is
//! admitted, and replay instead checks that each decoded ctor/recursor
//! is structurally identical (`constant_info_eq`, Task 11) to the
//! regenerated one. A missing or unequal ctor/recursor is a hard error
//! (`ConstructorMismatch`/`RecursorMismatch`).
//!
//! Everything here runs on UNTRUSTED input: the constants map, all
//! cross-references inside it, and the dependency chains between decls
//! are attacker-controlled. Nothing may panic. The oracle uses
//! `unreachable!`/`[n]!` at points that a well-formed module can never
//! reach; each becomes a real error for us (`MissingConstant`,
//! `InvalidInductive`). The recursion that follows dependency chains is
//! bounded and stack-safe via `RecGuard` (guard.rs).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::{
    constant_info_eq, ConstantInfo, Declaration, DefinitionSafety, InductiveType, KernelError,
    Name, RecGuard,
};

/// `KernelError` plus the declaration being replayed when it fired,
/// mirroring Replay.lean:135's `while replaying declaration '<name>'`
/// wrapping. Lives here rather than in `error.rs` because it is a
/// replay-layer concept (the `KernelError` list is the frozen kernel
/// vocabulary; `decl` is the replay driver's context around it).
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
/// modules-to-check's `ConstantInfo`s (decode order irrelevant); `env`
/// starts as the already-trusted base (empty for fresh checking) and is
/// extended in place with every admitted declaration.
pub fn replay(
    env: &mut crate::Environment,
    constants: HashMap<Arc<Name>, ConstantInfo>,
) -> Result<ReplayStats, ReplayError> {
    // Replay.lean:177-182 — seed `remaining` with every safe, non-partial
    // constant; count the rest as skipped without ever checking them.
    let mut remaining: HashSet<Arc<Name>> = HashSet::new();
    let mut skipped_unsafe = 0usize;
    for (n, ci) in &constants {
        if is_unsafe(ci) || is_partial(ci) {
            skipped_unsafe += 1;
        } else {
            remaining.insert(Arc::clone(n));
        }
    }

    let mut g = RecGuard::new();

    // Pre-intern the whole input through the env's interner so the input map
    // shares `Arc`s with what admission stores (`add_core` interns into the
    // same interner). Verdict-preserving. This eliminates the un-interned-
    // input double-count that otherwise peaks when the largest modules admit
    // last: their still-resident input would hold separate copies of subterms
    // the env already holds interned.
    let constants: HashMap<Arc<Name>, ConstantInfo> = {
        let mut interned = HashMap::with_capacity(constants.len());
        for (n, ci) in constants {
            let ci = env.intern_input(&ci, &mut g).map_err(|e| ReplayError {
                decl: Arc::clone(&n),
                error: e,
            })?;
            interned.insert(n, ci);
        }
        interned
    };

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
    let names: Vec<Arc<Name>> = st.remaining.iter().map(Arc::clone).collect();
    for n in names {
        st.replay_constant(n, &mut g).map_err(|e| st.wrap(e))?;
    }

    // Replay.lean:187-188 — the postponed structural checks.
    st.check_postponed_constructors(&mut g)?;
    st.check_postponed_recursors(&mut g)?;

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
    /// constant can be released once it has been successfully admitted into
    /// `env` (Change 2, M1b Task 16): as `env` grows the map shrinks, so the
    /// stdlib-sized `ConstantInfo` spine is not retained twice at peak.
    /// Constructors/recursors are never removed — they are re-read here for
    /// the postponed structural checks.
    constants: HashMap<Arc<Name>, ConstantInfo>,
    env: &'a mut crate::Environment,
    remaining: HashSet<Arc<Name>>,
    pending: HashSet<Arc<Name>>,
    postponed_constructors: HashSet<Arc<Name>>,
    postponed_recursors: HashSet<Arc<Name>>,
    checked: usize,
    /// The declaration being processed when the first `KernelError` fired
    /// during the recursive descent. The recursive core returns bare
    /// `KernelError` (so it can thread `RecGuard::enter`, which is typed
    /// to `KernelError`); this side channel records *which* declaration
    /// to attribute the failure to, set once and never overwritten so the
    /// innermost failing decl wins (matching the decl the oracle's
    /// innermost `catch` names).
    failing_decl: Option<Arc<Name>>,
}

impl Replayer<'_> {
    /// Build a `ReplayError` from a bare kernel error plus the recorded
    /// failing declaration.
    fn wrap(&self, error: KernelError) -> ReplayError {
        let decl = self
            .failing_decl
            .clone()
            .unwrap_or_else(|| Arc::new(Name::Anonymous));
        ReplayError { decl, error }
    }

    /// Record `name` as the failing declaration if none recorded yet, and
    /// return the error unchanged.
    fn blame(&mut self, name: &Arc<Name>, error: KernelError) -> KernelError {
        if self.failing_decl.is_none() {
            self.failing_decl = Some(Arc::clone(name));
        }
        error
    }

    /// Replay.lean:46-52 — if `name` still needs processing, move it from
    /// `remaining` to `pending` and return true.
    fn is_todo(&mut self, name: &Arc<Name>) -> bool {
        if self.remaining.remove(name) {
            self.pending.insert(Arc::clone(name));
            true
        } else {
            false
        }
    }

    /// Replay.lean:74-136 — `replayConstant`, threaded through `RecGuard`
    /// because dependency chains are attacker-controlled.
    fn replay_constant(&mut self, name: Arc<Name>, g: &mut RecGuard) -> Result<(), KernelError> {
        g.enter(|g| self.replay_constant_inner(name, g))
    }

    fn replay_constant_inner(
        &mut self,
        name: Arc<Name>,
        g: &mut RecGuard,
    ) -> Result<(), KernelError> {
        if !self.is_todo(&name) {
            return Ok(());
        }
        // Replay.lean:76 — `newConstants[name]? | unreachable!`. `name`
        // came from `remaining`, which only holds keys of `constants`, so
        // this lookup always succeeds; the fallback is defence in depth.
        let ci = match self.constants.get(&name) {
            Some(ci) => ci.clone(),
            None => return Err(self.blame(&name, KernelError::MissingConstant(Arc::clone(&name)))),
        };

        // Replay.lean:77 — replay dependencies first.
        for dep in crate::used_consts::used_constants(&ci) {
            self.replay_constant(dep, g)?;
        }

        // Replay.lean:79 — a mutual (inductive) block may already have
        // cleared this name; only act if it is still pending.
        if !self.pending.contains(&name) {
            return Ok(());
        }

        match &ci {
            ConstantInfo::Defn(v) => {
                self.add_decl(&name, Declaration::Defn(v.clone()))?;
            }
            ConstantInfo::Axiom(v) => {
                self.add_decl(&name, Declaration::Axiom(v.clone()))?;
            }
            ConstantInfo::Opaque(v) => {
                self.add_decl(&name, Declaration::Opaque(v.clone()))?;
            }
            ConstantInfo::Thm(v) => {
                // Replay.lean:84-97 — tolerate a duplicate theorem iff an
                // existing entry is a theorem with identical name, type,
                // level params, and `all`. (The module system can present
                // the same private theorem twice; we always load full
                // .olean data, so we may see the duplicate.)
                if let Some(ConstantInfo::Thm(existing)) = self.env.get(&name) {
                    if existing.val.name == v.val.name
                        && exprs_eq(&existing.val.ty, &v.val.ty, g)?
                        && names_eq(&existing.val.level_params, &v.val.level_params)
                        && names_eq(&existing.all, &v.all)
                    {
                        self.pending.remove(&name);
                        // Change 2: the theorem is already in `env` (as the
                        // tolerated duplicate); release the working copy.
                        self.constants.remove(&name);
                        return Ok(());
                    }
                }
                self.add_decl(&name, Declaration::Thm(v.clone()))?;
            }
            ConstantInfo::Induct(_) => {
                self.replay_inductive(&name, &ci, g)?;
            }
            // Replay.lean:124-128 — postpone; checked structurally at the
            // end against the kernel's regenerated version.
            ConstantInfo::Ctor(_) => {
                self.postponed_constructors.insert(Arc::clone(&name));
            }
            ConstantInfo::Rec(_) => {
                self.postponed_recursors.insert(Arc::clone(&name));
            }
            ConstantInfo::Quot(_) => {
                // Replay.lean:129-133 — `Quot.lift`/`Quot.ind` types
                // reference `Eq`, so replay `Eq` first, then admit the
                // single quotient declaration. Subsequent quot infos find
                // the env already quot-initialized and their `add_decl`
                // is a no-op re-init guarded inside `add_quot`.
                self.replay_constant(eq_name(), g)?;
                self.add_decl(&name, Declaration::Quot)?;
            }
        }

        self.pending.remove(&name);
        // Change 2 (M1b Task 16): this constant is now in `env`; release the
        // working copy so only `env` retains it. Constructors and recursors
        // are the exception — they are never admitted here (only postponed)
        // and `check_postponed_{constructors,recursors}` re-reads the decoded
        // value from `constants` at the end, so they must stay. `is_todo`
        // guarantees an already-admitted (hence removed) name is never read
        // from `constants` again — its dependency lookups short-circuit
        // before the `constants.get` on line ~206.
        if !matches!(ci, ConstantInfo::Ctor(_) | ConstantInfo::Rec(_)) {
            self.constants.remove(&name);
        }
        Ok(())
    }

    /// Replay.lean:102-120 — rebuild and admit a whole inductive block.
    fn replay_inductive(
        &mut self,
        name: &Arc<Name>,
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
        // block is admitted as a unit). `newConstants[n]!` → a missing
        // member is untrusted-input malformation, so `MissingConstant`.
        let mut members: Vec<ConstantInfo> = Vec::with_capacity(info.all.len());
        for n in &info.all {
            let member = self
                .constants
                .get(n)
                .cloned()
                .ok_or_else(|| self.blame(name, KernelError::MissingConstant(Arc::clone(n))))?;
            members.push(member);
        }
        for m in &members {
            let mn = m.name();
            self.remaining.remove(mn);
            self.pending.remove(mn);
        }

        // Replay.lean:109-119 — per member, gather its constructor infos
        // (in declared order) and build the `InductiveType`.
        let mut types: Vec<InductiveType> = Vec::with_capacity(members.len());
        let mut all_ctor_infos: Vec<ConstantInfo> = Vec::new();
        for member in &members {
            // Replay.lean:110 `ci.inductiveVal!` — a non-inductive member
            // is malformed; reject rather than panic.
            let ConstantInfo::Induct(miv) = member else {
                return Err(self.blame(
                    name,
                    KernelError::InvalidInductive {
                        name: Arc::clone(member.name()),
                        what: "mutual block member is not an inductive",
                    },
                ));
            };
            let mut ctor_pairs: Vec<(Arc<Name>, Arc<crate::Expr>)> =
                Vec::with_capacity(miv.ctors.len());
            for cn in &miv.ctors {
                let cinfo = self.constants.get(cn).cloned().ok_or_else(|| {
                    self.blame(name, KernelError::MissingConstant(Arc::clone(cn)))
                })?;
                ctor_pairs.push((
                    Arc::clone(cinfo.name()),
                    Arc::clone(&cinfo.constant_val().ty),
                ));
                all_ctor_infos.push(cinfo);
            }
            types.push(InductiveType {
                name: Arc::clone(&miv.val.name),
                ty: Arc::clone(&miv.val.ty),
                ctors: ctor_pairs,
            });
        }

        // Replay.lean:112-115 — make sure the constructors' own
        // dependencies are replayed before we admit the block.
        for cinfo in &all_ctor_infos {
            for dep in crate::used_consts::used_constants(cinfo) {
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
        // Change 2 (M1b Task 16): the whole block's inductive infos are now
        // in `env`; drop them from the working map. Their members were
        // already removed from `remaining`/`pending` above, so no later
        // `is_todo` will read them back. Constructors are NOT removed here —
        // they remain in `remaining` (processed later, then postponed) and
        // the postponed structural check re-reads them from `constants`.
        for m in &members {
            self.constants.remove(m.name());
        }
        Ok(())
    }

    /// `add_decl` wrapper that blames `name` on failure and counts the
    /// successful kernel admission.
    fn add_decl(&mut self, name: &Arc<Name>, d: Declaration) -> Result<(), KernelError> {
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
    fn check_postponed_constructors(&mut self, g: &mut RecGuard) -> Result<(), ReplayError> {
        for ctor in &self.postponed_constructors {
            let ok = match (self.env.get(ctor), self.constants.get(ctor)) {
                (
                    Some(regenerated @ ConstantInfo::Ctor(_)),
                    Some(decoded @ ConstantInfo::Ctor(_)),
                ) => constant_info_eq(decoded, regenerated, g).map_err(|e| ReplayError {
                    decl: Arc::clone(ctor),
                    error: e,
                })?,
                _ => false,
            };
            if !ok {
                return Err(ReplayError {
                    decl: Arc::clone(ctor),
                    error: KernelError::ConstructorMismatch(Arc::clone(ctor)),
                });
            }
        }
        Ok(())
    }

    /// Replay.lean:159-164 — same, for recursors.
    fn check_postponed_recursors(&mut self, g: &mut RecGuard) -> Result<(), ReplayError> {
        for rec in &self.postponed_recursors {
            let ok = match (self.env.get(rec), self.constants.get(rec)) {
                (
                    Some(regenerated @ ConstantInfo::Rec(_)),
                    Some(decoded @ ConstantInfo::Rec(_)),
                ) => constant_info_eq(decoded, regenerated, g).map_err(|e| ReplayError {
                    decl: Arc::clone(rec),
                    error: e,
                })?,
                _ => false,
            };
            if !ok {
                return Err(ReplayError {
                    decl: Arc::clone(rec),
                    error: KernelError::RecursorMismatch(Arc::clone(rec)),
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

fn names_eq(a: &[Arc<Name>], b: &[Arc<Name>]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x == y)
}

fn exprs_eq(
    a: &Arc<crate::Expr>,
    b: &Arc<crate::Expr>,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    crate::Expr::structural_eq(a, b, g)
}

#[cfg(test)]
mod tests;
