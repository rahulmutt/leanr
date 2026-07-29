//! Reduction/defeq configuration, and the cache key derived from it.
//!
//! oracle: `Lean.Meta.Config` (src/Lean/Meta/Basic.lean) and its
//! `toKey`, toolchain leanprover/lean4:v4.33.0-rc1.
//!
//! # Why the cache key is derived from the whole struct
//!
//! A semantically relevant config field that is absent from the cache
//! key produces WRONG ANSWERS, and only under cache pressure — the
//! hardest possible failure to attribute. This is not speculative: Lean
//! shipped this bug twice in a mature codebase.
//!
//! - #13768: `TransparencyMode` was packed into two bits while having
//!   more than four constructors, so value 4 collided with the
//!   `foApprox` bit in the key.
//! - #13772: `Config.zetaUnused` was missing from `toKey` entirely.
//!
//! So the key hashes every field, and `ASSERT_CONFIG_SIZE` below breaks
//! the build when a field is added, forcing whoever adds it to decide
//! whether it belongs in the key rather than silently defaulting to
//! "no".
//!
//! # A deliberate subset of the oracle's fields
//!
//! The oracle's `Config`/`toKey` covers 19 fields; this `Config` covers
//! 16. That gap is intentional, not an oversight: `offset_cnstrs` and
//! `eta_struct` arrive with the features that consult them, and
//! `ASSERT_CONFIG_SIZE` forces
//! the cache-key decision at that point rather than letting a field
//! silently default to "unconsulted" (`assign_synthetic_opaque` was the
//! third such deferred field until M4b-3 P3 task 4, which added it
//! together with `withAssignableSyntheticOpaque`, the scope that turns
//! it on — see that field's own doc for which of this crate's
//! `syntheticOpaque` checks consult it, and which deliberately do not).
//! `isDefEqStuckEx` is spec-mandated
//! to become a typed error variant rather than a bool field, so it is
//! not tracked here at all.

use std::hash::{Hash, Hasher};

use crate::TransparencyMode;

/// How projections may reduce. `YesWithDelta` additionally unfolds the
/// structure's constructor application to expose the field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProjReduction {
    No,
    Yes,
    YesWithDelta,
    /// like `YesWithDelta` but caps the discriminant whnf at `.instances`
    /// transparency (oracle `ProjReductionKind.yesWithDeltaI`).
    YesWithDeltaI,
}

/// Reduction and unification configuration.
///
/// The five `*_approx` flags deliberately make higher-order unification
/// INCOMPLETE and order-dependent. They are not optimizations: they
/// define which terms unify, and therefore the accepted language. They
/// are explicit fields consulted at named call sites, never implicit
/// fallback behavior, so they can be audited against the oracle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Config {
    pub transparency: TransparencyMode,
    pub beta: bool,
    pub zeta: bool,
    pub zeta_delta: bool,
    pub proj: ProjReduction,
    pub fo_approx: bool,
    pub ctx_approx: bool,
    pub quasi_pattern_approx: bool,
    pub const_approx: bool,
    /// Use proof irrelevance in defeq: two proofs of the same `Prop`
    /// are equal. oracle: `Config.proofIrrelevance` (Basic.lean:138,
    /// default `true`), consulted by `isDefEqProofIrrel`
    /// (ExprDefEq.lean:1766).
    pub proof_irrelevance: bool,
    /// Oracle default is `true` (`Basic.lean:161`,
    /// `univApprox : Bool := true`) — unlike the other four
    /// `*_approx` flags, which default off. Do not "fix" this back to
    /// `false` to match its siblings; the oracle does not.
    pub univ_approx: bool,
    pub unification_hints: bool,
    /// Reduce recursor/matcher applications (iota). oracle: Basic.lean,
    /// `iota : Bool := true`; consulted by whnfCore's app arm
    /// (WHNF.lean:685 `unless cfg.iota do return e`).
    pub iota: bool,
    /// Drop `let x := v; e` when `x` does not occur in `e`. oracle:
    /// `zetaUnused : Bool := true`; takes precedence over zeta/zetaHave.
    pub zeta_unused: bool,
    /// Reduce nondependent lets (have) when zeta is enabled. oracle:
    /// Basic.lean, `zetaHave : Bool := true`; consulted by whnfCore's
    /// letE arm.
    pub zeta_have: bool,
    /// Allow `isDefEq` to assign a `syntheticOpaque` metavariable.
    /// oracle: `Config.assignSyntheticOpaque` (Basic.lean:145), scoped by
    /// `withAssignableSyntheticOpaque` (Basic.lean:1312-1313).
    ///
    /// Default `false` — the whole point of `syntheticOpaque` is that
    /// ordinary unification must not assign it. IN the cache key: it
    /// changes which terms unify, so two queries under different values
    /// are different questions (this module's own doc, and Lean's
    /// #13772; the oracle keeps it in `toKey` too, Basic.lean:209).
    ///
    /// The oracle turns it on in ELEVEN places, not one (fix round 1,
    /// review Minor 1 — this crate's own earlier claim of "exactly one
    /// caller" was carried over from the task brief unverified). Ten go
    /// through `withAssignableSyntheticOpaque`: `assignOutParams`
    /// (`Meta/SynthInstance.lean:842`), `synthesizeUsingDefaultInstance`
    /// (`Elab/SyntheticMVars.lean:164` — the one this plan ports, where a
    /// default instance must be able to assign an outParam mvar that
    /// `coeAtOutParam` marked opaque), and eight tactic-layer sites
    /// (`Elab/Tactic/ElabTerm.lean:58`/`:165`, `Simpa.lean:94`,
    /// `Change.lean:43`, `BuiltinTactic.lean:304`/`:311`/`:445`,
    /// `Induction.lean:182`). The eleventh sets the field directly:
    /// `Delaborator/TopDownAnalyze.lean:197`. Only
    /// `synthesizeUsingDefaultInstance` is in this milestone's scope;
    /// `assignOutParams` lives in the subsystem `synth.rs` ports and is
    /// not transcribed yet, so its absence is a missing feature, not a
    /// divergence.
    ///
    /// **NAMED SEAM — three of this crate's `syntheticOpaque` checks,
    /// two of which consult the flag.** In the oracle the flag is read
    /// inside `MVarId.isReadOnlyOrSyntheticOpaque` itself
    /// (`Basic.lean:979-986`), so every caller of THAT predicate is gated
    /// by it. This crate open-codes the predicate at three sites (the
    /// oracle's other two callers, `isAbstractedUnassignedMVar`
    /// `:99-109` and `isEtaUnassignedMVar` `:233-242`, are not
    /// transcribed here at all):
    ///
    /// - `assign.rs::unassigned_mvar_id` (`isAssignable`,
    ///   `ExprDefEq.lean:1731-1733`) — **gated.**
    /// - `lazy_delta.rs::is_def_eq_singleton`'s assignability check
    ///   (`isDefEqSingleton`'s `isAssignable sFn`,
    ///   `ExprDefEq.lean:2156` -> the same `isAssignable` at
    ///   `:1731-1733`) — **gated** in fix round 1: it is reachable from
    ///   inside an `isDefEq` (`is_def_eq_proj` -> `is_def_eq_singleton`),
    ///   so under an open scope an ungated copy would refuse an
    ///   assignment the oracle permits.
    /// - `discr_path.rs`'s discrimination-key builder
    ///   (`DiscrTree/Main.lean:308`) — **not gated,** and deliberately
    ///   so. The flag genuinely does survive into instance synthesis
    ///   (`isDefEqGuarded` -> `whnf` -> `synthPending` ->
    ///   `synthInstance?`, and `synthInstanceCore?`'s `withConfig`,
    ///   `SynthInstance.lean:963-964`, overrides six fields but not this
    ///   one), so the earlier "the oracle never runs it inside the scope"
    ///   claim was false. What actually makes the gate moot there is
    ///   `withNewMCtxDepth` (`SynthInstance.lean:978`): every mvar from
    ///   outside is at a different depth, so
    ///   `isReadOnlyOrSyntheticOpaque`'s FIRST arm
    ///   (`Basic.lean:981-982`) returns `true` before the kind is ever
    ///   examined. Depth is this crate's standing tier-1 seam
    ///   (`level.rs`'s module doc); wiring the flag in here without
    ///   modelling depth would flip `Star`/`Other` keys the oracle keeps
    ///   at `Other`.
    ///
    /// `whnf.rs`'s `synth_pending` guard is NOT on this list: the
    /// oracle's `synthPendingImp` (`SynthInstance.lean:1033-1036`)
    /// matches `mvarDecl.kind` DIRECTLY and never consults the config, so
    /// that site is faithful as written and gating it would introduce a
    /// divergence — TC synthesis running on a `syntheticOpaque` mvar the
    /// oracle refuses.
    pub assign_synthetic_opaque: bool,
}

/// Breaks the build when `Config` changes size — i.e. when a field is
/// added or removed. Whoever trips this must decide whether the new
/// field is semantically relevant to defeq and therefore belongs in
/// `cache_key`, then update this constant. See the module doc for the
/// two Lean bugs this guards against.
const ASSERT_CONFIG_SIZE: () = assert!(
    std::mem::size_of::<Config>() == 16,
    "Config changed size: a field was added or removed. Decide whether \
     it is semantically relevant to definitional equality and therefore \
     belongs in Config::cache_key, then update this assertion. A field \
     missing from the key produces wrong answers under cache pressure \
     only (see Lean #13768, #13772)."
);
const _: () = ASSERT_CONFIG_SIZE;

impl Default for Config {
    fn default() -> Config {
        Config {
            transparency: TransparencyMode::Default,
            beta: true,
            zeta: true,
            zeta_delta: true,
            proj: ProjReduction::YesWithDelta,
            fo_approx: false,
            ctx_approx: false,
            quasi_pattern_approx: false,
            const_approx: false,
            proof_irrelevance: true,
            // Oracle default: Basic.lean:161, `univApprox : Bool := true`.
            univ_approx: true,
            unification_hints: true,
            iota: true,
            zeta_unused: true,
            zeta_have: true,
            // Oracle default: Basic.lean:145,
            // `assignSyntheticOpaque : Bool := false`.
            assign_synthetic_opaque: false,
        }
    }
}

impl Config {
    /// Cache key covering EVERY field, via the derived `Hash`. Derived
    /// rather than hand-written precisely so that adding a field cannot
    /// silently omit it from the key — the field joins `Hash`
    /// automatically, and `ASSERT_CONFIG_SIZE` forces a human to notice.
    pub fn cache_key(&self) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut h);
        h.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{Config, ProjReduction};
    use crate::TransparencyMode;

    // Four of the five `*_approx` flags default off; `univ_approx` is the
    // exception and defaults ON, matching the oracle (Basic.lean:161,
    // `univApprox : Bool := true`). This is oracle fidelity, not a
    // blanket "approximations off" policy.
    #[test]
    fn default_matches_oracle_defaults() {
        let c = Config::default();
        assert_eq!(c.transparency, TransparencyMode::Default);
        assert!(!c.fo_approx);
        assert!(!c.ctx_approx);
        assert!(!c.quasi_pattern_approx);
        assert!(!c.const_approx);
        assert!(c.univ_approx);
        assert!(c.unification_hints);
        assert!(c.proof_irrelevance);
        // Basic.lean:145, `assignSyntheticOpaque : Bool := false` —
        // ordinary unification must not assign a syntheticOpaque mvar.
        assert!(!c.assign_synthetic_opaque);
    }

    // Plan-2 additions match the oracle defaults (Basic.lean): iota,
    // zetaUnused, zetaHave all default true.
    #[test]
    fn plan2_fields_default_on() {
        let c = Config::default();
        assert!(c.iota);
        assert!(c.zeta_unused);
        assert!(c.zeta_have);
    }

    #[test]
    fn equal_configs_share_a_key() {
        assert_eq!(Config::default().cache_key(), Config::default().cache_key());
    }

    // The #13768 shape: two configs differing ONLY in transparency must
    // not collide. Every level is checked against every other.
    #[test]
    fn every_transparency_level_gets_a_distinct_key() {
        let levels = [
            TransparencyMode::None,
            TransparencyMode::Reducible,
            TransparencyMode::Instances,
            TransparencyMode::Implicit,
            TransparencyMode::Default,
            TransparencyMode::All,
        ];
        let keys: Vec<u64> = levels
            .iter()
            .map(|&t| {
                Config {
                    transparency: t,
                    ..Config::default()
                }
                .cache_key()
            })
            .collect();
        for i in 0..keys.len() {
            for j in (i + 1)..keys.len() {
                assert_ne!(
                    keys[i], keys[j],
                    "{:?} and {:?} collide in the cache key",
                    levels[i], levels[j]
                );
            }
        }
    }

    // The #13772 shape: flipping ANY single field must change the key.
    // Written as one mutation per field so adding a field and forgetting
    // to test it is visible against ASSERT_CONFIG_SIZE.
    #[test]
    fn flipping_any_single_field_changes_the_key() {
        let base = Config::default();
        let k = base.cache_key();

        let mutations: Vec<Config> = vec![
            Config {
                transparency: TransparencyMode::All,
                ..base
            },
            Config {
                beta: !base.beta,
                ..base
            },
            Config {
                zeta: !base.zeta,
                ..base
            },
            Config {
                zeta_delta: !base.zeta_delta,
                ..base
            },
            Config {
                proj: ProjReduction::No,
                ..base
            },
            Config {
                fo_approx: !base.fo_approx,
                ..base
            },
            Config {
                ctx_approx: !base.ctx_approx,
                ..base
            },
            Config {
                quasi_pattern_approx: !base.quasi_pattern_approx,
                ..base
            },
            Config {
                const_approx: !base.const_approx,
                ..base
            },
            Config {
                univ_approx: !base.univ_approx,
                ..base
            },
            Config {
                unification_hints: !base.unification_hints,
                ..base
            },
            Config {
                iota: !base.iota,
                ..base
            },
            Config {
                zeta_unused: !base.zeta_unused,
                ..base
            },
            Config {
                zeta_have: !base.zeta_have,
                ..base
            },
            Config {
                proof_irrelevance: !base.proof_irrelevance,
                ..base
            },
            Config {
                assign_synthetic_opaque: !base.assign_synthetic_opaque,
                ..base
            },
        ];

        // One mutation per field: if this count drifts from the field
        // count, a field is untested.
        assert_eq!(mutations.len(), 16);

        for (i, m) in mutations.iter().enumerate() {
            assert_ne!(m.cache_key(), k, "mutation {i} did not change the key");
        }
    }

    #[test]
    fn proj_variants_are_distinct_in_the_key() {
        let base = Config::default();
        let a = Config {
            proj: ProjReduction::No,
            ..base
        }
        .cache_key();
        let b = Config {
            proj: ProjReduction::Yes,
            ..base
        }
        .cache_key();
        let c = Config {
            proj: ProjReduction::YesWithDelta,
            ..base
        }
        .cache_key();
        let d = Config {
            proj: ProjReduction::YesWithDeltaI,
            ..base
        }
        .cache_key();
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_ne!(a, c);
        assert_ne!(c, d);
        assert_ne!(a, d);
        assert_ne!(b, d);
    }
}
