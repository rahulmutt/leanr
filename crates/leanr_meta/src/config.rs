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

use std::hash::{Hash, Hasher};

use crate::TransparencyMode;

/// How projections may reduce. `YesWithDelta` additionally unfolds the
/// structure's constructor application to expose the field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProjReduction {
    No,
    Yes,
    YesWithDelta,
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
    pub eta: bool,
    pub zeta: bool,
    pub zeta_delta: bool,
    pub proj: ProjReduction,
    pub fo_approx: bool,
    pub ctx_approx: bool,
    pub quasi_pattern_approx: bool,
    pub const_approx: bool,
    pub univ_approx: bool,
    pub unification_hints: bool,
}

/// Breaks the build when `Config` changes size — i.e. when a field is
/// added or removed. Whoever trips this must decide whether the new
/// field is semantically relevant to defeq and therefore belongs in
/// `cache_key`, then update this constant. See the module doc for the
/// two Lean bugs this guards against.
const ASSERT_CONFIG_SIZE: () = assert!(
    std::mem::size_of::<Config>() == 12,
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
            eta: true,
            zeta: true,
            zeta_delta: true,
            proj: ProjReduction::YesWithDelta,
            fo_approx: false,
            ctx_approx: false,
            quasi_pattern_approx: false,
            const_approx: false,
            univ_approx: false,
            unification_hints: true,
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

    #[test]
    fn default_is_default_transparency_with_no_approximations() {
        let c = Config::default();
        assert_eq!(c.transparency, TransparencyMode::Default);
        assert!(!c.fo_approx);
        assert!(!c.ctx_approx);
        assert!(!c.quasi_pattern_approx);
        assert!(!c.const_approx);
        assert!(!c.univ_approx);
        assert!(c.unification_hints);
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
                eta: !base.eta,
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
        ];

        // One mutation per field: if this count drifts from the field
        // count, a field is untested.
        assert_eq!(mutations.len(), 12);

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
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_ne!(a, c);
    }
}
