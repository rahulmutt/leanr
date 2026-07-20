//! The six-level transparency model and the unfolding predicate.
//!
//! oracle: `Lean.Meta.TransparencyMode` (src/Lean/Meta/TransparencyMode.lean)
//! and `canUnfoldDefault` (src/Lean/Meta/GetUnfoldableConst.lean),
//! toolchain leanprover/lean4:v4.33.0-rc1.
//!
//! There are SIX levels, not four: `implicit` was split out from
//! `instances` so that `@[implicit_reducible]` no longer carries the
//! side effects `@[instance_reducible]` has.
//!
//! THE ORDERING IS WRITTEN BY HAND AND NEVER DERIVED. In Lean the
//! constructor order of both `TransparencyMode` and `ReducibilityStatus`
//! deliberately does not match the unfolding order (a bootstrapping
//! constraint, documented in both source files). A `#[derive(PartialOrd)]`
//! here would silently produce a wrong hierarchy that still typechecks,
//! so `rank` is explicit and `PartialOrd`/`Ord` are derived from it
//! rather than from declaration order.

use leanr_olean::ReducibilityStatus;

/// How aggressively `whnf`/`is_def_eq` may unfold definitions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TransparencyMode {
    None,
    Reducible,
    Instances,
    Implicit,
    Default,
    All,
}

impl TransparencyMode {
    /// Explicit unfolding rank: `none < reducible < instances <
    /// implicit < default < all`. Hand-written — see the module doc.
    pub fn rank(self) -> u8 {
        match self {
            TransparencyMode::None => 0,
            TransparencyMode::Reducible => 1,
            TransparencyMode::Instances => 2,
            TransparencyMode::Implicit => 3,
            TransparencyMode::Default => 4,
            TransparencyMode::All => 5,
        }
    }
}

impl PartialOrd for TransparencyMode {
    fn partial_cmp(&self, other: &TransparencyMode) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TransparencyMode {
    fn cmp(&self, other: &TransparencyMode) -> std::cmp::Ordering {
        self.rank().cmp(&other.rank())
    }
}

/// May a constant with reducibility `status` be delta-unfolded at
/// transparency `mode`?
///
/// oracle: `canUnfoldDefault`. Transcribed as the specification rather
/// than reimplemented:
///
/// ```text
/// | .none    => false
/// | .all     => true
/// | .default => !isIrreducible
/// | m        => status == .reducible
///            || (status == .instanceReducible && (m == .instances || m == .implicit))
///            || (status == .implicitReducible && m == .implicit)
/// ```
///
/// `.implicit` unfolds for implicit-argument defeq and instance-diamond
/// resolution but stays OPAQUE to typeclass search, which runs at
/// `.instances`. Collapsing the two reintroduces the bug class Lean's
/// v4.29 change (PR #12179) set out to fix.
pub fn can_unfold(mode: TransparencyMode, status: ReducibilityStatus) -> bool {
    use ReducibilityStatus as S;
    use TransparencyMode as M;
    match mode {
        M::None => false,
        M::All => true,
        M::Default => status != S::Irreducible,
        M::Reducible | M::Instances | M::Implicit => {
            status == S::Reducible
                || (status == S::InstanceReducible && matches!(mode, M::Instances | M::Implicit))
                || (status == S::ImplicitReducible && matches!(mode, M::Implicit))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{can_unfold, TransparencyMode as M};
    use leanr_olean::ReducibilityStatus as S;

    #[test]
    fn ordering_is_the_unfolding_chain_not_declaration_order() {
        assert!(M::None < M::Reducible);
        assert!(M::Reducible < M::Instances);
        assert!(M::Instances < M::Implicit);
        assert!(M::Implicit < M::Default);
        assert!(M::Default < M::All);
    }

    #[test]
    fn none_unfolds_nothing() {
        for s in [
            S::Reducible,
            S::Semireducible,
            S::Irreducible,
            S::ImplicitReducible,
            S::InstanceReducible,
        ] {
            assert!(!can_unfold(M::None, s), "none must not unfold {s:?}");
        }
    }

    #[test]
    fn all_unfolds_everything_including_irreducible() {
        for s in [
            S::Reducible,
            S::Semireducible,
            S::Irreducible,
            S::ImplicitReducible,
            S::InstanceReducible,
        ] {
            assert!(can_unfold(M::All, s), "all must unfold {s:?}");
        }
    }

    #[test]
    fn default_unfolds_all_but_irreducible() {
        assert!(can_unfold(M::Default, S::Reducible));
        assert!(can_unfold(M::Default, S::Semireducible));
        assert!(can_unfold(M::Default, S::ImplicitReducible));
        assert!(can_unfold(M::Default, S::InstanceReducible));
        assert!(!can_unfold(M::Default, S::Irreducible));
    }

    #[test]
    fn reducible_mode_unfolds_only_reducible() {
        assert!(can_unfold(M::Reducible, S::Reducible));
        assert!(!can_unfold(M::Reducible, S::Semireducible));
        assert!(!can_unfold(M::Reducible, S::Irreducible));
        assert!(!can_unfold(M::Reducible, S::ImplicitReducible));
        assert!(!can_unfold(M::Reducible, S::InstanceReducible));
    }

    // The v4.29/v4.33 split: instance_reducible unfolds at BOTH
    // .instances and .implicit, but implicit_reducible unfolds ONLY at
    // .implicit. Collapsing these is the bug this test exists to catch.
    #[test]
    fn instances_and_implicit_differ_exactly_on_implicit_reducible() {
        assert!(can_unfold(M::Instances, S::InstanceReducible));
        assert!(can_unfold(M::Implicit, S::InstanceReducible));

        assert!(!can_unfold(M::Instances, S::ImplicitReducible));
        assert!(can_unfold(M::Implicit, S::ImplicitReducible));
    }

    #[test]
    fn semireducible_needs_default_or_higher() {
        assert!(!can_unfold(M::Reducible, S::Semireducible));
        assert!(!can_unfold(M::Instances, S::Semireducible));
        assert!(!can_unfold(M::Implicit, S::Semireducible));
        assert!(can_unfold(M::Default, S::Semireducible));
        assert!(can_unfold(M::All, S::Semireducible));
    }
}
