//! The elaborator's `Meta.Config`.
//!
//! oracle: `Lean.Elab.Term.setElabConfig` (`Elab/Config.lean:61-62`),
//! applied to the whole run by `TermElabM.run`'s
//! `withConfig setElabConfig` (`Elab/Term/TermElabM.lean:2226-2227`).
//! leanr's `TermElabM` owns its `MetaCtx` for its whole lifetime, so
//! `TermElabM::new` applies it once at construction.
//!
//! `ctx_approx` is set for fidelity but is inert in leanr: its rescue
//! lives in the oracle's slow `CheckAssignment.checkAssignmentAux`,
//! which `assign.rs` names as a SEAM
//! (`docs/superpowers/specs/2026-10-01-set-elab-config-design.md`).

use leanr_meta::Config;

/// oracle: `setElabConfig` (`Elab/Config.lean:61-62`):
/// `{ cfg with foApprox := true, ctxApprox := true, constApprox := false,
/// quasiPatternApprox := false }`.
pub fn set_elab_config(cfg: Config) -> Config {
    Config {
        fo_approx: true,
        ctx_approx: true,
        const_approx: false,
        quasi_pattern_approx: false,
        ..cfg
    }
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::Store;
    use leanr_kernel::Environment;
    use leanr_meta::{Config, EnvExtensions, MetaCtx, TransparencyMode};

    use super::set_elab_config;
    use crate::elab::TermElabM;

    /// Every field the oracle does not touch passes through. The input
    /// is non-default on purpose: each of the four approx fields is set
    /// to the opposite of its target, and `univ_approx` (default `true`)
    /// and `iota` are flipped, so that a rewrite that starts from
    /// `Config::default()` instead of `cfg` fails.
    #[test]
    fn set_elab_config_sets_the_four_approx_fields_and_nothing_else() {
        let input = Config {
            transparency: TransparencyMode::Reducible,
            fo_approx: false,
            ctx_approx: false,
            const_approx: true,
            quasi_pattern_approx: true,
            univ_approx: false,
            iota: false,
            ..Config::default()
        };
        let expected = Config {
            fo_approx: true,
            ctx_approx: true,
            const_approx: false,
            quasi_pattern_approx: false,
            ..input
        };
        assert_eq!(set_elab_config(input), expected);
    }

    /// `TermElabM::new` installs the elab config. A single-field scope
    /// (`with_transparency`) leaves it intact; the whole-cfg scope
    /// (`with_full_approx_def_eq`) restores it, not `Config::default()`
    /// (which would flip `fo_approx`/`ctx_approx` to false).
    #[test]
    fn term_elab_m_new_applies_elab_config() {
        let env = Environment::default();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions::default(),
        );
        let mut elab = TermElabM::new(mctx, view);
        let want = set_elab_config(Config::default());
        assert_eq!(elab.mctx.cfg(), want);
        elab.mctx
            .with_transparency(TransparencyMode::Reducible, |_| ());
        assert_eq!(elab.mctx.cfg(), want);
        elab.mctx.with_full_approx_def_eq(|_| ());
        assert_eq!(elab.mctx.cfg(), want);
    }
}
