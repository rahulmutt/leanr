//! Command elaboration (M4c). M4c-1: a single non-recursive
//! `def`/`theorem`/`abbrev`/`opaque`/`axiom`/`example` becomes kernel
//! declarations (spec `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`,
//! plan `docs/superpowers/plans/2026-10-03-m4c1-p2-command-elab.md`).
//!
//! Files: `view.rs` decodes the command (oracle `mkDefView`) and raises the
//! out-of-scope seams; `header.rs` ports `expandDeclId` and `elabHeaders`'
//! per-view body; `def.rs` ports `finishElab` → `addPreDefinitions` →
//! `addNonRecAux` for `def`/`abbrev`/`opaque`/`example` (value, level
//! params, unassigned-mvar check, declaration build); `levels.rs` ports the
//! term-level `withLevelNames`/`levelMVarToParam`. This file owns
//! [`CommandElab`] and the kernel commit.

mod axiom;
mod def;
mod header;
mod levels;
pub(crate) mod view;

use leanr_kernel::bank::scratch::promote_name;
use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{check_declaration, Declaration, Environment};
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::elab::TermElabM;
use crate::error::ElabError;
use view::{DefKind, DefView};

/// What one declaration's elaboration scope hands to the commit step.
pub(crate) enum Built {
    /// Admit these in order: aux `_proof_N` theorems first, then the main
    /// declaration (each aux's `addDecl` precedes the main one's in the
    /// oracle, `Meta/Tactic/AuxLemma.lean:43-73`).
    Add(Vec<Declaration>),
    /// `example`: kernel-checked, then discarded (`withoutModifyingEnv`,
    /// `MutualDef.lean:1195-1203`).
    Check(Declaration),
}

/// The M4c-1 command elaborator: an environment that grows by one
/// declaration per [`CommandElab::elab_decl`] (spec § Architecture, Approach A).
pub struct CommandElab<'x> {
    env: Environment,
    exts: EnvExtensions<'x>,
}

impl<'x> CommandElab<'x> {
    pub fn new(env: Environment, exts: EnvExtensions<'x>) -> Self {
        CommandElab { env, exts }
    }

    pub fn env(&self) -> &Environment {
        &self.env
    }

    pub fn into_env(self) -> Environment {
        self.env
    }

    /// Elaborate one declaration command. Returns the admitted constants'
    /// persistent names in admission order (aux `_proof_N` theorems first,
    /// the main declaration last); empty for `example`. On `Err`, the
    /// constants already admitted (aux theorems before a rejected main
    /// declaration) stay: the oracle's `mkAuxLemma` `addDecl`s them as it
    /// goes, and `liftCoreM` (`observing`, `Elab/Command.lean:219-220`) copies
    /// the CoreM env back into the command state even when the run throws
    /// (`runCore`, `:172-217`). Only declarations `Built::Add` carries
    /// count here; see `def::elab_def` for the pre-commit failure case.
    pub fn elab_decl(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<Vec<NameId>, ElabError> {
        let view = DefView::from_syntax(cmd, kinds)?;
        // One scratch store per declaration: `add_decl_in`'s scratch
        // lifecycle contract (`leanr_kernel/src/env.rs`).
        let mut scratch = Store::scratch();
        let built = {
            let env_view = self.env.view();
            let mctx = MetaCtx::new(env_view, &mut scratch, Config::default(), self.exts);
            let mut elab = TermElabM::new(mctx, env_view);
            match view.kind {
                DefKind::Axiom => axiom::elab_axiom(&mut elab, &view, kinds),
                _ => def::elab_def(&mut elab, &view, kinds),
            }?
        };
        self.commit(&mut scratch, built)
    }

    fn commit(&mut self, scratch: &mut Store, built: Built) -> Result<Vec<NameId>, ElabError> {
        match built {
            Built::Check(d) => {
                check_declaration(self.env.view(), scratch, d).map_err(ElabError::Kernel)?;
                Ok(Vec::new())
            }
            Built::Add(decls) => {
                // Promote the names first: after the first `add_decl_in` the
                // scratch store may only be passed to further `add_decl_in`s.
                // `promote_name` only reads it.
                let mut names = Vec::with_capacity(decls.len());
                for d in &decls {
                    let n = decl_name(d)?;
                    names.push(
                        promote_name(self.env.store_mut(), scratch, n)
                            .map_err(ElabError::Kernel)?,
                    );
                }
                for d in decls {
                    self.env
                        .add_decl_in(scratch, d)
                        .map_err(ElabError::Kernel)?;
                }
                Ok(names)
            }
        }
    }
}

fn decl_name(d: &Declaration) -> Result<NameId, ElabError> {
    match d {
        Declaration::Axiom(v) => Ok(v.val.name),
        Declaration::Defn(v) => Ok(v.val.name),
        Declaration::Thm(v) => Ok(v.val.name),
        Declaration::Opaque(v) => Ok(v.val.name),
        _ => Err(ElabError::Internal(
            "command elaboration built an inductive/quot declaration".into(),
        )),
    }
}
