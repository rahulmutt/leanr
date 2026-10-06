//! Command elaboration (M4c). M4c-2c-i: scope universe names and section
//! variables — `universe`/`variable`/`include`/`omit` and the per-kind
//! inclusion regimes (`vars.rs`, `scope.rs`), spec
//! `docs/superpowers/specs/2026-10-05-m4c2c-i-universe-variable-design.md`.
//! M4c-2b-i: scopes, `open` and declaration
//! names (`scope.rs`, `header.rs`'s `mkDeclName`), spec
//! `docs/superpowers/specs/2026-10-04-m4c2b-scopes-design.md`.
//! M4c-2a: a header-less source of many commands
//! (`elab_commands`), spec `docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md`.
//! M4c-1: a single non-recursive
//! `def`/`theorem`/`abbrev`/`opaque`/`axiom`/`example` becomes kernel
//! declarations (spec `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`,
//! plan `docs/superpowers/plans/2026-10-03-m4c1-p2-command-elab.md`).
//!
//! Files: `view.rs` decodes the command (oracle `mkDefView`) and raises the
//! out-of-scope seams; `header.rs` ports `expandDeclId` and `elabHeaders`'
//! per-view body; `def.rs` ports `finishElab` → `addPreDefinitions` →
//! `addNonRecAux` for `def`/`abbrev`/`opaque`/`example` (value, level
//! params, unassigned-mvar check, declaration build); `axiom.rs` builds an
//! `axiom`; `levels.rs` ports the term-level
//! `withLevelNames`/`levelMVarToParam`; `scope.rs` holds the scope stack
//! and the scope commands (including `universe`); `vars.rs` holds the
//! section-variable runner, `variable`/`include`/`omit` and the inclusion
//! helpers. This file owns [`CommandElab`],
//! the command dispatch and the kernel commit.

mod axiom;
mod def;
pub(crate) mod header;
mod levels;
mod scope;
mod vars;
pub(crate) mod view;

use leanr_kernel::bank::scratch::promote_name;
use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{check_declaration, Declaration, Environment};
use leanr_meta::{aux_lemma_key, AuxLemmaCache, Config, EnvExtensions, MetaCtx};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::dispatch::non_trivia_children;
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::names::NameTables;
use crate::resolve::ResolveCtx;
use scope::Scope;
use vars::SecVars;
use view::{expand_decl_namespace, DefKind, DefView};

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

/// What [`CommandElab::elab_commands`] did with a source's commands.
#[derive(Debug)]
pub struct FileOutcome {
    /// One entry per command elaborated successfully, in source order:
    /// its admitted names (aux `_proof_N` first, the main declaration
    /// last); empty for `example`.
    pub done: Vec<Vec<NameId>>,
    /// The first command that failed: its index and error. `None` = every
    /// command succeeded. Nothing after it was elaborated.
    pub stopped: Option<(usize, ElabError)>,
}

/// The command elaborator: an environment that grows by one declaration
/// per declaration command, and the oracle's scope stack
/// (spec § Architecture, Approach A).
///
/// Aux lemmas: the oracle's `mkAuxLemma` cache (`auxLemmasExt`,
/// `Meta/Tactic/AuxLemma.lean:29-30`, looked up at `:70-78`) is
/// ENVIRONMENT-wide: a later declaration whose nested proof has the type
/// (and level params) of an earlier `_proof_N` reuses that constant
/// instead of minting its own. `aux_cache` is that state; each declaration's
/// `AuxLemmas` is seeded from it.
pub struct CommandElab<'x> {
    env: Environment,
    exts: EnvExtensions<'x>,
    /// The environment's `auxLemmasExt` state (`Meta/Tactic/AuxLemma.lean:
    /// 29-30`): every admitted `_proof_N`'s type → (name, levelParams), in
    /// admission order, so a later same-type mint overwrites (`:68`).
    /// Environment-store ids only (see `commit`).
    aux_cache: AuxLemmaCache,
    /// The oracle's `Command.State.scopes`, bottom-up: index 0 is the root
    /// scope, the last entry the innermost (`scope.rs`).
    scopes: Vec<Scope>,
    /// `protectedExt`, `namespacesExt` and `aliasExtension`, grown as the
    /// source declares names and opens namespaces.
    tables: NameTables,
    /// The next section-variable uid (`elabVariable`'s fresh macro-scoped
    /// `varUIds`, `BuiltinCommand.lean:428`). The oracle's uids are only
    /// map keys, so a counter is enough.
    next_var_uid: u32,
}

impl<'x> CommandElab<'x> {
    pub fn new(env: Environment, exts: EnvExtensions<'x>, tables: NameTables) -> Self {
        CommandElab {
            env,
            exts,
            aux_cache: AuxLemmaCache::new(),
            scopes: vec![Scope::root()],
            tables,
            next_var_uid: 0,
        }
    }

    pub fn env(&self) -> &Environment {
        &self.env
    }

    pub fn into_env(self) -> Environment {
        self.env
    }

    /// Elaborate one command: a scope command (`namespace`, `section`,
    /// `end`, `open`, `… in …`) or a declaration. Returns the admitted
    /// constants' persistent names in admission order (aux `_proof_N`
    /// theorems first, the main declaration last); empty for `example` and
    /// the scope commands. On `Err`, the
    /// constants already admitted (aux theorems before a rejected main
    /// declaration) stay: the oracle's `mkAuxLemma` `addDecl`s them as it
    /// goes, and `liftCoreM` (`observing`, `Elab/Command.lean:219-220`) copies
    /// the CoreM env back into the command state even when the run throws
    /// (`runCore`, `:172-217`). Only declarations `Built::Add` carries
    /// count here; see `def::elab_def` for the pre-commit failure case.
    ///
    /// Every `UnsupportedSyntax` carries a slice label: a term- or
    /// binder-layer seam that has none (`"Lean.Parser.Term.sorry"`) gets
    /// ` — later M4` (`label_seam`).
    pub fn elab_command(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<Vec<NameId>, ElabError> {
        self.elab_command_unlabelled(cmd, kinds).map_err(label_seam)
    }

    /// Elaborate a header-less source's commands in order against this
    /// growing environment (the oracle frontend's command loop, threading
    /// one `Command.State`).
    ///
    /// Stops at the first error (spec decision 2). The oracle logs the error
    /// and goes on, but it has usually ADDED the failed declaration with
    /// `sorry` in place of the failing subterm (`errToSorry`), so every
    /// later command runs against an environment leanr does not have. Error
    /// recovery is a later slice. What the failed command committed before
    /// failing stays (`elab_command`'s contract).
    pub fn elab_commands(&mut self, cmds: &[SyntaxNode], kinds: &KindInterner) -> FileOutcome {
        let mut done = Vec::with_capacity(cmds.len());
        for (i, cmd) in cmds.iter().enumerate() {
            match self.elab_command(cmd, kinds) {
                Ok(names) => done.push(names),
                Err(e) => {
                    return FileOutcome {
                        done,
                        stopped: Some((i, e)),
                    }
                }
            }
        }
        FileOutcome {
            done,
            stopped: None,
        }
    }

    /// The command dispatch (oracle `elabCommand`'s table).
    fn elab_command_unlabelled(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<Vec<NameId>, ElabError> {
        let none = |r: Result<(), ElabError>| r.map(|()| Vec::new());
        match kinds.name(cmd.kind()) {
            "Lean.Parser.Command.namespace" => none(self.elab_namespace(cmd, kinds)),
            "Lean.Parser.Command.section" => none(self.elab_section(cmd, kinds)),
            "Lean.Parser.Command.end" => none(self.elab_end(cmd, kinds)),
            "Lean.Parser.Command.universe" => none(self.elab_universe(cmd, kinds)),
            "Lean.Parser.Command.variable" => none(self.elab_variable(cmd, kinds)),
            "Lean.Parser.Command.include" => none(self.elab_include(cmd, kinds)),
            "Lean.Parser.Command.omit" => none(self.elab_omit(cmd, kinds)),
            "Lean.Parser.Command.open" => none(self.elab_open(cmd, kinds)),
            "Lean.Parser.Command.set_option" => none(self.elab_set_option(cmd, kinds)),
            "Lean.Parser.Command.in" => self.elab_in(cmd, kinds),
            "Lean.Parser.Command.declaration" => self.elab_declaration(cmd, kinds),
            other => Err(command_seam(other)),
        }
    }

    /// oracle: `expandNamespacedDeclaration` (`Elab/Declaration.lean:
    /// 149-158`): `def A.B.f` is `namespace A.B def f end A.B`, so the
    /// namespace scopes are pushed around the declaration and always
    /// popped. Then `elabDeclaration` in the head scope.
    fn elab_declaration(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<Vec<NameId>, ElabError> {
        let mut view = DefView::from_syntax(cmd, kinds)?;
        let Some((ns, short)) = expand_decl_namespace(&view)? else {
            return self.elab_declaration_in_scope(&view, kinds);
        };
        self.add_scopes(&ns, true)?;
        view.name = Some(vec![short]);
        let out = self.elab_declaration_in_scope(&view, kinds);
        self.pop_scopes(ns.len());
        out
    }

    fn elab_declaration_in_scope(
        &mut self,
        view: &DefView,
        kinds: &KindInterner,
    ) -> Result<Vec<NameId>, ElabError> {
        let (built, mut scratch) = self.with_term_elab(kinds, |elab, sv| match view.kind {
            DefKind::Axiom => axiom::elab_axiom(elab, view, kinds, sv),
            _ => def::elab_def(elab, view, kinds, &self.aux_cache, sv),
        })?;
        let names = self.commit(&mut scratch, built)?;
        // `applyVisibility`'s `addProtected` (`DeclModifiers.lean:249-250`).
        if let (true, Some(&main)) = (view.protected, names.last()) {
            self.tables.add_protected(main);
        }
        Ok(names)
    }

    /// One scratch `TermElabM` over the environment with the head scope's
    /// resolution context, level names and section variables (oracle
    /// `runTermElabM`, `Elab/Command.lean:774-797`); `f` runs with the
    /// variables in the local context. Returns `f`'s result and the
    /// scratch store (for `commit`): one scratch store per run,
    /// `add_decl_in`'s scratch lifecycle contract
    /// (`leanr_kernel/src/env.rs`).
    fn with_term_elab<R>(
        &self,
        kinds: &KindInterner,
        f: impl FnOnce(&mut TermElabM, &SecVars) -> Result<R, ElabError>,
    ) -> Result<(R, Store), ElabError> {
        let mut scratch = Store::scratch();
        let out = {
            let env_view = self.env.view();
            let mctx = MetaCtx::new(env_view, &mut scratch, Config::default(), self.exts);
            let mut elab = TermElabM::new(mctx, env_view);
            let head = self.scopes.last().expect("the root scope is never popped");
            elab.resolve = ResolveCtx {
                ns: head.curr_namespace,
                open_decls: &head.open_decls,
                tables: &self.tables,
                aux_decl: None,
            };
            // `liftTermElabM`: the scope's `levelNames` seed the term context.
            elab.level_names = head.level_names.clone();
            elab.options = head.options;
            let fvars = vars::elab_section_vars(&mut elab, &head.var_decls, kinds)?;
            if fvars.len() != head.var_uids.len() {
                return Err(ElabError::Internal(
                    "section variables: one uid per binder id".into(),
                ));
            }
            let sv = SecVars {
                fvars,
                uids: head.var_uids.clone(),
                included: head.included_vars.clone(),
                omitted: head.omitted_vars.clone(),
            };
            f(&mut elab, &sv)
        }?;
        Ok((out, scratch))
    }

    /// oracle: `elabVariable` (`BuiltinCommand.lean:415-430`):
    /// `[<atom> "variable", null(bracketedBinder+)]`.
    pub(crate) fn elab_variable(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        let binders: Vec<SyntaxNode> = match non_trivia_children(cmd).get(1) {
            Some(NodeOrToken::Node(n)) => non_trivia_children(n)
                .into_iter()
                .map(|el| match el {
                    NodeOrToken::Node(b) => Ok(b),
                    NodeOrToken::Token(_) => Err(ElabError::IllFormedSyntax(
                        "variable: expected a bracketed binder".into(),
                    )),
                })
                .collect::<Result<_, _>>()?,
            _ => {
                return Err(ElabError::IllFormedSyntax(
                    "variable: expected a binder list".into(),
                ))
            }
        };
        // `replaceBinderAnnotation` (`:343-413`) acts on a typeless binder:
        // `(x)`/`{x}`/`⦃x⦄` always, `[x]` when `x` is a section variable.
        let head = self.scopes.last().expect("the root scope is never popped");
        let mut var_ids = Vec::new();
        for b in &head.var_decls {
            var_ids.extend(vars::bracketed_binder_ids(b, kinds)?);
        }
        for b in &binders {
            let update = vars::typeless_binder(b, kinds)
                || vars::inst_binder_ident(b, kinds)?.is_some_and(|id| var_ids.contains(&Some(id)));
            if update {
                return Err(ElabError::UnsupportedSyntax(
                    "variable binder-annotation update (`replaceBinderAnnotation`) — later M4"
                        .into(),
                ));
            }
        }
        // The sanity elaboration (`:419-425`): the scope's variables, then these.
        self.with_term_elab(kinds, |elab, _| {
            vars::elab_section_vars(elab, &binders, kinds).map(|_| ())
        })?;
        // `:427-429`: one fresh uid per binder id.
        let mut n_ids = 0usize;
        for b in &binders {
            n_ids += vars::bracketed_binder_ids(b, kinds)?.len();
        }
        let first = self.next_var_uid;
        let end = u32::try_from(n_ids)
            .ok()
            .and_then(|n| first.checked_add(n))
            .ok_or_else(|| ElabError::Internal("section variable uid overflow".into()))?;
        self.next_var_uid = end;
        let head = self
            .scopes
            .last_mut()
            .expect("the root scope is never popped");
        head.var_decls.extend(binders);
        head.var_uids.extend(first..end);
        Ok(())
    }

    fn commit(&mut self, scratch: &mut Store, built: Built) -> Result<Vec<NameId>, ElabError> {
        match built {
            Built::Check(d) => {
                check_declaration(self.env.view(), scratch, d).map_err(ElabError::Kernel)?;
                Ok(Vec::new())
            }
            Built::Add(decls) => {
                // `decls` = aux theorems ++ [main] (`def::elab_def`).
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
                let n_aux = decls.len().saturating_sub(1);
                for (i, d) in decls.into_iter().enumerate() {
                    self.env
                        .add_decl_in(scratch, d)
                        .map_err(ElabError::Kernel)?;
                    // `addDecl` → `registerNamePrefixes` (`AddDecl.lean:107`).
                    self.tables
                        .register_name_prefixes(self.env.store(), names[i]);
                    if i < n_aux {
                        // `mkAuxLemma` inserts right after the aux's own
                        // `addDecl` (`AuxLemma.lean:64-68`), so an aux stays
                        // cached even if the main declaration is then
                        // rejected. Read back from the ADMITTED constant:
                        // its type and names are environment-store ids,
                        // which the next declaration's scratch store
                        // resolves to (it interns through its base).
                        let cv = self
                            .env
                            .get(names[i])
                            .ok_or_else(|| {
                                ElabError::Internal(
                                    "admitted aux lemma is not in the environment".into(),
                                )
                            })?
                            .constant_val();
                        let (name, lps, ty) = (cv.name, cv.level_params.clone(), cv.ty);
                        // Keyed up to `Expr.eqv` (binder names/info
                        // ignored), as `mk_aux_lemma` looks it up.
                        let key = aux_lemma_key(self.env.store_mut(), None, ty)
                            .map_err(ElabError::Kernel)?;
                        self.aux_cache.insert(key, (name, lps));
                    }
                }
                Ok(names)
            }
        }
    }
}

/// Named-seam discipline at the command boundary: a seam message with no
/// ` — <slice label>` gets ` — later M4`. The term and binder layers name
/// their seams by kind alone (`"Lean.Parser.Level.paren"`,
/// `"fun: Lean.Parser.Term.matchAlts"`).
fn label_seam(e: ElabError) -> ElabError {
    match e {
        ElabError::UnsupportedSyntax(m) if !m.contains(" — ") => {
            ElabError::UnsupportedSyntax(format!("{m} — later M4"))
        }
        e => e,
    }
}

/// The named seam for a command `elab_command` does not port, labelled
/// with the slice that ports it (spec § Decomposition). Since M4c-2c-i
/// (`universe`/`variable`/`include`/`omit` became dispatch arms) every
/// remaining command is `— later M4`.
pub(crate) fn command_seam(kind: &str) -> ElabError {
    ElabError::UnsupportedSyntax(format!("command `{kind}` — later M4"))
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

#[cfg(test)]
mod tests {
    use super::*;

    fn msg(e: ElabError) -> String {
        match e {
            ElabError::UnsupportedSyntax(m) => m,
            e => panic!("expected a seam, got {e:?}"),
        }
    }

    #[test]
    fn unlabelled_seams_get_the_later_m4_label() {
        // `binder group: no names` is unreachable from source (the parser
        // needs at least one binder identifier), so it is pinned here.
        assert_eq!(
            msg(label_seam(ElabError::UnsupportedSyntax(
                "binder group: no names".into()
            ))),
            "binder group: no names — later M4"
        );
        assert_eq!(
            msg(label_seam(ElabError::UnsupportedSyntax(
                "`where` declarations — later M4".into()
            ))),
            "`where` declarations — later M4"
        );
        assert!(matches!(
            label_seam(ElabError::UnknownIdent("x".into())),
            ElabError::UnknownIdent(_)
        ));
    }

    #[test]
    fn aux_admitted_before_a_failed_main_is_cached() {
        // oracle: `mkAuxLemma` inserts into `auxLemmasExt` right after the
        // aux's own `addDecl` (`Meta/Tactic/AuxLemma.lean:64-68`), so the
        // entry survives the main declaration's rejection.
        use leanr_kernel::{
            BinderInfo, ConstantVal, DefinitionSafety, DefinitionVal, Nat, ReducibilityHints,
            TheoremVal,
        };
        let exts = EnvExtensions {
            reducibility: &[],
            matchers: &[],
            instances: &[],
            default_instances: &[],
            projection_fns: &[],
            classes: &[],
            coe_decls: &[],
            structures: &[],
            aux_recs: &[],
            elab_as_elim: &[],
        };
        let mut ce = CommandElab::new(Environment::default(), exts, NameTables::default());
        let mut scratch = Store::scratch();
        let (aux, main) = {
            let base = Some(ce.env.store());
            let s = &mut scratch;
            let zero = s.level_zero(base).unwrap();
            let prop = s.expr_sort(base, zero).unwrap();
            let b0 = s.expr_bvar(base, &Nat::from(0u64)).unwrap();
            let b1 = s.expr_bvar(base, &Nat::from(1u64)).unwrap();
            // `t._proof_1 : ∀ (p : Prop) (h : p), p := fun p h => h`
            let inner_ty = s
                .expr_forall(base, None, b0, b1, BinderInfo::Default)
                .unwrap();
            let ty = s
                .expr_forall(base, None, prop, inner_ty, BinderInfo::Default)
                .unwrap();
            let inner_val = s.expr_lam(base, None, b0, b0, BinderInfo::Default).unwrap();
            let value = s
                .expr_lam(base, None, prop, inner_val, BinderInfo::Default)
                .unwrap();
            let t = s.intern_str(base, "t").unwrap();
            let t = s.name_str(base, None, t).unwrap();
            let p1 = s.intern_str(base, "_proof_1").unwrap();
            let p1 = s.name_str(base, Some(t), p1).unwrap();
            let aux = Declaration::Thm(TheoremVal {
                val: ConstantVal {
                    name: p1,
                    level_params: vec![],
                    ty,
                },
                value,
                all: vec![p1],
            });
            // `def t : Prop := Prop` is ill-typed (`Prop : Type`): the
            // kernel rejects the main declaration after admitting the aux.
            let main = Declaration::Defn(DefinitionVal {
                val: ConstantVal {
                    name: t,
                    level_params: vec![],
                    ty: prop,
                },
                value: prop,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![t],
            });
            (aux, main)
        };
        let r = ce.commit(&mut scratch, Built::Add(vec![aux, main]));
        assert!(matches!(r, Err(ElabError::Kernel(_))), "{r:?}");
        assert_eq!(ce.env.len(), 1, "the aux stays admitted");
        assert_eq!(ce.aux_cache.len(), 1, "and cached");
        let (&ty, &(name, ref lps)) = ce.aux_cache.iter().next().unwrap();
        let cv = ce
            .env
            .get(name)
            .expect("cached name is admitted")
            .constant_val();
        assert_eq!(
            cv.ty, ty,
            "keyed by the admitted type (already alpha-canonical)"
        );
        assert!(lps.is_empty());
    }
}
