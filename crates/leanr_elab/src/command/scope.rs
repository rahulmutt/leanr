//! Command scopes (oracle `Command.Scope`, `Elab/Command.lean`) and the
//! scope commands (`Elab/BuiltinCommand.lean:45-266, 312-316, 532-536`,
//! `Elab/Open.lean:38-118`).
//!
//! `CommandElab::scopes` is the oracle's `scopes` list stored bottom-up:
//! index 0 is the anonymous root scope, the LAST entry is the oracle's
//! head (the innermost scope). Every name a scope holds (namespace, open
//! declarations) is a persistent-store id, so each declaration's scratch
//! store resolves it through its base.

use leanr_kernel::bank::scratch::promote_name;
use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::EnvView;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use super::CommandElab;
use crate::app::head::ident_components;
use crate::dispatch::{non_trivia_children, SynElem};
use crate::error::ElabError;
use crate::names::{self, NameTables};
use crate::resolve::{resolve_global_name, resolve_namespace, OpenDecl, ResolveCtx};

/// oracle: `Command.Scope`, the fields M4c-2b-i ports.
#[derive(Clone, Debug)]
pub(crate) struct Scope {
    /// The decoded component this scope was opened with; `""` for an
    /// anonymous `section` (and the root).
    pub header: String,
    pub curr_namespace: Option<NameId>,
    /// NEWEST FIRST, as the oracle's list (`Elab/Open.lean:46` conses):
    /// `resolve_open_decls` / `resolve_namespace` walk it in this order.
    pub open_decls: Vec<OpenDecl>,
}

impl Scope {
    pub(crate) fn root() -> Scope {
        Scope {
            header: String::new(),
            curr_namespace: None,
            open_decls: Vec::new(),
        }
    }
}

fn ill(what: &str) -> ElabError {
    ElabError::IllFormedSyntax(format!("scope command: {what}"))
}

/// The identifier token at `el`, decoded (`getId`).
fn ident(el: Option<&SynElem>, kinds: &KindInterner) -> Result<Vec<String>, ElabError> {
    match el {
        Some(NodeOrToken::Token(t)) if kinds.name(t.kind()) == "<ident>" => {
            ident_components(t.text())
        }
        _ => Err(ill("expected an identifier")),
    }
}

/// The identifier tokens directly under the node at `el` (`ident+`,
/// separators skipped).
fn idents(el: Option<&SynElem>, kinds: &KindInterner) -> Result<Vec<Vec<String>>, ElabError> {
    let Some(NodeOrToken::Node(n)) = el else {
        return Err(ill("expected an identifier list"));
    };
    non_trivia_children(n)
        .iter()
        .map(|c| ident(Some(c), kinds))
        .collect()
}

fn node(el: Option<&SynElem>, what: &str) -> Result<SyntaxNode, ElabError> {
    match el {
        Some(NodeOrToken::Node(n)) => Ok(n.clone()),
        _ => Err(ill(what)),
    }
}

/// `comps` interned on top of `parent` (with `base`); the anonymous
/// `parent` and no components give `None`.
fn intern_onto(
    st: &mut Store,
    base: Option<&Store>,
    parent: Option<NameId>,
    comps: &[String],
) -> Result<Option<NameId>, ElabError> {
    let mut cur = parent;
    for c in comps {
        let s = st.intern_str(base, c).map_err(ElabError::Kernel)?;
        cur = Some(st.name_str(base, cur, s).map_err(ElabError::Kernel)?);
    }
    Ok(cur)
}

/// `n` and each of its prefixes, outermost first: `prefixes[k]` names the
/// first `k + 1` components (`resolve_global_name`'s input).
fn prefixes_of(st: &Store, base: Option<&Store>, n: NameId) -> Vec<NameId> {
    let mut out = vec![n];
    let mut cur = names::parent(st, base, n);
    while let Some(p) = cur {
        out.push(p);
        cur = names::parent(st, base, p);
    }
    out.reverse();
    out
}

/// `elabOpenDecl`'s local resolution state (`Elab/Open.lean:28-36`,
/// `StateRefT'.run'` at `:75`): a scratch store over the environment, the
/// head scope's namespace and a LOCAL copy of its open declarations, so
/// `open A B` resolves `B` with `A` already open.
struct OpenState<'a> {
    st: Store,
    view: EnvView<'a>,
    tables: &'a NameTables,
    ns: Option<NameId>,
    open_decls: Vec<OpenDecl>,
}

impl OpenState<'_> {
    fn base(&self) -> Option<&Store> {
        Some(self.view.store)
    }

    fn intern(&mut self, comps: &[String]) -> Result<NameId, ElabError> {
        let base = Some(self.view.store);
        intern_onto(&mut self.st, base, None, comps)?.ok_or_else(|| ill("empty identifier"))
    }

    fn render(&self, n: Option<NameId>) -> String {
        names::render(&self.st, self.base(), n)
    }

    /// `addOpenDecl` (`Open.lean:45-46`): cons.
    fn add_open_decl(&mut self, d: OpenDecl) {
        self.open_decls.insert(0, d);
    }

    /// oracle: `resolveNamespace` → `resolveNamespaceCore`
    /// (`ResolveName.lean:334-350`): every interpretation, none an error.
    fn resolve_namespace(&mut self, comps: &[String]) -> Result<Vec<Option<NameId>>, ElabError> {
        let id = self.intern(comps)?;
        let rc = ResolveCtx {
            ns: self.ns,
            open_decls: &self.open_decls,
            tables: self.tables,
            aux_decl: None,
        };
        let out = resolve_namespace(&mut self.st, &self.view, &rc, id)?;
        if out.is_empty() {
            return Err(ElabError::UnknownNamespace(self.render(Some(id))));
        }
        Ok(out)
    }

    /// oracle: `resolveUniqueNamespace` (`ResolveName.lean:353-356`).
    fn resolve_unique_namespace(&mut self, comps: &[String]) -> Result<Option<NameId>, ElabError> {
        let nss = self.resolve_namespace(comps)?;
        match nss.as_slice() {
            [ns] => Ok(*ns),
            _ => Err(ElabError::AmbiguousNamespace {
                id: comps.join("."),
                cands: nss.iter().map(|&n| self.render(n)).collect(),
            }),
        }
    }

    /// oracle: `OpenDecl.resolveId` (`Open.lean:38-43`): `ns ++ id` if
    /// declared, else `resolveGlobalConstNoOverloadCore (ns ++ id)`
    /// (`ResolveName.lean:359-380`: the candidates with no field
    /// components; none is `Unknown constant`, two or more ambiguous).
    fn resolve_id(&mut self, ns: Option<NameId>, id: &[String]) -> Result<NameId, ElabError> {
        let base = Some(self.view.store);
        let decl =
            intern_onto(&mut self.st, base, ns, id)?.ok_or_else(|| ill("empty identifier"))?;
        if self.view.get(decl).is_some() {
            return Ok(decl);
        }
        let prefixes = prefixes_of(&self.st, base, decl);
        let rc = ResolveCtx {
            ns: self.ns,
            open_decls: &self.open_decls,
            tables: self.tables,
            aux_decl: None,
        };
        let cands: Vec<NameId> = resolve_global_name(&mut self.st, &self.view, &rc, &prefixes)?
            .into_iter()
            .filter(|&(_, projs)| projs == 0)
            .map(|(c, _)| c)
            .collect();
        match cands.as_slice() {
            [] => Err(ElabError::UnknownConstant(self.render(Some(decl)))),
            [c] => Ok(*c),
            _ => Err(ElabError::UnsupportedSyntax(format!(
                "ambiguous identifier `{}` in `open` (`ensureNoOverload`'s \"Ambiguous \
                 identifier\" renders a `List Expr` of `mkConst`s, \
                 `ResolveName.lean:376`) — delab name rendering",
                self.render(Some(decl))
            ))),
        }
    }

    /// oracle: `resolveNameUsingNamespacesCore` (`Open.lean:53-72`): the
    /// per-namespace successes must be exactly one; when every namespace
    /// fails, one namespace's error is rethrown and several are `failed
    /// to open` (with the nested errors).
    fn resolve_name_using_namespaces(
        &mut self,
        nss: &[Option<NameId>],
        id: &[String],
    ) -> Result<NameId, ElabError> {
        let mut found = Vec::new();
        let mut errs = Vec::new();
        for &ns in nss {
            match self.resolve_id(ns, id) {
                Ok(n) => found.push(n),
                // `try … catch ex`: an oracle error, or the
                // `UnsupportedSyntax` of `resolve_id`'s delab seam, which
                // stands for an oracle `throwError` the catch would take.
                // `FailedToOpen`'s first line ignores its nested errors.
                Err(e) if e.is_oracle_error() || matches!(e, ElabError::UnsupportedSyntax(_)) => {
                    errs.push(e)
                }
                Err(e) => return Err(e),
            }
        }
        if errs.len() == nss.len() {
            if errs.len() == 1 {
                return Err(errs.remove(0));
            }
            return Err(ElabError::FailedToOpen(errs));
        }
        match found.as_slice() {
            [n] => Ok(*n),
            _ => Err(ElabError::UnsupportedSyntax(format!(
                "ambiguous identifier `{}` in `open` (`resolveNameUsingNamespacesCore`'s \
                 \"ambiguous identifier\" renders a `List Expr` of `mkConst`s, \
                 `Open.lean:72`) — delab name rendering",
                id.join(".")
            ))),
        }
    }
}

impl CommandElab<'_> {
    fn head(&self) -> &Scope {
        self.scopes.last().expect("the root scope is never popped")
    }

    /// oracle: `addScope` (`BuiltinCommand.lean:45-60`): register the
    /// namespace and push a copy of the head scope with the new header and
    /// namespace. `activateScoped` (new namespaces) is inert: no `scoped`
    /// entries exist (spec § Scopes).
    pub(crate) fn add_scope(&mut self, header: &str, new_ns: Option<NameId>) {
        self.tables.register_namespace(new_ns);
        let mut s = self.head().clone();
        s.header = header.to_string();
        s.curr_namespace = new_ns;
        self.scopes.push(s);
    }

    /// oracle: `addScopes` (`BuiltinCommand.lean:62-71`): one scope per
    /// component; a namespace's is `curr ++ comp`, a section keeps `curr`.
    /// On `Err` nothing stays pushed, so a caller pops only on `Ok`.
    pub(crate) fn add_scopes(
        &mut self,
        comps: &[String],
        is_new_ns: bool,
    ) -> Result<(), ElabError> {
        let depth = self.scopes.len();
        for c in comps {
            let curr = self.head().curr_namespace;
            let ns = if is_new_ns {
                match intern_onto(self.env.store_mut(), None, curr, std::slice::from_ref(c)) {
                    Ok(ns) => ns,
                    Err(e) => {
                        self.scopes.truncate(depth);
                        return Err(e);
                    }
                }
            } else {
                curr
            };
            self.add_scope(c, ns);
        }
        Ok(())
    }

    /// oracle: `popScopes` (`BuiltinCommand.lean:76-78`) with the
    /// `scopes.drop` before it.
    pub(crate) fn pop_scopes(&mut self, n: usize) {
        let keep = self.scopes.len().saturating_sub(n).max(1);
        self.scopes.truncate(keep);
    }

    /// oracle: `elabNamespace` (`BuiltinCommand.lean:101-104`):
    /// `[<atom> "namespace", <ident>]`.
    pub(crate) fn elab_namespace(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        let comps = ident(non_trivia_children(cmd).get(1), kinds)?;
        self.add_scopes(&comps, true)
    }

    /// oracle: `elabSection` (`BuiltinCommand.lean:106-118`):
    /// `[sectionHeader[@[expose]?, public?, noncomputable?, meta?],
    /// <atom> "section", null[<ident>?]]`. A modified section is a seam.
    pub(crate) fn elab_section(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        let ch = non_trivia_children(cmd);
        let header = node(ch.first(), "sectionHeader")?;
        if non_trivia_children(&header)
            .iter()
            .any(|s| !matches!(s, NodeOrToken::Node(n) if non_trivia_children(n).is_empty()))
        {
            return Err(ElabError::UnsupportedSyntax(
                "section modifier (`noncomputable`/`public`/`meta`/`@[expose]`) — later M4".into(),
            ));
        }
        let name = node(ch.get(2), "section name")?;
        match non_trivia_children(&name).first() {
            Some(id) => self.add_scopes(&ident(Some(id), kinds)?, false),
            None => {
                let curr = self.head().curr_namespace;
                self.add_scope("", curr);
                Ok(())
            }
        }
    }

    /// The decoded headers of the innermost `n` scopes, innermost LAST,
    /// stopping at the first anonymous one: oracle `nameOfScopes`
    /// (`BuiltinCommand.lean:130-136`) as components.
    fn name_of_scopes(&self, n: usize) -> Vec<String> {
        let mut out: Vec<String> = self
            .scopes
            .iter()
            .rev()
            .take(n)
            .take_while(|s| !s.header.is_empty())
            .map(|s| s.header.clone())
            .collect();
        out.reverse();
        out
    }

    /// oracle: `elabEnd` (`BuiltinCommand.lean:241-266`):
    /// `[<atom> "end", null[<ident>, null]?]`.
    pub(crate) fn elab_end(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        let opt = node(non_trivia_children(cmd).get(1), "end name")?;
        let header = match non_trivia_children(&opt).first() {
            Some(id) => Some(ident(Some(id), kinds)?),
            None => None,
        };
        self.end_scopes(header)
    }

    /// `elabEnd`'s body, from the decoded name after `end`.
    fn end_scopes(&mut self, header: Option<Vec<String>>) -> Result<(), ElabError> {
        let end_size = header.as_ref().map_or(1, Vec::len);
        let num_scopes = self.scopes.len();
        if num_scopes == 1 {
            return Err(ElabError::EndNoScope);
        }
        match &header {
            None => {
                // `innermostScopeName?`.
                let h = &self.head().header;
                if !h.is_empty() {
                    return Err(ElabError::EndMissingName(h.clone()));
                }
            }
            Some(h) => {
                if end_size >= num_scopes {
                    return Err(ElabError::EndTooManyComponents(h.join(".")));
                }
                let scopes_name = self.name_of_scopes(end_size);
                if &scopes_name != h {
                    if scopes_name.is_empty() {
                        return Err(ElabError::EndUnnecessaryName(h.join(".")));
                    }
                    return Err(ElabError::EndNameMismatch {
                        expected: scopes_name.join("."),
                        found: h.join("."),
                    });
                }
            }
        }
        self.pop_scopes(end_size);
        Ok(())
    }

    /// oracle: `elabOpen` (`BuiltinCommand.lean:312-316`) over
    /// `elabOpenDecl` (`Open.lean:74-118`): `[<atom> "open", openDecl]`.
    /// The head scope's open declarations become the local copy's.
    pub(crate) fn elab_open(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        let decl = node(non_trivia_children(cmd).get(1), "openDecl")?;
        let ch = non_trivia_children(&decl);
        let (open_decls, st) = {
            let head = self.head();
            let mut s = OpenState {
                st: Store::scratch(),
                view: self.env.view(),
                tables: &self.tables,
                ns: head.curr_namespace,
                open_decls: head.open_decls.clone(),
            };
            match kinds.name(decl.kind()) {
                // `$nss*` (`:77-83`).
                "Lean.Parser.Command.openSimple" => {
                    for ns in idents(ch.first(), kinds)? {
                        for r in s.resolve_namespace(&ns)? {
                            s.add_open_decl(OpenDecl::Simple {
                                ns: r,
                                except: Vec::new(),
                            });
                        }
                    }
                }
                // `$ns ($ids*)` (`:90-97`).
                "Lean.Parser.Command.openOnly" => {
                    let nss = s.resolve_namespace(&ident(ch.first(), kinds)?)?;
                    for id in idents(ch.get(2), kinds)? {
                        let decl = s.resolve_name_using_namespaces(&nss, &id)?;
                        let id = s.intern(&id)?;
                        s.add_open_decl(OpenDecl::Explicit { id, decl });
                    }
                }
                // `$ns hiding $ids*` (`:98-107`).
                "Lean.Parser.Command.openHiding" => {
                    let ns = s.resolve_unique_namespace(&ident(ch.first(), kinds)?)?;
                    let mut except = Vec::new();
                    for id in idents(ch.get(2), kinds)? {
                        s.resolve_id(ns, &id)?;
                        except.push(s.intern(&id)?);
                    }
                    s.add_open_decl(OpenDecl::Simple { ns, except });
                }
                // `$ns renaming $[$froms → $tos],*` (`:108-116`).
                "Lean.Parser.Command.openRenaming" => {
                    let ns = s.resolve_unique_namespace(&ident(ch.first(), kinds)?)?;
                    let items = node(ch.get(2), "renaming items")?;
                    for item in non_trivia_children(&items) {
                        let NodeOrToken::Node(item) = item else {
                            continue; // `,`
                        };
                        let parts = non_trivia_children(&item);
                        let from = ident(parts.first(), kinds)?;
                        let to = ident(parts.get(2), kinds)?;
                        let decl = s.resolve_id(ns, &from)?;
                        let id = s.intern(&to)?;
                        s.add_open_decl(OpenDecl::Explicit { id, decl });
                    }
                }
                "Lean.Parser.Command.openScoped" => {
                    return Err(ElabError::UnsupportedSyntax(
                        "`open scoped` (scoped extensions) — later M4".into(),
                    ))
                }
                other => return Err(ill(&format!("openDecl kind {other}"))),
            }
            (s.open_decls, s.st)
        };
        // Promote every name the scope keeps into the persistent store.
        let base = self.env.store_mut();
        let promote =
            |base: &mut Store, n: NameId| promote_name(base, &st, n).map_err(ElabError::Kernel);
        let mut promoted = Vec::with_capacity(open_decls.len());
        for d in open_decls {
            promoted.push(match d {
                OpenDecl::Simple { ns, except } => OpenDecl::Simple {
                    ns: ns.map(|n| promote(base, n)).transpose()?,
                    except: except
                        .into_iter()
                        .map(|n| promote(base, n))
                        .collect::<Result<_, _>>()?,
                },
                OpenDecl::Explicit { id, decl } => OpenDecl::Explicit {
                    id: promote(base, id)?,
                    decl: promote(base, decl)?,
                },
            });
        }
        self.scopes
            .last_mut()
            .expect("the root scope is never popped")
            .open_decls = promoted;
        Ok(())
    }

    /// oracle: `expandInCmd` (`BuiltinCommand.lean:532-536`): `cmd₁ in
    /// cmd₂` is `section cmd₁ end_local_scope cmd₂ end`
    /// (`[cmd₁, <atom> "in", cmd₂]`). `end_local_scope` only touches scoped
    /// extensions: inert. Returns both commands' admitted names.
    pub(crate) fn elab_in(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<Vec<NameId>, ElabError> {
        let ch = non_trivia_children(cmd);
        let cmd1 = node(ch.first(), "`in` command")?;
        let cmd2 = node(ch.get(2), "`in` body")?;
        let depth = self.scopes.len();
        let curr = self.head().curr_namespace;
        self.add_scope("", curr);
        let both = self
            .elab_command_unlabelled(&cmd1, kinds)
            .and_then(|mut names| {
                names.extend(self.elab_command_unlabelled(&cmd2, kinds)?);
                Ok(names)
            });
        let names = match both {
            Ok(names) => names,
            // The oracle logs the error and still runs the expansion's
            // `end`; drop the section (and anything `cmd₁` opened in it)
            // so nothing outlives the command.
            Err(e) => {
                self.scopes.truncate(depth);
                return Err(e);
            }
        };
        // The expansion's closing bare `end`: it errors if `cmd₂` left a
        // named scope open.
        self.end_scopes(None)?;
        Ok(names)
    }
}
