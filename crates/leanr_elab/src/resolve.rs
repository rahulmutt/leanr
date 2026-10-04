//! Name resolution. Oracle: `resolveName`
//! (`Lean/Elab/Term/TermElabM.lean:2170-2192`) over `resolveLocalName`
//! (`Lean/ResolveName.lean:460-622`) and `ResolveName.resolveGlobalName`
//! (`:194-216`), which split a dotted identifier into a head and trailing
//! field components.
//!
//! **Global side.** `resolve_global_name` is the oracle's candidate-list
//! `resolveGlobalName` against a [`ResolveCtx`]: the current namespace
//! (`resolveUsingNamespace`), `_root_` (`resolveExact`), the `open`
//! declarations (`resolveOpenDecls`) and aliases (`getAliases`). It returns
//! every candidate; a caller that needs one goes through [`expect_one`],
//! whose two-or-more arm is the overloaded-elaboration seam (M4c-2b-ii).
//! `resolve_namespace` is `ResolveName.resolveNamespace`. Not ported:
//! `resolvePrivateName` (unreachable: no module header, `private` is
//! seamed), reserved names (`containsDeclOrReserved` is `EnvView::get`;
//! `realizeGlobalName`, e.g. `f.eq_1`, is not realized) and macro scopes
//! (leanr names carry none, so `extractMacroScopes` is the identity).
//!
//! **Local side.** `resolve_local_name` ports `resolveLocalName` with
//! `matchAuxRecDecl?` and the `globalDeclFound` / `skipAuxDecl` workaround.
//! The only aux declaration is the one being defined (`let rec` / `where`
//! have no producer); leanr has no recursion, so matching it is the named
//! recursion seam.

use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::EnvView;

use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::names::{
    append, is_atomic, is_prefix_of, is_suffix_of, mk_atomic, parent, replace_prefix, NameTables,
};

/// oracle: `OpenDecl` (`Lean/Data/OpenDecl.lean:17-20`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OpenDecl {
    /// `open ns hiding except`.
    Simple {
        ns: Option<NameId>,
        except: Vec<NameId>,
    },
    /// `open N (x)` / `open N renaming x → id`: `id` stands for `decl`.
    Explicit { id: NameId, decl: NameId },
}

/// The declaration being defined: its full name and the short name its
/// aux local carries (`MutualDef.lean`'s `withAuxDecl shortDeclName`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuxDecl {
    pub full: NameId,
    pub short: NameId,
}

/// What resolution reads from the command scope: `currNamespace`,
/// `openDecls`, the environment's name tables and the declaration being
/// defined.
#[derive(Clone, Copy)]
pub struct ResolveCtx<'a> {
    pub ns: Option<NameId>,
    pub open_decls: &'a [OpenDecl],
    pub tables: &'a NameTables,
    pub aux_decl: Option<AuxDecl>,
}

impl ResolveCtx<'static> {
    /// The anonymous namespace, no `open`s, empty tables, no declaration:
    /// what a term-only caller resolves against.
    pub fn root() -> ResolveCtx<'static> {
        ResolveCtx {
            ns: None,
            open_decls: &[],
            tables: NameTables::empty(),
            aux_decl: None,
        }
    }
}

/// oracle: `resolveLocalName` (`ResolveName.lean:460-622`). Its `loop`
/// (`:595-621`) tries the whole name first and then ever shorter
/// prefixes; the first prefix that matches wins, and the components it
/// dropped become fields. `prefixes[k]` names the first `k + 1`
/// components. Per prefix, longest first:
/// 1. A regular local whose user name is the prefix wins
///    (`matchLocalDecl?`, `:468-471`; the reverse scan of `findLocalDecl?`,
///    `:555-577`). `intern_binder_name` (`builtin/binder/mod.rs`) interns
///    the decoded name, so only a `let` name can have more than one
///    component.
/// 2. Unless `skipAuxDecl`, the declaration being defined (`rc.aux_decl`,
///    installed by `withFunLocalDecls`, `MutualDef.lean:359-366`) is tried
///    with `matchAuxRecDecl?` (`:497-548`), then by exact user name (the
///    second pass, `:568-572`). leanr has no aux local to return, so a
///    hit is the recursion seam.
/// 3. Else, unless a global was already found, `resolveGlobalName` on the
///    prefix decides `globalDeclFound` for the next, shorter prefix
///    (`:600-618`).
///
/// The aux local is OUTERMOST in the oracle's context, so every regular
/// local is checked before it. Returns the local and its number of field
/// components; `Err` is the recursion seam (or an interning error).
pub fn resolve_local_name(
    elab: &mut TermElabM,
    prefixes: &[NameId],
) -> Result<Option<(ExprId, usize)>, ElabError> {
    let n = prefixes.len();
    let mut global_found = false;
    for (k, &given) in prefixes.iter().enumerate().rev() {
        let projs = n - 1 - k;
        if let Some(fvar) = elab.mctx.lctx_lookup_by_name(given) {
            return Ok(Some((fvar, projs)));
        }
        // `findLocalDecl? … (skipAuxDecl := globalDeclFound && !projs.isEmpty)`.
        let skip_aux = global_found && projs > 0;
        if !skip_aux {
            if let Some(aux) = elab.resolve.aux_decl {
                if match_aux_rec_decl(elab, aux, given)? || aux.short == given {
                    let base = Some(elab.view.store);
                    let shown = crate::names::render(elab.mctx.store(), base, Some(aux.short));
                    return Err(ElabError::UnsupportedSyntax(format!(
                        "recursive reference to `{shown}` — later M4 (recursion)"
                    )));
                }
            }
        }
        if !global_found
            && elab
                .resolve_global(&prefixes[..=k])?
                .iter()
                .any(|&(_, f)| f == 0)
        {
            global_found = true;
        }
    }
    Ok(None)
}

/// oracle: `matchAuxRecDecl?` (`ResolveName.lean:497-548`) for the
/// declaration being defined. leanr names carry no macro scopes and no
/// private prefix (`private` is seamed), so the views are the names.
/// When the current namespace is a prefix of the full name, the relaxed
/// match: the aux local's name is a suffix of the given name, which is a
/// suffix of the full name. Otherwise `go`: the given name under the
/// namespace or any enclosing one equals the full name.
fn match_aux_rec_decl(
    elab: &mut TermElabM,
    aux: AuxDecl,
    given: NameId,
) -> Result<bool, ElabError> {
    let base = Some(elab.view.store);
    let ns = elab.resolve.ns;
    let st = elab.mctx.store_mut();
    if is_prefix_of(st, base, ns, Some(aux.full)) {
        return Ok(is_suffix_of(st, base, Some(aux.short), Some(given))
            && is_suffix_of(st, base, Some(given), Some(aux.full)));
    }
    let mut cur = ns;
    loop {
        let cand = append(st, base, cur, Some(given)).map_err(leanr_meta::MetaError::from)?;
        if cand == Some(aux.full) {
            return Ok(true);
        }
        match cur {
            Some(c) if crate::names::last_str(st, base, c).is_some() => {
                cur = parent(st, base, c);
            }
            _ => return Ok(false),
        }
    }
}

/// oracle: `ResolveName.resolveGlobalName` (`ResolveName.lean:194-216`).
/// `prefixes[k]` names the identifier's first `k + 1` components (interned
/// with `base`, Global Constraints § Name identity). Returns every
/// candidate with its number of trailing field components; empty = not
/// found. `eraseDups` keeps first occurrences.
///
/// `loop` strips trailing components until some step finds a candidate,
/// so the LONGEST resolving prefix wins and the stripped components
/// become fields: `Nat.zero.succ` is `Nat.zero` plus the field `succ`,
/// not `Nat` plus `zero.succ`. `st` is the scratch store (`view.store`
/// its base): `ns ++ id` and friends are interned there.
pub fn resolve_global_name(
    st: &mut Store,
    view: &EnvView,
    rc: &ResolveCtx,
    prefixes: &[NameId],
) -> Result<Vec<(NameId, usize)>, ElabError> {
    let n = prefixes.len();
    for (k, &id) in prefixes.iter().enumerate().rev() {
        let projs = n - 1 - k;
        // `match resolveUsingNamespace … with | resolvedIds@(_ :: _) => …`.
        let mut found = resolve_using_namespace(st, view, rc, id, rc.ns)?;
        if found.is_empty() {
            if let Some(exact) = resolve_exact(st, view, id)? {
                return Ok(vec![(exact, projs)]);
            }
            if view.get(id).is_some() {
                found.push(id);
            }
            found = resolve_open_decls(st, view, rc, id, found)?;
            let mut al = rc
                .tables
                .get_aliases(id, is_atomic(st, Some(view.store), Some(id)));
            al.extend(found);
            found = al;
        }
        if !found.is_empty() {
            let mut seen = Vec::new();
            for c in found {
                if !seen.contains(&c) {
                    seen.push(c);
                }
            }
            return Ok(seen.into_iter().map(|c| (c, projs)).collect());
        }
    }
    Ok(Vec::new())
}

/// oracle: `resolveQualifiedName` (`ResolveName.lean:134-143`): `ns ++ id`
/// if declared and not (protected with `id` atomic), after the aliases of
/// `ns ++ id` (protected ones skipped for an atomic `id`).
fn resolve_qualified_name(
    st: &mut Store,
    view: &EnvView,
    rc: &ResolveCtx,
    ns: Option<NameId>,
    id: NameId,
) -> Result<Vec<NameId>, ElabError> {
    let base = Some(view.store);
    let resolved = append(st, base, ns, Some(id))
        .map_err(leanr_meta::MetaError::from)?
        .expect("`ns ++ id` with `id` non-anonymous is non-anonymous");
    let atomic = is_atomic(st, base, Some(id));
    let mut out = rc.tables.get_aliases(resolved, atomic);
    if (!atomic || !rc.tables.is_protected(resolved)) && view.get(resolved).is_some() {
        out.insert(0, resolved);
    }
    Ok(out)
}

/// oracle: `resolveUsingNamespace` (`ResolveName.lean:146-151`): `ns` and
/// then each enclosing namespace, innermost first, stopping at the first
/// with a hit. The root is never consulted (`| _ => []`), and neither is a
/// namespace ending in a numeric component.
fn resolve_using_namespace(
    st: &mut Store,
    view: &EnvView,
    rc: &ResolveCtx,
    id: NameId,
    ns: Option<NameId>,
) -> Result<Vec<NameId>, ElabError> {
    let base = Some(view.store);
    let mut cur = ns;
    while let Some(c) = cur {
        if crate::names::last_str(st, base, c).is_none() {
            break;
        }
        let found = resolve_qualified_name(st, view, rc, Some(c), id)?;
        if !found.is_empty() {
            return Ok(found);
        }
        cur = parent(st, base, c);
    }
    Ok(Vec::new())
}

/// The `_root_` name.
fn root_namespace(st: &mut Store, view: &EnvView) -> Result<NameId, ElabError> {
    Ok(mk_atomic(st, Some(view.store), "_root_").map_err(leanr_meta::MetaError::from)?)
}

/// oracle: `resolveExact` (`ResolveName.lean:154-162`): for a non-atomic
/// `id` only, `id` with a leading `_root_` dropped, if declared.
fn resolve_exact(st: &mut Store, view: &EnvView, id: NameId) -> Result<Option<NameId>, ElabError> {
    let base = Some(view.store);
    if is_atomic(st, base, Some(id)) {
        return Ok(None);
    }
    let root = root_namespace(st, view)?;
    let resolved = replace_prefix(st, base, Some(id), Some(root), None)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(resolved.filter(|&r| view.get(r).is_some()))
}

/// oracle: `resolveOpenDecls` (`ResolveName.lean:165-185`), each hit
/// prepended (`newResolvedIds ++ resolvedIds`). `simple ns exs`:
/// `resolveQualifiedName ns id` unless `id ∈ exs`. `explicit o r`: `r`
/// when `o == id`, else `id` with prefix `o` replaced by `r` when that is
/// declared.
fn resolve_open_decls(
    st: &mut Store,
    view: &EnvView,
    rc: &ResolveCtx,
    id: NameId,
    mut resolved: Vec<NameId>,
) -> Result<Vec<NameId>, ElabError> {
    let base = Some(view.store);
    for d in rc.open_decls {
        match d {
            OpenDecl::Simple { ns, except } => {
                if except.contains(&id) {
                    continue;
                }
                let mut new = resolve_qualified_name(st, view, rc, *ns, id)?;
                new.extend(resolved);
                resolved = new;
            }
            OpenDecl::Explicit { id: opened, decl } => {
                if *opened == id {
                    resolved.insert(0, *decl);
                } else if is_prefix_of(st, base, Some(*opened), Some(id)) {
                    let cand = replace_prefix(st, base, Some(id), Some(*opened), Some(*decl))
                        .map_err(leanr_meta::MetaError::from)?;
                    if let Some(c) = cand.filter(|&c| view.get(c).is_some()) {
                        resolved.insert(0, c);
                    }
                }
            }
        }
    }
    Ok(resolved)
}

/// One candidate, or the error the caller's oracle path raises: none is
/// `Unknown identifier`; two or more is overloaded elaboration
/// (`elabAppFnResolutions` → `elabAppAux` candidates), M4c-2b-ii.
pub fn expect_one(
    cands: Vec<(NameId, usize)>,
    display: &str,
) -> Result<(NameId, usize), ElabError> {
    match cands.len() {
        0 => Err(ElabError::UnknownIdent(display.to_string())),
        1 => Ok(cands[0]),
        n => Err(ElabError::UnsupportedSyntax(format!(
            "overloaded identifier `{display}` ({n} candidates) — M4c-2b-ii"
        ))),
    }
}

/// oracle: `ResolveName.resolveNamespace` (`ResolveName.lean:252-255`):
/// `resolveNamespaceUsingScope?` (`:220-230`; the innermost enclosing
/// namespace `ns'` with `ns' ++ id` a namespace, else at the root `id`
/// with `_root_` dropped) followed by `resolveNamespaceUsingOpenDecls`
/// (`:232-239`; every simple open `ns` with `ns ++ id` a namespace and
/// `id` not hidden). The result can be the anonymous namespace (`_root_`).
pub fn resolve_namespace(
    st: &mut Store,
    view: &EnvView,
    rc: &ResolveCtx,
    id: NameId,
) -> Result<Vec<Option<NameId>>, ElabError> {
    let base = Some(view.store);
    let mut out = Vec::new();
    let mut cur = rc.ns;
    loop {
        match cur {
            Some(c) => {
                // `| _ => unreachable!` on a numeric namespace: stop.
                if crate::names::last_str(st, base, c).is_none() {
                    break;
                }
                let cand =
                    append(st, base, Some(c), Some(id)).map_err(leanr_meta::MetaError::from)?;
                if rc.tables.is_namespace(cand) {
                    out.push(cand);
                    break;
                }
                cur = parent(st, base, c);
            }
            None => {
                let root = root_namespace(st, view)?;
                let cand = replace_prefix(st, base, Some(id), Some(root), None)
                    .map_err(leanr_meta::MetaError::from)?;
                if rc.tables.is_namespace(cand) {
                    out.push(cand);
                }
                break;
            }
        }
    }
    for d in rc.open_decls {
        if let OpenDecl::Simple { ns, except } = d {
            let cand = append(st, base, *ns, Some(id)).map_err(leanr_meta::MetaError::from)?;
            if rc.tables.is_namespace(cand) && !except.contains(&id) {
                out.push(cand);
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{expect_one, resolve_global_name, resolve_namespace, OpenDecl, ResolveCtx};
    use crate::names::NameTables;
    use leanr_kernel::bank::{NameId, Store};
    use leanr_kernel::{AxiomVal, ConstantInfo, ConstantVal, Environment};

    fn child(env: &mut Environment, parent: NameId, s: &str) -> NameId {
        let store = env.store_mut();
        let sid = store.intern_str(None, s).unwrap();
        store.name_str(None, Some(parent), sid).unwrap()
    }

    fn admit_axiom(env: &mut Environment, name: NameId) {
        let prop = {
            let store = env.store_mut();
            let zero = store.level_zero(None).unwrap();
            store.expr_sort(None, zero).unwrap()
        };
        env.admit_unchecked(ConstantInfo::Axiom(AxiomVal {
            val: ConstantVal {
                name,
                level_params: vec![],
                ty: prop,
            },
            is_unsafe: false,
        }))
        .unwrap();
    }

    /// A tiny environment declaring one axiom `Foo : Sort 0` (`Prop`),
    /// built directly against the public id-native `Environment`/
    /// `Store` API (`ConstantInfo`/`admit_unchecked`) rather than
    /// `leanr_kernel::testenv`'s Arc-based fixture helpers: `testenv` is
    /// a private, `#[cfg(test)]`-only module of `leanr_kernel` itself
    /// (`mod testenv;`, no `pub`), so it is never visible to an
    /// external crate's own test build — this crate has to build its
    /// own minimal fixture from the public surface instead.
    fn env_with_foo() -> (Environment, NameId) {
        let mut env = Environment::default();
        let foo = name_id(&mut env, "Foo");
        admit_axiom(&mut env, foo);
        (env, foo)
    }

    fn name_id(env: &mut Environment, s: &str) -> NameId {
        let store = env.store_mut();
        let sid = store.intern_str(None, s).unwrap();
        store.name_str(None, None, sid).unwrap()
    }

    /// The dotted name `s` and every prefix of it, interned persistently:
    /// `prefixes(env, "A.b")[k]` names the first `k + 1` components.
    fn prefixes(env: &mut Environment, s: &str) -> Vec<NameId> {
        let mut parts = s.split('.');
        let mut out = vec![name_id(env, parts.next().unwrap())];
        for p in parts {
            let last = *out.last().unwrap();
            out.push(child(env, last, p));
        }
        out
    }

    /// The dotted name `s`, interned persistently.
    fn dotted(env: &mut Environment, s: &str) -> NameId {
        *prefixes(env, s).last().unwrap()
    }

    fn rc<'a>(ns: Option<NameId>, open: &'a [OpenDecl], t: &'a NameTables) -> ResolveCtx<'a> {
        ResolveCtx {
            ns,
            open_decls: open,
            tables: t,
            aux_decl: None,
        }
    }

    fn resolve(env: &Environment, rc: &ResolveCtx, prefixes: &[NameId]) -> Vec<(NameId, usize)> {
        let mut scratch = Store::scratch();
        resolve_global_name(&mut scratch, &env.view(), rc, prefixes).unwrap()
    }

    #[test]
    fn resolves_declared_global() {
        let (env, foo) = env_with_foo();
        assert_eq!(resolve(&env, &ResolveCtx::root(), &[foo]), vec![(foo, 0)]);
    }

    /// An undeclared name has no candidates, and `expect_one` turns that
    /// into `UnknownIdent` with the caller-supplied display text (the
    /// scratch-region pipeline is covered by
    /// `app::head::tests::unknown_ident_via_real_scratch_pipeline`).
    #[test]
    fn unknown_ident_when_not_declared() {
        let (mut env, _foo) = env_with_foo();
        let nope = name_id(&mut env, "Nope");
        let cands = resolve(&env, &ResolveCtx::root(), &[nope]);
        assert!(cands.is_empty());
        match expect_one(cands, "Nope") {
            Err(crate::ElabError::UnknownIdent(s)) => assert_eq!(s, "Nope"),
            other => panic!("expected UnknownIdent, got {other:?}"),
        }
    }

    /// `resolveGlobalName`'s `loop` (ResolveName.lean:197-215): the longest
    /// declared prefix wins; the rest are fields.
    #[test]
    fn longest_declared_prefix_wins_and_the_rest_are_fields() {
        let (mut env, foo) = env_with_foo();
        let foo_bar = child(&mut env, foo, "bar");
        let foo_bar_baz = child(&mut env, foo_bar, "baz");
        let prefixes = [foo, foo_bar, foo_bar_baz];
        assert_eq!(
            resolve(&env, &ResolveCtx::root(), &prefixes),
            vec![(foo, 2)]
        );
        admit_axiom(&mut env, foo_bar);
        assert_eq!(
            resolve(&env, &ResolveCtx::root(), &prefixes),
            vec![(foo_bar, 1)]
        );
    }

    /// ResolveName.lean:146-151: the innermost namespace with a hit wins;
    /// the root is not consulted.
    #[test]
    fn enclosing_namespace_innermost_hit_wins() {
        let mut env = Environment::default();
        let w = name_id(&mut env, "w");
        let aw = dotted(&mut env, "A.w");
        let ab = dotted(&mut env, "A.B");
        let abw = dotted(&mut env, "A.B.w");
        admit_axiom(&mut env, w);
        admit_axiom(&mut env, aw);
        let t = NameTables::default();
        // `A.B.w` undeclared: the walk moves out to `A`, which hits, and
        // stops before the root.
        assert_eq!(resolve(&env, &rc(Some(ab), &[], &t), &[w]), vec![(aw, 0)]);
        // `A.B.w` declared: the innermost of two namespace hits wins.
        admit_axiom(&mut env, abw);
        assert_eq!(resolve(&env, &rc(Some(ab), &[], &t), &[w]), vec![(abw, 0)]);
    }

    /// :134-143: `ns ++ id` protected and `id` atomic → skipped; not atomic → found.
    #[test]
    fn protected_is_skipped_only_for_atomic_ids() {
        let mut env = Environment::default();
        let a = name_id(&mut env, "A");
        let ap = prefixes(&mut env, "A.p");
        let p = name_id(&mut env, "p");
        let cp = prefixes(&mut env, "C.p");
        let acp = dotted(&mut env, "A.C.p");
        admit_axiom(&mut env, ap[1]);
        admit_axiom(&mut env, acp);
        let t = NameTables::new(&[ap[1], acp], &[], &[]);
        let r = rc(Some(a), &[], &t);
        // Atomic `p`: `A.p` is protected, so the namespace walk skips it.
        assert_eq!(resolve(&env, &r, &[p]), vec![]);
        // `A.p` itself: resolveExact.
        assert_eq!(resolve(&env, &r, &ap), vec![(ap[1], 0)]);
        // Non-atomic `C.p` in namespace `A`: the protected `A.C.p` is found
        // by the namespace walk (nothing else could find it).
        assert_eq!(resolve(&env, &r, &cp), vec![(acp, 0)]);
    }

    /// :154-162: resolveExact strips `_root_` and applies only to non-atomic ids.
    #[test]
    fn root_prefix_is_stripped_by_resolve_exact() {
        let mut env = Environment::default();
        let a = name_id(&mut env, "A");
        let foo = name_id(&mut env, "Foo");
        let afoo = dotted(&mut env, "A.Foo");
        let root_foo = prefixes(&mut env, "_root_.Foo");
        admit_axiom(&mut env, foo);
        admit_axiom(&mut env, afoo);
        let t = NameTables::default();
        assert_eq!(
            resolve(&env, &rc(Some(a), &[], &t), &root_foo),
            vec![(foo, 0)]
        );

        // ns = A, `A.x` and root `x`: the namespace walk hits first.
        let x = name_id(&mut env, "x");
        let ax = dotted(&mut env, "A.x");
        admit_axiom(&mut env, x);
        admit_axiom(&mut env, ax);
        assert_eq!(resolve(&env, &rc(Some(a), &[], &t), &[x]), vec![(ax, 0)]);

        // Ruling R2's discriminator: at the root, an atomic `x` is NOT
        // resolveExact'd, so step 3 sees both `x` and the opened `S.x`
        // (`resolveOpenDecls` prepends its hits onto `[x]`).
        let s = name_id(&mut env, "S");
        let sx = dotted(&mut env, "S.x");
        admit_axiom(&mut env, sx);
        let open = [OpenDecl::Simple {
            ns: Some(s),
            except: vec![],
        }];
        assert_eq!(
            resolve(&env, &rc(None, &open, &t), &[x]),
            vec![(sx, 0), (x, 0)]
        );
    }

    /// :165-185: simple open with `except`; explicit with prefix replacement.
    #[test]
    fn open_decls_simple_hiding_and_explicit() {
        let mut env = Environment::default();
        let scope = name_id(&mut env, "Scope");
        let scope_k = dotted(&mut env, "Scope.k");
        let scope_k_sub = dotted(&mut env, "Scope.k.sub");
        let k_sub = prefixes(&mut env, "k.sub");
        let k = k_sub[0];
        admit_axiom(&mut env, scope_k);
        admit_axiom(&mut env, scope_k_sub);
        let t = NameTables::default();

        let open = [OpenDecl::Simple {
            ns: Some(scope),
            except: vec![],
        }];
        assert_eq!(
            resolve(&env, &rc(None, &open, &t), &[k]),
            vec![(scope_k, 0)]
        );

        let hiding = [OpenDecl::Simple {
            ns: Some(scope),
            except: vec![k],
        }];
        assert_eq!(resolve(&env, &rc(None, &hiding, &t), &[k]), vec![]);

        let explicit = [OpenDecl::Explicit {
            id: k,
            decl: scope_k,
        }];
        assert_eq!(
            resolve(&env, &rc(None, &explicit, &t), &[k]),
            vec![(scope_k, 0)]
        );
        assert_eq!(
            resolve(&env, &rc(None, &explicit, &t), &k_sub),
            vec![(scope_k_sub, 0)]
        );
    }

    /// :68-81, :210: aliases are prepended; protected targets skipped for atomic ids.
    #[test]
    fn aliases_resolve_at_the_root() {
        let mut env = Environment::default();
        let ex = name_id(&mut env, "ex");
        let b_ex = dotted(&mut env, "B.ex");
        let ex2 = name_id(&mut env, "ex2");
        let b_ex2 = dotted(&mut env, "B.ex2");
        admit_axiom(&mut env, b_ex);
        admit_axiom(&mut env, b_ex2);
        let t = NameTables::new(&[b_ex2], &[], &[(ex, b_ex), (ex2, b_ex2)]);
        assert_eq!(resolve(&env, &rc(None, &[], &t), &[ex]), vec![(b_ex, 0)]);
        assert_eq!(resolve(&env, &rc(None, &[], &t), &[ex2]), vec![]);
        // Prepended: the alias target comes before a declared `ex`.
        admit_axiom(&mut env, ex);
        assert_eq!(
            resolve(&env, &rc(None, &[], &t), &[ex]),
            vec![(b_ex, 0), (ex, 0)]
        );
    }

    /// :204-212: root hit plus an open hit are BOTH returned (two candidates).
    #[test]
    fn two_candidates_are_returned_and_expect_one_seams() {
        let mut env = Environment::default();
        let shown = name_id(&mut env, "shown");
        let scope0 = name_id(&mut env, "Scope0");
        let scope0_shown = dotted(&mut env, "Scope0.shown");
        admit_axiom(&mut env, shown);
        admit_axiom(&mut env, scope0_shown);
        let t = NameTables::default();
        let open = [OpenDecl::Simple {
            ns: Some(scope0),
            except: vec![],
        }];
        let cands = resolve(&env, &rc(None, &open, &t), &[shown]);
        assert_eq!(cands.len(), 2, "{cands:?}");
        match expect_one(cands, "shown") {
            Err(crate::ElabError::UnsupportedSyntax(m)) => assert!(
                m.contains("overloaded identifier `shown` (2 candidates) — M4c-2b-ii"),
                "{m}"
            ),
            other => panic!("expected the M4c-2b-ii seam, got {other:?}"),
        }
        assert_eq!(expect_one(vec![(shown, 1)], "shown").unwrap(), (shown, 1));
    }

    /// :252-255 + :220-239: scope first (innermost), then open decls; `_root_` stripped at the root.
    #[test]
    fn resolve_namespace_scope_then_open_decls() {
        let mut env = Environment::default();
        let a = name_id(&mut env, "A");
        let c = name_id(&mut env, "C");
        let ac = dotted(&mut env, "A.C");
        let x = name_id(&mut env, "X");
        let xc = dotted(&mut env, "X.C");
        let root_c = dotted(&mut env, "_root_.C");
        let t = NameTables::new(&[], &[Some(a), Some(ac), Some(c), Some(x), Some(xc)], &[]);
        let view = env.view();
        let mut st = Store::scratch();
        // Scope stops at the first hit: `A.C`, not also the root `C`.
        assert_eq!(
            resolve_namespace(&mut st, &view, &rc(Some(a), &[], &t), c).unwrap(),
            vec![Some(ac)]
        );
        let open = [OpenDecl::Simple {
            ns: Some(x),
            except: vec![],
        }];
        assert_eq!(
            resolve_namespace(&mut st, &view, &rc(Some(a), &open, &t), c).unwrap(),
            vec![Some(ac), Some(xc)]
        );
        // At the root, `_root_` is stripped.
        assert_eq!(
            resolve_namespace(&mut st, &view, &rc(None, &[], &t), root_c).unwrap(),
            vec![Some(c)]
        );
        // `except` hides an opened namespace too.
        let hiding = [OpenDecl::Simple {
            ns: Some(x),
            except: vec![c],
        }];
        assert_eq!(
            resolve_namespace(&mut st, &view, &rc(None, &hiding, &t), c).unwrap(),
            vec![Some(c)]
        );
    }
}
