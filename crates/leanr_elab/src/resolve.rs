//! Reduced name resolution. Oracle: `resolveName`
//! (`Lean/Elab/Term/TermElabM.lean:2170-2192`) over `resolveLocalName`
//! (`Lean/ResolveName.lean:460-622`) and `ResolveName.resolveGlobalName`
//! (`:194-216`), which split a dotted identifier into a head and trailing
//! field components.
//!
//! **Scope.** Global resolution is exact-name, with `currNamespace :=
//! .anonymous` and no `open`: the `open` / alias / `export` / `_root_`
//! slice owns `resolveUsingNamespace`, `resolveOpenDecls`, aliases and
//! `resolveExact`'s `_root_` stripping. Reserved names
//! (`realizeGlobalName`, e.g. `f.eq_1`) are not realized. The local side
//! has no auxiliary declarations (`let rec` / `where` has no producer), so
//! `matchAuxRecDecl?` and the `globalDeclFound` / `skipAuxDecl`
//! workaround, which only ever skips aux decls, have nothing to act on.
//!
//! The committed corpus stays fully-qualified so it never needs any of
//! that; when `open` lands, its own task adds a test exercising the
//! `AmbiguousIdent` branch below (kept wired now, unreachable until
//! then).

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::EnvView;
use leanr_meta::MetaCtx;

use crate::error::ElabError;

/// oracle: `resolveLocalName` (`ResolveName.lean:460-622`), reduced (see
/// the module doc). Its `loop` (`:595-621`) tries the whole name first and
/// then ever shorter prefixes; the first prefix that is a local's user
/// name wins, and the components it dropped become fields. `prefixes[k]`
/// names the first `k + 1` components. Returns the local and the number
/// of field components.
///
/// The order is the oracle's but is not observable yet: leanr interns a
/// binder's name as ONE component (`builtin/binder/mod.rs`'s
/// `intern_binder_name`), so only `prefixes[0]` can ever match.
pub fn resolve_local_name(mctx: &MetaCtx, prefixes: &[NameId]) -> Option<(ExprId, usize)> {
    let n = prefixes.len();
    prefixes
        .iter()
        .enumerate()
        .rev()
        .find_map(|(k, &p)| mctx.lctx_lookup_by_name(p).map(|fvar| (fvar, n - 1 - k)))
}

/// oracle: `ResolveName.resolveGlobalName` (`ResolveName.lean:194-216`)
/// with `ns := .anonymous` and no `open`s. Its `loop` strips trailing
/// components until what is left names a declared constant, so the
/// LONGEST declared prefix wins and the stripped components become
/// fields: `Nat.zero.succ` is `Nat.zero` plus the field `succ`, not
/// `Nat` plus `zero.succ`.
///
/// `display` is the identifier's raw source text, used verbatim in
/// either error. A prefix is often a SCRATCH-region `NameId`
/// (`app::head::intern_prefixes` mints one for any name not already
/// interned in the persistent store), which `view.store` alone cannot
/// render; see `app::head::unknown_ident_via_real_scratch_pipeline`.
pub fn resolve_global_name(
    view: &EnvView,
    prefixes: &[NameId],
    display: &str,
) -> Result<(NameId, usize), ElabError> {
    let n = prefixes.len();
    for (k, &p) in prefixes.iter().enumerate().rev() {
        // One namespace (the root) and no `open`s: at most one candidate
        // per prefix. The `AmbiguousIdent` arm is kept for the `open`
        // slice, whose candidates can number more than one.
        let candidates: Vec<NameId> = view.get(p).is_some().then_some(p).into_iter().collect();
        match candidates.len() {
            0 => continue,
            1 => return Ok((candidates[0], n - 1 - k)),
            _ => return Err(ElabError::AmbiguousIdent(display.to_string())),
        }
    }
    Err(ElabError::UnknownIdent(display.to_string()))
}

#[cfg(test)]
mod tests {
    use super::resolve_global_name;
    use leanr_kernel::bank::NameId;
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

    #[test]
    fn resolves_declared_global() {
        let (env, foo) = env_with_foo();
        let view = env.view();
        assert_eq!(resolve_global_name(&view, &[foo], "Foo").unwrap(), (foo, 0));
    }

    /// Unit-level check that an unresolved name (interned directly in
    /// the PERSISTENT store here — the scratch-region pipeline
    /// `app::head::elab_app_fn_id` actually drives is covered separately,
    /// by `app::head::tests::unknown_ident_via_real_scratch_pipeline`,
    /// since `resolve_global_name` alone can no longer reproduce that
    /// region-routing bug: it takes `display` verbatim from the caller
    /// instead of re-deriving it from a prefix through any store) still
    /// produces `UnknownIdent` with the caller-supplied display text.
    #[test]
    fn unknown_ident_when_not_declared() {
        let (mut env, _foo) = env_with_foo();
        let nope = name_id(&mut env, "Nope");
        let view = env.view();
        match resolve_global_name(&view, &[nope], "Nope") {
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
        {
            let view = env.view();
            assert_eq!(
                resolve_global_name(&view, &prefixes, "Foo.bar.baz").unwrap(),
                (foo, 2)
            );
        }
        admit_axiom(&mut env, foo_bar);
        let view = env.view();
        assert_eq!(
            resolve_global_name(&view, &prefixes, "Foo.bar.baz").unwrap(),
            (foo_bar, 1)
        );
    }
}
