//! Reduced global-name resolution (design spec's "named seam" —
//! oracle: `Lean.Elab.resolveName`, `Lean/Elab/Extra.lean`/
//! `Lean/ResolveName.lean`).
//!
//! **Scope (Global Constraint: slice 1 only resolves global constants
//! declared with the name AS WRITTEN).** The real `resolveName` also
//! consults: the current namespace + every `open`ed namespace (prefix
//! search), `export`ed aliases, `_root_`-qualified names, local
//! variables/section variables in scope, and dot-notation
//! (`.foo`/`Struct.foo` via the expected type). None of that exists
//! yet — M4b-3/M4b-4 own `open`/alias/export/`_root_`/dot-notation.
//! The committed corpus stays fully-qualified so it never needs any of
//! that; when `open` lands, its own task adds a test exercising the
//! `AmbiguousIdent` branch below (kept wired now, unreachable until
//! then).

use leanr_kernel::bank::NameId;
use leanr_kernel::EnvView;

use crate::error::ElabError;

/// Reduced `Lean.Elab.resolveName`: resolve `name` against `view`'s
/// declared global constants only. Slice 1's candidate set is trivial —
/// `{name}` if `view` declares it, `{}` otherwise — so ambiguity cannot
/// yet arise (there is only ever one namespace to search: none). The
/// `AmbiguousIdent` branch is dead code today but stays wired for when
/// namespace-prefix search (M4b-3/4) can produce more than one
/// candidate; see the module doc.
///
/// `display` is the identifier's raw SOURCE TEXT (what the user actually
/// wrote — `elab_ident`'s own `tok.text()`), used verbatim in either
/// error's message. This is deliberate, not a shortcut: `name` may be a
/// SCRATCH-region `NameId` (`elab_ident`'s `intern_dotted` mints one for
/// any identifier not already interned in the persistent store — i.e.
/// every unknown identifier, the exact case that lands here) with no
/// meaning against `view.store` (the PERSISTENT store) alone —
/// `view.store.to_name(None, Some(name))` would route a scratch id's
/// index through `Store::store_for`'s `scratch_bit=true` branch, which
/// returns `self` (persistent) unconditionally, i.e. read the
/// PERSISTENT pool at the SCRATCH row's index: a wrong/garbage name, or
/// an out-of-bounds panic in `name_row`'s own `.expect(..)` if that
/// index exceeds the persistent pool's length. Taking `display` as the
/// already-known-correct text sidesteps that store round-trip entirely
/// rather than routing it through the right store.
pub fn resolve_global(view: &EnvView, name: NameId, display: &str) -> Result<NameId, ElabError> {
    let mut candidates: Vec<NameId> = Vec::new();
    if view.get(name).is_some() {
        candidates.push(name);
    }
    match candidates.len() {
        0 => Err(ElabError::UnknownIdent(display.to_string())),
        1 => Ok(candidates[0]),
        _ => Err(ElabError::AmbiguousIdent(display.to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::resolve_global;
    use leanr_kernel::bank::NameId;
    use leanr_kernel::{AxiomVal, ConstantInfo, ConstantVal, Environment};

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
        let prop = {
            let store = env.store_mut();
            let zero = store.level_zero(None).unwrap();
            store.expr_sort(None, zero).unwrap()
        };
        let foo = {
            let store = env.store_mut();
            let s = store.intern_str(None, "Foo").unwrap();
            store.name_str(None, None, s).unwrap()
        };
        let ci = ConstantInfo::Axiom(AxiomVal {
            val: ConstantVal {
                name: foo,
                level_params: vec![],
                ty: prop,
            },
            is_unsafe: false,
        });
        env.admit_unchecked(ci).unwrap();
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
        assert_eq!(resolve_global(&view, foo, "Foo").unwrap(), foo);
    }

    /// Unit-level check that an unresolved name (interned directly in
    /// the PERSISTENT store here — the scratch-region pipeline
    /// `elab_ident` actually drives is covered separately, by
    /// `builtin::ident::tests::unknown_ident_via_real_scratch_pipeline`,
    /// since `resolve_global` alone can no longer reproduce that
    /// region-routing bug: it takes `display` verbatim from the caller
    /// instead of re-deriving it from `name` through any store) still
    /// produces `UnknownIdent` with the caller-supplied display text.
    #[test]
    fn unknown_ident_when_not_declared() {
        let (mut env, _foo) = env_with_foo();
        let nope = name_id(&mut env, "Nope");
        let view = env.view();
        match resolve_global(&view, nope, "Nope") {
            Err(crate::ElabError::UnknownIdent(s)) => assert_eq!(s, "Nope"),
            other => panic!("expected UnknownIdent, got {other:?}"),
        }
    }
}
