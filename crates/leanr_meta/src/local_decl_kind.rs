//! `LocalDeclKind`: whether a local declaration takes part in type-class
//! resolution. oracle: `Lean.LocalDeclKind` (`Lean/LocalContext.lean:23`),
//! minus `auxDecl` (recursive-call auxiliaries; leanr has no `let rec`
//! producer).
//!
//! The kind is NOT stored on the declaration: `LocalDecl` lives in
//! `leanr_kernel`, which this crate does not change. The caller decides it
//! at push time and `MetaCtx::install_local_instance_for` consumes it
//! there. The oracle's only other elaborator-side reader,
//! `withLocalInstancesImp` (`Lean/Meta/Basic.lean:1937`, whose
//! `isImplementationDetail` test is `:1941`, reached from
//! `Lean/Elab/Match.lean:826`), belongs to the match slice.

use leanr_kernel::bank::names::NameRow;
use leanr_kernel::bank::{NameId, Store};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalDeclKind {
    /// Takes part in type-class resolution. Every declaration the oracle
    /// pushes WITHOUT `kind := .ofBinderName` — telescopes,
    /// implicit-lambda binders, eta arguments — whatever its name.
    Default,
    /// Invisible to type-class resolution: a user-written binder whose
    /// name's root component starts with `__`.
    ImplDetail,
}

impl LocalDeclKind {
    /// oracle: `LocalDeclKind.ofBinderName` (`Lean/Elab/BindersUtil.lean:21-25`)
    /// over `Name.isImplementationDetail` (`Lean/Data/Name.lean:167-171`):
    ///
    /// ```lean
    /// def isImplementationDetail : Name → Bool
    ///   | str anonymous s => s.startsWith "__"
    ///   | num p _ => p.isImplementationDetail
    ///   | str p _ => p.isImplementationDetail
    ///   | anonymous => false
    /// ```
    ///
    /// Only the ROOT component is tested. A loop, because name parent
    /// chains are attacker-depth. `store`/`base` are the usual pair for a
    /// `Store` read: the scratch store and its persistent base.
    ///
    /// Call this only where the oracle passes `kind := .ofBinderName` —
    /// see `leanr_elab`'s `builtin/binder/mod.rs`, `user_binder_kind`.
    pub fn of_binder_name(
        store: &Store,
        base: Option<&Store>,
        name: Option<NameId>,
    ) -> LocalDeclKind {
        let Some(mut id) = name else {
            return LocalDeclKind::Default;
        };
        loop {
            match store.name_row(base, id) {
                NameRow::Str {
                    parent: Some(p), ..
                }
                | NameRow::Num {
                    parent: Some(p), ..
                } => id = *p,
                NameRow::Str { parent: None, part } => {
                    return if store.str_at(base, *part).starts_with("__") {
                        LocalDeclKind::ImplDetail
                    } else {
                        LocalDeclKind::Default
                    };
                }
                NameRow::Num { parent: None, .. } => return LocalDeclKind::Default,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::{NameId, Store};
    use leanr_kernel::Nat;

    use super::LocalDeclKind;

    fn str_name(store: &mut Store, parent: Option<NameId>, s: &str) -> NameId {
        let part = store.intern_str(None, s).expect("intern");
        store.name_str(None, parent, part).expect("name")
    }

    fn kind(store: &Store, name: NameId) -> LocalDeclKind {
        LocalDeclKind::of_binder_name(store, None, Some(name))
    }

    /// oracle: `Name.isImplementationDetail`'s base case
    /// (`Lean/Data/Name.lean:168`), `str anonymous s => s.startsWith "__"`.
    #[test]
    fn a_root_double_underscore_name_is_an_implementation_detail() {
        let mut store = Store::scratch();
        let n = str_name(&mut store, None, "__i");
        assert_eq!(kind(&store, n), LocalDeclKind::ImplDetail);
    }

    #[test]
    fn plain_single_underscore_and_anonymous_names_are_default() {
        let mut store = Store::scratch();
        for s in ["i", "_i", "_", "i__", "_leanr_elab_fresh_0"] {
            let n = str_name(&mut store, None, s);
            assert_eq!(kind(&store, n), LocalDeclKind::Default, "{s}");
        }
        assert_eq!(
            LocalDeclKind::of_binder_name(&store, None, None),
            LocalDeclKind::Default,
            "an anonymous binder (`_`, `[C a]`) is `.default`"
        );
    }

    /// oracle `:169-170`: `num p _` and `str p _` recurse into the
    /// PARENT, so only the root component is ever tested.
    #[test]
    fn only_the_root_component_is_tested() {
        let mut store = Store::scratch();
        let root_dd = str_name(&mut store, None, "__a");
        let dd_dot_b = str_name(&mut store, Some(root_dd), "b");
        assert_eq!(kind(&store, dd_dot_b), LocalDeclKind::ImplDetail, "`__a.b`");

        let root_a = str_name(&mut store, None, "a");
        let a_dot_dd = str_name(&mut store, Some(root_a), "__b");
        assert_eq!(kind(&store, a_dot_dd), LocalDeclKind::Default, "`a.__b`");
    }

    #[test]
    fn a_numeric_component_is_looked_through_and_a_numeric_root_is_default() {
        let mut store = Store::scratch();
        let one = store.intern_nat(None, &Nat::from(1u64)).expect("nat");
        let root_dd = str_name(&mut store, None, "__x");
        let dd_1 = store.name_num(None, Some(root_dd), one).expect("name");
        assert_eq!(kind(&store, dd_1), LocalDeclKind::ImplDetail, "`__x.1`");

        let num_root = store.name_num(None, None, one).expect("name");
        assert_eq!(kind(&store, num_root), LocalDeclKind::Default, "`1`");
    }
}
