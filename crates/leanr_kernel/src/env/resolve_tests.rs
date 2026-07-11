//! `resolve_constant_info` — read-only twin of `promote_constant_info`
//! (M1-final, Task 5a). Fixtures build a frozen `base` store, a scratch
//! survivor, and assert resolve's three cases: all-hits ⇒ `Some` equal to
//! the base twin; a miss ⇒ `None`; all-hits-but-different ⇒ `Some` that
//! `constant_info_eq` rejects. See the 2026-07-10 execution amendment in
//! `docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md`.

use super::{promote_constant_info, resolve_constant_info};
use crate::bank::{ExprId, Store};
use crate::{constant_info_eq, AxiomVal, ConstantInfo, ConstantVal, Name};
use std::sync::Arc;

fn nm(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

/// `Sort 0` (Prop) interned into `store` (routing through `base`).
fn sort0(store: &mut Store, base: Option<&Store>) -> ExprId {
    let z = store.level_zero(base).unwrap();
    store.expr_sort(base, z).unwrap()
}

/// A nullary constant `name` (`Const name []`) interned into `store`
/// (routing through `base`).
fn cst(store: &mut Store, base: Option<&Store>, name: &str) -> ExprId {
    let n = store.intern_name(base, &nm(name)).unwrap();
    let ls = store.intern_level_list(base, &[]).unwrap();
    store.expr_const(base, n, ls).unwrap()
}

/// An axiom `name : ty`, its name interned into `store` (routing through
/// `base`), reusing the caller-supplied `ty`.
fn axiom(store: &mut Store, base: Option<&Store>, name: &str, ty: ExprId) -> ConstantInfo {
    let name_id = store.intern_name(base, &nm(name)).unwrap().unwrap();
    ConstantInfo::Axiom(AxiomVal {
        val: ConstantVal {
            name: name_id,
            level_params: vec![],
            ty,
        },
        is_unsafe: false,
    })
}

#[test]
fn resolve_all_hits_returns_base_twin() {
    let mut base = Store::persistent();
    let ty_b = sort0(&mut base, None);
    let twin = axiom(&mut base, None, "Foo", ty_b);

    // Survivor built with `base = None` ⇒ genuinely scratch-region ids
    // even though the same structure is present in `base`. This exercises
    // the read-only base lookup (not the persistent-id pass-through) and
    // proves resolve re-derives the base-canonical id from structure.
    let mut scratch = Store::scratch();
    let ty_s = sort0(&mut scratch, None);
    assert!(ty_s.is_scratch());
    let survivor = axiom(&mut scratch, None, "Foo", ty_s);

    let resolved = resolve_constant_info(&base, &scratch, &survivor)
        .unwrap()
        .expect("every sub-value is present in base");
    assert!(constant_info_eq(&twin, &resolved));
    match (&twin, &resolved) {
        (ConstantInfo::Axiom(a), ConstantInfo::Axiom(b)) => {
            assert_eq!(a.val.name, b.val.name);
            assert_eq!(a.val.ty, b.val.ty);
            assert!(!b.val.name.is_scratch(), "resolved ids are base-canonical");
            assert!(!b.val.ty.is_scratch());
        }
        _ => panic!("expected axioms"),
    }
}

#[test]
fn resolve_missing_subvalue_rejects() {
    let mut base = Store::persistent();
    let ty_b = sort0(&mut base, None);
    let _twin = axiom(&mut base, None, "Foo", ty_b);

    // Type present in base (base id); name genuinely absent from base.
    let mut scratch = Store::scratch();
    let ty_s = sort0(&mut scratch, Some(&base));
    assert!(!ty_s.is_scratch(), "Sort 0 already in base ⇒ base id");
    let survivor = axiom(&mut scratch, Some(&base), "Absent", ty_s);

    let resolved = resolve_constant_info(&base, &scratch, &survivor).unwrap();
    assert!(resolved.is_none(), "a sub-name absent from base ⇒ reject");
}

#[test]
fn resolve_all_hits_but_different_structure_not_eq() {
    let mut base = Store::persistent();
    let ty_b = sort0(&mut base, None);
    let foo_twin = axiom(&mut base, None, "Foo", ty_b);
    // "Bar" and Sort 0 are both present in base (second axiom).
    let bar_twin = axiom(&mut base, None, "Bar", ty_b);

    // Survivor = axiom "Bar" : Sort 0 — every sub-value ("Bar", Sort 0)
    // is present in base, but this is a different declaration than the
    // "Foo" twin. Built with `base = None` to force the probe lookup.
    let mut scratch = Store::scratch();
    let ty_s = sort0(&mut scratch, None);
    let survivor = axiom(&mut scratch, None, "Bar", ty_s);

    let resolved = resolve_constant_info(&base, &scratch, &survivor)
        .unwrap()
        .expect("'Bar' and Sort 0 are both present in base");
    assert!(
        !constant_info_eq(&foo_twin, &resolved),
        "resolve must not accept a structurally different declaration as the twin"
    );
    // Positive: resolve returns the *correct* other declaration's
    // base-canonical ids (the "Bar" twin), not merely "not Foo".
    assert!(
        constant_info_eq(&bar_twin, &resolved),
        "resolve must return the 'Bar' twin's canonical ids"
    );
}

#[test]
fn resolve_composite_term_one_absent_child_rejects() {
    // Load-bearing: a COMPOSITE `ty` with one base-present child and one
    // base-absent child must miss — the absent child forces the whole
    // `App` into the throwaway probe region ⇒ scratch id ⇒ `Ok(None)`.
    // This is the no-partial-false-accept property the amendment rests on.
    let mut base = Store::persistent();
    // `f` is interned in base; `g` is NOT.
    let _f = cst(&mut base, None, "f");

    // Build the survivor's `App(f, g)` type in a scratch reading base:
    // `f`'s structure is present ⇒ base id; `g`'s is absent ⇒ scratch id.
    let mut scratch = Store::scratch();
    let f_s = cst(&mut scratch, Some(&base), "f");
    assert!(!f_s.is_scratch(), "'f' already in base ⇒ base id");
    let g_s = cst(&mut scratch, Some(&base), "g");
    assert!(g_s.is_scratch(), "'g' absent from base ⇒ scratch id");
    let app = scratch.expr_app(Some(&base), f_s, g_s).unwrap();
    assert!(app.is_scratch(), "App over an absent child is itself novel");

    let survivor = axiom(&mut scratch, Some(&base), "Composite", app);
    let resolved = resolve_constant_info(&base, &scratch, &survivor).unwrap();
    assert!(
        resolved.is_none(),
        "one absent transitive child ⇒ composite term absent from base ⇒ reject"
    );
}

#[test]
fn resolve_matches_promote_on_hits() {
    let mut base = Store::persistent();
    let ty_b = sort0(&mut base, None);
    let _twin = axiom(&mut base, None, "Foo", ty_b);

    let mut scratch = Store::scratch();
    let ty_s = sort0(&mut scratch, None);
    let survivor = axiom(&mut scratch, None, "Foo", ty_s);

    let resolved = resolve_constant_info(&base, &scratch, &survivor)
        .unwrap()
        .unwrap();
    // Promote the same survivor and confirm the two translations agree
    // structurally (shared field enumeration, equivalent leaf verdicts).
    let promoted = promote_constant_info(&mut base, &scratch, &survivor).unwrap();
    assert!(constant_info_eq(&promoted, &resolved));
}
