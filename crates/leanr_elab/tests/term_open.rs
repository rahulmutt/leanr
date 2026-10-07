//! Term-level `open … in` (`builtin::open`, oracle `elabOpen`,
//! `BuiltinTerm.lean:400-408`). The file corpus (`tOpen/*` rows) pins
//! scoping, `openDecl` forms and postponement; this file pins what no
//! row can see.

mod support;

/// `elabOpen` passes its `expectedType?` to the body. A corpus row cannot
/// observe a dropped expected type: every elaborator that reads it
/// postpones on `none` and resumes against the instantiated mvar type.
/// Without postponing, an anonymous constructor needs it at once.
#[test]
fn the_body_sees_the_expected_type() {
    support::with_elab(
        "open Nat in ⟨Nat.zero, Nat.zero⟩",
        |elab, elem, kinds| {
            // `with_elab` resolves against empty tables; `open Nat` needs `Nat`
            // registered as a namespace.
            let nat = support::name_id(elab, "Nat");
            let tables = leanr_elab::names::NameTables::new(&[], &[Some(nat)], &[]);
            elab.resolve.tables = Box::leak(Box::new(tables));
            let ty = support::parse_type(elab, "PProd Nat Nat");
            let r = elab.without_postponing(|e| e.elab_term(elem, kinds, Some(ty)));
            assert!(r.is_ok(), "{r:?}");
        },
    );
}
