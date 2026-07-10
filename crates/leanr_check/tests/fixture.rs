//! Hand-built `CheckedConstants` fixtures for `graph_tests.rs`.
//!
//! Mirrors the kernel's own `env::tests`/`testenv` fixture style (hand-
//! roll a tiny environment, intern names/exprs, build `ConstantInfo`s
//! directly), but goes through the id-native `Store`/bank API rather
//! than the `Arc*`-side bridges: those bridges (`ArcConstantInfo`,
//! `intern_constant_info`, `testenv::{nm, g}`, …) are `#[cfg(test)]`
//! items private to `leanr_kernel`'s own compilation — an external
//! crate's tests never see them, `#[cfg(test)] pub use` notwithstanding
//! (see that crate's `lib.rs` module doc). So each fixture interns
//! names/levels/exprs straight into a fresh persistent `Store` and
//! assembles the plain (non-Arc) `ConstantVal`/`AxiomVal`/`InductiveVal`/
//! `ConstructorVal` types by hand — structurally valid enough for
//! `build_graph` to walk (`used_constants`, block grouping, edges), but
//! not type-checked (no `Environment`/`replay` involved).

use std::collections::HashMap;
use std::sync::Arc;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{
    AxiomVal, CheckedConstants, ConstantInfo, ConstantVal, ConstructorVal, InductiveVal, Name, Nat,
};

fn nm(part: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: part.to_string(),
    })
}

fn nm2(a: &str, b: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: nm(a),
        part: b.to_string(),
    })
}

/// Names produced by [`chain_a_b`].
pub struct ChainNames {
    pub a: NameId,
    pub b: NameId,
}

/// `axiom A : Sort 0` and `axiom B : A` — `B`'s type is literally
/// `Const A []`, so `used_constants(B)` yields `A` and `build_graph`
/// must record an edge `B -> A`'s task.
pub fn chain_a_b() -> (Store, CheckedConstants, ChainNames) {
    let mut st = Store::persistent();
    let a = st.intern_name(None, &nm("A")).unwrap().unwrap();
    let b = st.intern_name(None, &nm("B")).unwrap().unwrap();

    let zero = st.level_zero(None).unwrap();
    let sort0 = st.expr_sort(None, zero).unwrap();
    let no_levels = st.intern_level_list(None, &[]).unwrap();
    let a_ty_ref = st.expr_const(None, Some(a), no_levels).unwrap();

    let axiom_a = ConstantInfo::Axiom(AxiomVal {
        val: ConstantVal {
            name: a,
            level_params: vec![],
            ty: sort0,
        },
        is_unsafe: false,
    });
    let axiom_b = ConstantInfo::Axiom(AxiomVal {
        val: ConstantVal {
            name: b,
            level_params: vec![],
            ty: a_ty_ref,
        },
        is_unsafe: false,
    });

    let mut map = HashMap::new();
    map.insert(a, axiom_a);
    map.insert(b, axiom_b);
    (st, CheckedConstants::new(map), ChainNames { a, b })
}

/// Names produced by [`inductive_foo`].
pub struct IndNames {
    pub foo: NameId,
    pub foo_mk: NameId,
}

/// `inductive Foo : Type` with one constructor `Foo.mk : Foo` — a
/// single, non-mutual block (`all = [Foo]`, `ctors = [Foo.mk]`).
pub fn inductive_foo() -> (Store, CheckedConstants, IndNames) {
    let mut st = Store::persistent();
    let foo_id = st.intern_name(None, &nm("Foo")).unwrap().unwrap();
    let foo_mk = st.intern_name(None, &nm2("Foo", "mk")).unwrap().unwrap();

    let zero = st.level_zero(None).unwrap();
    let one = st.level_succ(None, zero).unwrap(); // Sort 1 = Type
    let type1 = st.expr_sort(None, one).unwrap();
    let no_levels = st.intern_level_list(None, &[]).unwrap();
    let foo_ty_ref = st.expr_const(None, Some(foo_id), no_levels).unwrap();

    let ind = ConstantInfo::Induct(InductiveVal {
        val: ConstantVal {
            name: foo_id,
            level_params: vec![],
            ty: type1,
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![foo_id],
        ctors: vec![foo_mk],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    let ctor = ConstantInfo::Ctor(ConstructorVal {
        val: ConstantVal {
            name: foo_mk,
            level_params: vec![],
            ty: foo_ty_ref,
        },
        induct: foo_id,
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
    });

    let mut map = HashMap::new();
    map.insert(foo_id, ind);
    map.insert(foo_mk, ctor);
    (
        st,
        CheckedConstants::new(map),
        IndNames {
            foo: foo_id,
            foo_mk,
        },
    )
}

/// `axiom B : C` where `C` is interned into the store (so its `NameId`
/// exists and can appear inside `B`'s type) but never inserted into the
/// table's map — `build_graph` must report it as a missing dependency
/// rather than panicking or silently dropping the edge.
pub fn dangling_ref() -> (Store, CheckedConstants) {
    let mut st = Store::persistent();
    let b = st.intern_name(None, &nm("B")).unwrap().unwrap();
    let c = st.intern_name(None, &nm("C")).unwrap().unwrap();

    let no_levels = st.intern_level_list(None, &[]).unwrap();
    let c_ty_ref = st.expr_const(None, Some(c), no_levels).unwrap();

    let axiom_b = ConstantInfo::Axiom(AxiomVal {
        val: ConstantVal {
            name: b,
            level_params: vec![],
            ty: c_ty_ref,
        },
        is_unsafe: false,
    });

    let mut map = HashMap::new();
    map.insert(b, axiom_b);
    (st, CheckedConstants::new(map))
}
