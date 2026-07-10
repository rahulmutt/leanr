use leanr_check::graph::{build_graph, TaskKind};

// Helper builds a CheckedConstants with: axiom A, axiom B (uses A),
// inductive Foo with ctor Foo.mk, and returns (store, table, names).
mod fixture; // small module in tests/ that hand-builds the table

#[test]
fn simple_dependency_becomes_an_edge() {
    let (store, table, n) = fixture::chain_a_b();
    let g = build_graph(&store, &table).unwrap();
    let ta = g.name_to_task[&n.a];
    let tb = g.name_to_task[&n.b];
    assert!(g.tasks[tb].deps.contains(&ta));
    assert!(!g.tasks[ta].deps.contains(&tb));
}

#[test]
fn inductive_block_groups_type_and_ctor_into_one_task() {
    let (store, table, n) = fixture::inductive_foo();
    let g = build_graph(&store, &table).unwrap();
    let tfoo = g.name_to_task[&n.foo];
    // The constructor maps to the SAME task as its inductive.
    assert_eq!(g.name_to_task[&n.foo_mk], tfoo);
    match &g.tasks[tfoo].kind {
        TaskKind::InductiveBlock { members, ctors } => {
            assert!(members.contains(&n.foo));
            assert!(ctors.contains(&n.foo_mk));
        }
        _ => panic!("expected an inductive block task"),
    }
}

#[test]
fn missing_dependency_is_an_error() {
    let (store, table) = fixture::dangling_ref(); // B references absent C
    let err = build_graph(&store, &table).unwrap_err();
    assert!(matches!(err, leanr_kernel::KernelError::MissingConstant(_)));
}
