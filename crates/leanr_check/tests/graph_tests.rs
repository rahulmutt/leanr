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

#[test]
fn quot_task_has_explicit_edge_to_eq() {
    let (store, table, n) = fixture::quot_with_eq();
    let g = build_graph(&store, &table).unwrap();
    let tquot = g.name_to_task[&n.quot];
    let teq = g.name_to_task[&n.eq];
    // The quotient constant's type does not reference `Eq`, so this edge
    // exists ONLY because build_graph adds it explicitly (spec: quotient
    // init has an explicit edge to `Eq`). It also confirms the Quot task
    // really is a distinct task from `Eq`'s.
    assert_ne!(tquot, teq);
    assert!(
        g.tasks[tquot].deps.contains(&teq),
        "quotient task must depend on Eq's task"
    );
}

#[test]
fn recursor_groups_into_its_inductive_block() {
    let (store, table, n) = fixture::inductive_foo_with_rec();
    let g = build_graph(&store, &table).unwrap();
    let tfoo = g.name_to_task[&n.foo];
    // The recursor maps to the SAME task as its inductive, resolved via
    // RecursorVal.all[0]. Its type references only the unrelated `Other`,
    // so a used_constants-based fallback would misassign it to Other's
    // task — hence the explicit `!= tother` check below.
    assert_eq!(g.name_to_task[&n.foo_rec], tfoo);
    assert_eq!(g.name_to_task[&n.foo_mk], tfoo);
    let tother = g.name_to_task[&n.other];
    assert_ne!(
        g.name_to_task[&n.foo_rec], tother,
        "recursor must not be grouped into the unrelated Other's task"
    );
    match &g.tasks[tfoo].kind {
        TaskKind::InductiveBlock { members, ctors } => {
            assert!(members.contains(&n.foo));
            assert!(ctors.contains(&n.foo_mk));
        }
        _ => panic!("expected an inductive block task"),
    }
    // The recursor's flag must flip with the block → it is in `admits`.
    assert!(g.tasks[tfoo].admits.contains(&n.foo_rec));
}

#[test]
fn high_degree_deps_are_deduplicated() {
    // A declaration whose type references 500 distinct axioms, each twice
    // (a 1000-element duplicate-heavy `used_constants` list). The old
    // `Vec::contains` dedup was quadratic on exactly this shape; the
    // HashSet dedup must yield exactly the 500 distinct dep-tasks, once
    // each, in first-occurrence order.
    let n_deps = 500;
    let (store, table, h) = fixture::high_degree(n_deps);
    let g = build_graph(&store, &table).unwrap();
    let tdecl = g.name_to_task[&h.decl];
    let deps = &g.tasks[tdecl].deps;

    // Exactly one edge per distinct dep — no duplicates.
    assert_eq!(deps.len(), n_deps, "expected one edge per distinct dep");
    let unique: std::collections::HashSet<_> = deps.iter().copied().collect();
    assert_eq!(unique.len(), deps.len(), "deps must contain no duplicates");

    // Every distinct dep's task is present.
    for dep in &h.deps {
        let td = g.name_to_task[dep];
        assert!(deps.contains(&td), "missing edge to a distinct dep's task");
    }

    // First-occurrence order preserved: `deps` must equal the distinct
    // dep-tasks in the exact order `used_constants` first sees each name
    // (its own deterministic, already-deduplicated walk order) — this is
    // the property the HashSet `seen.insert` guard preserves versus the
    // old `!Vec::contains` guard. Derived from `used_constants` directly
    // rather than a hardcoded order, so it is independent of the walk's
    // internal traversal direction.
    let ci = table.get_decoded(h.decl).unwrap();
    let expected: Vec<_> = leanr_kernel::used_constants(&store, None, ci)
        .iter()
        .map(|name| g.name_to_task[name])
        .collect();
    assert_eq!(*deps, expected, "deps must be in first-occurrence order");
}
