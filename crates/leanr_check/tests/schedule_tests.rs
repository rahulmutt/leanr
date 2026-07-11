//! Scheduler tests over SYNTHETIC, hand-forged DAGs (spec §Testing:
//! "Scheduler on synthetic DAGs, no kernel [beyond trivial checks]").
//!
//! Each task is `Simple(X)` where `X` is an axiom `X : Sort 0` — a
//! `Sort 0` type always kernel-checks, so `check_declaration` passes
//! deterministically and the test isolates the scheduler's
//! ordering/liveness/cancellation behavior. The DAG edges come from the
//! **forged** `Task.deps`, not from `build_graph`'s `used_constants`
//! walk: the axiom types reference nothing, so the only dependencies are
//! the ones we wire by hand.

use std::collections::HashMap;
use std::sync::Arc;

use leanr_check::check_parallel;
use leanr_check::graph::{DepGraph, Task, TaskId, TaskKind};
use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{AxiomVal, CheckedConstants, ConstantInfo, ConstantVal, KernelError, Name};

/// Intern `n` axioms `T0..T{n-1}`, each `: Sort 0`, into a fresh
/// persistent store; return the `Arc<Store>`, the `Arc<CheckedConstants>`
/// table, and the constants' `NameId`s (index-aligned with `T{i}`).
fn axiom_fixture(n: usize) -> (Arc<Store>, Arc<CheckedConstants>, Vec<NameId>) {
    let mut st = Store::persistent();
    let zero = st.level_zero(None).unwrap();
    let sort0 = st.expr_sort(None, zero).unwrap();

    let mut names = Vec::with_capacity(n);
    let mut map = HashMap::new();
    for i in 0..n {
        let nm = Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: format!("T{i}"),
        });
        let id = st.intern_name(None, &nm).unwrap().unwrap();
        names.push(id);
        map.insert(
            id,
            ConstantInfo::Axiom(AxiomVal {
                val: ConstantVal {
                    name: id,
                    level_params: vec![],
                    ty: sort0,
                },
                is_unsafe: false,
            }),
        );
    }
    (Arc::new(st), Arc::new(CheckedConstants::new(map)), names)
}

/// Forge a `DepGraph` from `(name, deps)` per task, index-aligned: task `i`
/// checks axiom `names[i]` and depends on the listed task ids.
fn forge_graph(names: &[NameId], deps: Vec<Vec<TaskId>>) -> DepGraph {
    assert_eq!(names.len(), deps.len());
    let mut tasks = Vec::with_capacity(names.len());
    let mut name_to_task = HashMap::new();
    for (i, (&name, d)) in names.iter().zip(deps).enumerate() {
        name_to_task.insert(name, i);
        tasks.push(Task {
            id: i,
            kind: TaskKind::Simple(name),
            admits: vec![name],
            deps: d,
        });
    }
    DepGraph {
        tasks,
        name_to_task,
    }
}

#[test]
fn diamond_admits_shared_dep_once_and_all_four() {
    // A (no deps); B<-A; C<-A; D<-B,C.
    let (store, table, n) = axiom_fixture(4);
    let graph = forge_graph(
        &n,
        vec![
            vec![],     // T0 = A
            vec![0],    // T1 = B depends on A
            vec![0],    // T2 = C depends on A
            vec![1, 2], // T3 = D depends on B, C
        ],
    );
    let stats = check_parallel(store, table, graph, 4, |_| {}).expect("diamond checks green");
    assert_eq!(
        stats.checked, 4,
        "all four tasks must be checked exactly once"
    );
    assert_eq!(stats.skipped_unsafe, 0);
}

#[test]
fn cycle_reports_error_not_hang() {
    // T0 <-> T1: neither ever becomes ready. A correct scheduler drains and
    // reports a DependencyCycle promptly; a broken one would hang (the test
    // harness would then time out — still a failure, never a silent pass).
    let (store, table, n) = axiom_fixture(2);
    let graph = forge_graph(&n, vec![vec![1], vec![0]]);
    let err = check_parallel(store, table, graph, 4, |_| {}).expect_err("a 2-cycle must error");
    assert!(
        matches!(err.error, KernelError::DependencyCycle(_)),
        "expected DependencyCycle, got {:?}",
        err.error
    );
}

#[test]
fn single_worker_matches_multi_worker_count() {
    // 1 root + N leaves each depending on the root (wide fan-out).
    const N: usize = 64;
    let deps = |()| {
        let mut d = vec![vec![]]; // T0 = root
        for _ in 0..N {
            d.push(vec![0]); // each leaf depends on the root
        }
        d
    };

    let (store1, table1, n1) = axiom_fixture(N + 1);
    let g1 = forge_graph(&n1, deps(()));
    let s1 = check_parallel(store1, table1, g1, 1, |_| {}).expect("jobs=1 green");

    let (store8, table8, n8) = axiom_fixture(N + 1);
    let g8 = forge_graph(&n8, deps(()));
    let s8 = check_parallel(store8, table8, g8, 8, |_| {}).expect("jobs=8 green");

    assert_eq!(s1.checked, N + 1);
    assert_eq!(
        s8.checked, s1.checked,
        "checked count must be job-count-independent"
    );
}
