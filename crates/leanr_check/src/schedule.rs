//! Parallel worker-pool scheduler that drives kernel checks over the
//! dependency DAG (`crate::graph::DepGraph`) with the read-only
//! resolve-or-reject compare. Spec:
//! docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md
//! §Architecture Workstream 1 step 5, as amended by the dated "Amendment
//! (2026-07-10, execution)" in §Key enabling observation.
//!
//! Concurrency shape (post-amendment): the store is `Arc<Store>` and
//! read-only (`&Store`) throughout — no interior mutability, no `unsafe`,
//! **no promotion mutex**. Inductive/quotient survivors are canonicalized
//! against the frozen store by *looking them up* with the read-only kernel
//! primitive `resolve_constant_info`, so every task is lock-free apart
//! from the shared bookkeeping the plan calls for: the ready-queue
//! `Mutex`+`Condvar`, per-task atomic dependency counters + a per-task
//! atomic admitted flag (inside `CheckedConstants`), a cancellation flag,
//! and the first-failure slot.
//!
//! Liveness on hostile input: a dependency **cycle** (impossible from a
//! well-formed `.olean`, forgeable by an attacker) leaves its tasks
//! permanently un-ready. Workers drain when the ready queue is empty and
//! nothing is in flight; after the pool joins, `done != n_tasks` ⇒ a cycle
//! ⇒ `KernelError::DependencyCycle` naming a still-pending member. The
//! cycle path is always *reported*, never a hang — the untrusted-input
//! liveness guarantee (spec §Error handling, "Cycles / starvation").

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{
    build_inductive_types, check_declaration, constant_info_eq, resolve_constant_info, Admitted,
    CheckedConstants, ConstSource, ConstantInfo, Declaration, DefinitionSafety, EnvView,
    KernelError, Name,
};

use crate::graph::{DepGraph, Task, TaskId, TaskKind};

/// Stats from a successful parallel check (order-independent, so the CLI's
/// final line stays deterministic — spec §Architecture step 6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckStats {
    /// Declarations sent to the kernel: one per def/axiom/theorem/opaque,
    /// one per inductive block, one per quotient init (constructors and
    /// recursors are checked structurally within their block, not counted).
    pub checked: usize,
    /// Decoded constants skipped because they are `unsafe`/`partial`
    /// (never checked, never admitted — mirrors `replay`'s skip rule).
    pub skipped_unsafe: usize,
}

/// A check failure: the declaration being processed when the error fired,
/// plus the kernel error. The CLI adds module attribution via its owner
/// map (spec §Error handling).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckFailure {
    pub decl: NameId,
    pub error: KernelError,
}

/// Check every task of `graph` in parallel across `jobs.max(1)` worker
/// threads, gating each declaration's environment behind `table`'s
/// admitted flags. Returns `CheckStats` on an all-green run, or the
/// race-winning `CheckFailure` on the first failure / a
/// `DependencyCycle` on a cyclic graph. `progress` is called with the
/// running checked-count after each successful task (for the CLI's
/// periodic counter); it must be `Send + Sync` as workers call it
/// concurrently.
///
/// Spec: docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md
/// §Architecture Workstream 1 (parallel replay) + the 2026-07-10 execution
/// amendment (read-only resolve-or-reject, lock-free inductive/quot path).
pub fn check_parallel(
    store: Arc<Store>,
    table: Arc<CheckedConstants>,
    graph: DepGraph,
    jobs: usize,
    progress: impl Fn(usize) + Send + Sync,
) -> Result<CheckStats, CheckFailure> {
    let n_tasks = graph.tasks.len();

    // Decoded constants the graph never checks (unsafe/partial) — counted
    // once, single-threaded, mirroring `replay`'s skip rule so the eventual
    // differential gate can match `checked`/`skipped` counts.
    let skipped_unsafe = table
        .iter_decoded()
        .filter(|(_, ci)| is_unsafe(ci) || is_partial(ci))
        .count();

    // Per-task remaining-dependency counters (a task is ready at 0) and the
    // reverse adjacency (dependents[d] = tasks that depend on task d).
    let pending: Vec<AtomicUsize> = graph
        .tasks
        .iter()
        .map(|t| AtomicUsize::new(t.deps.len()))
        .collect();
    let mut dependents: Vec<Vec<TaskId>> = vec![Vec::new(); n_tasks];
    for (i, t) in graph.tasks.iter().enumerate() {
        for &d in &t.deps {
            // Guard an out-of-range dep id from a forged graph: a bad dep is
            // simply never decremented, so the task stays pending and the
            // post-join cycle path reports it — a reject, never a hang.
            if let Some(slot) = dependents.get_mut(d) {
                slot.push(i);
            }
        }
    }

    // Seed the ready queue with the zero-dependency tasks.
    let mut queue: VecDeque<TaskId> = VecDeque::new();
    for (i, t) in graph.tasks.iter().enumerate() {
        if t.deps.is_empty() {
            queue.push_back(i);
        }
    }

    let shared = Shared {
        tasks: &graph.tasks,
        pending,
        dependents,
        ready: Mutex::new(ReadyState {
            queue,
            in_flight: 0,
            done: 0,
        }),
        cv: Condvar::new(),
        cancelled: AtomicBool::new(false),
        failure: Mutex::new(None),
        quot_initialized: AtomicBool::new(false),
    };

    let store_ref: &Store = &store;
    let table_ref: &CheckedConstants = &table;
    let progress_ref = &progress;
    let shared_ref = &shared;

    std::thread::scope(|scope| {
        for _ in 0..jobs.max(1) {
            scope.spawn(move || worker(shared_ref, store_ref, table_ref, progress_ref));
        }
    });

    // The pool has joined: every worker returned.
    if let Some(f) = shared.failure.into_inner().unwrap() {
        return Err(f);
    }
    let done = shared.ready.into_inner().unwrap().done;
    if done != n_tasks {
        // Some task never became ready ⇒ a dependency cycle (or a dangling
        // forged dep). A cyclic graph is ALWAYS reported, never a false
        // `Ok` and never a hang. Blame a still-pending member; fall back to
        // any graph/table name, and finally to a placeholder so even a
        // content-free forged graph still errors.
        let (decl, name) = match stuck_decl(&graph, &shared.pending)
            .or_else(|| graph.name_to_task.keys().next().copied())
            .or_else(|| table.iter_decoded().next().map(|(&n, _)| n))
        {
            Some(d) => (d, store_ref.to_name(None, Some(d))),
            None => (
                NameId::from_index(0, false).expect("row-0 base id is always valid"),
                Arc::new(Name::Anonymous),
            ),
        };
        return Err(CheckFailure {
            decl,
            error: KernelError::DependencyCycle(name),
        });
    }
    Ok(CheckStats {
        checked: done,
        skipped_unsafe,
    })
}

/// Cross-thread scheduler state. Everything shared is here: the immutable
/// task slice, the per-task atomic dependency counters + reverse
/// adjacency, the ready-queue mutex/condvar, the cancellation flag, and
/// the first-failure slot. No promotion mutex — the store never moves.
struct Shared<'a> {
    tasks: &'a [Task],
    pending: Vec<AtomicUsize>,
    dependents: Vec<Vec<TaskId>>,
    ready: Mutex<ReadyState>,
    cv: Condvar,
    cancelled: AtomicBool,
    failure: Mutex<Option<CheckFailure>>,
    /// Set exactly once, by the single quotient task after it successfully
    /// checks+admits (`Release`); every task's view reads it (`Acquire`) so
    /// quotient-using declarations reduce `Quot.lift`/`Quot.ind` just as the
    /// sequential `replay` does once quotients are initialized. Correct
    /// because any quotient-using task has a graph edge to the sole Quot
    /// task (Task 4 groups all quotient constants into one task and adds the
    /// dependency), so it runs strictly after — the ready-queue mutex's
    /// release/acquire plus this flag's own ordering give the happens-before
    /// that makes the `true` visible; tasks that never reduce a quotient
    /// recursor are unaffected by a racy read.
    quot_initialized: AtomicBool,
}

struct ReadyState {
    queue: VecDeque<TaskId>,
    /// Tasks popped but not yet completed. Guards the drain condition:
    /// `queue.is_empty() && in_flight == 0` can only hold once every
    /// completing task has finished pushing its newly-ready dependents
    /// (both happen in the same critical section), so no ready task is
    /// ever missed.
    in_flight: usize,
    /// Successfully completed tasks. `done == n_tasks` ⇒ all green;
    /// `done < n_tasks` after drain ⇒ a cycle.
    done: usize,
}

fn worker<P: Fn(usize) + Sync>(
    shared: &Shared,
    store: &Store,
    table: &CheckedConstants,
    progress: &P,
) {
    loop {
        // --- acquire a ready task (or exit) ---
        let task_id = {
            let mut st = shared.ready.lock().unwrap();
            loop {
                if shared.cancelled.load(Ordering::Acquire) {
                    return;
                }
                if let Some(t) = st.queue.pop_front() {
                    st.in_flight += 1;
                    break t;
                }
                if st.in_flight == 0 {
                    // Drain: nothing queued and nothing running ⇒ no task
                    // can ever become ready. Wake peers so they also exit,
                    // then leave. (A cycle, if present, is reported after
                    // the pool joins — never a hang.)
                    shared.cv.notify_all();
                    return;
                }
                st = shared.cv.wait(st).unwrap();
            }
        };

        // --- run it (no lock held) ---
        match run_task(
            store,
            table,
            &shared.tasks[task_id],
            &shared.quot_initialized,
        ) {
            Ok(()) => {
                // Decrement dependents' counters; a 1->0 transition means
                // that dependent is now ready. `fetch_sub` is atomic, so at
                // most one decrementer observes the transition.
                let mut newly: Vec<TaskId> = Vec::new();
                for &dep in &shared.dependents[task_id] {
                    if shared.pending[dep].fetch_sub(1, Ordering::AcqRel) == 1 {
                        newly.push(dep);
                    }
                }
                let done_count = {
                    let mut st = shared.ready.lock().unwrap();
                    st.in_flight -= 1;
                    st.done += 1;
                    for t in newly {
                        st.queue.push_back(t);
                    }
                    shared.cv.notify_all();
                    st.done
                };
                progress(done_count);
            }
            Err(f) => {
                {
                    let mut fl = shared.failure.lock().unwrap();
                    if fl.is_none() {
                        *fl = Some(f);
                    }
                }
                shared.cancelled.store(true, Ordering::Release);
                {
                    let mut st = shared.ready.lock().unwrap();
                    st.in_flight -= 1;
                    shared.cv.notify_all();
                }
                return;
            }
        }
    }
}

/// Run one task against the gated table with a fresh per-task scratch
/// store (dropped when this returns). The view's `quot_initialized` reads
/// the shared flag (`Acquire`): a quotient-using declaration runs strictly
/// after the sole Quot task (a graph edge guarantees it), so it observes
/// the flag `true` and reduces quotient recursors exactly as sequential
/// `replay` does. The Quot task's own view reads `false` (the flag is set
/// only after `run_quot` succeeds), so quot init still happens once.
fn run_task(
    store: &Store,
    table: &CheckedConstants,
    task: &Task,
    quot_flag: &AtomicBool,
) -> Result<(), CheckFailure> {
    let mut scratch = Store::scratch();
    let view = EnvView {
        consts: ConstSource::Gated(table),
        extra: None,
        quot_initialized: quot_flag.load(Ordering::Acquire),
        store,
    };
    match &task.kind {
        TaskKind::Simple(n) => {
            let n = *n;
            let ci = table.get_decoded(n).ok_or_else(|| CheckFailure {
                decl: n,
                error: KernelError::MissingConstant(store.to_name(None, Some(n))),
            })?;
            let decl =
                declaration_of(store, ci).map_err(|error| CheckFailure { decl: n, error })?;
            check_declaration(view, &mut scratch, decl)
                .map_err(|error| CheckFailure { decl: n, error })?;
            table.admit(n);
            Ok(())
        }
        TaskKind::InductiveBlock { members, ctors } => {
            run_block(store, table, view, &mut scratch, members, ctors)
        }
        TaskKind::Quot { names, .. } => {
            run_quot(store, table, view, &mut scratch, names, quot_flag)
        }
    }
}

/// Reconstruct a `Declaration` from a decoded `ConstantInfo` for a
/// `Simple` task. `Induct`/`Ctor`/`Rec` never reach a `Simple` task (they
/// live in blocks), so those arms are unreachable *by construction* — but
/// on untrusted `.olean`-derived input `unreachable!` is inappropriate:
/// reject with a `KernelError` (plus a `debug_assert` to catch a driver
/// bug in tests) rather than panic.
fn declaration_of(store: &Store, ci: &ConstantInfo) -> Result<Declaration, KernelError> {
    Ok(match ci {
        ConstantInfo::Defn(v) => Declaration::Defn(v.clone()),
        ConstantInfo::Axiom(v) => Declaration::Axiom(v.clone()),
        ConstantInfo::Opaque(v) => Declaration::Opaque(v.clone()),
        ConstantInfo::Thm(v) => Declaration::Thm(v.clone()),
        ConstantInfo::Quot(_) => Declaration::Quot,
        ConstantInfo::Induct(_) | ConstantInfo::Ctor(_) | ConstantInfo::Rec(_) => {
            debug_assert!(
                false,
                "declaration_of on a block-only kind (Induct/Ctor/Rec)"
            );
            return Err(KernelError::MissingConstant(
                store.to_name(None, Some(ci.name())),
            ));
        }
    })
}

/// An inductive-block task: rebuild the mutual block, kernel-check it, then
/// resolve-and-compare every regenerated survivor against its decoded twin
/// (read-only, no lock), then admit members + ctors + survivors.
fn run_block(
    store: &Store,
    table: &CheckedConstants,
    view: EnvView,
    scratch: &mut Store,
    members: &[NameId],
    ctors: &[NameId],
) -> Result<(), CheckFailure> {
    // A block always has >=1 member; an empty one is degenerate (nothing
    // to build, check, or admit).
    let Some(&principal) = members.first() else {
        return Ok(());
    };

    let types = build_inductive_types(store, |n| table.get_decoded(n).cloned(), members).map_err(
        |error| CheckFailure {
            decl: principal,
            error,
        },
    )?;

    // lparams/nparams from members[0]'s InductiveVal — mirrors replay.
    let (lparams, nparams) = match table.get_decoded(principal) {
        Some(ConstantInfo::Induct(iv)) => (iv.val.level_params.clone(), iv.num_params.clone()),
        _ => {
            return Err(CheckFailure {
                decl: principal,
                error: KernelError::MissingConstant(store.to_name(None, Some(principal))),
            });
        }
    };

    let decl = Declaration::Inductive {
        lparams,
        nparams,
        types,
        is_unsafe: false,
    };
    let Admitted { survivors, .. } =
        check_declaration(view, scratch, decl).map_err(|error| CheckFailure {
            decl: principal,
            error,
        })?;

    resolve_and_compare(store, table, scratch, principal, &survivors)?;

    for &m in members {
        table.admit(m);
    }
    for &c in ctors {
        table.admit(c);
    }
    for surv in &survivors {
        table.admit(surv.name());
    }
    Ok(())
}

/// A quotient-init task: kernel-check `Declaration::Quot`, resolve-and-
/// compare survivors, admit every quotient constant (+ survivors), then
/// publish the shared `quot_initialized` flag so later quotient-using tasks
/// reduce quotient recursors.
fn run_quot(
    store: &Store,
    table: &CheckedConstants,
    view: EnvView,
    scratch: &mut Store,
    names: &[NameId],
    quot_flag: &AtomicBool,
) -> Result<(), CheckFailure> {
    let Some(&principal) = names.first() else {
        return Ok(());
    };
    let Admitted { survivors, .. } =
        check_declaration(view, scratch, Declaration::Quot).map_err(|error| CheckFailure {
            decl: principal,
            error,
        })?;

    resolve_and_compare(store, table, scratch, principal, &survivors)?;

    for &n in names {
        table.admit(n);
    }
    for surv in &survivors {
        table.admit(surv.name());
    }
    // Publish AFTER the admits: a task observing this `true` (via its view's
    // Acquire load, ordered after this thread's ready-queue unlock) is
    // guaranteed to also see the admitted quotient constants.
    quot_flag.store(true, Ordering::Release);
    Ok(())
}

/// Resolve-and-compare each regenerated survivor against its decoded twin,
/// read-only (spec: the 2026-07-10 execution amendment). `resolve_constant_info`
/// looks each survivor up in the frozen `store` (never appends); a miss
/// means the survivor is structurally different from anything interned, and
/// since the twin *is* interned, survivor != twin ⇒ reject. On a hit, the
/// resolved (base-canonical) info is compared against the decoded twin with
/// `constant_info_eq` verbatim (id equality = structural equality in one
/// store). No lock, no mutation of the shared store.
///
/// **Region discipline (untrusted input).** A regenerated survivor's name
/// may be SCRATCH-region — e.g. a recursor whose name is absent from the
/// frozen store gets a fresh scratch `NameId`. Such an id is meaningless to
/// `store.to_name(None, ..)` (it would read the base name-pool at a scratch
/// index → wrong name, or panic on `.expect`), so every survivor-name
/// rendering here goes through `scratch.to_name(Some(store), ..)` (correct
/// for both scratch- and base-region ids). And `CheckFailure.decl` is
/// attributed to `principal` (the block/quot task's base-region head name,
/// a valid table/owner key), never a possibly-scratch survivor name. The
/// `Some` arm's `resolved.name()` IS base-region (it resolved into the
/// frozen store), so it renders/attributes fine.
fn resolve_and_compare(
    store: &Store,
    table: &CheckedConstants,
    scratch: &Store,
    principal: NameId,
    survivors: &[ConstantInfo],
) -> Result<(), CheckFailure> {
    for surv in survivors {
        match resolve_constant_info(store, scratch, surv).map_err(|error| CheckFailure {
            decl: principal,
            error,
        })? {
            Some(resolved) => {
                let twin = table
                    .get_decoded(resolved.name())
                    .ok_or_else(|| CheckFailure {
                        decl: resolved.name(),
                        error: KernelError::MissingConstant(
                            store.to_name(None, Some(resolved.name())),
                        ),
                    })?;
                if !constant_info_eq(twin, &resolved) {
                    return Err(CheckFailure {
                        decl: resolved.name(),
                        error: KernelError::ConstructorMismatch(
                            store.to_name(None, Some(resolved.name())),
                        ),
                    });
                }
            }
            None => {
                // Survivor absent from the frozen store ⇒ differs from its
                // decoded twin (which IS interned) ⇒ reject. Render its name
                // via `scratch` (its id may be scratch-region) and blame the
                // base-region `principal`.
                return Err(CheckFailure {
                    decl: principal,
                    error: KernelError::ConstructorMismatch(
                        scratch.to_name(Some(store), Some(surv.name())),
                    ),
                });
            }
        }
    }
    Ok(())
}

/// Find a still-pending task (a member of a cycle) and return a name to
/// blame. Returns `None` only if no pending task carries a name.
fn stuck_decl(graph: &DepGraph, pending: &[AtomicUsize]) -> Option<NameId> {
    for (i, t) in graph.tasks.iter().enumerate() {
        if pending
            .get(i)
            .is_some_and(|p| p.load(Ordering::Acquire) > 0)
        {
            if let Some(&n) = t.admits.first() {
                return Some(n);
            }
        }
    }
    None
}

// `is_unsafe`/`is_partial`: the driver's copy of `replay`'s skip predicates
// (those are private to `leanr_kernel`). Kept in lockstep with
// `crates/leanr_kernel/src/replay.rs` so `skipped_unsafe` matches the
// sequential reference the differential gate compares against.
fn is_unsafe(ci: &ConstantInfo) -> bool {
    match ci {
        ConstantInfo::Defn(v) => v.safety == DefinitionSafety::Unsafe,
        ConstantInfo::Axiom(v) => v.is_unsafe,
        ConstantInfo::Opaque(v) => v.is_unsafe,
        ConstantInfo::Induct(v) => v.is_unsafe,
        ConstantInfo::Ctor(v) => v.is_unsafe,
        ConstantInfo::Rec(v) => v.is_unsafe,
        ConstantInfo::Thm(_) | ConstantInfo::Quot(_) => false,
    }
}

fn is_partial(ci: &ConstantInfo) -> bool {
    matches!(ci, ConstantInfo::Defn(v) if v.safety == DefinitionSafety::Partial)
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::{AxiomVal, ConstantVal};
    use std::collections::HashMap;

    fn name(part: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: part.to_string(),
        })
    }

    /// Finding 1 regression (untrusted input): a regenerated survivor whose
    /// name is SCRATCH-region and absent from the frozen base — e.g. an
    /// `I.rec` the module omitted — must be REJECTED
    /// (`ConstructorMismatch`), its name rendered via `scratch` (NOT
    /// `base.to_name(None, ..)`, which reads the base name-pool at a scratch
    /// index → wrong name or a panicking `.expect`), and the failure blamed
    /// on the base-region `principal`, never the scratch survivor name. This
    /// directly pins the exact defective code path; reaching the same `None`
    /// arm through `check_parallel` would require a full kernel-checkable
    /// inductive fixture, whereas this exercises the region-safe rendering
    /// itself. The old code either panicked out of `thread::scope` or set
    /// `decl` to the scratch id (≠ `principal`) — both caught below.
    #[test]
    fn resolve_miss_on_scratch_survivor_rejects_without_panic() {
        let mut base = Store::persistent();
        let principal = base.intern_name(None, &name("P")).unwrap().unwrap();

        // A survivor interned ONLY in scratch (base threaded, so a name
        // absent from base lands in the scratch region).
        let mut scratch = Store::scratch();
        let ghost = scratch
            .intern_name(Some(&base), &name("Ghost.rec"))
            .unwrap()
            .unwrap();
        assert!(
            ghost.is_scratch(),
            "the survivor name must be scratch-region to exercise the fix"
        );
        let zero = scratch.level_zero(Some(&base)).unwrap();
        let sort0 = scratch.expr_sort(Some(&base), zero).unwrap();
        let survivor = ConstantInfo::Axiom(AxiomVal {
            val: ConstantVal {
                name: ghost,
                level_params: vec![],
                ty: sort0,
            },
            is_unsafe: false,
        });

        let table = CheckedConstants::new(HashMap::new());
        let err = resolve_and_compare(&base, &table, &scratch, principal, &[survivor])
            .expect_err("a scratch-region survivor absent from base must be rejected");
        assert!(
            matches!(err.error, KernelError::ConstructorMismatch(_)),
            "expected ConstructorMismatch, got {:?}",
            err.error
        );
        assert_eq!(
            err.decl, principal,
            "blame must be the base-region principal, not the scratch survivor name"
        );
    }
}
