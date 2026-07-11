//! Dependency DAG over a frozen `CheckedConstants`, grouping mutual
//! inductive blocks (and their constructors + recursors) into single
//! tasks — the same admission units `crate::replay` processes. Spec
//! §Architecture Workstream 1 step 4. Built single-threaded and
//! deterministically (names sorted) so the task set is reproducible.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{used_constants, CheckedConstants, ConstantInfo, KernelError};

pub type TaskId = usize;

#[derive(Debug)]
pub enum TaskKind {
    Simple(NameId),
    InductiveBlock {
        members: Vec<NameId>,
        ctors: Vec<NameId>,
    },
    Quot {
        names: Vec<NameId>,
        eq: NameId,
    },
}

#[derive(Debug)]
pub struct Task {
    pub id: TaskId,
    pub kind: TaskKind,
    /// Names this task admits (flags to flip on success): for Simple, the
    /// one name; for InductiveBlock, members + ctors + recursors; for
    /// Quot, every quotient constant.
    pub admits: Vec<NameId>,
    pub deps: Vec<TaskId>,
}

#[derive(Debug)]
pub struct DepGraph {
    pub tasks: Vec<Task>,
    pub name_to_task: HashMap<NameId, TaskId>,
}

pub fn build_graph(store: &Store, table: &CheckedConstants) -> Result<DepGraph, KernelError> {
    // Deterministic iteration: sort names by raw bits.
    let t = Instant::now();
    let mut names: Vec<NameId> = table.iter_decoded().map(|(&n, _)| n).collect();
    names.sort_by_key(|n| n.bits());
    eprintln!(
        "build_graph: sort {} names in {:.1}s",
        names.len(),
        t.elapsed().as_secs_f64()
    );

    // 1. Assign every name to exactly one task, grouping inductive blocks.
    //    `name_to_task` maps members, ctors, AND recursors to their block.
    let t = Instant::now();
    let mut name_to_task: HashMap<NameId, TaskId> = HashMap::new();
    let mut tasks: Vec<Task> = Vec::new();

    for &n in &names {
        if name_to_task.contains_key(&n) {
            continue; // already claimed by an inductive block
        }
        let ci = table.get_decoded(n).expect("name came from the table");
        match ci {
            ConstantInfo::Induct(iv) => {
                let id = tasks.len();
                // Gather block members (iv.val.all) and their ctors.
                let mut members: Vec<NameId> = Vec::new();
                let mut ctors: Vec<NameId> = Vec::new();
                for &m in &iv.all {
                    members.push(m);
                    let ConstantInfo::Induct(miv) = table.get_decoded(m).ok_or_else(|| {
                        KernelError::MissingConstant(store.to_name(None, Some(m)))
                    })?
                    else {
                        return Err(KernelError::MissingConstant(store.to_name(None, Some(m))));
                    };
                    ctors.extend_from_slice(&miv.ctors);
                }
                let mut admits = members.clone();
                admits.extend_from_slice(&ctors);
                // Recursors: a recursor references its inductive in its
                // type, so any decoded Rec whose used_constants meets this
                // block's member set belongs here. Claimed below in pass 1b.
                for &nm in members.iter().chain(ctors.iter()) {
                    name_to_task.insert(nm, id);
                }
                tasks.push(Task {
                    id,
                    kind: TaskKind::InductiveBlock { members, ctors },
                    admits,
                    deps: Vec::new(),
                });
            }
            ConstantInfo::Ctor(_) => {
                // Claimed by its inductive's block once that block is built;
                // if we reach it first, force its block by visiting induct.
                // (Handled by pass ordering: see below.)
                continue;
            }
            ConstantInfo::Rec(_) => continue, // claimed in pass 1b
            ConstantInfo::Quot(_) => {
                let id = tasks.len();
                // `Eq` = Name::Str { parent: Anonymous, part: "Eq" } — the
                // same name replay.rs::eq_name() builds. `build_graph`
                // only borrows `store` immutably (see the signature in
                // the brief's Interfaces section), so unlike the
                // Arc-side fixture helpers we cannot *intern* a fresh
                // name here — `Eq` must already be one of the table's
                // own decoded names (it's the quotient axioms' own
                // dependency), so resolve it by scanning `names` and
                // comparing decoded `Name`s instead.
                let eq_name = std::sync::Arc::new(leanr_kernel::Name::Str {
                    parent: std::sync::Arc::new(leanr_kernel::Name::Anonymous),
                    part: "Eq".to_string(),
                });
                let eq = names
                    .iter()
                    .copied()
                    .find(|&cand| store.to_name(None, Some(cand)) == eq_name)
                    .ok_or_else(|| KernelError::MissingConstant(eq_name.clone()))?;
                // All quotient constants share one task.
                let quot_names: Vec<NameId> = names
                    .iter()
                    .copied()
                    .filter(|&q| matches!(table.get_decoded(q), Some(ConstantInfo::Quot(_))))
                    .collect();
                for &q in &quot_names {
                    name_to_task.insert(q, id);
                }
                tasks.push(Task {
                    id,
                    kind: TaskKind::Quot {
                        names: quot_names.clone(),
                        eq,
                    },
                    admits: quot_names,
                    deps: Vec::new(),
                });
            }
            _ => {
                let id = tasks.len();
                name_to_task.insert(n, id);
                tasks.push(Task {
                    id,
                    kind: TaskKind::Simple(n),
                    admits: vec![n],
                    deps: Vec::new(),
                });
            }
        }
    }

    eprintln!(
        "build_graph: pass1 (tasks) {} tasks in {:.1}s",
        tasks.len(),
        t.elapsed().as_secs_f64()
    );

    // Pass 1b: claim any not-yet-claimed ctor/rec by resolving to a block.
    let t = Instant::now();
    for &n in &names {
        if name_to_task.contains_key(&n) {
            continue;
        }
        let ci = table.get_decoded(n).expect("name from table");
        let block = resolve_block(store, table, &name_to_task, n, ci)?;
        name_to_task.insert(n, block);
        // Also record it in the block's `admits` so its flag is set.
        tasks[block].admits.push(n);
    }
    eprintln!(
        "build_graph: pass1b (ctor/rec claim) in {:.1}s",
        t.elapsed().as_secs_f64()
    );

    // 2. Edges: for every name, its used_constants → the owning task.
    //    `used_constants` is internally an explicit-stack (iterative) walk,
    //    bounded by input size — no external `RecGuard` is needed here, so
    //    none is threaded through this file.
    //
    //    `used_constants` returns a RAW, duplicate-heavy list (a constant
    //    referenced N times in a term appears N times), so dedup with a
    //    `HashSet<TaskId>` (O(1) membership) instead of `Vec::contains`
    //    (O(current deps)) — the latter made this pass
    //    O(term_size × unique_deps) per task, quadratic on Mathlib's
    //    large proof terms. `seen.insert` returns `true` only on first
    //    sight, so we still push each distinct dep exactly once in
    //    first-occurrence order (identical `deps` to the old `!contains`
    //    guard). One `HashSet` is reused across names, cleared per name
    //    to avoid reallocation.
    let t = Instant::now();
    let mut seen: HashSet<TaskId> = HashSet::new();
    for &n in &names {
        let ci = table.get_decoded(n).expect("name from table");
        let owner = name_to_task[&n];
        seen.clear();
        for dep in used_constants(store, None, ci) {
            let Some(&dep_task) = name_to_task.get(&dep) else {
                return Err(KernelError::MissingConstant(store.to_name(None, Some(dep))));
            };
            if dep_task != owner && seen.insert(dep_task) {
                tasks[owner].deps.push(dep_task);
            }
        }
    }

    // 2b. Quotient init needs an EXPLICIT edge to `Eq` (spec: "one [task]
    //     for quotient init with an explicit edge to `Eq`"). Pass 2's
    //     generic `used_constants` walk only produces this edge
    //     incidentally (because `Quot.lift`'s type embeds a `Const Eq`
    //     node); make it a guaranteed dependency and fail safely with
    //     `MissingConstant` if `Eq` is absent from the table. Reuse the
    //     `seen` set (seeded from the task's existing deps) so the
    //     membership check stays O(1), matching pass 2.
    for (id, task) in tasks.iter_mut().enumerate() {
        let TaskKind::Quot { eq, .. } = task.kind else {
            continue;
        };
        // `eq: NameId` is `Copy`, so the destructure above copies it out.
        let eq_task = *name_to_task
            .get(&eq)
            .ok_or_else(|| KernelError::MissingConstant(store.to_name(None, Some(eq))))?;
        seen.clear();
        seen.extend(task.deps.iter().copied());
        if eq_task != id && seen.insert(eq_task) {
            task.deps.push(eq_task);
        }
    }
    eprintln!(
        "build_graph: pass2 (edges) {} tasks in {:.1}s",
        tasks.len(),
        t.elapsed().as_secs_f64()
    );

    Ok(DepGraph {
        tasks,
        name_to_task,
    })
}

/// Resolve a stray constructor/recursor to its inductive block.
fn resolve_block(
    store: &Store,
    _table: &CheckedConstants,
    name_to_task: &HashMap<NameId, TaskId>,
    n: NameId,
    ci: &ConstantInfo,
) -> Result<TaskId, KernelError> {
    match ci {
        // A constructor names its inductive directly.
        ConstantInfo::Ctor(cv) => name_to_task
            .get(&cv.induct)
            .copied()
            .ok_or_else(|| KernelError::MissingConstant(store.to_name(None, Some(cv.induct)))),
        // A recursor carries `rv.all` — the mutual inductives it recurses
        // over. Every member of `rv.all` was claimed into the SAME
        // `InductiveBlock` task in pass 1, so its block is the one owning
        // `rv.all[0]`. (Resolving via `used_constants` instead would grab
        // the first dep with any task entry — possibly an unrelated
        // `Simple` — and silently misassign the recursor.)
        ConstantInfo::Rec(rv) => rv
            .all
            .first()
            .and_then(|m| name_to_task.get(m))
            .copied()
            .ok_or_else(|| KernelError::MissingConstant(store.to_name(None, Some(n)))),
        _ => Err(KernelError::MissingConstant(store.to_name(None, Some(n)))),
    }
}
