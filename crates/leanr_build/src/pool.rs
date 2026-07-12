//! Generic dependency-counter scheduler (M2b spec §Architecture,
//! component `pool`): the leanr_check shape — ready queue under a
//! Mutex+Condvar, fail-fast, first-failure slot — reimplemented for
//! index-based jobs. One Mutex around all state (not leanr_check's
//! lock-free atomics): pool items here are 100ms+ subprocesses, so
//! lock contention is noise. Knows nothing about modules or processes;
//! this genericity is the seam where M2c inserts cache lookups and M4
//! swaps in leanr's own elaborator.
//!
//! Cycles are the caller's problem: `resolve()` already rejects them
//! (`topo_waves`), and the in-flight guard below turns an impossible
//! stall into a clean return rather than a hang.

use std::collections::VecDeque;
use std::sync::{Condvar, Mutex};

#[derive(Debug)]
pub struct PoolFailure {
    pub item: usize,
    pub message: String,
}

struct State {
    ready: VecDeque<usize>,
    remaining: Vec<usize>,
    in_flight: usize,
    done: usize,
    cancelled: bool,
    failure: Option<PoolFailure>,
}

/// Run `job` for every item, respecting `deps` (deps[i] = indices i
/// waits on), at most `jobs` at a time. Fail-fast: the first failure
/// abandons everything not yet started; in-flight jobs finish.
/// `on_done(item, done_count, total)` fires after each success.
pub fn run(
    deps: &[Vec<usize>],
    jobs: usize,
    job: &(dyn Fn(usize) -> Result<(), String> + Sync),
    on_done: &(dyn Fn(usize, usize, usize) + Sync),
) -> Result<(), PoolFailure> {
    let total = deps.len();
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); total];
    let mut remaining = vec![0usize; total];
    for (i, ds) in deps.iter().enumerate() {
        remaining[i] = ds.len();
        for &d in ds {
            dependents[d].push(i);
        }
    }
    let state = Mutex::new(State {
        ready: (0..total).filter(|&i| remaining[i] == 0).collect(),
        remaining,
        in_flight: 0,
        done: 0,
        cancelled: false,
        failure: None,
    });
    let cv = Condvar::new();
    let workers = jobs.max(1).min(total.max(1));
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let item = {
                    let mut st = state.lock().unwrap();
                    loop {
                        if st.cancelled || st.done == total {
                            return;
                        }
                        if let Some(i) = st.ready.pop_front() {
                            st.in_flight += 1;
                            break i;
                        }
                        if st.in_flight == 0 {
                            // Nothing ready, nothing running: exhausted
                            // (or a cycle, excluded upstream) — don't hang.
                            return;
                        }
                        st = cv.wait(st).unwrap();
                    }
                };
                let result = job(item);
                let mut st = state.lock().unwrap();
                st.in_flight -= 1;
                match result {
                    Ok(()) => {
                        st.done += 1;
                        let done = st.done;
                        for &d in &dependents[item] {
                            st.remaining[d] -= 1;
                            if st.remaining[d] == 0 {
                                st.ready.push_back(d);
                            }
                        }
                        drop(st);
                        cv.notify_all();
                        on_done(item, done, total);
                    }
                    Err(message) => {
                        if st.failure.is_none() {
                            st.failure = Some(PoolFailure { item, message });
                        }
                        st.cancelled = true;
                        drop(st);
                        cv.notify_all();
                        return;
                    }
                }
            });
        }
    });
    let mut st = state.lock().unwrap();
    match st.failure.take() {
        Some(f) => Err(f),
        None => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    fn record_order(deps: &[Vec<usize>], jobs: usize) -> Vec<usize> {
        let order = Mutex::new(Vec::new());
        run(
            deps,
            jobs,
            &|i| {
                order.lock().unwrap().push(i);
                Ok(())
            },
            &|_, _, _| {},
        )
        .unwrap();
        order.into_inner().unwrap()
    }

    #[test]
    fn empty_graph_completes() {
        assert!(run(&[], 4, &|_| Ok(()), &|_, _, _| {}).is_ok());
    }

    #[test]
    fn diamond_respects_dependency_order() {
        // 0 -> {1, 2} -> 3   (deps[i] lists what i waits on)
        let deps = vec![vec![], vec![0], vec![0], vec![1, 2]];
        for jobs in [1, 4] {
            let order = record_order(&deps, jobs);
            assert_eq!(order.len(), 4);
            let pos = |x: usize| order.iter().position(|&i| i == x).unwrap();
            assert!(pos(0) < pos(1) && pos(0) < pos(2) && pos(1) < pos(3) && pos(2) < pos(3));
        }
    }

    #[test]
    fn long_chain_completes_with_many_workers() {
        let deps: Vec<Vec<usize>> = (0..100)
            .map(|i| if i == 0 { vec![] } else { vec![i - 1] })
            .collect();
        let order = record_order(&deps, 8);
        assert_eq!(order, (0..100).collect::<Vec<_>>());
    }

    #[test]
    fn failure_cancels_downstream_and_reports_first_failure() {
        // 0 -> 1(fails) -> 2 ; 3 independent
        let deps = vec![vec![], vec![0], vec![1], vec![]];
        let ran = Mutex::new(Vec::new());
        let err = run(
            &deps,
            1,
            &|i| {
                ran.lock().unwrap().push(i);
                if i == 1 {
                    Err("boom".into())
                } else {
                    Ok(())
                }
            },
            &|_, _, _| {},
        )
        .unwrap_err();
        assert_eq!(err.item, 1);
        assert_eq!(err.message, "boom");
        assert!(
            !ran.lock().unwrap().contains(&2),
            "dependent of a failure must never run"
        );
    }

    #[test]
    fn parallelism_is_bounded_by_jobs() {
        let deps: Vec<Vec<usize>> = (0..16).map(|_| vec![]).collect();
        let current = AtomicUsize::new(0);
        let high = AtomicUsize::new(0);
        run(
            &deps,
            2,
            &|_| {
                let c = current.fetch_add(1, Ordering::SeqCst) + 1;
                high.fetch_max(c, Ordering::SeqCst);
                std::thread::sleep(std::time::Duration::from_millis(10));
                current.fetch_sub(1, Ordering::SeqCst);
                Ok(())
            },
            &|_, _, _| {},
        )
        .unwrap();
        assert!(high.load(Ordering::SeqCst) <= 2);
    }

    #[test]
    fn on_done_counts_monotonically_to_total() {
        let deps: Vec<Vec<usize>> = (0..5).map(|_| vec![]).collect();
        let seen = Mutex::new(Vec::new());
        run(&deps, 3, &|_| Ok(()), &|_, done, total| {
            assert_eq!(total, 5);
            seen.lock().unwrap().push(done);
        })
        .unwrap();
        let mut s = seen.into_inner().unwrap();
        s.sort_unstable();
        assert_eq!(s, vec![1, 2, 3, 4, 5]);
    }
}
