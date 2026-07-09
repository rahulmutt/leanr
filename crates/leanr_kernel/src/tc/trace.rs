//! Feature-gated reduction-step tally for the Result-B diagnosis spike.
//! Off by default (`trace-reductions`), so the shipped kernel is unchanged.
//!
//! `reset`/`snapshot`/`total` are consumed by the gated unit test today
//! and by the later diagnosis-spike driver (Task 3); only `record` has a
//! non-test caller yet, so the unused half of this crate-internal API
//! needs an explicit allow rather than tripping the lint gate.
#![allow(dead_code, unused_imports)]

#[cfg(feature = "trace-reductions")]
mod imp {
    use std::cell::RefCell;
    use std::collections::HashMap;

    thread_local! {
        static TALLY: RefCell<HashMap<(String, &'static str), u64>> =
            RefCell::new(HashMap::new());
    }

    pub fn record(callee: &str, major_kind: &'static str) {
        TALLY.with(|t| {
            *t.borrow_mut()
                .entry((callee.to_string(), major_kind))
                .or_insert(0) += 1;
        });
    }

    pub fn reset() {
        TALLY.with(|t| t.borrow_mut().clear());
    }

    pub fn total() -> u64 {
        TALLY.with(|t| t.borrow().values().sum())
    }

    pub fn snapshot() -> Vec<((String, &'static str), u64)> {
        TALLY.with(|t| {
            let mut v: Vec<_> = t.borrow().iter().map(|(k, &c)| (k.clone(), c)).collect();
            v.sort_by_key(|b| std::cmp::Reverse(b.1));
            v
        })
    }
}

#[cfg(not(feature = "trace-reductions"))]
mod imp {
    #[inline(always)]
    pub fn record(_callee: &str, _major_kind: &'static str) {}
    #[inline(always)]
    pub fn reset() {}
    #[inline(always)]
    pub fn total() -> u64 {
        0
    }
    #[inline(always)]
    pub fn snapshot() -> Vec<((String, &'static str), u64)> {
        Vec::new()
    }
}

pub use imp::{record, reset, snapshot, total};
