//! Feature-gated reduction-step tally for the Result-B diagnosis spike.
//! Off by default (`trace-reductions`), so the shipped kernel is unchanged.
//!
//! `record` is the only fn with a non-test caller today (the `tc.rs`
//! recursor site). `reset`/`snapshot`/`total` are the read side, consumed
//! by the gated unit test now and by the diagnosis-spike driver (Task 3)
//! later — so they carry per-item `dead_code` allows, keeping `record`
//! itself lint-checked and leaving any genuinely-dead fn added here later
//! flagged. With the feature OFF the record site in `tc.rs` is entirely
//! `#[cfg]`-compiled away, so the whole no-op module below is uncalled
//! (its module-level allow), and the re-export has no user (its allow).

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

    #[allow(dead_code)] // read side: test + Task-3 spike only, no lib caller yet
    pub fn reset() {
        TALLY.with(|t| t.borrow_mut().clear());
    }

    #[allow(dead_code)] // read side: test + Task-3 spike only, no lib caller yet
    pub fn total() -> u64 {
        TALLY.with(|t| t.borrow().values().sum())
    }

    #[allow(dead_code)] // read side: test + Task-3 spike only, no lib caller yet
    pub fn snapshot() -> Vec<((String, &'static str), u64)> {
        TALLY.with(|t| {
            let mut v: Vec<_> = t.borrow().iter().map(|(k, &c)| (k.clone(), c)).collect();
            v.sort_by_key(|b| std::cmp::Reverse(b.1));
            v
        })
    }
}

#[cfg(not(feature = "trace-reductions"))]
#[allow(dead_code)] // no caller in the feature-off config (record site is #[cfg]-gated out)
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

// Narrow, single-statement allow: `record` has a lib user only under the
// feature; the read side (`reset`/`snapshot`/`total`) has none outside the
// test/spike. This lint is `unused_imports` on one re-export line only, so
// it cannot mask a genuinely-dead function (those are `dead_code`, checked
// per item above).
#[allow(unused_imports)]
pub use imp::{record, reset, snapshot, total};
