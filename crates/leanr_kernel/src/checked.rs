//! The gated declaration table (`CheckedConstants`) and the `ConstSource`
//! seam the checker's `EnvView` consults. Spec:
//! docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md
//! (§Components, §Key enabling observation). `CheckedConstants` is
//! populated in Task 2; this task only introduces the enum so `EnvView`
//! can be generalized without a behavior change.

use std::collections::HashMap;

use crate::bank::NameId;
use crate::ConstantInfo;

/// Where an `EnvView` resolves a `NameId` to a `ConstantInfo`.
/// `Plain` is the sequential environment's plain map (identical behavior
/// to the pre-refactor `&HashMap`); `Gated` is the parallel driver's
/// admitted-flag-gated table (Task 2).
#[derive(Clone, Copy)]
pub enum ConstSource<'a> {
    Plain(&'a HashMap<NameId, ConstantInfo>),
    Gated(&'a CheckedConstants),
}

impl<'a> ConstSource<'a> {
    pub fn get(&self, n: NameId) -> Option<&'a ConstantInfo> {
        match self {
            ConstSource::Plain(m) => m.get(&n),
            ConstSource::Gated(c) => c.get(n),
        }
    }
}

/// Placeholder filled in by Task 2. Present now only so `ConstSource`'s
/// `Gated` variant type-checks.
pub struct CheckedConstants {
    map: HashMap<NameId, ConstantInfo>,
}

impl CheckedConstants {
    pub fn get(&self, n: NameId) -> Option<&ConstantInfo> {
        self.map.get(&n)
    }
}
