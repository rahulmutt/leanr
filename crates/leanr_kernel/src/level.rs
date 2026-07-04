use std::fmt;
use std::mem;
use std::sync::Arc;

use crate::Name;

/// Universe level (oracle: src/Lean/Level.lean:90-103). The oracle also
/// stores a computed `data` u64 (hash/depth/flags); we drop it on
/// decode and recompute in M1b. `MVar` is decoded faithfully; the
/// checker rejects metavariables, not the parser (spec).
///
/// No derived Eq/Ord/Hash: adversarial depth makes derived recursive
/// traversals a stack-overflow hazard; M1b adds hash-consed comparison.
/// Manual iterative Debug impl (see Name for pattern): depth is
/// attacker-controlled and recursion is forbidden.
pub enum Level {
    Zero,
    Succ(Arc<Level>),
    Max(Arc<Level>, Arc<Level>),
    IMax(Arc<Level>, Arc<Level>),
    Param(Arc<Name>),
    MVar(Arc<Name>),
}

/// Manual (non-derived) impl: iterative formatting instead of recursing
/// into Arc children, so it stays safe on adversarially deep chains.
/// Renders as `Level::Zero`, `Level::Succ(..)`, etc.
impl fmt::Debug for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Level::Zero => f.write_str("Level::Zero"),
            Level::Succ(_) => f.write_str("Level::Succ(..)"),
            Level::Max(_, _) => f.write_str("Level::Max(.., ..)"),
            Level::IMax(_, _) => f.write_str("Level::IMax(.., ..)"),
            Level::Param(n) => write!(f, "Level::Param({:?})", n),
            Level::MVar(n) => write!(f, "Level::MVar({:?})", n),
        }
    }
}

impl Drop for Level {
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Level>> = Vec::new();
        take_level_children(self, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_level_children(&mut owned, &mut stack);
            }
        }
    }
}

/// Detach `Arc<Level>` children into `stack`, leaving cheap leaves
/// behind so the node's own drop is O(1).
fn take_level_children(l: &mut Level, stack: &mut Vec<Arc<Level>>) {
    let zero = || Arc::new(Level::Zero);
    match l {
        Level::Zero | Level::Param(_) | Level::MVar(_) => {}
        Level::Succ(a) => stack.push(mem::replace(a, zero())),
        Level::Max(a, b) | Level::IMax(a, b) => {
            stack.push(mem::replace(a, zero()));
            stack.push(mem::replace(b, zero()));
        }
    }
}
