use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::sync::Arc;

use crate::Nat;

/// Lean hierarchical name (oracle: Init/Prelude.lean:4693-4717). The
/// oracle's runtime objects also carry a cached hash as a computed
/// field; we drop it on decode and recompute lazily when needed (M1b).
///
/// INVARIANT (crate docs): parent chains can be untrusted-deep, so
/// PartialEq/Hash/Display/Drop below are all loops, never recursion.
/// Deriving any of them would reintroduce a stack overflow on
/// adversarial input — do not "simplify" back to derives.
#[derive(Debug)]
pub enum Name {
    Anonymous,
    Str { parent: Arc<Name>, part: String },
    Num { parent: Arc<Name>, part: Nat },
}

impl Name {
    fn parent(&self) -> Option<&Arc<Name>> {
        match self {
            Name::Anonymous => None,
            Name::Str { parent, .. } | Name::Num { parent, .. } => Some(parent),
        }
    }
}

impl PartialEq for Name {
    fn eq(&self, other: &Name) -> bool {
        let (mut a, mut b) = (self, other);
        loop {
            match (a, b) {
                (Name::Anonymous, Name::Anonymous) => return true,
                (
                    Name::Str {
                        parent: pa,
                        part: sa,
                    },
                    Name::Str {
                        parent: pb,
                        part: sb,
                    },
                ) => {
                    if sa != sb {
                        return false;
                    }
                    (a, b) = (pa, pb);
                }
                (
                    Name::Num {
                        parent: pa,
                        part: na,
                    },
                    Name::Num {
                        parent: pb,
                        part: nb,
                    },
                ) => {
                    if na != nb {
                        return false;
                    }
                    (a, b) = (pa, pb);
                }
                _ => return false,
            }
        }
    }
}

impl Eq for Name {}

impl Hash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut cur = self;
        loop {
            match cur {
                Name::Anonymous => {
                    state.write_u8(0);
                    return;
                }
                Name::Str { parent, part } => {
                    state.write_u8(1);
                    part.hash(state);
                    cur = parent;
                }
                Name::Num { parent, part } => {
                    state.write_u8(2);
                    part.hash(state);
                    cur = parent;
                }
            }
        }
    }
}

/// Matches the oracle's `Name.toString (escape := false)`: components
/// joined with `.`, no identifier escaping. The golden-fixture dump
/// script (tests/fixtures/dump_decls.lean) prints names the same way,
/// so the two sides compare byte-for-byte.
impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if matches!(self, Name::Anonymous) {
            return f.write_str("[anonymous]");
        }
        let mut components: Vec<&Name> = Vec::new();
        let mut cur = self;
        while !matches!(cur, Name::Anonymous) {
            components.push(cur);
            cur = cur.parent().expect("non-anonymous names have parents");
        }
        for (i, component) in components.iter().rev().enumerate() {
            if i > 0 {
                f.write_str(".")?;
            }
            match component {
                Name::Anonymous => unreachable!("filtered above"),
                Name::Str { part, .. } => f.write_str(part)?,
                Name::Num { part, .. } => write!(f, "{part}")?,
            }
        }
        Ok(())
    }
}

impl Drop for Name {
    fn drop(&mut self) {
        // Detach the parent and unwind the chain with an explicit
        // stack. Each node we uniquely own gets its parent replaced by
        // Anonymous before it drops, so its own Drop recursion is O(1).
        let mut stack: Vec<Arc<Name>> = Vec::new();
        if let Some(parent) = self.parent_mut() {
            stack.push(mem::replace(parent, Arc::new(Name::Anonymous)));
        }
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                if let Some(parent) = owned.parent_mut() {
                    stack.push(mem::replace(parent, Arc::new(Name::Anonymous)));
                }
            }
        }
    }
}

impl Name {
    fn parent_mut(&mut self) -> Option<&mut Arc<Name>> {
        match self {
            Name::Anonymous => None,
            Name::Str { parent, .. } | Name::Num { parent, .. } => Some(parent),
        }
    }
}
