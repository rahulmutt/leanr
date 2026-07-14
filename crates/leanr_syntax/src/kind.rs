//! Interned syntax-node kinds. Lean kinds are an open set of hierarchical
//! NAMES (`Lean.Parser.Command.declaration`, Mathlib's own kinds, …);
//! rowan raw kinds are u16. `KindInterner` bridges (spec §Architecture:
//! a few thousand kinds in practice, far under 65k). Kind names must
//! match official Lean's byte-for-byte — oracle equality depends on it.

use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxKind(pub u16);

// Fixed leaf/utility kinds. Leaves first (tests use `is_trivia`/`is_leaf`).
pub const KIND_WHITESPACE: SyntaxKind = SyntaxKind(0);
pub const KIND_LINE_COMMENT: SyntaxKind = SyntaxKind(1);
pub const KIND_BLOCK_COMMENT: SyntaxKind = SyntaxKind(2);
/// Keyword/symbol leaf ("def", ":=", "=>", …) — Lean `Syntax.atom`.
pub const KIND_ATOM: SyntaxKind = SyntaxKind(3);
/// Identifier leaf — Lean `Syntax.ident` (raw source text, incl. escapes).
pub const KIND_IDENT: SyntaxKind = SyntaxKind(4);
/// Unlexable byte run (untrusted-input totality; never panic).
pub const KIND_ERROR_TOKEN: SyntaxKind = SyntaxKind(5);
/// Error NODE produced by recovery (contains skipped tokens).
pub const KIND_ERROR: SyntaxKind = SyntaxKind(6);
/// Lean `Syntax.missing`.
pub const KIND_MISSING: SyntaxKind = SyntaxKind(7);
/// Lean nullKind ("null"): optional/many/sepBy grouping.
pub const KIND_NULL: SyntaxKind = SyntaxKind(8);
pub const KIND_GROUP: SyntaxKind = SyntaxKind(9);
pub const KIND_CHOICE: SyntaxKind = SyntaxKind(10);
pub const FIRST_DYNAMIC_KIND: u16 = 11;

pub fn is_trivia(k: SyntaxKind) -> bool {
    k == KIND_WHITESPACE || k == KIND_LINE_COMMENT || k == KIND_BLOCK_COMMENT
}

pub fn is_leaf(k: SyntaxKind) -> bool {
    k.0 <= KIND_ERROR_TOKEN.0
}

/// Append-only name↔u16 interner. Built once per `GrammarSnapshot`
/// (snapshot construction pre-interns every kind its grammar can emit),
/// shared `Arc` with every tree parsed under it — parsing itself never
/// mutates the interner. `Clone` is cheap (an `Arc<str>` per name) and
/// is used by `parse`'s test harness, which builds trees straight from
/// a test-owned interner rather than a `GrammarSnapshot`'s `Arc`.
#[derive(Clone, Debug)]
pub struct KindInterner {
    names: Vec<Arc<str>>,
    map: HashMap<Arc<str>, u16>,
}

impl KindInterner {
    pub fn new() -> Self {
        let mut it = KindInterner {
            names: Vec::new(),
            map: HashMap::new(),
        };
        // Fixed slots — order MUST match the constants above. The oracle-
        // visible names among them: "null", "group", "choice", "<missing>".
        for name in [
            "<whitespace>",
            "<line-comment>",
            "<block-comment>",
            "<atom>",
            "<ident>",
            "<error-token>",
            "<error>",
            "<missing>",
            "null",
            "group",
            "choice",
        ] {
            it.intern(name);
        }
        it
    }

    pub fn intern(&mut self, name: &str) -> SyntaxKind {
        if let Some(&k) = self.map.get(name) {
            return SyntaxKind(k);
        }
        let k = u16::try_from(self.names.len())
            .expect("more than 65535 distinct syntax kinds in one snapshot");
        let arc: Arc<str> = Arc::from(name);
        self.names.push(arc.clone());
        self.map.insert(arc, k);
        SyntaxKind(k)
    }

    pub fn lookup(&self, name: &str) -> Option<SyntaxKind> {
        self.map.get(name).map(|&k| SyntaxKind(k))
    }

    pub fn name(&self, k: SyntaxKind) -> &str {
        &self.names[k.0 as usize]
    }
}

impl Default for KindInterner {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_kinds_occupy_their_slots() {
        let it = KindInterner::new();
        assert_eq!(it.name(KIND_NULL), "null");
        assert_eq!(it.name(KIND_MISSING), "<missing>");
        assert_eq!(it.lookup("group"), Some(KIND_GROUP));
    }

    #[test]
    fn intern_is_idempotent_and_dynamic_kinds_start_after_fixed() {
        let mut it = KindInterner::new();
        let k1 = it.intern("Lean.Parser.Command.declaration");
        let k2 = it.intern("Lean.Parser.Command.declaration");
        assert_eq!(k1, k2);
        assert_eq!(k1.0, FIRST_DYNAMIC_KIND);
        assert_eq!(it.name(k1), "Lean.Parser.Command.declaration");
    }
}
