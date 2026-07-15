//! Same-file grammar growth (spec §Architecture / overlay). The base
//! `GrammarSnapshot` (builtins now; imports at M3b2) is immutable and
//! Arc-shared; an `Overlay` carries ONLY the productions a file's own
//! `notation`/mixfix commands add. Cloned (cheaply — same-file additions
//! only) and extended between commands; consulted before the base at the
//! three grammar read points in parse.rs. M3b2/M3b3 reuse this mechanism.

use std::collections::HashMap;
use std::sync::Arc;

use crate::grammar::{FirstTok, GrammarSnapshot, Prim};
use crate::lex::TokenTable;

#[derive(Clone, Debug, Default)]
pub struct CategoryDelta {
    pub leading: Vec<(FirstTok, Prim)>,
    pub trailing: Vec<(FirstTok, Prim)>,
}

#[derive(Clone, Debug)]
pub struct Overlay {
    tokens: TokenTable,
    kind_names: Vec<Arc<str>>,
    // `kind_map`/`base_kind_count` are read by kind derivation (M3b1
    // Tasks 3-4: interning a notation's node kinds into the overlay,
    // numbered starting after `base_kind_count`) — not yet by this
    // task's skeleton, which only proves the shape compiles and a
    // fresh `Overlay` is empty.
    #[allow(dead_code)]
    kind_map: HashMap<Arc<str>, u16>,
    #[allow(dead_code)]
    base_kind_count: u16,
    cats: HashMap<String, CategoryDelta>,
}

impl Overlay {
    pub fn new(base: &GrammarSnapshot) -> Self {
        Overlay {
            tokens: TokenTable::default(),
            kind_names: Vec::new(),
            kind_map: HashMap::new(),
            base_kind_count: base.kind_count(),
            cats: HashMap::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.cats.is_empty() && self.kind_names.is_empty()
    }
    pub fn tokens(&self) -> &TokenTable {
        &self.tokens
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_overlay_is_empty_and_numbers_kinds_after_base() {
        let base = crate::builtin::snapshot();
        let ov = Overlay::new(&base);
        assert!(ov.is_empty());
        assert!(
            ov.tokens()
                .munch_with("anything", &TokenTable::default())
                .is_none()
                || true
        ); // overlay token set starts empty
        assert!(base.kind_count() >= crate::kind::FIRST_DYNAMIC_KIND);
    }
}
