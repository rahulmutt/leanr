//! Same-file grammar growth (spec §Architecture / overlay). The base
//! `GrammarSnapshot` (builtins now; imports at M3b2) is immutable and
//! Arc-shared; an `Overlay` carries ONLY the productions a file's own
//! `notation`/mixfix commands add. Cloned (cheaply — same-file additions
//! only) and extended between commands; consulted before the base at the
//! three grammar read points in parse.rs. M3b2/M3b3 reuse this mechanism.

use std::collections::HashMap;
use std::sync::Arc;

use crate::grammar::{encode_prim, index_entries, FirstTok, GrammarSnapshot, NotationSpec, Prim};
use crate::kind::SyntaxKind;
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
    kind_map: HashMap<Arc<str>, u16>,
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

    /// Fold a derived `NotationSpec` (M3b1 Task 4) into this overlay:
    /// intern its generated kind, harvest its token(s), wrap its body in
    /// `Prim::Node` (leading) or `Prim::TrailingNode` (trailing — a
    /// same-category placeholder led the declaration and becomes the
    /// Pratt-wrapped lhs), index the whole production by first-token via
    /// the SAME `index_entries` `SnapshotBuilder::leading2`/`trailing2`
    /// use for the base grammar (`grammar/mod.rs`), and append it to the
    /// right side of the category's delta. Structurally identical to
    /// what `SnapshotBuilder` builds for a base production — the only
    /// difference is `CategoryDelta` (Task 1) stores `(FirstTok, Prim)`
    /// pairs directly rather than `(FirstTok, usize)` indices into a
    /// separate parser vec, since an overlay's deltas are small,
    /// same-file additions, not a whole snapshot's worth of productions.
    pub fn register(&mut self, spec: NotationSpec) -> SyntaxKind {
        // Intern the generated kind AFTER the base (overlay-local,
        // bounded by command count — never per-token).
        let kind = self.intern(&spec.kind_name);
        for t in &spec.tokens {
            self.tokens.insert(t);
        }
        // `spec.leading == spec.lhs_prec.is_none()` always holds (Task
        // 4's `build_spec`: a leading placeholder sets BOTH `leading =
        // false` and `lhs_prec = Some(..)` together, a leading symbol
        // sets both the opposite way) — route on `lhs_prec` per the
        // brief, and check that invariant rather than silently trusting
        // it twice.
        debug_assert_eq!(
            spec.leading,
            spec.lhs_prec.is_none(),
            "NotationSpec::leading must equal lhs_prec.is_none()"
        );
        let is_trailing = spec.lhs_prec.is_some();
        let prim = if let Some(lhs) = spec.lhs_prec {
            Prim::TrailingNode {
                kind,
                prec: spec.prec,
                lhs_prec: lhs,
                body: Arc::new(spec.body),
            }
        } else {
            Prim::Node {
                kind,
                prec: Some(spec.prec),
                body: Arc::new(spec.body),
            }
        };
        let fts = index_entries(&prim);
        let cd = self.cats.entry(spec.category).or_default();
        for ft in fts {
            if is_trailing {
                cd.trailing.push((ft, prim.clone()));
            } else {
                cd.leading.push((ft, prim.clone()));
            }
        }
        kind
    }

    /// Intern `name` into the overlay's OWN kind space, numbered
    /// starting at `base_kind_count` (never colliding with the base
    /// snapshot's kinds — see `new`'s own doc comment). Idempotent: a
    /// second `register` for the same generated kind name (re-running
    /// the same notation command, or two notations that happen to mangle
    /// to the same name) returns the SAME `SyntaxKind` rather than
    /// interning a duplicate — collision-suffixing (`_1`/`_2`, real
    /// Lean's `mkUnusedBaseName`) is out of scope for M3b1 (task brief).
    fn intern(&mut self, name: &str) -> SyntaxKind {
        if let Some(&k) = self.kind_map.get(name) {
            return SyntaxKind(k);
        }
        let k = self.base_kind_count + self.kind_names.len() as u16;
        let arc: Arc<str> = Arc::from(name);
        self.kind_names.push(arc.clone());
        self.kind_map.insert(arc, k);
        SyntaxKind(k)
    }

    /// `k`'s overlay-local name, if `k` was interned by THIS overlay
    /// (`k.0 >= base_kind_count`) — a base-snapshot kind (or a kind from
    /// a different overlay) is never resolvable here, matching
    /// `KindInterner::name`'s own "only its own kinds" contract.
    pub fn kind_name(&self, k: SyntaxKind) -> Option<&str> {
        k.0.checked_sub(self.base_kind_count)
            .and_then(|i| self.kind_names.get(i as usize))
            .map(|s| &**s)
    }
    pub fn lookup_kind(&self, name: &str) -> Option<SyntaxKind> {
        self.kind_map.get(name).map(|&k| SyntaxKind(k))
    }
    pub fn category_delta(&self, name: &str) -> Option<&CategoryDelta> {
        self.cats.get(name)
    }

    /// This overlay's own kind names, in REGISTRATION order — i.e.
    /// exactly the order `intern` handed out the ids `base_kind_count..`
    /// (see `intern`'s own doc comment). `pub(crate)`: the one thing
    /// `parse.rs`'s `Ps::merged_kinds` (M3b1 Task 6) needs to fold this
    /// overlay's kinds into a fresh clone of the base `KindInterner` and
    /// get back the SAME numbering `Overlay::intern` already assigned —
    /// `KindInterner::intern` is append-only, so re-interning these names
    /// in this exact order, into an interner that already has
    /// `base_kind_count` entries, reproduces `base_kind_count + i` for
    /// the `i`-th name here.
    pub(crate) fn kind_names(&self) -> &[Arc<str>] {
        &self.kind_names
    }

    /// Extend `h` with this overlay's contribution to the grammar's
    /// fingerprint (spec: the M5 query-firewall seam) — so registering a
    /// notation changes the effective (base + overlay) fingerprint (Task
    /// 10). Mirrors `GrammarSnapshot::fingerprint`'s own shape: tokens
    /// (the `TokenTable`'s `BTreeSet` iteration order is already sorted),
    /// kind names in REGISTRATION order (not sorted — order is itself
    /// part of the grammar's history, same as `kind_names`'s role in
    /// `kind_name`), then each category (sorted by name, since `cats` is
    /// a `HashMap`) walked leading-then-trailing through the SAME
    /// `encode_prim` the base fingerprint uses, resolving kinds via this
    /// overlay's own `kind_name` (never a `GrammarSnapshot`'s — see
    /// `encode_prim`'s own doc comment in `grammar/mod.rs` for why its
    /// kind-name resolver is a closure rather than a bare snapshot ref).
    pub fn fingerprint_into(&self, h: &mut blake3::Hasher) {
        h.update(b"leanr-m3b1-overlay-v1\0");
        for t in self.tokens.iter() {
            h.update(t.as_bytes());
            h.update(b"\0");
        }
        for name in &self.kind_names {
            h.update(name.as_bytes());
            h.update(b"\0");
        }
        let kind_name = |k: SyntaxKind| -> String {
            self.kind_name(k)
                .map(|s| s.to_string())
                .unwrap_or_else(|| format!("<overlay-unknown-kind-{}>", k.0))
        };
        let mut names: Vec<&String> = self.cats.keys().collect();
        names.sort();
        for name in names {
            h.update(name.as_bytes());
            h.update(b"\x01");
            let cd = &self.cats[name];
            for (_, p) in cd.leading.iter().chain(&cd.trailing) {
                encode_prim(p, &kind_name, h);
            }
        }
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
        assert!(ov
            .tokens()
            .munch_with("anything", &TokenTable::default())
            .is_none()); // overlay token set starts empty
        assert!(base.kind_count() >= crate::kind::FIRST_DYNAMIC_KIND);
    }

    #[test]
    fn register_adds_token_kind_and_trailing_entry() {
        let base = crate::builtin::snapshot();
        let mut ov = Overlay::new(&base);
        let spec = NotationSpec {
            category: "term".into(),
            kind_name: "«term_⊕_»".into(),
            leading: false,
            prec: 65,
            lhs_prec: Some(65),
            tokens: vec!["⊕".into()],
            body: crate::grammar::seq([
                crate::grammar::cat("term", 66),
                crate::grammar::sym("⊕"),
                crate::grammar::cat("term", 66),
            ]),
        };
        let k = ov.register(spec);
        // kind numbered after the base
        assert!(k.0 >= base.kind_count());
        assert_eq!(ov.kind_name(k), Some("«term_⊕_»"));
        assert_eq!(ov.lookup_kind("«term_⊕_»"), Some(k));
        // token now munches
        assert_eq!(
            ov.tokens()
                .munch_with("⊕ x", &crate::lex::TokenTable::default()),
            Some("⊕")
        );
        // a trailing entry exists for the term category
        assert!(ov.category_delta("term").unwrap().trailing.len() == 1);
        assert!(!ov.is_empty());
    }
}
