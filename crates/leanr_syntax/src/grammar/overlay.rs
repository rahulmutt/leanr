//! Same-file grammar growth (spec §Architecture / overlay). The base
//! `GrammarSnapshot` (builtins now; imports at M3b2) is immutable and
//! Arc-shared; an `Overlay` carries ONLY the productions a file's own
//! `notation`/mixfix commands add. Cloned (cheaply — same-file additions
//! only) and extended between commands; consulted before the base at the
//! three grammar read points in parse.rs. M3b2/M3b3 reuse this mechanism.

use std::collections::HashMap;
use std::sync::Arc;

use crate::grammar::{
    encode_prim, index_entries, FirstTok, GrammarSnapshot, LeadingIdentBehavior, NotationSpec,
    Prim, SpecScope,
};
use crate::kind::SyntaxKind;
use crate::lex::TokenTable;

/// M3b3 Task 4: deterministic byte encoding of an entry's activation
/// tag into the overlay fingerprint (`fingerprint_into`): `\x00` for
/// `Global`, `\x01 ++ ns ++ \0` for `Scoped`, `\x02 ++ scope_len` for
/// `Local`. Distinct lead bytes keep the three cases unambiguous.
fn encode_spec_scope(scope: &SpecScope, h: &mut blake3::Hasher) {
    match scope {
        SpecScope::Global => h.update(b"\x00"),
        SpecScope::Scoped(ns) => {
            h.update(b"\x01");
            h.update(ns.as_bytes());
            h.update(b"\0")
        }
        SpecScope::Local { scope_len } => {
            h.update(b"\x02");
            h.update(&(*scope_len as u64).to_le_bytes())
        }
    };
}

#[derive(Clone, Debug, Default)]
pub struct CategoryDelta {
    /// M3b3 Task 4: each entry carries its activation `SpecScope`
    /// alongside the `(FirstTok, Prim)` pair — every overlay read point
    /// in `parse.rs` filters candidates by `ps.scope.is_active(scope)`
    /// so a `scoped`/`local` production only dispatches while in force.
    pub leading: Vec<(FirstTok, Prim, SpecScope)>,
    pub trailing: Vec<(FirstTok, Prim, SpecScope)>,
}

#[derive(Clone, Debug)]
pub struct Overlay {
    tokens: TokenTable,
    kind_names: Vec<Arc<str>>,
    kind_map: HashMap<Arc<str>, u16>,
    base_kind_count: u16,
    cats: HashMap<String, CategoryDelta>,
    /// M3b3 Task 4: every overlay-registered token paired with its
    /// entry's activation `SpecScope`. `self.tokens` (above) still holds
    /// the FULL set — used for the fingerprint and `is_empty`, both of
    /// which are activation-independent grammar identity — but LEXING
    /// must only see tokens whose scope is currently active (dump-pinned:
    /// `StxScopedInactive.lean`'s inactive `wobsc2` lexes as an IDENT,
    /// not an atom, because its `scoped` token is NOT in force after
    /// `end Widgsc2`). `Ps` (parse.rs) rebuilds an active-token table
    /// from this list on every scope/registration event and feeds THAT
    /// to `next_token`, never `self.tokens`.
    token_scopes: Vec<(String, SpecScope)>,
    /// M3b2b Task 7: brand-new categories a same-file
    /// `declare_syntax_cat` command registers — distinct from `cats`
    /// above, which only ever holds PRODUCTIONS added into a category
    /// (base or overlay) that some `NotationSpec` names, never the fact
    /// that the category itself exists. A category registered here has
    /// no productions of its own yet (Task 8 registers `syntax`/etc.
    /// into it via ordinary `register`/`cats`) — `category()`'s overlay
    /// fallback (`parse.rs`) is what makes it resolvable at all in the
    /// meantime, backed by an owned, empty `Category` carrying just
    /// this behavior.
    categories: HashMap<String, LeadingIdentBehavior>,
}

impl Overlay {
    pub fn new(base: &GrammarSnapshot) -> Self {
        Overlay {
            tokens: TokenTable::default(),
            kind_names: Vec::new(),
            kind_map: HashMap::new(),
            base_kind_count: base.kind_count(),
            cats: HashMap::new(),
            token_scopes: Vec::new(),
            categories: HashMap::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.cats.is_empty()
            && self.kind_names.is_empty()
            && self.tokens.is_empty()
            && self.categories.is_empty()
    }

    /// M3b3 Task 4: every registered token paired with its activation
    /// scope, in registration order — `Ps` (parse.rs) folds this into
    /// its active-token table, including a token iff
    /// `scope.is_active(scope)` at the current scope. Registration order
    /// is irrelevant to the resulting `TokenTable` (a `BTreeSet`), but
    /// this mirrors `kind_names`'s "registration-order view" contract.
    pub(crate) fn token_scopes(&self) -> &[(String, SpecScope)] {
        &self.token_scopes
    }

    /// `declare_syntax_cat`'s registration (M3b2b Task 7): record a
    /// brand-new category name + its `LeadingIdentBehavior` (`Default`
    /// unless an explicit `(behavior := both/symbol)` clause said
    /// otherwise — `notation.rs`'s `derive_syntax_cat`). Idempotent in
    /// the same sense `register`'s `intern` is: re-declaring the same
    /// name just overwrites the recorded behavior rather than erroring
    /// (real Lean's own re-declaration diagnostics are out of scope
    /// here, same as `register`'s own collision-suffixing note).
    pub fn register_category(&mut self, name: &str, behavior: LeadingIdentBehavior) {
        self.categories.insert(name.to_string(), behavior);
    }

    /// Whether `name` was registered via `register_category` — NOT
    /// whether it merely has an entry in `cats` (a `NotationSpec` that
    /// targets an as-yet-undeclared category name populates `cats` too,
    /// but that's a bug elsewhere, not this method's concern; M3b1 only
    /// ever targeted the base `term` category, so that case never arose
    /// before this task).
    pub fn has_category(&self, name: &str) -> bool {
        self.categories.contains_key(name)
    }

    /// `name`'s registered `LeadingIdentBehavior`, if `register_category`
    /// was ever called for it — `parse.rs`'s `category()` overlay
    /// fallback consumes this directly to build the owned, empty
    /// `Category` an overlay-only category resolves to.
    pub fn category_behavior(&self, name: &str) -> Option<LeadingIdentBehavior> {
        self.categories.get(name).copied()
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
    ///
    /// Note: calling `register` twice with the same `kind_name` interns
    /// idempotently (`intern` returns the SAME `SyntaxKind` both times)
    /// BUT still appends a second `(FirstTok, Prim)` entry to the
    /// category delta; this is harmless because `longest_match`'s
    /// strict-greater tie-break makes the first identical entry win,
    /// producing the same tree either way. The one diverging case — two
    /// DISTINCT notations whose atoms mangle to the SAME kind name — is
    /// Lean's `mkUnusedBaseName` collision-suffixing, out of scope for
    /// M3b1 (see `intern`'s own doc comment).
    pub fn register(&mut self, spec: NotationSpec) -> SyntaxKind {
        // Intern the generated kind AFTER the base (overlay-local,
        // bounded by command count — never per-token).
        let kind = self.intern(&spec.kind_name);
        for t in &spec.tokens {
            self.tokens.insert(t);
            // M3b3 Task 4: record each token's activation scope so `Ps`
            // can build a scope-filtered active-token table for lexing.
            self.token_scopes.push((t.clone(), spec.scope.clone()));
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
        let scope = spec.scope;
        let cd = self.cats.entry(spec.category).or_default();
        for ft in fts {
            if is_trailing {
                cd.trailing.push((ft, prim.clone(), scope.clone()));
            } else {
                cd.leading.push((ft, prim.clone(), scope.clone()));
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
    pub(crate) fn intern(&mut self, name: &str) -> SyntaxKind {
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
    ///
    /// Widened semantics (`kind_names` above): a FAILED antiquot attempt
    /// still interns its kind (e.g. `term.pseudo.antiquot`,
    /// `parse.rs`'s `Ps::antiquot`) via `Overlay::intern` before the
    /// caller's save/restore unwinds the attempt — `restore` rewinds
    /// events/pos, not the overlay's kind table — so this fingerprint
    /// depends on quotation CONTENTS parsed so far, not only on
    /// registered grammar deltas (`register`/`register_category`).
    /// Still deterministic per input (same source, same attempted
    /// antiquots, same interning order) → caching stays sound; intern-
    /// on-commit (only intern a kind once its production actually wins)
    /// is the real fix, deferred (M3b3 candidate).
    pub fn fingerprint_into(&self, h: &mut blake3::Hasher) {
        // M3b3 Task 4: bumped from `leanr-m3b1-overlay-v1` when each
        // overlay entry gained its `SpecScope` activation tag (hashed
        // below) — a grammar that only differs in an entry's scope must
        // fingerprint differently.
        h.update(b"leanr-m3b3-overlay-v1\0");
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
            for (_, p, scope) in cd.leading.iter().chain(&cd.trailing) {
                encode_prim(p, &kind_name, h);
                encode_spec_scope(scope, h);
            }
        }
        // M3b2b Task 7: brand-new categories (`declare_syntax_cat`),
        // sorted by name (same `HashMap`-needs-sorting rationale as
        // `cats` above) — name bytes + the behavior byte, SAME encoding
        // `GrammarSnapshot::fingerprint`'s own per-category behavior
        // byte uses (`grammar/mod.rs`), so a category that only differs
        // in `ident_behavior` still changes the fingerprint here too.
        let mut cat_names: Vec<&String> = self.categories.keys().collect();
        cat_names.sort();
        for name in cat_names {
            h.update(name.as_bytes());
            h.update(b"\x02");
            let behavior_byte: u8 = match self.categories[name] {
                LeadingIdentBehavior::Default => 0,
                LeadingIdentBehavior::Symbol => 1,
                LeadingIdentBehavior::Both => 2,
            };
            h.update(&[behavior_byte]);
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
            scope: SpecScope::Global,
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

    /// Mirrors `parse.rs::tests::sum_spec()` (Task 6) — same
    /// operator-first trailing shape (`seq([sym("⊕"), cat("term", 66)])`)
    /// — kept as a local copy since that helper lives in a different
    /// module's private `#[cfg(test)]` and this file's tests should not
    /// depend on `parse.rs`'s test internals.
    fn sum_spec() -> NotationSpec {
        NotationSpec {
            category: "term".into(),
            kind_name: "«term_⊕_»".into(),
            leading: false,
            prec: 65,
            lhs_prec: Some(65),
            tokens: vec!["⊕".into()],
            body: crate::grammar::seq([crate::grammar::sym("⊕"), crate::grammar::cat("term", 66)]),
            scope: SpecScope::Global,
        }
    }

    /// Task 10 Step 1 (M3b1 plan): the M5 firewall seam — same-file
    /// grammar growth (a registered notation) must change the effective
    /// (base + overlay) fingerprint, so a query cache keyed on it is
    /// correctly invalidated.
    #[test]
    fn overlay_changes_effective_fingerprint() {
        let base = crate::builtin::snapshot();
        let base_fp = base.fingerprint();
        let mut ov = Overlay::new(&base);
        ov.register(sum_spec());
        let mut h = blake3::Hasher::new();
        h.update(base_fp.as_bytes());
        ov.fingerprint_into(&mut h);
        let with_overlay = h.finalize();
        assert_ne!(
            with_overlay, base_fp,
            "grammar growth must change the fingerprint"
        );
    }

    /// Task 10 Part B (absorbed from Task 5 review): `fingerprint_into`
    /// must be deterministic — two independently built overlays that
    /// register the SAME spec must hash identically. Guards against a
    /// future regression (e.g. iterating `cats`, a `HashMap`, without
    /// the `.sort()` this file's `fingerprint_into` already does).
    #[test]
    fn fingerprint_into_is_deterministic_across_independent_overlays() {
        let base = crate::builtin::snapshot();
        let mut ov1 = Overlay::new(&base);
        ov1.register(sum_spec());
        let mut ov2 = Overlay::new(&base);
        ov2.register(sum_spec());

        let mut h1 = blake3::Hasher::new();
        ov1.fingerprint_into(&mut h1);
        let mut h2 = blake3::Hasher::new();
        ov2.fingerprint_into(&mut h2);

        assert_eq!(
            h1.finalize(),
            h2.finalize(),
            "fingerprint_into must be deterministic for equivalent overlays"
        );
    }

    /// Task 10 Part B (absorbed from Task 5 review): `intern` (via
    /// `register`) is idempotent on a repeated kind name — registering
    /// the same spec TWICE into one overlay must hand back the SAME
    /// `SyntaxKind` both times, not a duplicate.
    #[test]
    fn intern_is_idempotent_for_the_same_kind_name() {
        let base = crate::builtin::snapshot();
        let mut ov = Overlay::new(&base);
        let k1 = ov.register(sum_spec());
        let k2 = ov.register(sum_spec());
        assert_eq!(
            k1, k2,
            "re-registering the same spec must not mint a new kind"
        );
    }

    /// M3b3 Task 4: two overlays identical except for ONE entry's
    /// activation `SpecScope` tag must fingerprint differently — locks
    /// the per-entry scope byte into the hash (`encode_spec_scope`), the
    /// grammar-identity guarantee the `leanr-m3b3-overlay-v1` domain bump
    /// exists for.
    #[test]
    fn entries_differing_only_in_scope_tag_fingerprint_differently() {
        let base = crate::builtin::snapshot();
        let fp = |scope: SpecScope| {
            let mut ov = Overlay::new(&base);
            let mut spec = sum_spec();
            spec.scope = scope;
            ov.register(spec);
            let mut h = blake3::Hasher::new();
            ov.fingerprint_into(&mut h);
            h.finalize()
        };
        let g = fp(SpecScope::Global);
        let s = fp(SpecScope::Scoped("Widg".into()));
        let l = fp(SpecScope::Local { scope_len: 1 });
        assert_ne!(g, s, "Global vs Scoped must differ");
        assert_ne!(g, l, "Global vs Local must differ");
        assert_ne!(s, l, "Scoped vs Local must differ");
        // And the namespace inside `Scoped` participates.
        assert_ne!(
            fp(SpecScope::Scoped("Widg".into())),
            fp(SpecScope::Scoped("Other".into())),
            "Scoped namespace must participate in the fingerprint"
        );
    }

    /// M3b2b Task 7 Step 1 (RED first): `declare_syntax_cat` grows the
    /// grammar by registering a brand-new, initially-empty CATEGORY
    /// (not a production into an existing one) — the overlay needs its
    /// own tracking for that, distinct from `cats`/`register` above,
    /// which only ever adds productions into a category name a
    /// `NotationSpec` names but never actually registers as existing on
    /// its own.
    #[test]
    fn overlay_categories_register_and_fingerprint() {
        let base = crate::builtin::snapshot();
        let mut ov = Overlay::new(&base);
        assert!(!ov.has_category("widgetish"));
        ov.register_category("widgetish", LeadingIdentBehavior::Default);
        assert!(ov.has_category("widgetish"));
        // A new category changes the effective fingerprint.
        let mut h1 = blake3::Hasher::new();
        Overlay::new(&base).fingerprint_into(&mut h1);
        let mut h2 = blake3::Hasher::new();
        ov.fingerprint_into(&mut h2);
        assert_ne!(h1.finalize(), h2.finalize());
    }

    /// M3b2b Task 8 preliminary (controller-added, from Task 7's
    /// review): the SAME category name, differing ONLY in its
    /// registered `LeadingIdentBehavior`, must still fingerprint
    /// differently — locks the behavior BYTE into the hash (not just
    /// "a category exists", which `overlay_categories_register_and_
    /// fingerprint` above already covers). Mirrors
    /// `GrammarSnapshot::fingerprint`'s own module-doc "v2" bump, which
    /// added the identical per-category behavior byte for base
    /// categories (M3a Task 10 review Finding 1) — this is that same
    /// guarantee for an OVERLAY-registered (same-file
    /// `declare_syntax_cat`) category.
    #[test]
    fn overlay_categories_differing_only_in_behavior_fingerprint_differently() {
        let base = crate::builtin::snapshot();

        let mut ov_default = Overlay::new(&base);
        ov_default.register_category("widgetish", LeadingIdentBehavior::Default);
        let mut h_default = blake3::Hasher::new();
        ov_default.fingerprint_into(&mut h_default);

        let mut ov_symbol = Overlay::new(&base);
        ov_symbol.register_category("widgetish", LeadingIdentBehavior::Symbol);
        let mut h_symbol = blake3::Hasher::new();
        ov_symbol.fingerprint_into(&mut h_symbol);

        let mut ov_both = Overlay::new(&base);
        ov_both.register_category("widgetish", LeadingIdentBehavior::Both);
        let mut h_both = blake3::Hasher::new();
        ov_both.fingerprint_into(&mut h_both);

        let (d, s, b) = (h_default.finalize(), h_symbol.finalize(), h_both.finalize());
        assert_ne!(d, s, "Default vs Symbol must fingerprint differently");
        assert_ne!(d, b, "Default vs Both must fingerprint differently");
        assert_ne!(s, b, "Symbol vs Both must fingerprint differently");
    }
}
