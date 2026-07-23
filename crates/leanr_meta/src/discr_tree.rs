//! A generic discrimination-tree trie over `leanr_olean::DiscrKey`.
//!
//! oracle: `Lean.Meta.DiscrTree` (`Lean/Meta/DiscrTree/Basic.lean`,
//! `Lean/Meta/DiscrTree/Main.lean`), pinned toolchain
//! `leanprover/lean4:v4.33.0-rc1`.
//!
//! This is a pure data structure with NO dependency on `MetaCtx`: PR-B
//! Task B2 supplies expression-to-`Vec<DiscrKey>` flattening and Task
//! B3 builds the instance table on top of it; simp/rw slices reuse
//! this module later (spec: docs/superpowers/specs/2026-07-20-m4a-meta-core-design.md).
//!
//! **Layering note** (deviation from the design's wording): the design
//! placed the `Key` model inside `discr_tree.rs`, but instance keys
//! are decoded olean data (`InstanceEntry.keys`) that `leanr_meta`
//! consumes from `leanr_olean`, and the dependency direction is
//! meta → olean, never the reverse. So the `DiscrKey` *enum* lives in
//! `leanr_olean` (see `leanr_olean::module_data::DiscrKey`'s doc
//! comment for its own ctor-tag provenance) and this generic *trie*
//! lives here — the only split that keeps the dependency direction
//! correct while keeping the trie itself standalone and reusable.
//!
//! ## Node shape
//!
//! `Basic.lean`'s `Trie α` is `.node (values : Array α) (children :
//! Array (Key × Trie α))` — a sorted array of key/child pairs, plus
//! terminal values. Insertion (`insertAux`/`createNodes`,
//! `Basic.lean:125-173`) walks the key array one key per trie level,
//! unconditionally: a key's own `arity` is never consulted to decide
//! how many *trie levels* a key spans, only baked into the `Key` value
//! itself (so e.g. `Const Add 1` and `Const Add 2` hash/compare
//! unequal). We use a `HashMap<DiscrKey, Node<V>>` in place of the
//! sorted array — this changes nothing observable because we never
//! rely on iteration order for the specific/star precedence; that
//! precedence is branched on explicitly (see `process` below), exactly
//! as the oracle's `getMatchLoop`/`getUnify.process` explicitly branch
//! on `first.1 == .star` rather than relying on array order beyond the
//! documented "`Key.star` is minimal" convention.
//!
//! ## Match traversal
//!
//! `get_match_keys` transcribes `Lean.Meta.DiscrTree.getUnify`
//! (`Main.lean:567-606`), not the plainer `getMatch`/`getMatchCore`
//! (`Main.lean:438-478`): `getMatch`'s query side only ever consults
//! the *stored* `Star` child when the query itself is a concrete key
//! (`visitStar`), and refuses to explore further when the query's own
//! key is `Star` (it returns only `getStarResult`, i.e. the *root's*
//! star bucket) — that asymmetry is wrong for this trie's contract,
//! which needs a `Star` **query** key to match every child at that
//! position (brief requirement, pinned by `wildcard_query_matches_both`).
//! `getUnify` has exactly that symmetric behavior
//! (`Main.lean:604-606`: `| .star => cs.foldlM ... process k.arity todo
//! c result`), so it — not `getMatch` — is the faithful oracle for this
//! module's contract.
//!
//! `getUnify.process`'s `skip : Nat` accumulator (`Main.lean:578-606`)
//! is the "skip" mechanism the arity-storing remark at
//! `Main.lean:47-50` promises ("store the arity in the keys ... to be
//! able to implement the skip operation when retrieving candidate
//! unifiers"): when a `Star` needs to swallow a whole stored subtree of
//! unknown depth, `process` doesn't know that depth up front, so it
//! keeps a debt counter instead — descend into a child unconditionally
//! (paying down 1 unit of debt) while adding that child key's own
//! `arity` back onto the debt (because that child's arguments are
//! *also* inside the swallowed subtree and must be skipped too), and
//! resume ordinary matching only once the debt reaches zero
//! (`Main.lean:579-584` vs. `585-606`). Termination is structural (each
//! recursive call descends one real trie level into a finite tree), not
//! metric on `skip`, which can legitimately grow before it shrinks.

use std::collections::HashMap;

use leanr_olean::DiscrKey;

/// One trie level: values terminating exactly here, plus the outgoing
/// edges keyed by the next `DiscrKey` in a stored path. Mirrors
/// `Lean.Meta.DiscrTree.Trie` (`Basic.lean`'s `.node vs cs`), with `cs`
/// represented as a map instead of a sorted array (see the module doc).
struct Node<V> {
    values: Vec<V>,
    children: HashMap<DiscrKey, Node<V>>,
}

// Written by hand (not `#[derive(Default)]`) so `Node<V>: Default`
// holds for every `V`, not just `V: Default` — `Vec::new()` and
// `HashMap::new()` never need it, and a derived impl would wrongly
// demand it of every `DiscrTree<V>` caller.
impl<V> Default for Node<V> {
    fn default() -> Self {
        Node {
            values: Vec::new(),
            children: HashMap::new(),
        }
    }
}

/// A generic discrimination-tree trie over `DiscrKey` paths, reusable
/// by any consumer that has its own notion of "value" (instance
/// entries for Task B3; simp/rw lemmas later) — see the module doc for
/// the full oracle correspondence.
pub struct DiscrTree<V> {
    root: Node<V>,
}

impl<V> Default for DiscrTree<V> {
    fn default() -> Self {
        DiscrTree {
            root: Node::default(),
        }
    }
}

/// `Lean.Meta.DiscrTree.Key.arity` (`Main.lean:53-67`): the number of
/// further path positions a key's own arguments occupy. `Star`,
/// `Other`, and `Lit` are the oracle's catch-all `| _ => 0` arm;
/// `Arrow` is pinned at `1` (indexing the forall's domain, `arity`'s
/// doc comment at `Main.lean:56-64`); `Proj` is `1 + a` (the
/// projection's structure argument, plus its own trailing `a` args).
fn key_arity(key: &DiscrKey) -> usize {
    match key {
        DiscrKey::Const { arity, .. } => *arity,
        DiscrKey::Fvar { arity } => *arity,
        DiscrKey::Arrow => 1,
        DiscrKey::Proj { arity, .. } => 1 + *arity,
        DiscrKey::Star | DiscrKey::Other | DiscrKey::Lit(_) => 0,
    }
}

impl<V> DiscrTree<V> {
    /// Insert `value` under `path`, creating any missing trie levels.
    /// Mirrors `insertKeyValue`/`insertAux`/`createNodes`
    /// (`Basic.lean:125-173`): one trie level per path element,
    /// regardless of that element's own arity (arity is match-time-only
    /// metadata, never a level-count). An empty `path` inserts at the
    /// root rather than panicking (`Basic.lean:166`'s `insertKeyValue`
    /// panics on `keys.isEmpty`) — this crate never panics on caller
    /// input, only on already-validated invariants.
    pub fn insert(&mut self, path: &[DiscrKey], value: V) {
        let mut node = &mut self.root;
        for key in path {
            node = node.children.entry(key.clone()).or_default();
        }
        node.values.push(value);
    }

    /// Return every value whose stored path matches `path`, informally
    /// "unifying" `Star` positions in either side, specific matches
    /// before wildcard matches (an explicit contract for this generic
    /// trie — see this module's doc for why the plainer oracle
    /// `getMatch` isn't the transcription target for the `Star`-query
    /// side).
    pub fn get_match_keys(&self, path: &[DiscrKey]) -> Vec<&V> {
        let mut out = Vec::new();
        Self::process(0, path, &self.root, &mut out);
        out
    }

    /// oracle: `Lean.Meta.DiscrTree.getUnify.process`
    /// (`Main.lean:578-606`), adapted from `todo : Array Expr` (a stack
    /// of pending sub-expressions still to be flattened) to `query :
    /// &[DiscrKey]` (an already-flattened path — flattening is Task
    /// B2's job, out of scope here): both are "the remaining query
    /// positions", walked one at a time.
    fn process<'v>(skip: usize, query: &[DiscrKey], node: &'v Node<V>, out: &mut Vec<&'v V>) {
        if skip > 0 {
            // Main.lean:580-584 (`skip+1, .node _ cs`): blindly pay down
            // one level of skip debt per child, re-crediting that
            // child's own arity (its arguments are inside the same
            // swallowed subtree). `node`'s own `values` are never
            // collected while debt remains — landing here mid-skip
            // means the stored path is shorter than what the `Star` is
            // swallowing, i.e. not actually a match.
            for (key, child) in &node.children {
                Self::process(skip - 1 + key_arity(key), query, child, out);
            }
            return;
        }
        match query.split_first() {
            // Main.lean:586-587 (`todo.isEmpty => result ++ vs`).
            None => out.extend(node.values.iter()),
            // Main.lean:604-606: a `Star` query key matches every
            // child, regardless of key, paying down that child's own
            // arity as skip debt before resuming ordinary matching on
            // the rest of the query.
            Some((DiscrKey::Star, rest)) => {
                for (key, child) in &node.children {
                    Self::process(key_arity(key), rest, child, out);
                }
            }
            // Main.lean:600-603 (`visitNonStar`) then Main.lean:594-599
            // (`visitStar`) — specific before wildcard, per this
            // module's contract (the oracle itself accumulates
            // wildcard-then-specific; deliberately reversed here, see
            // the module doc and `specific_beats_wildcard`).
            Some((key, rest)) => {
                if let Some(child) = node.children.get(key) {
                    Self::process(0, rest, child, out);
                }
                if let Some(star_child) = node.children.get(&DiscrKey::Star) {
                    Self::process(0, rest, star_child, out);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::bank::NameId;
    use leanr_olean::DiscrKey;

    /// Build a `Const` key with a cheap, Store-free test `NameId`:
    /// `NameId::from_index` (`leanr_kernel::bank::id_type!`) is a plain
    /// index-to-id constructor that needs no interning `Store`, exactly
    /// like other `leanr_meta` unit tests that only need *some* stable,
    /// distinct `NameId`s (e.g. `mvar_ctx.rs`'s doc on `MVarId`/`NameId`
    /// having no `Ord`). Distinct `name_arity.0` values give distinct
    /// `NameId`s, which is all these tests need.
    fn c(name_arity: (u32, usize)) -> DiscrKey {
        DiscrKey::Const {
            name: NameId::from_index(name_arity.0, false).unwrap(),
            arity: name_arity.1,
        }
    }

    #[test]
    fn specific_beats_wildcard() {
        let mut t: DiscrTree<&'static str> = DiscrTree::default();
        // Add a → [Const Add 1, Const N 0] and a wildcard a → [Const Add 1, Star]
        t.insert(&[/*Add*/ c((1, 1)), /*N*/ c((2, 0))], "specific");
        t.insert(&[/*Add*/ c((1, 1)), DiscrKey::Star], "wildcard");
        // A concrete query Add N returns specific FIRST, then wildcard.
        let got = t.get_match_keys(&[c((1, 1)), c((2, 0))]);
        assert_eq!(got, vec![&"specific", &"wildcard"]);
    }

    #[test]
    fn wildcard_query_matches_both() {
        let mut t: DiscrTree<&'static str> = DiscrTree::default();
        t.insert(&[c((1, 1)), c((2, 0))], "n");
        t.insert(&[c((1, 1)), c((3, 0))], "m");
        // Query Add ?  (Star) returns both stored branches.
        let got = t.get_match_keys(&[c((1, 1)), DiscrKey::Star]);
        assert_eq!(got.len(), 2);
    }

    #[test]
    fn empty_tree_has_no_matches() {
        let t: DiscrTree<&'static str> = DiscrTree::default();
        assert!(t.get_match_keys(&[c((1, 1))]).is_empty());
    }

    #[test]
    fn empty_query_matches_root_values_only() {
        let mut t: DiscrTree<&'static str> = DiscrTree::default();
        t.insert(&[], "root-value");
        t.insert(&[c((1, 0))], "not-root");
        assert_eq!(t.get_match_keys(&[]), vec![&"root-value"]);
    }

    #[test]
    fn arity_skip_lets_wildcard_swallow_a_deeper_subtree() {
        let mut t: DiscrTree<&'static str> = DiscrTree::default();
        // f applied to (g applied to one arg): [Const f 1, Const g 1, Const x 0].
        t.insert(&[c((10, 1)), /*g*/ c((11, 1)), /*x*/ c((12, 0))], "deep");
        // Query: f applied to a wildcard argument of unknown shape.
        let got = t.get_match_keys(&[c((10, 1)), DiscrKey::Star]);
        assert_eq!(got, vec![&"deep"]);
    }
}
