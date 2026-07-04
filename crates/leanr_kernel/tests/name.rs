use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use leanr_kernel::{Name, Nat};

fn str_name(parent: Arc<Name>, part: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent,
        part: part.to_string(),
    })
}

fn simple(parts: &[&str]) -> Arc<Name> {
    parts
        .iter()
        .fold(Arc::new(Name::Anonymous), |p, s| str_name(p, s))
}

fn hash_of(n: &Name) -> u64 {
    let mut h = DefaultHasher::new();
    n.hash(&mut h);
    h.finish()
}

#[test]
fn display_matches_lean_unescaped_tostring() {
    assert_eq!(Name::Anonymous.to_string(), "[anonymous]");
    assert_eq!(simple(&["Init"]).to_string(), "Init");
    assert_eq!(simple(&["Init", "Nat", "add"]).to_string(), "Init.Nat.add");
    let hygienic = Arc::new(Name::Num {
        parent: simple(&["foo", "_hyg"]),
        part: Nat::from(23u64),
    });
    assert_eq!(hygienic.to_string(), "foo._hyg.23");
}

#[test]
fn equality_and_hashing_are_structural() {
    assert_eq!(*simple(&["a", "b"]), *simple(&["a", "b"]));
    assert_ne!(*simple(&["a", "b"]), *simple(&["a", "c"]));
    assert_ne!(*simple(&["a"]), Name::Anonymous);
    assert_eq!(hash_of(&simple(&["a", "b"])), hash_of(&simple(&["a", "b"])));
}

/// Untrusted input can produce arbitrarily deep parent chains; every
/// operation on `Name` (drop, eq, hash, display) must be iterative.
#[test]
fn deep_chains_do_not_overflow_the_stack() {
    const DEPTH: usize = 200_000;
    let build = || {
        let mut n = Arc::new(Name::Anonymous);
        for _ in 0..DEPTH {
            n = str_name(n, "x");
        }
        n
    };
    let a = build();
    let b = build();
    assert_eq!(*a, *b);
    assert_eq!(hash_of(&a), hash_of(&b));
    let rendered = a.to_string();
    assert_eq!(rendered.len(), DEPTH * 2 - 1); // "x.x.....x"
    let debug_rendered = format!("{:?}", &*a); // iterative Debug: must not overflow
    assert!(!debug_rendered.is_empty());
    drop(a);
    drop(b); // iterative Drop: must not overflow
}
