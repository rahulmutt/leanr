//! Never-panic / always-terminate gate over arbitrary bytes
//! (docs/THREAT_MODEL.md: source text). Also asserts total
//! losslessness — the cheapest strong invariant a fuzzer can check.
#![no_main]

use libfuzzer_sys::fuzz_target;
use std::sync::OnceLock;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    static SNAP: OnceLock<leanr_syntax::grammar::GrammarSnapshot> = OnceLock::new();
    let snap = SNAP.get_or_init(leanr_syntax::builtin::snapshot);
    let r = leanr_syntax::parse_module(src, snap);
    assert_eq!(r.tree.text(), src);
});
