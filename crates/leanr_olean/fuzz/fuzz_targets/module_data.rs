#![no_main]

use libfuzzer_sys::fuzz_target;

use leanr_kernel::bank::Store;
use leanr_olean::{ModuleData, PartKind};

// The never-panic guarantee (docs/THREAT_MODEL.md): any byte input must
// produce Ok or a structured OleanError — no panic, no abort, no hang, no
// unbounded allocation.
//
// The first byte selects the entry so BOTH the single-region path
// (`ModuleData::parse`) and the multi-region path (`ModuleData::parse_parts`,
// M1b Task 13a) are fuzz-reachable. For the multi-region case we split the
// remaining bytes into a base part and a companion part at a length prefix,
// exercising cross-region pointer resolution / overlap / truncation.
// Direct-to-id decode (term-bank phase 3): decoding interns straight into a
// `&mut Store`, so each fuzz iteration gets a fresh one — a failed decode may
// leave partial rows in it, which is fine (unreachable ids are inert) but
// must not carry over between iterations.
fuzz_target!(|data: &[u8]| {
    let Some((&selector, rest)) = data.split_first() else {
        let mut st = Store::persistent();
        let _ = ModuleData::parse(data, &mut st);
        return;
    };
    if selector & 1 == 0 {
        let mut st = Store::persistent();
        let _ = ModuleData::parse(rest, &mut st);
    } else {
        // Split `rest` into two parts at a byte-driven cut point.
        let cut = rest.first().map(|&b| b as usize).unwrap_or(0) % (rest.len().max(1));
        let (base, private) = rest.split_at(cut.min(rest.len()));
        let mut st = Store::persistent();
        let _ = ModuleData::parse_parts(
            &[(PartKind::Base, base), (PartKind::Private, private)],
            &mut st,
        );
    }
});
