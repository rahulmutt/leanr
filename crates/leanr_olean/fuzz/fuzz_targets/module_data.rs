#![no_main]

use libfuzzer_sys::fuzz_target;

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
fuzz_target!(|data: &[u8]| {
    let Some((&selector, rest)) = data.split_first() else {
        let _ = ModuleData::parse(data);
        return;
    };
    if selector & 1 == 0 {
        let _ = ModuleData::parse(rest);
    } else {
        // Split `rest` into two parts at a byte-driven cut point.
        let cut = rest.first().map(|&b| b as usize).unwrap_or(0) % (rest.len().max(1));
        let (base, private) = rest.split_at(cut.min(rest.len()));
        let _ = ModuleData::parse_parts(&[
            (PartKind::Base, base),
            (PartKind::Private, private),
        ]);
    }
});
