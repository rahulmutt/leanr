#![no_main]

use libfuzzer_sys::fuzz_target;

// The never-panic guarantee (docs/THREAT_MODEL.md): any byte input
// must produce Ok or a structured OleanError — no panic, no abort, no
// hang, no unbounded allocation.
fuzz_target!(|data: &[u8]| {
    let _ = leanr_olean::ModuleData::parse(data);
});
