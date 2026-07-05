//! Integration: decode fixture `.olean`s and replay them through the
//! kernel (Task 12). This is where decoded modules meet the checker.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use leanr_kernel::{ConstantInfo, Environment, Name};
use leanr_olean::ModuleData;

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn constants_of(md: ModuleData) -> HashMap<Arc<Name>, ConstantInfo> {
    md.constants
        .into_iter()
        .map(|c| (Arc::clone(c.name()), c))
        .collect()
}

/// Hermetic (runs in CI): the import-free `Prelude0` fixture replays from
/// an empty environment. No toolchain needed at test time — the committed
/// `.olean` is the entire input.
#[test]
fn prelude0_replays_from_empty_env() {
    let bytes = std::fs::read(fixture_path("Prelude0.olean")).unwrap();
    let m = ModuleData::parse(&bytes).unwrap();
    assert!(m.imports.is_empty(), "Prelude0 imports nothing");

    let constants = constants_of(m);
    let mut env = Environment::default();
    let stats = leanr_kernel::replay(&mut env, constants).unwrap();
    // N block, Truth block, N.add, triv, and the two generated `recOn`
    // definitions — at least the three the fixture explicitly declares.
    assert!(
        stats.checked >= 3,
        "expected >= 3 checked, got {}",
        stats.checked
    );
    assert_eq!(stats.skipped_unsafe, 0);
}

/// Toolchain-dependent (local, like the M1a sweep): the M1a fixtures
/// import `Init`, so their dependency closure comes from the pinned
/// toolchain. A manual transitive import walk over `LEANR_SWEEP_DIR`
/// gathers the closure here; Task 13's loader will replace it. Skipped
/// when `LEANR_SWEEP_DIR` is unset (i.e. in CI).
///
/// KNOWN LIMITATION (why this stays `#[ignore]`d beyond just needing the
/// toolchain): the module system splits a module into a base `.olean`
/// plus `.olean.private`/`.olean.server` companion parts that SHARE the
/// base part's compactor and are not independently decodable (parsing one
/// standalone yields "bad object pointer"). This naive walk reads only
/// base parts, so a public constant that references a `_private.*` helper
/// living in a companion part fails to replay with `UnknownConstant`.
/// Resolving that is precisely Task 13's module-aware loader; until then
/// this test documents the intended end-to-end shape rather than passing.
#[test]
#[ignore = "needs the pinned toolchain + Task 13's module-aware loader for private parts"]
fn fixture_modules_replay_clean_with_closure() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    let lib = PathBuf::from(&dir);
    for fx in ["Sample.olean", "SampleRich.olean"] {
        let constants = decode_with_import_closure(&fixture_path(fx), &lib);
        let mut env = Environment::default();
        let stats = leanr_kernel::replay(&mut env, constants)
            .unwrap_or_else(|e| panic!("{fx} failed to replay: {e}"));
        assert!(stats.checked > 0, "{fx} checked nothing");
    }
}

/// Decode `entry` plus the transitive closure of its imports (resolved
/// against the toolchain `lib` dir, `Foo.Bar` → `lib/Foo/Bar.olean`),
/// unioning all constants into one map. On a name collision the first
/// decoded module wins — the toolchain's `.olean`s share base declarations
/// consistently, so this only ever coalesces identical entries.
fn decode_with_import_closure(entry: &Path, lib: &Path) -> HashMap<Arc<Name>, ConstantInfo> {
    let mut constants: HashMap<Arc<Name>, ConstantInfo> = HashMap::new();
    let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut stack: Vec<PathBuf> = vec![entry.to_path_buf()];

    while let Some(path) = stack.pop() {
        let key = path.to_string_lossy().into_owned();
        if !visited.insert(key) {
            continue;
        }
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue, // a builtin/synthetic import with no file
        };
        let md = ModuleData::parse(&bytes)
            .unwrap_or_else(|e| panic!("decode {} failed: {e}", path.display()));
        for imp in &md.imports {
            let rel: PathBuf = imp
                .module
                .to_string()
                .split('.')
                .collect::<Vec<_>>()
                .join("/")
                .into();
            let mut p = lib.join(rel);
            p.set_extension("olean");
            stack.push(p);
        }
        for c in md.constants {
            constants.entry(Arc::clone(c.name())).or_insert(c);
        }
    }
    constants
}
