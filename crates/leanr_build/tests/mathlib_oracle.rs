//! Differential tier (spec §Testing): leanr's package model vs pinned
//! official lake over the Mathlib closure. All #[ignore]; run via
//! `mise run build:differential` (needs `mise run mathlib:fetch` first).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use leanr_build::bridge::{translate_lakefile, LakeInvoker};
use leanr_build::modules::ModuleName;
use leanr_build::{resolve, ResolveOptions};
use leanr_kernel::{bank::Store, Name};
use leanr_olean::{ModuleData, SearchPath};

fn mathlib_dir() -> PathBuf {
    PathBuf::from(std::env::var("LEANR_MATHLIB_DIR").expect("set LEANR_MATHLIB_DIR"))
}

fn olean_search_path() -> SearchPath {
    let raw = std::env::var("LEANR_OLEAN_PATH").expect("set LEANR_OLEAN_PATH");
    SearchPath::new(raw.split(':').map(PathBuf::from).collect())
}

fn kernel_name(m: &ModuleName) -> Arc<Name> {
    let mut n = Arc::new(Name::Anonymous);
    for part in m.components() {
        n = Arc::new(Name::Str {
            parent: n,
            part: part.clone(),
        });
    }
    n
}

fn resolve_mathlib() -> leanr_build::Workspace {
    let root = mathlib_dir();
    let toolchain = std::fs::read_to_string(root.join("lean-toolchain"))
        .ok()
        .map(|s| s.trim().to_string());
    // Toolchain olean dir = the LEAN_PATH entry that contains Init.olean.
    let sp = olean_search_path();
    let init = sp
        .find(&kernel_name(&ModuleName::parse("Init").unwrap()))
        .expect("Init.olean on LEANR_OLEAN_PATH");
    let toolchain_olean_dir = init
        .parent()
        .expect("Init.olean has a parent")
        .to_path_buf();
    let opts = ResolveOptions {
        targets: Vec::new(), // defaultTargets = ["Mathlib"]
        lake: LakeInvoker {
            toolchain,
            ..LakeInvoker::default()
        },
        toolchain_olean_dir,
    };
    resolve(&root, &opts).expect("mathlib resolves")
}

/// Oracle 1 (bridge golden): translate-config output for Mathlib's
/// lakefile.lean is byte-identical to the committed fixture.
#[test]
#[ignore]
fn bridge_golden_matches_committed_fixture() {
    let out = tempfile::TempDir::new().unwrap();
    let out_file = out.path().join("translated.toml");
    let toolchain = std::fs::read_to_string(mathlib_dir().join("lean-toolchain"))
        .ok()
        .map(|s| s.trim().to_string());
    let lake = LakeInvoker {
        toolchain,
        ..LakeInvoker::default()
    };
    let lakefile = mathlib_dir().join("lakefile.lean");
    translate_lakefile(&mathlib_dir(), &lakefile, &lake, &out_file).unwrap();
    let got = std::fs::read_to_string(&out_file).unwrap();
    let want = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mathlib-lakefile-golden.toml"),
    )
    .unwrap();
    assert_eq!(
        got, want,
        "regen via `mise run fixtures:regen` if the pin moved"
    );
}

/// Oracle 2 (import graph — the strong one): for every planned module,
/// header-scanned imports == the .olean's recorded imports.
///
/// Implicit-`Init` rule: `leanr_build::graph::add_implicit_init`
/// (production code, not a test-local workaround) unconditionally appends
/// `Init` to every non-`prelude` module's `imports`, matching the pinned
/// toolchain's `HeaderSyntax.imports`
/// (src/lean/Lean/Elab/Import.lean:29-40, v4.32.0-rc1) — Init is implicit
/// regardless of whether the module has other explicit imports. An earlier
/// "only if the header had zero imports" version of this rule was wrong:
/// this sweep found 8,532 real mismatches, all of the shape "olean =
/// scanned ∪ {Init}", none needing anything beyond that fix.
#[test]
#[ignore]
fn scanned_imports_match_olean_imports_across_the_closure() {
    let ws = resolve_mathlib();
    let sp = olean_search_path();
    let mut checked = 0usize;
    let mut mismatches = Vec::new();
    for m in &ws.graph.modules {
        let olean = sp
            .find(&kernel_name(&m.name))
            .unwrap_or_else(|| panic!("{}: no .olean on LEANR_OLEAN_PATH", m.name));
        let bytes = std::fs::read(&olean).unwrap();
        let mut store = Store::persistent();
        let md = ModuleData::parse(&bytes, &mut store).unwrap();
        let olean_imports: BTreeSet<String> =
            md.imports.iter().map(|i| i.module.to_string()).collect();
        let scanned: BTreeSet<String> = m.imports.iter().map(|i| i.to_string()).collect();
        if scanned != olean_imports {
            mismatches.push(format!(
                "{}: scanned {:?} != olean {:?}",
                m.name, scanned, olean_imports
            ));
        }
        checked += 1;
    }
    assert!(
        checked > 5000,
        "expected the full closure, checked only {checked}"
    );
    assert!(
        mismatches.is_empty(),
        "{} mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// Oracle 3 (module set): (a) every planned module has an .olean lake
/// built; (b) planned root-package modules == the on-disk Mathlib
/// build's module set (mk_all guarantees Mathlib.lean imports them all).
#[test]
#[ignore]
fn planned_module_set_matches_lakes_build() {
    let ws = resolve_mathlib();
    let sp = olean_search_path();
    // (a) subset: everything planned exists as an olean.
    for m in &ws.graph.modules {
        assert!(
            sp.find(&kernel_name(&m.name)).is_some(),
            "{}: planned but lake never built it",
            m.name
        );
    }
    // (b) equality on the root package.
    let planned: BTreeSet<String> = ws
        .graph
        .modules
        .iter()
        .filter(|m| m.package == ws.root.name)
        .map(|m| m.name.to_string())
        .collect();
    let build_dir = mathlib_dir().join(".lake/build/lib/lean");
    let mut on_disk = BTreeSet::new();
    let mut stack = vec![build_dir.clone()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().map(|x| x == "olean").unwrap_or(false) {
                let rel = p.strip_prefix(&build_dir).unwrap().with_extension("");
                let name = rel
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect::<Vec<_>>()
                    .join(".");
                on_disk.insert(name);
            }
        }
    }
    // The build dir holds only root-package modules (deps build in their
    // own .lake dirs); restrict to the planned targets' prefixes anyway
    // in case lake built extra targets (Cache, MathlibTest, ...).
    let planned_prefixes: BTreeSet<&str> = planned
        .iter()
        .map(|n| n.split('.').next().unwrap())
        .collect();
    let on_disk_restricted: BTreeSet<String> = on_disk
        .into_iter()
        .filter(|n| planned_prefixes.contains(n.split('.').next().unwrap()))
        .collect();
    assert_eq!(
        planned, on_disk_restricted,
        "planned vs lake-built module sets differ for the root package"
    );
}

/// Warnings check: resolving the whole closure emits no unknown-key
/// warnings (the schema covers everything the closure exercises).
#[test]
#[ignore]
fn closure_resolves_without_warnings() {
    let ws = resolve_mathlib();
    assert!(
        ws.warnings.is_empty(),
        "unexpected warnings: {:?}",
        ws.warnings
    );
}
