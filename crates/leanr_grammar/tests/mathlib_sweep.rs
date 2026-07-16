//! Local-only Mathlib parse sweep + pass-list ratchet (M3b2a
//! acceptance; grows into M3b3's 100% gate). Needs `mise run
//! mathlib:fetch` first. Run via `mise run parse:mathlib`.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use leanr_grammar::assemble;
use leanr_kernel::bank::Store;
use leanr_olean::SearchPath;

fn passlist_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/syntax/mathlib-passlist.txt")
}

/// Oracle dump with per-file cache under target/leanr-stx-cache/.
/// Key: (oracle githash, blake3 of file bytes). Dumper: the elaborating
/// one — arbitrary real files may grow the grammar mid-file.
fn oracle_dump(mathlib: &Path, lean_path: &str, githash: &str, file: &Path) -> Option<String> {
    let bytes = std::fs::read(file).ok()?;
    let key = format!("{githash}-{}", blake3::hash(&bytes).to_hex());
    let cache = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/leanr-stx-cache")
        .join(&key);
    if let Ok(hit) = std::fs::read_to_string(&cache) {
        return Some(hit);
    }
    let dumper = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/syntax/dump_syntax_elab.lean");
    let out = Command::new("lean")
        .env("LEAN_PATH", lean_path)
        .current_dir(mathlib)
        .arg("--run")
        .arg(&dumper)
        .arg(file)
        .output()
        .ok()?;
    if !out.status.success() {
        return None; // oracle itself failed on this file → not sweepable yet
    }
    let s = String::from_utf8(out.stdout).ok()?;
    std::fs::create_dir_all(cache.parent().unwrap()).ok()?;
    std::fs::write(&cache, &s).ok();
    Some(s)
}

#[test]
#[ignore = "needs .mathlib (mise run mathlib:fetch); run via mise run parse:mathlib"]
fn mathlib_sweep_ratchet() {
    let mathlib = PathBuf::from(std::env::var("LEANR_MATHLIB_DIR").expect("LEANR_MATHLIB_DIR"));
    let lean_path = std::env::var("LEANR_OLEAN_PATH").expect("LEANR_OLEAN_PATH");
    let githash = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/oracle-githash.txt"),
    )
    .expect("oracle-githash.txt (mise run fixtures:regen)")
    .trim()
    .to_string();
    let limit: usize = std::env::var("LEANR_SWEEP_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);

    let roots: Vec<PathBuf> = lean_path.split(':').filter(|s| !s.is_empty()).map(Into::into).collect();
    let sp = SearchPath::new(roots);

    // Enumerate: Mathlib/**/*.lean + each package's source tree.
    let mut files: Vec<PathBuf> = Vec::new();
    collect_lean_files(&mathlib.join("Mathlib"), &mut files);
    if let Ok(pkgs) = std::fs::read_dir(mathlib.join(".lake/packages")) {
        for p in pkgs.flatten() {
            collect_lean_files(&p.path(), &mut files);
        }
    }
    files.sort();
    files.truncate(limit);

    // Snapshot cache keyed by the file's import list.
    let mut snap_cache: BTreeMap<Vec<String>, Option<Arc<leanr_syntax::grammar::GrammarSnapshot>>> =
        BTreeMap::new();

    let mut green: Vec<String> = Vec::new();
    for file in &files {
        let rel = file.strip_prefix(&mathlib).unwrap_or(file).display().to_string();
        let Ok(src) = std::fs::read_to_string(file) else { continue };
        let imports = leanr_syntax::parse_header_imports(&src);
        let snap = snap_cache.entry(imports.clone()).or_insert_with(|| {
            let mut st = Store::persistent();
            let targets: Vec<_> = imports
                .iter()
                .map(|m| dotted_to_name(m))
                .collect();
            leanr_olean::load_closure(&sp, &targets, &mut st)
                .ok()
                .map(|loaded| Arc::new(assemble(&loaded, &st).snapshot))
        });
        let Some(snap) = snap else { continue };
        let r = leanr_syntax::parse_module(&src, snap);
        if r.tree.text() != src || !r.errors.is_empty() {
            continue;
        }
        let Some(want) = oracle_dump(&mathlib, &lean_path, &githash, file) else { continue };
        if leanr_syntax::canon::canon_jsonl(&r.tree) == want {
            green.push(rel);
        }
    }
    green.sort();

    let committed: Vec<String> = std::fs::read_to_string(passlist_path())
        .unwrap_or_default()
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(String::from)
        .collect();

    let regressions: Vec<_> = committed.iter().filter(|f| !green.contains(f)).collect();
    let newly_green: Vec<_> = green.iter().filter(|f| !committed.contains(f)).collect();
    eprintln!(
        "sweep: {} files, {} green, {} on pass-list, {} regressions, {} newly green",
        files.len(), green.len(), committed.len(), regressions.len(), newly_green.len()
    );

    if std::env::var("LEANR_PASSLIST_UPDATE").as_deref() == Ok("1") {
        let mut out = String::from(
            "# Mathlib-closure files that parse oracle-green (M3b2a ratchet).\n\
             # Regenerate: mise run passlist:update. NEVER hand-edit to hide a regression.\n",
        );
        for f in &green {
            out.push_str(f);
            out.push('\n');
        }
        std::fs::write(passlist_path(), out).unwrap();
        return;
    }
    assert!(regressions.is_empty(), "pass-list regressions: {regressions:#?}");
}

fn collect_lean_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            // Skip build dirs — only source trees.
            if p.file_name().is_some_and(|n| n == ".lake" || n == "build") {
                continue;
            }
            collect_lean_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "lean") {
            out.push(p);
        }
    }
}

fn dotted_to_name(dotted: &str) -> Arc<leanr_kernel::Name> {
    use leanr_kernel::Name;
    let mut n = Arc::new(Name::Anonymous);
    for part in dotted.split('.') {
        n = Arc::new(Name::Str { parent: n, part: part.to_string() });
    }
    n
}
