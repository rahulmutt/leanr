//! The fmt self-consistency gate over the parser pass-list (spec
//! §Acceptance harness). Only runs when the Mathlib checkout is present
//! (env LEANR_FMT_CORPUS=1, set by `mise run fmt:mathlib`); otherwise it
//! is a no-op so `cargo test` in a bare checkout stays green. Mirrors the
//! per-file snapshot build in leanr_grammar/tests/mathlib_sweep.rs.

use std::path::{Path, PathBuf};

fn passlist_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax/mathlib-passlist.txt")
}

fn mathlib_root() -> PathBuf {
    // The pass-list paths are relative to the Mathlib checkout root.
    // Reuse the same location leanr_grammar's sweep uses.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.mathlib")
}

#[test]
fn fmt_holds_all_invariants_over_passlist() {
    if std::env::var("LEANR_FMT_CORPUS").as_deref() != Ok("1") {
        eprintln!("skipping fmt corpus gate (set LEANR_FMT_CORPUS=1 via `mise run fmt:mathlib`)");
        return;
    }
    // An empty LEANR_OLEAN_PATH would make every non-Builtin `snapshot_for`
    // call fail closed (`None`), which — if that were still treated as a
    // skip below — would make the whole gate vacuously green while checking
    // nothing. Fail loudly up front instead, mirroring
    // `leanr_grammar/tests/mathlib_sweep.rs`'s identical `roots` assert.
    let roots: Vec<String> = std::env::var("LEANR_OLEAN_PATH")
        .unwrap_or_default()
        .split(':')
        .filter(|s| !s.is_empty())
        .map(String::from)
        .collect();
    assert!(
        !roots.is_empty(),
        "LEANR_OLEAN_PATH is empty — run via `mise run fmt:mathlib`; check that `lake env \
         printenv LEAN_PATH` succeeds in .mathlib"
    );
    let list = std::fs::read_to_string(passlist_path()).unwrap();
    let root = mathlib_root();

    // Group pass-list files by import set so one grammar snapshot is built
    // per DISTINCT set rather than per file — the same per-import-set reuse
    // `leanr_grammar/tests/mathlib_sweep.rs` does. The key is derived from
    // the same `parse_header_imports` call the snapshot build itself makes,
    // so there is no second notion of "this file's imports" to drift.
    let mut groups: std::collections::BTreeMap<String, Vec<(String, String)>> =
        std::collections::BTreeMap::new();
    let mut checked = 0;
    for rel in list.lines() {
        let rel = rel.trim();
        if rel.is_empty() || rel.starts_with('#') {
            continue;
        }
        let file = root.join(rel);
        let src = match std::fs::read_to_string(&file) {
            Ok(s) => s,
            Err(_) => continue, // upstream churn: absent file, not a fmt regression
        };
        // The file is confirmed PRESENT, so it is now counted — a
        // present-but-unloadable file must never be silently dropped from
        // the gate (that would let a "green" run quietly check fewer files
        // than it claims).
        checked += 1;
        let mut imports = leanr_syntax::parse_header_imports(&src);
        imports.sort();
        imports.dedup();
        groups
            .entry(imports.join("\0"))
            .or_default()
            .push((rel.to_string(), src));
    }

    let mut failures = Vec::new();
    for (key, files) in &groups {
        // Any file in the group resolves the same closure; use the first.
        let (_, probe_src) = &files[0];
        let snap = match support::snapshot_for(probe_src, &root) {
            Some(s) => s,
            None => {
                // Record ONE failure PER FILE, not per group: a broken
                // closure must not shrink the effective checked count.
                for (rel, _) in files {
                    failures.push(format!(
                        "{rel}: import closure unavailable (LEANR_OLEAN_PATH / load_closure \
                         failed; import set {key:?})"
                    ));
                }
                continue;
            }
        };
        for (rel, src) in files {
            if let Err(e) = leanr_fmt::verify::check_invariants(src, snap.snapshot()) {
                failures.push(format!("{rel}: {e}"));
            }
        }
    }

    eprintln!(
        "fmt corpus gate: {checked} file(s) across {} distinct import set(s)",
        groups.len()
    );
    assert!(
        checked > 0,
        "corpus empty — pass-list or checkout wiring broken"
    );
    assert!(
        failures.is_empty(),
        "fmt invariants failed:\n{}",
        failures.join("\n")
    );
}

mod support {
    //! Snapshot build for a source file's import closure. Ported from
    //! `crates/leanr_grammar/tests/mathlib_sweep.rs`'s per-import-set
    //! snapshot build: the search path is `LEANR_OLEAN_PATH` (colon
    //! separated, the same env var the sweep reads — computed by the
    //! calling mise task via `lake env printenv LEAN_PATH` run inside the
    //! Mathlib checkout), `dotted_to_name` + `leanr_olean::load_closure`
    //! resolve the import closure into a fresh `Store`, and
    //! `leanr_grammar::assemble` folds it onto the builtin grammar into a
    //! self-contained `GrammarSnapshot`. Kept in sync with that logic
    //! deliberately, rather than inventing a second way to build a
    //! snapshot for the same corpus.
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use leanr_grammar::{assemble, AssembledGrammar};
    use leanr_kernel::bank::Store;
    use leanr_kernel::Name;
    use leanr_olean::SearchPath;
    use leanr_syntax::grammar::GrammarSnapshot;

    /// Owns whatever backs the assembled grammar snapshot. The decoded
    /// `Store` used to build it is dropped inside `snapshot_for` right after
    /// `assemble` runs — same as mathlib_sweep.rs, which never holds a
    /// closure's `Store` past the `assemble` call that produces its
    /// snapshot.
    pub enum Holder {
        Assembled(AssembledGrammar),
        Builtin(GrammarSnapshot),
    }

    impl Holder {
        pub fn snapshot(&self) -> &GrammarSnapshot {
            match self {
                Holder::Assembled(a) => &a.snapshot,
                Holder::Builtin(s) => s,
            }
        }
    }

    /// Ported verbatim from `mathlib_sweep.rs::dotted_to_name`.
    fn dotted_to_name(dotted: &str) -> Arc<Name> {
        let mut n = Arc::new(Name::Anonymous);
        for part in dotted.split('.') {
            n = Arc::new(Name::Str {
                parent: n,
                part: part.to_string(),
            });
        }
        n
    }

    /// Ported verbatim from `mathlib_sweep.rs::mathlib_sweep_ratchet`'s
    /// `LEANR_OLEAN_PATH` -> `roots` derivation:
    /// `lean_path.split(':').filter(|s| !s.is_empty()).map(Into::into)`.
    fn search_roots() -> Vec<PathBuf> {
        std::env::var("LEANR_OLEAN_PATH")
            .unwrap_or_default()
            .split(':')
            .filter(|s| !s.is_empty())
            .map(Into::into)
            .collect()
    }

    /// Build the grammar snapshot for `src`'s import closure, resolving
    /// imports against `.mathlib` via `LEANR_OLEAN_PATH`. `root` is unused
    /// beyond identifying the checkout for callers (the search path itself
    /// comes from `LEANR_OLEAN_PATH`, exactly as in mathlib_sweep.rs); kept
    /// as a parameter so the corpus test's join of `root` + pass-list-
    /// relative path stays the single source of truth for file resolution.
    pub fn snapshot_for(src: &str, _root: &Path) -> Option<Holder> {
        let imports = leanr_syntax::parse_header_imports(src);
        if imports.is_empty() {
            return Some(Holder::Builtin(leanr_syntax::builtin::snapshot()));
        }
        let roots = search_roots();
        if roots.is_empty() {
            return None;
        }
        let sp = SearchPath::new(roots);
        let targets: Vec<_> = imports.iter().map(|m| dotted_to_name(m)).collect();
        let mut st = Store::persistent();
        let loaded = leanr_olean::load_closure(&sp, &targets, &mut st).ok()?;
        let assembled = assemble(&loaded, &st);
        // `st` (the decoded olean Store) drops here, same as the sweep —
        // only the assembled, self-contained snapshot survives.
        Some(Holder::Assembled(assembled))
    }
}
