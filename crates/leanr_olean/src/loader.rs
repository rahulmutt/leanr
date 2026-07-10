//! Import-closure loader: resolve a module name to an `.olean` file on a
//! search path, then load a set of target modules together with the
//! transitive closure of their imports, topologically sorted
//! (dependencies first).
//!
//! Trust boundary: module names come from decoded `.olean` bytes, which
//! are UNTRUSTED (docs/THREAT_MODEL.md). The name→path mapping therefore
//! rejects any component that could escape a search root (path-traversal
//! hardening) *before* touching the filesystem, and the closure walk is
//! an iterative DFS with an explicit stack and an on-path set so an
//! attacker-crafted import graph can neither overflow the stack nor hang.
//!
//! # Multi-part modules (`.olean.private` / `.olean.server`)
//!
//! The oracle's module system (pinned toolchain v4.32.0-rc1) can split one
//! module into a base `Foo.olean` plus companion parts `Foo.olean.server`
//! and `Foo.olean.private` (oracle: `OLeanLevel.adjustFileName`,
//! src/Lean/Environment.lean:1793-1796). Only the base part is a
//! self-contained compacted region; the companion parts deduplicate objects
//! against the earlier parts and store cross-region pointers into them:
//!
//! * `saveModuleDataParts` (Environment.lean:1739-1749): "Objects shared with
//!   prior parts are not duplicated. Thus the data cannot be loaded with
//!   individual `readModuleData` calls but must [be] loaded by passing (a
//!   prefix of) the file names to `readModuleDataParts`."
//! * `readModuleDataParts` (Environment.lean:1755-1763) loads parts in order,
//!   accumulating each part's `CompactedRegion` into a `depRegions` array that
//!   the next part is read against, so a part's pointers can target objects in
//!   an earlier part's mapping.
//! * The base part carries only the module's public *interface* (a public
//!   `def`/`theorem` with an unexported body is a bare `axiom` stub there);
//!   the `.private` part carries the module's FULL, checkable constant set
//!   (`mkModuleData`, Environment.lean:1843-1852).
//!
//! [`FileSource`] loads all present parts of a found module together via
//! [`ModuleData::parse_parts`] (M1b Task 13a's multi-region decoder), so a
//! public constant that references a `_private.*` helper living in the
//! `.olean.private` part now resolves during replay. Missing companion parts
//! are fine (pre-module-system oleans have none); a malformed companion is a
//! [`LoadError::Decode`] carrying the offending part's path.

use std::collections::HashMap;
use std::ffi::OsStr;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use leanr_kernel::bank::Store;
use leanr_kernel::Name;

use crate::{ModuleData, OleanError, PartKind};

/// An ordered list of directories to resolve module names against.
///
/// The library takes its roots verbatim: it never reads `LEAN_PATH` or
/// invokes `lean --print-libdir` (that discovery is the CLI's job, Task 14).
pub struct SearchPath {
    /// Roots searched in priority order; the first match wins.
    pub roots: Vec<PathBuf>,
}

impl SearchPath {
    /// Build a search path from `roots`, searched in order.
    pub fn new(roots: Vec<PathBuf>) -> SearchPath {
        SearchPath { roots }
    }

    /// Resolve a module name to the first root that contains its base
    /// `.olean` file: `Init.Data.Nat` → the first `root` for which
    /// `root/Init/Data/Nat.olean` is a file.
    ///
    /// Returns `None` (no filesystem access outside a root) when the name
    /// cannot be mapped to a safe relative path — a numeric component, an
    /// empty component, or a component containing `/`, `\`, `..`, or NUL
    /// (path-traversal hardening; names come from untrusted `.olean` bytes).
    pub fn find(&self, module: &Name) -> Option<PathBuf> {
        let rel = module_rel_path(module)?;
        for root in &self.roots {
            let candidate = root.join(&rel);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
        None
    }
}

/// Map a module name to its relative base-`.olean` path, or `None` if any
/// component is unsafe. Iterative (never recurses into `parent`) so an
/// attacker-deep name chain cannot overflow the stack.
fn module_rel_path(module: &Name) -> Option<PathBuf> {
    // Walk the name chain leaf→root collecting string components; a numeric
    // component makes the whole name unmappable to a path.
    let mut parts: Vec<&str> = Vec::new();
    let mut cur = module;
    loop {
        match cur {
            Name::Anonymous => break,
            Name::Str { parent, part } => {
                parts.push(part.as_str());
                cur = parent.as_ref();
            }
            // Numeric components never name an on-disk module.
            Name::Num { .. } => return None,
        }
    }
    if parts.is_empty() {
        // The anonymous name maps to no file.
        return None;
    }
    parts.reverse();
    // Path-traversal hardening, in two layers:
    //
    // 1. ALLOW-LIST (load-bearing on the platform we run on): the component
    //    must parse as exactly one `Component::Normal` equal to itself. This
    //    structurally guarantees `PathBuf::push`/`Path::join` can only append
    //    a single ordinary segment — it can never replace the accumulated
    //    path or the search root, which `push` is documented to do for
    //    absolute paths and for Windows prefixed paths ("if `path` has a
    //    prefix but no root, it replaces `self`", e.g. `C:` or `\\?\...`).
    //    Whatever separator/prefix syntax the current platform has,
    //    `components()` speaks it, so nothing platform-specific can slip
    //    through as `Normal`.
    //
    // 2. Explicit rejects for FOREIGN platform syntax: on Unix, `\`, `:`,
    //    and `..`-containing strings are ordinary filename bytes and would
    //    pass check 1, but they are Windows separators/drive-prefix syntax
    //    (`a\b`, `C:`) or traversal material. Rejecting them here keeps the
    //    accept/reject decision identical on every platform (and these names
    //    never occur in real Lean modules). `/` and NUL are also listed for
    //    explicitness even though check 1 (`/`) and the OS (`NUL`) already
    //    exclude them.
    for part in &parts {
        if part.is_empty()
            || part.contains('/')
            || part.contains('\\')
            || part.contains(':')
            || part.contains("..")
            || part.contains('\0')
        {
            return None;
        }
        let mut components = Path::new(part).components();
        match (components.next(), components.next()) {
            (Some(Component::Normal(c)), None) if c == OsStr::new(part) => {}
            _ => return None,
        }
    }
    let mut rel = PathBuf::new();
    for part in &parts {
        rel.push(part);
    }
    // Append (not replace) the extension so a component that itself contains
    // a `.` keeps all its characters: `Init/Data/Nat` → `Init/Data/Nat.olean`.
    let mut os = rel.into_os_string();
    os.push(".olean");
    Some(PathBuf::from(os))
}

/// Failure loading a module or its import closure.
///
/// Does not derive `PartialEq`: the `Io`/`Decode` variants carry a
/// `std::io::Error`, which is not comparable. Tests match with `matches!`.
#[derive(Debug, thiserror::Error)]
pub enum LoadError {
    /// No search root contains the module (or its name is unmappable to a
    /// safe path — see [`SearchPath::find`]).
    #[error("module '{0}' not found in search path")]
    ModuleNotFound(String),
    /// The import graph contains a cycle reaching the named module. Real
    /// Lean modules are acyclic; a crafted cycle errors, never hangs.
    #[error("import cycle through '{0}'")]
    ImportCycle(String),
    /// The module's file could not be read.
    #[error("{path}: {source}")]
    Io {
        /// The file that failed to read.
        path: PathBuf,
        /// The underlying I/O error.
        #[source]
        source: std::io::Error,
    },
    /// The module's bytes did not decode as an `.olean` module.
    #[error("{path}: {source}")]
    Decode {
        /// The file that failed to decode.
        path: PathBuf,
        /// The underlying decode error.
        #[source]
        source: OleanError,
    },
}

/// Seam between the closure-walk algorithm and where module data comes
/// from. The production impl ([`FileSource`]) reads and decodes `.olean`
/// files; tests supply an in-memory graph to exercise cycle/diamond/topo
/// behavior without crafting byte-identical cyclic `.olean` files (which
/// the oracle cannot even produce).
trait ModuleSource {
    /// The loaded representation of one module.
    type Module;
    /// Load a single module by name.
    fn load(&mut self, module: &Name) -> Result<Self::Module, LoadError>;
    /// The direct imports of a loaded module.
    fn imports(module: &Self::Module) -> Vec<Arc<Name>>;
}

/// Production [`ModuleSource`]: resolve names on a [`SearchPath`], read the
/// bytes, and decode with [`ModuleData::parse`] directly into `st` (the
/// caller's store — direct-to-id decode, phase 3).
struct FileSource<'a> {
    search_path: &'a SearchPath,
    st: &'a mut Store,
}

impl ModuleSource for FileSource<'_> {
    type Module = ModuleData;

    fn load(&mut self, module: &Name) -> Result<ModuleData, LoadError> {
        let path = self
            .search_path
            .find(module)
            .ok_or_else(|| LoadError::ModuleNotFound(module.to_string()))?;
        load_module_at(&path, self.st)
    }

    fn imports(module: &ModuleData) -> Vec<Arc<Name>> {
        module
            .imports
            .iter()
            .map(|i| Arc::clone(&i.module))
            .collect()
    }
}

/// The companion-part file for an ALREADY-VALIDATED base `.olean` path:
/// `Foo.olean` + `"private"` → `Foo.olean.private` (oracle:
/// `OLeanLevel.adjustFileName`, src/Lean/Environment.lean:1793-1796, which
/// is `base.addExtension ext`). The base path came from [`SearchPath::find`]
/// (its module name was already traversal-checked), so appending a fixed
/// literal suffix introduces no new untrusted component — no re-validation
/// needed.
fn companion_path(base: &Path, ext: &str) -> PathBuf {
    let mut os = base.as_os_str().to_os_string();
    os.push(".");
    os.push(ext);
    PathBuf::from(os)
}

/// Read and decode the module rooted at base `.olean` path `base`, pulling
/// in its `.olean.server`/`.olean.private` companion parts when they exist.
///
/// Mirrors the oracle's fresh-check consumer (`ImportArtifacts.oleanParts`
/// with `inServer := false`, src/Lean/Setup.lean:92-103): the base is always
/// loaded; the `.private` part is loaded when present; the `.server` part is
/// loaded only as a dependency of `.private` (a `.private` part's pointers
/// can target objects deduplicated into the `.server` region). A missing
/// companion is fine — pre-module-system oleans have none.
fn load_module_at(base: &Path, st: &mut Store) -> Result<ModuleData, LoadError> {
    let base_bytes = read_part(base)?;

    let private = companion_path(base, "private");
    if !private.is_file() {
        // No `.private` companion: a plain single-region module.
        return ModuleData::parse(&base_bytes, st).map_err(|source| LoadError::Decode {
            path: base.to_path_buf(),
            source,
        });
    }

    // Base first, then `.server` (dep region for `.private`) if present, then
    // `.private` — the oracle's load order (readModuleDataPartsOfMod,
    // Environment.lean:2042-2055).
    let server = companion_path(base, "server");
    let server_bytes = if server.is_file() {
        Some(read_part(&server)?)
    } else {
        None
    };
    let private_bytes = read_part(&private)?;

    // Attribute a malformed companion HEADER (truncated/bad magic/version/
    // githash) to that companion's own path. A deeper cross-region pointer
    // failure is a property of the whole part set, so it falls through to the
    // base path in the `parse_parts` call below.
    for (path, bytes) in [
        (&server, server_bytes.as_deref()),
        (&private, Some(private_bytes.as_slice())),
    ] {
        if let Some(bytes) = bytes {
            crate::OleanHeader::parse(bytes).map_err(|source| LoadError::Decode {
                path: path.clone(),
                source,
            })?;
        }
    }

    let mut parts: Vec<(PartKind, &[u8])> = vec![(PartKind::Base, &base_bytes)];
    if let Some(sb) = &server_bytes {
        parts.push((PartKind::Server, sb));
    }
    parts.push((PartKind::Private, &private_bytes));

    ModuleData::parse_parts(&parts, st).map_err(|source| LoadError::Decode {
        path: base.to_path_buf(),
        source,
    })
}

/// Read one part file, mapping I/O failure to [`LoadError::Io`] with its path.
fn read_part(path: &Path) -> Result<Vec<u8>, LoadError> {
    std::fs::read(path).map_err(|source| LoadError::Io {
        path: path.to_path_buf(),
        source,
    })
}

/// Load `targets` plus the transitive closure of their imports, returned
/// topologically sorted with dependencies before the modules that import
/// them. Each module appears exactly once even under diamond imports.
///
/// Iterative DFS with an explicit stack and an on-path set (import depth is
/// attacker-controlled): a cycle yields [`LoadError::ImportCycle`] rather
/// than hanging or overflowing the stack.
///
/// See the module docs for the base-part-only limitation regarding
/// `.olean.private`/`.olean.server` companion parts.
pub fn load_closure(
    sp: &SearchPath,
    targets: &[Arc<Name>],
    st: &mut Store,
) -> Result<LoadedModules<ModuleData>, LoadError> {
    load_closure_with(
        &mut FileSource {
            search_path: sp,
            st,
        },
        targets,
    )
}

/// A loaded closure: `(module name, loaded module)` pairs in
/// dependencies-first order.
type LoadedModules<M> = Vec<(Arc<Name>, M)>;

/// Where a name currently sits in the DFS: `OnPath` = its `Exit` is still
/// pending (an ancestor of whatever we process next), `Done` = fully loaded.
enum Status {
    OnPath,
    Done,
}

/// Generic closure walk over any [`ModuleSource`]. Post-order DFS: a node's
/// `Exit` runs only after all its imports are `Done`, so pushing at `Exit`
/// yields dependencies-first order.
fn load_closure_with<S: ModuleSource>(
    src: &mut S,
    targets: &[Arc<Name>],
) -> Result<LoadedModules<S::Module>, LoadError> {
    enum Frame {
        Enter(Arc<Name>),
        Exit(Arc<Name>),
    }

    let mut status: HashMap<Arc<Name>, Status> = HashMap::new();
    // Holds each module between its `Enter` (load) and `Exit` (emit).
    let mut loaded: HashMap<Arc<Name>, S::Module> = HashMap::new();
    let mut result: Vec<(Arc<Name>, S::Module)> = Vec::new();

    // Process targets in the given order: push them reversed so the first
    // target is entered first.
    let mut stack: Vec<Frame> = targets
        .iter()
        .rev()
        .map(|n| Frame::Enter(Arc::clone(n)))
        .collect();

    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Enter(name) => {
                match status.get(&name) {
                    // Already fully loaded (a shared/diamond dependency).
                    Some(Status::Done) => continue,
                    // Re-entered while still on the current path: back edge.
                    // Everything above this node's pending `Exit` on the stack
                    // is a descendant of it, so this is a genuine cycle.
                    Some(Status::OnPath) => {
                        return Err(LoadError::ImportCycle(name.to_string()));
                    }
                    None => {}
                }
                let module = src.load(&name)?;
                let imports = S::imports(&module);
                status.insert(Arc::clone(&name), Status::OnPath);
                loaded.insert(Arc::clone(&name), module);
                stack.push(Frame::Exit(Arc::clone(&name)));
                // Reversed so the first import is entered first.
                for imp in imports.into_iter().rev() {
                    stack.push(Frame::Enter(imp));
                }
            }
            Frame::Exit(name) => {
                let module = loaded
                    .remove(&name)
                    .expect("module was inserted at its Enter frame");
                status.insert(Arc::clone(&name), Status::Done);
                result.push((name, module));
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::Nat;
    use std::sync::atomic::{AtomicU64, Ordering};

    // --- test helpers ---------------------------------------------------

    /// Build a dotted module name, e.g. `Init.Data.Nat`.
    fn name(dotted: &str) -> Arc<Name> {
        let mut n = Arc::new(Name::Anonymous);
        for part in dotted.split('.') {
            n = Arc::new(Name::Str {
                parent: n,
                part: part.to_string(),
            });
        }
        n
    }

    /// A name with one string component appended to `parent` — for building
    /// deliberately unsafe components (`..`, `a/b`) the parser rejects.
    fn str_child(parent: Arc<Name>, part: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent,
            part: part.to_string(),
        })
    }

    /// Absolute path to the committed fixtures dir (hermetic, in-tree).
    fn fixtures_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures")
    }

    /// Minimal RAII temp dir (avoids a `tempfile` dependency). Creates a
    /// uniquely named directory and removes it on drop.
    struct TempDir {
        path: PathBuf,
    }

    impl TempDir {
        fn new() -> TempDir {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("leanr-loader-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir { path }
        }

        /// Create an (empty) file at `rel`, making parent dirs as needed.
        fn touch(&self, rel: &str) {
            let p = self.path.join(rel);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, b"").unwrap();
        }

        /// Write `bytes` to `rel`, making parent dirs as needed.
        fn write(&self, rel: &str, bytes: &[u8]) {
            let p = self.path.join(rel);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, bytes).unwrap();
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.path);
        }
    }

    /// In-memory [`ModuleSource`]: an adjacency list keyed by module name.
    /// A module's "loaded form" is just its list of imports, which lets the
    /// closure walk run over arbitrary graphs (including cyclic ones the
    /// oracle could never emit as bytes).
    struct GraphSource {
        edges: HashMap<String, Vec<Arc<Name>>>,
    }

    impl GraphSource {
        fn new(edges: &[(&str, &[&str])]) -> GraphSource {
            let mut map = HashMap::new();
            for (m, deps) in edges {
                map.insert(
                    (*m).to_string(),
                    deps.iter().map(|d| name(d)).collect::<Vec<_>>(),
                );
            }
            GraphSource { edges: map }
        }
    }

    impl ModuleSource for GraphSource {
        type Module = Vec<Arc<Name>>;

        fn load(&mut self, module: &Name) -> Result<Vec<Arc<Name>>, LoadError> {
            self.edges
                .get(&module.to_string())
                .cloned()
                .ok_or_else(|| LoadError::ModuleNotFound(module.to_string()))
        }

        fn imports(module: &Vec<Arc<Name>>) -> Vec<Arc<Name>> {
            module.clone()
        }
    }

    /// Names, in load order, of a graph closure result.
    fn order(result: &[(Arc<Name>, Vec<Arc<Name>>)]) -> Vec<String> {
        result.iter().map(|(n, _)| n.to_string()).collect()
    }

    // --- SearchPath::find / name→path mapping ---------------------------

    #[test]
    fn finds_module_in_second_root() {
        let a = TempDir::new();
        let b = TempDir::new();
        // Only the second root has the file.
        b.touch("Init/Data/Nat.olean");
        let sp = SearchPath::new(vec![a.path.clone(), b.path.clone()]);
        let found = sp.find(&name("Init.Data.Nat")).expect("should hit root b");
        assert_eq!(found, b.path.join("Init/Data/Nat.olean"));
    }

    #[test]
    fn name_to_path_mapping() {
        // `Init.Data.Nat` → `Init/Data/Nat.olean` under the matching root.
        let rel = module_rel_path(&name("Init.Data.Nat")).unwrap();
        assert_eq!(rel, PathBuf::from("Init").join("Data").join("Nat.olean"));

        // A single-component module maps to `Foo.olean`.
        assert_eq!(
            module_rel_path(&name("Foo")).unwrap(),
            PathBuf::from("Foo.olean")
        );
    }

    #[test]
    fn rejects_traversal_components() {
        let tmp = TempDir::new();
        // Plant a file the traversal would try to escape toward; the mapping
        // must refuse before the filesystem is ever consulted.
        tmp.touch("evil.olean");
        let sp = SearchPath::new(vec![tmp.path.clone()]);

        // `..` component.
        let dotdot = str_child(Arc::new(Name::Anonymous), "..");
        assert!(module_rel_path(&dotdot).is_none());
        assert!(sp.find(&dotdot).is_none());

        // Embedded path separator `a/b`.
        let slash = str_child(name("Init"), "a/b");
        assert!(module_rel_path(&slash).is_none());
        assert!(sp.find(&slash).is_none());

        // Backslash and NUL components.
        assert!(module_rel_path(&str_child(name("Init"), "a\\b")).is_none());
        assert!(module_rel_path(&str_child(name("Init"), "a\0b")).is_none());

        // Empty STRING component (distinct from the zero-component anonymous
        // name below: this exercises the per-component reject, not the
        // empty-parts early return).
        let empty = str_child(name("Init"), "");
        assert!(module_rel_path(&empty).is_none());
        assert!(sp.find(&empty).is_none());

        // Windows drive prefix: on Windows, `PathBuf::push("C:")` REPLACES
        // the accumulated path/root instead of appending (documented `push`
        // semantics for prefixed paths), so `C:` must be rejected on every
        // platform, not just where it parses as a prefix.
        let drive = str_child(Arc::new(Name::Anonymous), "C:");
        assert!(module_rel_path(&drive).is_none());
        assert!(sp.find(&drive).is_none());
        assert!(module_rel_path(&str_child(name("Init"), "C:evil")).is_none());

        // A numeric component is unmappable.
        let numeric = Arc::new(Name::Num {
            parent: name("Init"),
            part: Nat::from(3u64),
        });
        assert!(module_rel_path(&numeric).is_none());
        assert!(sp.find(&numeric).is_none());

        // The anonymous name maps to nothing.
        assert!(module_rel_path(&Arc::new(Name::Anonymous)).is_none());

        // Through the public API a rejected name is a `ModuleNotFound`, and
        // the planted sibling file is never reached.
        let mut st = Store::persistent();
        let err = load_closure(&sp, &[dotdot], &mut st).unwrap_err();
        assert!(matches!(err, LoadError::ModuleNotFound(_)), "got {err:?}");
    }

    // --- closure walk (in-memory graph seam) ----------------------------

    #[test]
    fn loads_closure_topo_sorted() {
        // A imports B imports C  →  [C, B, A], each exactly once.
        let mut src = GraphSource::new(&[("A", &["B"]), ("B", &["C"]), ("C", &[])]);
        let result = load_closure_with(&mut src, &[name("A")]).unwrap();
        assert_eq!(order(&result), vec!["C", "B", "A"]);
    }

    #[test]
    fn detects_cycle() {
        // A → B → A must error, not hang or overflow.
        let mut src = GraphSource::new(&[("A", &["B"]), ("B", &["A"])]);
        let err = load_closure_with(&mut src, &[name("A")]).unwrap_err();
        assert!(matches!(err, LoadError::ImportCycle(_)), "got {err:?}");
    }

    #[test]
    fn diamond_imports_loaded_once() {
        // A → {B, C}, B → D, C → D: D is loaded exactly once and before B/C.
        let mut src =
            GraphSource::new(&[("A", &["B", "C"]), ("B", &["D"]), ("C", &["D"]), ("D", &[])]);
        let result = load_closure_with(&mut src, &[name("A")]).unwrap();
        let names = order(&result);
        assert_eq!(names, vec!["D", "B", "C", "A"]);
        assert_eq!(names.iter().filter(|n| *n == "D").count(), 1);
    }

    #[test]
    fn self_cycle_detected() {
        // Degenerate 1-node cycle A → A.
        let mut src = GraphSource::new(&[("A", &["A"])]);
        let err = load_closure_with(&mut src, &[name("A")]).unwrap_err();
        assert!(matches!(err, LoadError::ImportCycle(_)), "got {err:?}");
    }

    #[test]
    fn shared_dependency_across_targets_loaded_once() {
        // Two targets that share a dependency: closure emits it once.
        let mut src = GraphSource::new(&[("A", &["C"]), ("B", &["C"]), ("C", &[])]);
        let result = load_closure_with(&mut src, &[name("A"), name("B")]).unwrap();
        let names = order(&result);
        assert_eq!(names, vec!["C", "A", "B"]);
        assert_eq!(names.iter().filter(|n| *n == "C").count(), 1);
    }

    // --- production FileSource path (hermetic, via committed fixtures) ---

    #[test]
    fn load_closure_reads_and_decodes_real_olean() {
        // `Prelude0` is the committed import-free fixture, so its closure is
        // just itself — this exercises find → read → ModuleData::parse.
        let sp = SearchPath::new(vec![fixtures_dir()]);
        let mut st = Store::persistent();
        let result = load_closure(&sp, &[name("Prelude0")], &mut st).unwrap();
        assert_eq!(result.len(), 1);
        let (n, md) = &result[0];
        assert_eq!(n.to_string(), "Prelude0");
        assert!(md.imports.is_empty(), "Prelude0 imports nothing");
        assert!(!md.constants.is_empty(), "Prelude0 declares constants");
    }

    #[test]
    fn missing_module_is_module_not_found() {
        let sp = SearchPath::new(vec![fixtures_dir()]);
        let mut st = Store::persistent();
        let err = load_closure(&sp, &[name("No.Such.Module")], &mut st).unwrap_err();
        assert!(matches!(err, LoadError::ModuleNotFound(_)), "got {err:?}");
    }

    #[test]
    fn garbage_file_is_decode_error() {
        let tmp = TempDir::new();
        tmp.write("Garbage.olean", b"definitely not an olean file");
        let sp = SearchPath::new(vec![tmp.path.clone()]);
        let mut st = Store::persistent();
        let err = load_closure(&sp, &[name("Garbage")], &mut st).unwrap_err();
        assert!(matches!(err, LoadError::Decode { .. }), "got {err:?}");
    }

    /// End-to-end over the pinned toolchain (needs it on disk, so ignored in
    /// CI): resolve and decode the *base-part* closure of a real module.
    /// `Init.Data.Nat` transitively imports `Init` (among others), so a
    /// successful, dependencies-first result with no duplicates exercises the
    /// production `FileSource` path against a genuine multi-level import graph.
    /// It does NOT touch `.olean.private`/`.olean.server` companion parts (see
    /// the module-level KNOWN LIMITATION); replaying this closure through the
    /// kernel can still hit `UnknownConstant` on `_private.*` helpers.
    #[test]
    #[ignore = "needs the pinned Lean toolchain; run via LEANR_SWEEP_DIR=$(lean --print-libdir)"]
    fn load_closure_over_real_toolchain_base_parts() {
        let dir = std::env::var("LEANR_SWEEP_DIR")
            .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
        let sp = SearchPath::new(vec![PathBuf::from(dir)]);
        let mut st = Store::persistent();
        let result = load_closure(&sp, &[name("Init.Data.Nat")], &mut st).unwrap();

        let names: Vec<String> = result.iter().map(|(n, _)| n.to_string()).collect();
        // A real multi-level closure: `Init.Data.Nat` pulls in well over a
        // hundred `Init.*` modules.
        assert!(names.len() > 100, "closure suspiciously small: {names:?}");
        // Dependencies come before the module that imports them, and the
        // requested target is emitted last.
        assert_eq!(names.last().unwrap(), "Init.Data.Nat");
        // `Init.Prelude` is the transitive base of everything and must appear
        // strictly before the modules that import it.
        assert!(
            names.contains(&"Init.Prelude".to_string()),
            "closure should include the transitively-imported Init.Prelude"
        );
        // No module appears twice (diamond dedup over the real graph).
        let mut sorted = names.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), names.len(), "duplicate module in {names:?}");
    }
}
