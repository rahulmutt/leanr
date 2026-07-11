//! Module resolution + import DAG (spec §Architecture, component 5).
//! BFS from the target seeds; header scans of each frontier run in
//! parallel (scoped threads, no external deps). All ordering is
//! deterministic: frontiers and waves are sorted by module name.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::error::BuildError;
use crate::modules::ModuleName;
use crate::scanner::{scan_header, Header};

pub struct LibUnit {
    pub package: String,
    pub src_dir: PathBuf,
    pub root: ModuleName,
}

pub struct ModuleResolver {
    units: Vec<LibUnit>,
}

impl ModuleResolver {
    pub fn new(units: Vec<LibUnit>) -> ModuleResolver {
        ModuleResolver { units }
    }

    /// Longest-root-prefix match over all libs; `Some` only if the mapped
    /// file exists on disk (a matching prefix with a missing file falls
    /// through to the next-longest candidate, then to the toolchain).
    pub fn resolve(&self, m: &ModuleName) -> Option<(String, PathBuf)> {
        let mut candidates: Vec<&LibUnit> = self
            .units
            .iter()
            .filter(|u| m.starts_with(&u.root))
            .collect();
        candidates.sort_by_key(|u| std::cmp::Reverse(u.root.components().len()));
        for u in candidates {
            let file = u.src_dir.join(m.rel_lean_path());
            if file.is_file() {
                return Some((u.package.clone(), file));
            }
        }
        None
    }
}

pub trait ToolchainIndex: Sync {
    fn contains(&self, m: &ModuleName) -> bool;
}

/// The real index: `<root>/<A/B/C>.olean` exists in the toolchain libdir
/// (`lean --print-libdir`).
pub struct OleanDirIndex {
    pub root: PathBuf,
}

impl ToolchainIndex for OleanDirIndex {
    fn contains(&self, m: &ModuleName) -> bool {
        let mut p: PathBuf = self.root.join(m.components().iter().collect::<PathBuf>());
        p.set_extension("olean");
        p.is_file()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleId(pub u32);

#[derive(Debug)]
pub struct ModuleInfo {
    pub name: ModuleName,
    pub package: String,
    pub file: PathBuf,
    /// Raw scanned imports, including toolchain-external ones.
    pub imports: Vec<ModuleName>,
    /// Workspace-internal dependency edges (deduplicated).
    pub deps: Vec<ModuleId>,
    pub prelude: bool,
    pub is_module: bool,
}

#[derive(Debug)]
pub struct ModuleGraph {
    pub modules: Vec<ModuleInfo>,
    index: HashMap<ModuleName, ModuleId>,
}

impl ModuleGraph {
    pub fn id_of(&self, m: &ModuleName) -> Option<ModuleId> {
        self.index.get(m).copied()
    }
}

/// Chunk size for splitting a frontier round of `len` files across
/// `parallelism` scanner threads (ceiling division, minimum chunk size 1
/// whenever `len > 0`). Bounds the thread count to `parallelism` regardless
/// of frontier size: at Mathlib scale a single frontier round can hold
/// thousands of files, and spawning one thread per file well past the core
/// count adds scheduling/allocation overhead with no parallelism gain
/// (Task 5's deferred follow-up, absorbed into Task 10's differential
/// sweep prep).
fn scan_chunk_size(len: usize, parallelism: usize) -> usize {
    let parallelism = parallelism.max(1);
    if len == 0 {
        return 1;
    }
    len.div_ceil(parallelism).max(1)
}

pub fn build_graph(
    seeds: &[ModuleName],
    resolver: &ModuleResolver,
    toolchain: &dyn ToolchainIndex,
) -> Result<ModuleGraph, BuildError> {
    // name -> (package, file, header); imports kept as names until all
    // nodes exist, then edges are wired up.
    let mut scanned: HashMap<ModuleName, (String, PathBuf, Header)> = HashMap::new();
    let mut external: HashSet<ModuleName> = HashSet::new();
    // Frontier entries carry their importer for error messages.
    let mut frontier: Vec<(ModuleName, String)> = seeds
        .iter()
        .map(|m| (m.clone(), "<target>".to_string()))
        .collect();

    while !frontier.is_empty() {
        frontier.sort();
        frontier.dedup();
        // Resolve + classify this frontier.
        let mut to_scan: Vec<(ModuleName, String, PathBuf)> = Vec::new();
        for (m, importer) in frontier.drain(..) {
            if scanned.contains_key(&m) || external.contains(&m) {
                continue;
            }
            match resolver.resolve(&m) {
                Some((pkg, file)) => to_scan.push((m, pkg, file)),
                None if toolchain.contains(&m) => {
                    external.insert(m);
                }
                None => {
                    return Err(BuildError::UnresolvedImport {
                        module: m.to_string(),
                        importer,
                    })
                }
            }
        }
        // Scan the frontier's files in parallel: chunked across at most
        // `available_parallelism` scoped threads (not one thread per file —
        // see `scan_chunk_size`), each thread scanning its chunk in a plain
        // loop.
        let parallelism = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        let chunk_size = scan_chunk_size(to_scan.len(), parallelism);
        let results: Vec<Result<(ModuleName, String, PathBuf, Header), BuildError>> =
            std::thread::scope(|s| {
                let handles: Vec<_> = to_scan
                    .chunks(chunk_size)
                    .map(|chunk| {
                        s.spawn(move || {
                            chunk
                                .iter()
                                .map(|(m, pkg, file)| {
                                    let bytes =
                                        std::fs::read(file).map_err(|e| BuildError::Io {
                                            path: file.clone(),
                                            err: e.to_string(),
                                        })?;
                                    Ok((m.clone(), pkg.clone(), file.clone(), scan_header(&bytes)))
                                })
                                .collect::<Vec<Result<(ModuleName, String, PathBuf, Header), BuildError>>>()
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .flat_map(|h| h.join().expect("scan thread"))
                    .collect()
            });
        for r in results {
            let (m, pkg, file, header) = r?;
            for imp in &header.imports {
                frontier.push((imp.clone(), m.to_string()));
            }
            scanned.insert(m, (pkg, file, header));
        }
    }

    // Deterministic node order: sorted by name.
    let mut names: Vec<ModuleName> = scanned.keys().cloned().collect();
    names.sort();
    let index: HashMap<ModuleName, ModuleId> = names
        .iter()
        .enumerate()
        .map(|(i, n)| (n.clone(), ModuleId(i as u32)))
        .collect();
    let mut modules = Vec::with_capacity(names.len());
    for name in names {
        let (package, file, header) = scanned.remove(&name).expect("scanned");
        let mut deps: Vec<ModuleId> = header
            .imports
            .iter()
            .filter_map(|i| index.get(i).copied())
            .collect();
        deps.sort_by_key(|id| id.0);
        deps.dedup();
        modules.push(ModuleInfo {
            name,
            package,
            file,
            imports: header.imports,
            deps,
            prelude: header.prelude,
            is_module: header.is_module,
        });
    }
    Ok(ModuleGraph { modules, index })
}

/// Kahn's algorithm into waves; each wave sorted by module name (module
/// order == index order, which is name-sorted). Cycles are reported with
/// one witness cycle path.
pub fn topo_waves(g: &ModuleGraph) -> Result<Vec<Vec<ModuleId>>, BuildError> {
    let n = g.modules.len();
    let mut remaining_deps: Vec<usize> = g.modules.iter().map(|m| m.deps.len()).collect();
    let mut dependents: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (i, m) in g.modules.iter().enumerate() {
        for d in &m.deps {
            dependents[d.0 as usize].push(i as u32);
        }
    }
    let mut waves = Vec::new();
    let mut done = 0usize;
    let mut ready: Vec<u32> = (0..n as u32)
        .filter(|&i| remaining_deps[i as usize] == 0)
        .collect();
    while !ready.is_empty() {
        ready.sort();
        let wave: Vec<ModuleId> = ready.iter().map(|&i| ModuleId(i)).collect();
        let mut next = Vec::new();
        for &i in &ready {
            for &dep in &dependents[i as usize] {
                remaining_deps[dep as usize] -= 1;
                if remaining_deps[dep as usize] == 0 {
                    next.push(dep);
                }
            }
        }
        done += wave.len();
        waves.push(wave);
        ready = next;
    }
    if done < n {
        // Extract one witness cycle by walking deps among leftover nodes.
        let start = (0..n).find(|&i| remaining_deps[i] > 0).expect("leftover");
        let mut path = vec![start];
        let mut seen = HashMap::from([(start, 0usize)]);
        loop {
            let cur = *path.last().expect("nonempty");
            let next = g.modules[cur]
                .deps
                .iter()
                .map(|d| d.0 as usize)
                .find(|&d| remaining_deps[d] > 0)
                .expect("cyclic node has a cyclic dep");
            if let Some(&at) = seen.get(&next) {
                let cycle: Vec<String> = path[at..]
                    .iter()
                    .chain(std::iter::once(&next))
                    .map(|&i| g.modules[i].name.to_string())
                    .collect();
                return Err(BuildError::ImportCycle { cycle });
            }
            seen.insert(next, path.len());
            path.push(next);
        }
    }
    Ok(waves)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modules::ModuleName;
    use std::collections::HashSet;

    fn mn(s: &str) -> ModuleName {
        ModuleName::parse(s).unwrap()
    }

    fn write(dir: &std::path::Path, rel: &str, text: &str) {
        let p = dir.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }

    /// Toolchain fake: a fixed set of module names.
    struct FakeToolchain(HashSet<String>);
    impl ToolchainIndex for FakeToolchain {
        fn contains(&self, m: &ModuleName) -> bool {
            self.0.contains(&m.to_string())
        }
    }

    fn fake_toolchain() -> FakeToolchain {
        FakeToolchain(
            ["Init", "Init.Core", "Lean"]
                .iter()
                .map(|s| s.to_string())
                .collect(),
        )
    }

    /// Two packages: `app` (lib App) depends on `dep` (lib Dep).
    fn two_package_workspace() -> (tempfile::TempDir, ModuleResolver) {
        let tmp = tempfile::TempDir::new().unwrap();
        write(tmp.path(), "app/App.lean", "import App.A\nimport Dep\n");
        write(tmp.path(), "app/App/A.lean", "import Init.Core\n");
        write(tmp.path(), "dep/Dep.lean", "prelude\n");
        let resolver = ModuleResolver::new(vec![
            LibUnit {
                package: "app".into(),
                src_dir: tmp.path().join("app"),
                root: mn("App"),
            },
            LibUnit {
                package: "dep".into(),
                src_dir: tmp.path().join("dep"),
                root: mn("Dep"),
            },
        ]);
        (tmp, resolver)
    }

    #[test]
    fn resolver_longest_prefix_and_existence() {
        let (tmp, r) = two_package_workspace();
        let (pkg, file) = r.resolve(&mn("App.A")).unwrap();
        assert_eq!(pkg, "app");
        assert_eq!(file, tmp.path().join("app/App/A.lean"));
        assert!(r.resolve(&mn("App.Missing")).is_none()); // root matches, file absent
        assert!(r.resolve(&mn("Other")).is_none());
    }

    #[test]
    fn build_graph_follows_transitive_imports_and_classifies_toolchain() {
        let (_tmp, r) = two_package_workspace();
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        let names: HashSet<String> = g.modules.iter().map(|m| m.name.to_string()).collect();
        assert_eq!(
            names,
            ["App", "App.A", "Dep"]
                .iter()
                .map(|s| s.to_string())
                .collect()
        );
        // Init.Core is toolchain-external: recorded in imports, no dep edge.
        let a = &g.modules[g.id_of(&mn("App.A")).unwrap().0 as usize];
        assert!(a.imports.contains(&mn("Init.Core")));
        assert!(a.deps.is_empty());
    }

    #[test]
    fn unresolved_import_names_module_and_importer() {
        let tmp = tempfile::TempDir::new().unwrap();
        write(tmp.path(), "app/App.lean", "import Ghost\n");
        let r = ModuleResolver::new(vec![LibUnit {
            package: "app".into(),
            src_dir: tmp.path().join("app"),
            root: mn("App"),
        }]);
        let err = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("Ghost") && msg.contains("App"), "got: {msg}");
    }

    #[test]
    fn waves_respect_deps_and_sort_lexicographically() {
        let (_tmp, r) = two_package_workspace();
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        let waves = topo_waves(&g).unwrap();
        let render: Vec<Vec<String>> = waves
            .iter()
            .map(|w| {
                w.iter()
                    .map(|id| g.modules[id.0 as usize].name.to_string())
                    .collect()
            })
            .collect();
        assert_eq!(
            render,
            [
                vec!["App.A".to_string(), "Dep".to_string()],
                vec!["App".to_string()]
            ]
        );
    }

    #[test]
    fn cycle_is_reported_with_its_members() {
        let tmp = tempfile::TempDir::new().unwrap();
        write(tmp.path(), "app/App.lean", "import App.B\n");
        write(tmp.path(), "app/App/B.lean", "import App\n");
        let r = ModuleResolver::new(vec![LibUnit {
            package: "app".into(),
            src_dir: tmp.path().join("app"),
            root: mn("App"),
        }]);
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        let err = topo_waves(&g).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("cycle") && msg.contains("App.B"), "got: {msg}");
    }

    #[test]
    fn scan_chunk_size_bounds_thread_count_and_covers_every_item() {
        // Empty frontier: any positive chunk size is fine, never zero
        // (a zero chunk size would make `slice::chunks` panic).
        assert_eq!(scan_chunk_size(0, 8), 1);
        // Fewer files than cores: one file per thread, never more threads
        // than files.
        assert_eq!(scan_chunk_size(3, 8), 1);
        // More files than cores: chunk so at most `parallelism` threads run,
        // covering every item (ceiling division).
        assert_eq!(scan_chunk_size(11_000, 8), 1375);
        let chunks = (11_000usize).div_ceil(scan_chunk_size(11_000, 8));
        assert!(chunks <= 8, "expected <= 8 chunks, got {chunks}");
        // Degenerate parallelism (0 reported, or 1 core) never panics and
        // still produces a usable chunk size.
        assert_eq!(scan_chunk_size(10, 0), 10);
        assert_eq!(scan_chunk_size(10, 1), 10);
    }

    #[test]
    fn build_graph_at_thousand_module_scale_is_chunked_and_still_correct() {
        // Not Mathlib-scale (that's the differential tier's job), but large
        // enough to exercise multiple scan chunks under
        // `available_parallelism` and confirm chunking didn't change
        // correctness: every generated module is present, sorted, deduped,
        // with the right toolchain-external edge dropped.
        let tmp = tempfile::TempDir::new().unwrap();
        let n = 1500;
        for i in 0..n {
            write(
                tmp.path(),
                &format!("app/App/M{i}.lean"),
                "import Init.Core\n",
            );
        }
        let roots: Vec<String> = (0..n).map(|i| format!("App.M{i}")).collect();
        write(
            tmp.path(),
            "app/App.lean",
            &roots
                .iter()
                .map(|r| format!("import {r}\n"))
                .collect::<String>(),
        );
        let r = ModuleResolver::new(vec![LibUnit {
            package: "app".into(),
            src_dir: tmp.path().join("app"),
            root: mn("App"),
        }]);
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        assert_eq!(g.modules.len(), n + 1); // App + App.M0..App.M{n-1}
        let mut names: Vec<String> = g.modules.iter().map(|m| m.name.to_string()).collect();
        let sorted = {
            let mut s = names.clone();
            s.sort();
            s
        };
        assert_eq!(
            names, sorted,
            "modules must stay name-sorted after chunking"
        );
        names.dedup();
        assert_eq!(names.len(), g.modules.len(), "no duplicate modules");
        let leaf = &g.modules[g.id_of(&mn("App.M0")).unwrap().0 as usize];
        assert!(leaf.imports.contains(&mn("Init.Core")));
        assert!(leaf.deps.is_empty(), "toolchain import is not a dep edge");
    }

    #[test]
    fn duplicate_imports_yield_one_dep_edge() {
        let tmp = tempfile::TempDir::new().unwrap();
        write(tmp.path(), "app/App.lean", "import App.B\nimport App.B\n");
        write(tmp.path(), "app/App/B.lean", "");
        let r = ModuleResolver::new(vec![LibUnit {
            package: "app".into(),
            src_dir: tmp.path().join("app"),
            root: mn("App"),
        }]);
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        let app = &g.modules[g.id_of(&mn("App")).unwrap().0 as usize];
        assert_eq!(app.deps.len(), 1);
    }
}
