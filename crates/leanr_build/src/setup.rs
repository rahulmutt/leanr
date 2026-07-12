//! Per-module `lean` invocation planning (M2b spec §Architecture,
//! component `setup`): artifact paths in leanr's own layout
//! (`.leanr/build/<pkg>/…`), the `--setup` JSON lake hands to lean
//! (verified against `lake build --verbose` on the pinned toolchain,
//! spec §Key empirical facts), and LEAN_PATH for transitive olean
//! loads. Pure functions — nothing here runs a process.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use crate::config::LeanOptionValue;
use crate::graph::{ModuleId, ModuleInfo};
use crate::modules::ModuleName;
use crate::Workspace;

pub struct Layout {
    /// `<workspace root>/.leanr/build`
    pub build_root: PathBuf,
}

impl Layout {
    pub fn new(root_dir: &Path) -> Layout {
        Layout {
            build_root: root_dir.join(".leanr").join("build"),
        }
    }

    pub fn lib_dir(&self, package: &str) -> PathBuf {
        self.build_root.join(package).join("lib")
    }

    fn module_path(&self, base: PathBuf, m: &ModuleName, ext: &str) -> PathBuf {
        let mut p = base.join(m.components().iter().collect::<PathBuf>());
        p.set_extension(ext);
        p
    }

    pub fn olean_path(&self, package: &str, m: &ModuleName) -> PathBuf {
        self.module_path(self.lib_dir(package), m, "olean")
    }

    pub fn ilean_path(&self, package: &str, m: &ModuleName) -> PathBuf {
        self.module_path(self.lib_dir(package), m, "ilean")
    }

    pub fn setup_path(&self, package: &str, m: &ModuleName) -> PathBuf {
        self.module_path(self.build_root.join(package).join("setup"), m, "setup.json")
    }

    /// The artifact family `lean` emits: `.olean` + `.ilean` always;
    /// module-system modules add `.ir`, `.olean.server`, `.olean.private`
    /// (siblings lean derives from `-o` — spec §Key empirical facts).
    pub fn artifact_paths(&self, package: &str, m: &ModuleInfo) -> Vec<PathBuf> {
        let mut arts = vec![
            self.olean_path(package, &m.name),
            self.ilean_path(package, &m.name),
        ];
        if m.is_module {
            for ext in ["ir", "olean.server", "olean.private"] {
                arts.push(self.module_path(self.lib_dir(package), &m.name, ext));
            }
        }
        arts
    }
}

/// The `--setup` JSON, shaped exactly like lake's (observed on the
/// pinned toolchain): importArts lists the exact artifact paths of each
/// direct *workspace* import (toolchain imports are omitted, resolved
/// via lean's own sysroot); options carry the owning package's
/// leanOptions overlaid by the owning lib's.
#[derive(Debug, serde::Serialize)]
pub struct SetupFile {
    pub package: String,
    pub name: String,
    #[serde(rename = "isModule")]
    pub is_module: bool,
    pub options: BTreeMap<String, serde_json::Value>,
    #[serde(rename = "importArts")]
    pub import_arts: BTreeMap<String, Vec<String>>,
    pub plugins: Vec<String>,
    pub dynlibs: Vec<String>,
}

fn option_value(v: &LeanOptionValue) -> serde_json::Value {
    match v {
        LeanOptionValue::Bool(b) => (*b).into(),
        LeanOptionValue::Int(i) => (*i).into(),
        LeanOptionValue::String(s) => s.clone().into(),
    }
}

fn module_options(ws: &Workspace, m: &ModuleInfo) -> BTreeMap<String, serde_json::Value> {
    let mut out = BTreeMap::new();
    let pkg = std::iter::once(&ws.root)
        .chain(ws.deps.iter())
        .find(|p| p.name == m.package);
    if let Some(p) = pkg {
        for (k, v) in &p.config.lean_options {
            out.insert(k.clone(), option_value(v));
        }
        if let Some(lib) = p.config.lean_libs.iter().find(|l| l.name == m.lib) {
            for (k, v) in &lib.lean_options {
                out.insert(k.clone(), option_value(v));
            }
        }
    }
    out
}

pub fn module_setup(ws: &Workspace, layout: &Layout, id: ModuleId) -> SetupFile {
    let m = &ws.graph.modules[id.0 as usize];
    let mut import_arts = BTreeMap::new();
    for &d in &m.deps {
        let dm = &ws.graph.modules[d.0 as usize];
        let mut arts = vec![layout
            .olean_path(&dm.package, &dm.name)
            .display()
            .to_string()];
        if dm.is_module {
            for ext in ["ir", "olean.server", "olean.private"] {
                arts.push(
                    layout
                        .module_path(layout.lib_dir(&dm.package), &dm.name, ext)
                        .display()
                        .to_string(),
                );
            }
        }
        import_arts.insert(dm.name.to_string(), arts);
    }
    SetupFile {
        package: m.package.clone(),
        name: m.name.to_string(),
        is_module: m.is_module,
        options: module_options(ws, m),
        import_arts,
        plugins: vec![],
        dynlibs: vec![],
    }
}

/// LEAN_PATH for every worker: each package's lib dir (transitive olean
/// loads resolve through it — lake sets it too, spec §Key empirical facts).
pub fn lean_path_env(ws: &Workspace, layout: &Layout) -> OsString {
    let dirs = std::iter::once(&ws.root)
        .chain(ws.deps.iter())
        .map(|p| layout.lib_dir(&p.name));
    std::env::join_paths(dirs).expect("lib dirs contain no path separators")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testws;

    #[test]
    fn layout_paths_are_under_leanr_build() {
        let t = testws::synthetic();
        let layout = Layout::new(&t.ws.root_dir);
        let sub = crate::modules::ModuleName::parse("App.Sub").unwrap();
        assert_eq!(
            layout.olean_path("app", &sub),
            t.ws.root_dir.join(".leanr/build/app/lib/App/Sub.olean")
        );
        assert_eq!(
            layout.ilean_path("app", &sub),
            t.ws.root_dir.join(".leanr/build/app/lib/App/Sub.ilean")
        );
        assert_eq!(
            layout.setup_path("app", &sub),
            t.ws.root_dir
                .join(".leanr/build/app/setup/App/Sub.setup.json")
        );
    }

    #[test]
    fn setup_file_carries_import_arts_options_and_is_module() {
        let t = testws::synthetic();
        let layout = Layout::new(&t.ws.root_dir);
        let app_id =
            t.ws.graph
                .id_of(&crate::modules::ModuleName::parse("App").unwrap())
                .unwrap();
        let s = module_setup(&t.ws, &layout, app_id);
        let got = serde_json::to_value(&s).unwrap();
        let sub_olean = layout
            .olean_path(
                "app",
                &crate::modules::ModuleName::parse("App.Sub").unwrap(),
            )
            .display()
            .to_string();
        assert_eq!(
            got,
            serde_json::json!({
                "package": "app",
                "name": "App",
                "isModule": false,
                "options": {"autoImplicit": false, "pp.unicode.fun": true},
                "importArts": {"App.Sub": [sub_olean]},
                "plugins": [],
                "dynlibs": []
            })
        );
    }

    #[test]
    fn module_system_modules_get_the_full_artifact_family() {
        let t = testws::synthetic();
        let layout = Layout::new(&t.ws.root_dir);
        let sub_id =
            t.ws.graph
                .id_of(&crate::modules::ModuleName::parse("App.Sub").unwrap())
                .unwrap();
        let m = &t.ws.graph.modules[sub_id.0 as usize];
        // Non-module module: olean + ilean only.
        assert_eq!(layout.artifact_paths("app", m).len(), 2);
        // A module-system ModuleInfo adds .ir/.olean.server/.olean.private.
        let mm = crate::graph::ModuleInfo {
            name: m.name.clone(),
            package: m.package.clone(),
            lib: m.lib.clone(),
            file: m.file.clone(),
            imports: vec![],
            deps: vec![],
            prelude: m.prelude,
            is_module: true,
        };
        let arts = layout.artifact_paths("app", &mm);
        let exts: Vec<String> = arts
            .iter()
            .map(|p| p.to_string_lossy().rsplit('/').next().unwrap().to_string())
            .collect();
        assert_eq!(
            exts,
            vec![
                "Sub.olean",
                "Sub.ilean",
                "Sub.ir",
                "Sub.olean.server",
                "Sub.olean.private"
            ]
        );
    }

    #[test]
    fn lean_path_lists_every_package_lib_dir() {
        let t = testws::synthetic();
        let layout = Layout::new(&t.ws.root_dir);
        let lp = lean_path_env(&t.ws, &layout);
        let parts: Vec<PathBuf> = std::env::split_paths(&lp).collect();
        assert!(parts.contains(&layout.lib_dir("app")));
    }
}
