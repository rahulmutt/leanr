//! Module names, globs, and glob expansion (spec §Architecture, component 5).

use std::fmt;
use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::error::BuildError;

/// A dot-separated Lean module name. Guillemet components (`«a.b»`) are
/// stored unquoted; a component never contains `«»` and is never empty.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleName(Vec<String>);

impl ModuleName {
    /// Parse `A.B.«c.d»`. Errors (message only; callers add file context)
    /// on empty input, empty components, unclosed guillemets, or
    /// whitespace outside guillemets.
    pub fn parse(s: &str) -> Result<ModuleName, String> {
        let mut comps = Vec::new();
        let mut chars = s.chars().peekable();
        loop {
            let mut comp = String::new();
            if chars.peek() == Some(&'«') {
                chars.next();
                loop {
                    match chars.next() {
                        Some('»') => break,
                        Some(c) => comp.push(c),
                        None => return Err(format!("unclosed «» in `{s}`")),
                    }
                }
            } else {
                while let Some(&c) = chars.peek() {
                    if c == '.' {
                        break;
                    }
                    if c.is_whitespace() || c == '«' || c == '»' {
                        return Err(format!("invalid character {c:?} in `{s}`"));
                    }
                    comp.push(c);
                    chars.next();
                }
            }
            if comp.is_empty() {
                return Err(format!("empty component in `{s}`"));
            }
            comps.push(comp);
            match chars.next() {
                None => break,
                Some('.') => continue,
                Some(c) => return Err(format!("unexpected {c:?} in `{s}`")),
            }
        }
        Ok(ModuleName(comps))
    }

    pub fn components(&self) -> &[String] {
        &self.0
    }

    pub fn starts_with(&self, prefix: &ModuleName) -> bool {
        self.0.len() >= prefix.0.len() && self.0[..prefix.0.len()] == prefix.0[..]
    }

    pub fn child(&self, part: &str) -> ModuleName {
        let mut c = self.0.clone();
        c.push(part.to_string());
        ModuleName(c)
    }

    /// `A.B.C` -> `A/B/C.lean` (component strings used verbatim).
    pub fn rel_lean_path(&self) -> PathBuf {
        let mut p: PathBuf = self.0.iter().collect();
        p.set_extension("lean");
        p
    }
}

impl fmt::Display for ModuleName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.join("."))
    }
}

/// Lake's TOML glob syntax: `X` (the module), `X.+` (strict submodules),
/// `X.*` (module and submodules). Only `X` and `X.+` are observed in the
/// Mathlib closure; `X.*` is implemented for completeness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Glob {
    One(ModuleName),
    Submodules(ModuleName),
    AndSubmodules(ModuleName),
}

impl Glob {
    pub fn parse(s: &str) -> Result<Glob, String> {
        if let Some(base) = s.strip_suffix(".+") {
            Ok(Glob::Submodules(ModuleName::parse(base)?))
        } else if let Some(base) = s.strip_suffix(".*") {
            Ok(Glob::AndSubmodules(ModuleName::parse(base)?))
        } else {
            Ok(Glob::One(ModuleName::parse(s)?))
        }
    }
}

impl<'de> Deserialize<'de> for Glob {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Glob, D::Error> {
        let s = String::deserialize(d)?;
        Glob::parse(&s).map_err(serde::de::Error::custom)
    }
}

/// Expand a glob against a library source directory (spec component 5).
/// `One` is purely nominal (existence is checked later, at resolve time);
/// the directory walks are iterative (explicit stack — untrusted-deep
/// trees must not overflow) and results are sorted for determinism.
pub fn expand_glob(glob: &Glob, src_dir: &Path) -> Result<Vec<ModuleName>, BuildError> {
    match glob {
        Glob::One(m) => Ok(vec![m.clone()]),
        Glob::Submodules(m) => walk_submodules(m, src_dir),
        Glob::AndSubmodules(m) => {
            let mut out = vec![m.clone()];
            out.extend(walk_submodules(m, src_dir)?);
            out.sort();
            out.dedup();
            Ok(out)
        }
    }
}

fn walk_submodules(root: &ModuleName, src_dir: &Path) -> Result<Vec<ModuleName>, BuildError> {
    let base: PathBuf = src_dir.join(root.components().iter().collect::<PathBuf>());
    let mut out = Vec::new();
    if !base.is_dir() {
        return Ok(out); // no submodule directory — an empty glob, like lake
    }
    let mut stack = vec![(base.clone(), root.clone())];
    while let Some((dir, prefix)) = stack.pop() {
        let entries = std::fs::read_dir(&dir).map_err(|e| BuildError::Io {
            path: dir.clone(),
            err: e.to_string(),
        })?;
        for entry in entries {
            let entry = entry.map_err(|e| BuildError::Io {
                path: dir.clone(),
                err: e.to_string(),
            })?;
            let path = entry.path();
            let Some(stem) = path
                .file_stem()
                .and_then(|s| s.to_str())
                .map(|s| s.to_string())
            else {
                continue; // non-UTF-8 file name: not a Lean module
            };
            if path.is_dir() {
                stack.push((path, prefix.child(&stem)));
            } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
                out.push(prefix.child(&stem));
            }
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_dotted_name() {
        let m = ModuleName::parse("Mathlib.Algebra.Group.Basic").unwrap();
        assert_eq!(m.components(), ["Mathlib", "Algebra", "Group", "Basic"]);
        assert_eq!(m.to_string(), "Mathlib.Algebra.Group.Basic");
        assert_eq!(
            m.rel_lean_path(),
            std::path::PathBuf::from("Mathlib/Algebra/Group/Basic.lean")
        );
    }

    #[test]
    fn guillemet_component_is_one_component_and_may_contain_dots() {
        let m = ModuleName::parse("Cache.«cache-test».Main").unwrap();
        assert_eq!(m.components(), ["Cache", "cache-test", "Main"]);
        let d = ModuleName::parse("«a.b»").unwrap();
        assert_eq!(d.components(), ["a.b"]);
    }

    #[test]
    fn rejects_malformed_names() {
        for bad in ["", ".", "A..B", "A.", ".A", "«unclosed", "A B"] {
            assert!(ModuleName::parse(bad).is_err(), "should reject {bad:?}");
        }
    }

    #[test]
    fn starts_with_and_child() {
        let root = ModuleName::parse("Mathlib").unwrap();
        let m = ModuleName::parse("Mathlib.Init").unwrap();
        assert!(m.starts_with(&root));
        assert!(root.starts_with(&root));
        assert!(!root.starts_with(&m));
        assert_eq!(root.child("Init"), m);
    }

    #[test]
    fn glob_forms() {
        assert_eq!(
            Glob::parse("Cache.+").unwrap(),
            Glob::Submodules(ModuleName::parse("Cache").unwrap())
        );
        assert_eq!(
            Glob::parse("Cache.*").unwrap(),
            Glob::AndSubmodules(ModuleName::parse("Cache").unwrap())
        );
        assert_eq!(
            Glob::parse("Cache").unwrap(),
            Glob::One(ModuleName::parse("Cache").unwrap())
        );
        assert!(Glob::parse("").is_err());
    }

    fn touch(dir: &std::path::Path, rel: &str) {
        let p = dir.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, "").unwrap();
    }

    #[test]
    fn expand_one_yields_the_module_without_touching_disk() {
        let m = ModuleName::parse("Mathlib").unwrap();
        let got = expand_glob(&Glob::One(m.clone()), std::path::Path::new("/nonexistent")).unwrap();
        assert_eq!(got, [m]);
    }

    #[test]
    fn expand_submodules_walks_the_directory() {
        let tmp = tempfile::TempDir::new().unwrap();
        touch(tmp.path(), "Cache/IO.lean");
        touch(tmp.path(), "Cache/Requests/Sub.lean");
        touch(tmp.path(), "Cache/README.md"); // ignored: not .lean
        touch(tmp.path(), "Cache.lean"); // ignored: Submodules is strict
        let g = Glob::Submodules(ModuleName::parse("Cache").unwrap());
        let got = expand_glob(&g, tmp.path()).unwrap();
        let names: Vec<String> = got.iter().map(|m| m.to_string()).collect();
        assert_eq!(names, ["Cache.IO", "Cache.Requests.Sub"]); // sorted
    }

    #[test]
    fn expand_and_submodules_includes_the_root_module() {
        let tmp = tempfile::TempDir::new().unwrap();
        touch(tmp.path(), "Cache.lean");
        touch(tmp.path(), "Cache/IO.lean");
        let g = Glob::AndSubmodules(ModuleName::parse("Cache").unwrap());
        let got = expand_glob(&g, tmp.path()).unwrap();
        let names: Vec<String> = got.iter().map(|m| m.to_string()).collect();
        assert_eq!(names, ["Cache", "Cache.IO"]);
    }

    #[test]
    fn expand_submodules_of_missing_dir_is_empty_not_an_error() {
        let g = Glob::Submodules(ModuleName::parse("Nope").unwrap());
        let tmp = tempfile::TempDir::new().unwrap();
        assert_eq!(expand_glob(&g, tmp.path()).unwrap(), []);
    }
}
