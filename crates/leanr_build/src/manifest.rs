//! `lake-manifest.json` reader (spec §Architecture, component 3).
//! Schema 1.x observed at the pinned toolchain; unknown major versions
//! error clearly rather than mis-resolving.

use std::path::{Component, Path, PathBuf};

use serde::Deserialize;

use crate::error::BuildError;

#[derive(Debug, Clone)]
pub enum PackageSource {
    Git {
        url: String,
        rev: String,
        sub_dir: Option<PathBuf>,
    },
    Path {
        dir: PathBuf,
    },
}

#[derive(Debug, Clone)]
pub struct ManifestPackage {
    pub name: String,
    pub source: PackageSource,
    pub config_file: PathBuf,
    pub inherited: bool,
}

#[derive(Debug, Clone)]
pub struct Manifest {
    pub packages_dir: PathBuf,
    pub packages: Vec<ManifestPackage>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct RawManifest {
    version: String,
    #[serde(default)]
    packages_dir: Option<PathBuf>,
    #[serde(default)]
    packages: Vec<RawPackage>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct RawPackage {
    name: String,
    #[serde(rename = "type")]
    kind: String,
    #[serde(default)]
    url: Option<String>,
    #[serde(default)]
    rev: Option<String>,
    #[serde(default)]
    sub_dir: Option<PathBuf>,
    #[serde(default)]
    dir: Option<PathBuf>,
    #[serde(default)]
    config_file: Option<PathBuf>,
    #[serde(default)]
    inherited: bool,
}

/// Reject `subDir` values that could escape `packages_dir/<name>` when
/// `resolve()` composes them via `base.join(sub_dir)` (dep-composition
/// step, crates/leanr_build/src/lib.rs): an absolute value replaces the
/// base entirely (`Path::join` semantics) and a `..` component walks back
/// up out of it. Same trust-boundary discipline as
/// `fetch::validate_package_name` / `fetch::validate_rev`, applied to the
/// one other manifest-supplied path leanr joins onto a filesystem base.
fn validate_sub_dir(sub_dir: &Path) -> Result<(), String> {
    if sub_dir.is_absolute() {
        return Err(format!("`{}` is an absolute path", sub_dir.display()));
    }
    for comp in sub_dir.components() {
        match comp {
            Component::ParentDir => {
                return Err(format!("`{}` contains a `..` component", sub_dir.display()));
            }
            Component::RootDir | Component::Prefix(_) => {
                return Err(format!("`{}` is an absolute path", sub_dir.display()));
            }
            Component::Normal(part) => {
                let part = part
                    .to_str()
                    .ok_or_else(|| format!("`{}` contains non-UTF-8 bytes", sub_dir.display()))?;
                if part.starts_with('-') {
                    return Err(format!(
                        "`{}` has a component starting with `-`: `{part}`",
                        sub_dir.display()
                    ));
                }
                if part.contains('\0') {
                    return Err(format!("`{}` contains a NUL byte", sub_dir.display()));
                }
            }
            Component::CurDir => {}
        }
    }
    Ok(())
}

pub fn parse_manifest(text: &str, path: &Path) -> Result<Manifest, BuildError> {
    let err = |msg: String| BuildError::Manifest {
        path: path.to_path_buf(),
        msg,
    };
    let raw: RawManifest = serde_json::from_str(text).map_err(|e| {
        err(format!(
            "{}; the file is not valid JSON — regenerate it with `lake update`",
            e
        ))
    })?;
    let major = raw.version.split('.').next().unwrap_or("");
    if major != "1" {
        return Err(err(format!(
            "unsupported manifest version `{}` (leanr understands major version 1); \
             a newer lake wrote this file",
            raw.version
        )));
    }
    let mut packages = Vec::new();
    for p in raw.packages {
        let source = match p.kind.as_str() {
            "git" => {
                if let Some(sd) = &p.sub_dir {
                    validate_sub_dir(sd).map_err(|msg| {
                        err(format!(
                            "package `{}`: subDir {msg} (from lake-manifest.json); \
                             fix the entry or regenerate with `lake update`",
                            p.name
                        ))
                    })?;
                }
                PackageSource::Git {
                    url: p
                        .url
                        .ok_or_else(|| err(format!("package `{}`: missing url; regenerate the manifest with `lake update`", p.name)))?,
                    rev: p
                        .rev
                        .ok_or_else(|| err(format!("package `{}`: missing rev; regenerate the manifest with `lake update`", p.name)))?,
                    sub_dir: p.sub_dir,
                }
            }
            "path" => PackageSource::Path {
                dir: p
                    .dir
                    .ok_or_else(|| err(format!("package `{}`: missing dir; regenerate the manifest with `lake update`", p.name)))?,
            },
            other => return Err(err(format!("package `{}`: unknown type `{other}`; a newer lake wrote this file — regenerate with a matching `lake update` or update leanr", p.name))),
        };
        packages.push(ManifestPackage {
            source,
            config_file: p
                .config_file
                .unwrap_or_else(|| PathBuf::from("lakefile.lean")),
            inherited: p.inherited,
            name: p.name,
        });
    }
    Ok(Manifest {
        packages_dir: raw
            .packages_dir
            .unwrap_or_else(|| PathBuf::from(".lake/packages")),
        packages,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn fixture() -> String {
        std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mathlib-manifest.json"),
        )
        .unwrap()
    }

    #[test]
    fn parses_mathlib_manifest() {
        let m = parse_manifest(&fixture(), Path::new("lake-manifest.json")).unwrap();
        assert_eq!(m.packages_dir, Path::new(".lake/packages"));
        assert_eq!(m.packages.len(), 8);
        let names: Vec<&str> = m.packages.iter().map(|p| p.name.as_str()).collect();
        assert!(names.contains(&"batteries") && names.contains(&"proofwidgets"));
        let b = m.packages.iter().find(|p| p.name == "batteries").unwrap();
        match &b.source {
            PackageSource::Git { url, rev, sub_dir } => {
                assert!(url.starts_with("https://github.com/"));
                assert_eq!(rev.len(), 40);
                assert!(sub_dir.is_none());
            }
            other => panic!("expected git source, got {other:?}"),
        }
        assert_eq!(b.config_file, Path::new("lakefile.toml"));
        let pw = m
            .packages
            .iter()
            .find(|p| p.name == "proofwidgets")
            .unwrap();
        assert_eq!(pw.config_file, Path::new("lakefile.lean"));
    }

    #[test]
    fn path_dependency_variant() {
        let text = r#"{"version": "1.2.0", "packagesDir": ".lake/packages",
            "packages": [{"type": "path", "name": "local", "dir": "../local",
                          "manifestFile": "lake-manifest.json", "inherited": false,
                          "configFile": "lakefile.toml"}]}"#;
        let m = parse_manifest(text, Path::new("m.json")).unwrap();
        match &m.packages[0].source {
            PackageSource::Path { dir } => assert_eq!(dir, Path::new("../local")),
            other => panic!("expected path source, got {other:?}"),
        }
    }

    #[test]
    fn unknown_major_version_is_a_clear_error() {
        let text = r#"{"version": "2.0.0", "packages": []}"#;
        let err = parse_manifest(text, Path::new("m.json")).unwrap_err();
        let msg = err.to_string();
        assert!(
            msg.contains("2.0.0") && msg.contains("m.json"),
            "got: {msg}"
        );
    }

    #[test]
    fn malformed_json_names_the_file() {
        let err = parse_manifest("{", Path::new("m.json")).unwrap_err();
        assert!(err.to_string().contains("m.json"));
    }

    #[test]
    fn git_package_missing_rev_is_an_error() {
        let text = r#"{"version": "1.2.0",
            "packages": [{"type": "git", "name": "x", "url": "https://e.com/x",
                          "configFile": "lakefile.toml", "inherited": false}]}"#;
        let err = parse_manifest(text, Path::new("m.json")).unwrap_err();
        assert!(err.to_string().contains("rev"));
    }

    // -- Finding 1: subDir traversal --------------------------------------

    #[test]
    fn git_sub_dir_traversal_is_rejected() {
        let text = r#"{"version": "1.2.0",
            "packages": [{"type": "git", "name": "evil", "url": "https://e.com/x",
                          "rev": "0123456789abcdef0123456789abcdef01234567",
                          "subDir": "../escape",
                          "configFile": "lakefile.toml", "inherited": false}]}"#;
        let err = parse_manifest(text, Path::new("lake-manifest.json")).unwrap_err();
        let msg = err.to_string();
        assert!(
            msg.contains("evil") && msg.contains("lake-manifest.json") && msg.contains(".."),
            "got: {msg}"
        );
    }

    #[test]
    fn git_sub_dir_absolute_path_is_rejected() {
        let text = r#"{"version": "1.2.0",
            "packages": [{"type": "git", "name": "evil", "url": "https://e.com/x",
                          "rev": "0123456789abcdef0123456789abcdef01234567",
                          "subDir": "/etc",
                          "configFile": "lakefile.toml", "inherited": false}]}"#;
        let err = parse_manifest(text, Path::new("lake-manifest.json")).unwrap_err();
        assert!(err.to_string().contains("evil"));
    }

    #[test]
    fn git_sub_dir_leading_dash_component_is_rejected() {
        let text = r#"{"version": "1.2.0",
            "packages": [{"type": "git", "name": "evil", "url": "https://e.com/x",
                          "rev": "0123456789abcdef0123456789abcdef01234567",
                          "subDir": "-x",
                          "configFile": "lakefile.toml", "inherited": false}]}"#;
        let err = parse_manifest(text, Path::new("lake-manifest.json")).unwrap_err();
        assert!(err.to_string().contains("evil"));
    }

    #[test]
    fn git_sub_dir_legitimate_value_is_accepted() {
        let text = r#"{"version": "1.2.0",
            "packages": [{"type": "git", "name": "dep", "url": "https://e.com/x",
                          "rev": "0123456789abcdef0123456789abcdef01234567",
                          "subDir": "sub/pkg",
                          "configFile": "lakefile.toml", "inherited": false}]}"#;
        let m = parse_manifest(text, Path::new("lake-manifest.json")).unwrap();
        match &m.packages[0].source {
            PackageSource::Git { sub_dir, .. } => {
                assert_eq!(sub_dir.as_deref(), Some(Path::new("sub/pkg")))
            }
            other => panic!("expected git source, got {other:?}"),
        }
    }
}
