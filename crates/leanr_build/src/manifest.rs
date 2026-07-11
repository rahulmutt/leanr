//! `lake-manifest.json` reader (spec §Architecture, component 3).
//! Schema 1.x observed at the pinned toolchain; unknown major versions
//! error clearly rather than mis-resolving.

use std::path::{Path, PathBuf};

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

pub fn parse_manifest(text: &str, path: &Path) -> Result<Manifest, BuildError> {
    let err = |msg: String| BuildError::Manifest {
        path: path.to_path_buf(),
        msg,
    };
    let raw: RawManifest = serde_json::from_str(text).map_err(|e| err(e.to_string()))?;
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
            "git" => PackageSource::Git {
                url: p
                    .url
                    .ok_or_else(|| err(format!("package `{}`: missing url", p.name)))?,
                rev: p
                    .rev
                    .ok_or_else(|| err(format!("package `{}`: missing rev", p.name)))?,
                sub_dir: p.sub_dir,
            },
            "path" => PackageSource::Path {
                dir: p
                    .dir
                    .ok_or_else(|| err(format!("package `{}`: missing dir", p.name)))?,
            },
            other => return Err(err(format!("package `{}`: unknown type `{other}`", p.name))),
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
}
