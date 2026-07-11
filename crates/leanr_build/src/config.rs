//! Native `lakefile.toml` schema (spec §Architecture, component 1).
//! Field coverage = what the Mathlib closure exercises plus obvious
//! basics; unknown keys warn (forward compatibility), never fail.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::error::BuildError;
use crate::modules::{Glob, ModuleName};

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(untagged)]
pub enum LeanOptionValue {
    Bool(bool),
    Int(i64),
    String(String),
}

pub type LeanOptions = BTreeMap<String, LeanOptionValue>;

/// Helper to flatten nested toml::Value into dotted keys.
fn flatten_toml_value(
    prefix: &str,
    val: &toml::Value,
    result: &mut BTreeMap<String, LeanOptionValue>,
) {
    match val {
        toml::Value::Boolean(b) => {
            let _ = result.insert(prefix.to_string(), LeanOptionValue::Bool(*b));
        }
        toml::Value::Integer(i) => {
            let _ = result.insert(prefix.to_string(), LeanOptionValue::Int(*i));
        }
        toml::Value::String(s) => {
            let _ = result.insert(prefix.to_string(), LeanOptionValue::String(s.clone()));
        }
        toml::Value::Table(t) => {
            for (k, v) in t {
                let key = if prefix.is_empty() {
                    k.clone()
                } else {
                    format!("{prefix}.{k}")
                };
                flatten_toml_value(&key, v, result);
            }
        }
        _ => {
            // Arrays, dates, etc. are ignored
        }
    }
}

/// Custom deserializer for LeanOptions that handles nested structures
/// and flattens them with dotted keys.
fn deserialize_lean_options<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> Result<LeanOptions, D::Error> {
    let val = toml::Value::deserialize(d)?;
    let mut result = BTreeMap::new();
    if let toml::Value::Table(t) = val {
        for (k, v) in t {
            flatten_toml_value(&k, &v, &mut result);
        }
    }
    Ok(result)
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Require {
    pub name: String,
    #[serde(default)]
    pub scope: Option<String>,
    #[serde(default)]
    pub rev: Option<String>,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub git: Option<String>,
    #[serde(default)]
    pub path: Option<PathBuf>,
    #[serde(default)]
    pub options: BTreeMap<String, toml::Value>,
    #[serde(flatten)]
    pub unknown: BTreeMap<String, toml::Value>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LeanLibConfig {
    pub name: String,
    #[serde(default)]
    pub src_dir: Option<PathBuf>,
    #[serde(default)]
    pub roots: Option<Vec<String>>,
    #[serde(default)]
    pub globs: Option<Vec<Glob>>,
    #[serde(default, deserialize_with = "deserialize_lean_options")]
    pub lean_options: LeanOptions,
    #[serde(default)]
    pub default_facets: Option<toml::Value>,
    // Parsed-but-unused (observed in the Mathlib closure — ProofWidgets'
    // `lean_lib` targets declare extra facet dependencies, e.g. a JS build
    // step, via `needs`; irrelevant to leanr's module resolution but must
    // not warn as an unknown key).
    #[serde(default)]
    pub needs: Option<Vec<String>>,
    #[serde(flatten)]
    pub unknown: BTreeMap<String, toml::Value>,
}

impl LeanLibConfig {
    /// Lake defaults: `roots` defaults to `[name]`.
    /// A root that fails to parse as a module name is dropped here and
    /// surfaces later as an unresolved import; real-world roots are plain
    /// identifiers.
    pub fn effective_roots(&self) -> Vec<ModuleName> {
        match &self.roots {
            Some(rs) => rs
                .iter()
                .filter_map(|r| ModuleName::parse(r).ok())
                .collect(),
            None => ModuleName::parse(&self.name).ok().into_iter().collect(),
        }
    }

    /// Lake defaults: `globs` defaults to `roots.map(Glob::One)`.
    pub fn effective_globs(&self) -> Vec<Glob> {
        match &self.globs {
            Some(gs) => gs.clone(),
            None => self.effective_roots().into_iter().map(Glob::One).collect(),
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LeanExeConfig {
    pub name: String,
    #[serde(default)]
    pub src_dir: Option<PathBuf>,
    #[serde(default)]
    pub root: Option<String>,
    #[serde(default)]
    pub support_interpreter: Option<bool>,
    #[serde(default)]
    pub weak_link_args: Option<Vec<String>>,
    #[serde(flatten)]
    pub unknown: BTreeMap<String, toml::Value>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PackageConfig {
    pub name: String,
    #[serde(default)]
    pub default_targets: Vec<String>,
    #[serde(default)]
    pub src_dir: Option<PathBuf>,
    #[serde(default, deserialize_with = "deserialize_lean_options")]
    pub lean_options: LeanOptions,
    // Parsed-but-unused (observed in the Mathlib closure; kept out of the
    // unknown-key warning path):
    #[serde(default)]
    pub test_driver: Option<String>,
    #[serde(default)]
    pub test_driver_args: Option<Vec<String>>,
    #[serde(default)]
    pub lint_driver: Option<String>,
    #[serde(default)]
    pub lint_driver_args: Option<Vec<String>>,
    #[serde(default)]
    pub precompile_modules: Option<bool>,
    #[serde(default)]
    pub platform_independent: Option<bool>,
    #[serde(default)]
    pub version: Option<toml::Value>,
    #[serde(default)]
    pub description: Option<String>,
    #[serde(default)]
    pub keywords: Option<Vec<String>>,
    #[serde(default)]
    pub license: Option<String>,
    #[serde(default)]
    pub license_files: Option<Vec<String>>,
    #[serde(default)]
    pub test_runner: Option<String>,
    // Parsed-but-unused (observed in the Mathlib closure: ProofWidgets
    // declares its bundled JS/TS sources via these array-of-table facet
    // declarations — snake_case in Lake's own TOML schema, unlike its other
    // camelCase keys, hence the explicit `rename`s below). Irrelevant to
    // leanr's module resolution.
    #[serde(default, rename = "input_file")]
    pub input_file: Option<Vec<toml::Value>>,
    #[serde(default, rename = "input_dir")]
    pub input_dir: Option<Vec<toml::Value>>,
    #[serde(default, rename = "require")]
    pub requires: Vec<Require>,
    #[serde(default, rename = "lean_lib")]
    pub lean_libs: Vec<LeanLibConfig>,
    #[serde(default, rename = "lean_exe")]
    pub lean_exes: Vec<LeanExeConfig>,
    #[serde(flatten)]
    pub unknown: BTreeMap<String, toml::Value>,
}

#[derive(Debug)]
pub struct ParsedConfig {
    pub config: PackageConfig,
    /// Unknown-key warnings, in document order: "path: unknown key `k` (ignored)".
    pub warnings: Vec<String>,
}

pub fn parse_lakefile_toml(text: &str, path: &Path) -> Result<ParsedConfig, BuildError> {
    let config: PackageConfig = toml::from_str(text).map_err(|e| BuildError::Config {
        path: path.to_path_buf(),
        msg: e.to_string(),
    })?;
    let mut warnings = Vec::new();
    let warn = |warnings: &mut Vec<String>, ctx: &str, keys: &BTreeMap<String, toml::Value>| {
        for k in keys.keys() {
            warnings.push(format!(
                "{}: unknown key `{k}` in {ctx} (ignored)",
                path.display()
            ));
        }
    };
    warn(&mut warnings, "package", &config.unknown);
    for l in &config.lean_libs {
        warn(&mut warnings, &format!("lean_lib `{}`", l.name), &l.unknown);
    }
    for e in &config.lean_exes {
        warn(&mut warnings, &format!("lean_exe `{}`", e.name), &e.unknown);
    }
    for r in &config.requires {
        warn(&mut warnings, &format!("require `{}`", r.name), &r.unknown);
    }
    Ok(ParsedConfig { config, warnings })
}
