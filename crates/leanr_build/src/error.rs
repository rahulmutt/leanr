use std::path::PathBuf;

/// Every user-facing failure of the build pipeline. Postcondition of the
/// whole crate: errors name the file/package they came from and the action
/// that fixes them (spec §Error handling & trust).
#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error("no lakefile.toml or lakefile.lean found in {0} or any parent directory")]
    NoWorkspaceRoot(PathBuf),
    #[error("{path}: {msg}")]
    Config { path: PathBuf, msg: String },
    #[error("no lake-manifest.json in {0}; run `lake update` once and commit it")]
    NoManifest(PathBuf),
    #[error("{path}: {msg}")]
    Manifest { path: PathBuf, msg: String },
    #[error("manifest is stale: `require {name}` in {config} has no lake-manifest.json entry; run `lake update` and commit the result")]
    StaleManifest { name: String, config: PathBuf },
    #[error("package `{name}`: {msg}")]
    Fetch { name: String, msg: String },
    #[error("`{cmd}` {reason}\n{stderr}")]
    Subprocess {
        cmd: String,
        reason: String,
        stderr: String,
    },
    #[error("import cycle: {}", cycle.join(" -> "))]
    ImportCycle { cycle: Vec<String> },
    #[error(
        "module `{module}` (imported by `{importer}`) not found in the workspace or the toolchain"
    )]
    UnresolvedImport { module: String, importer: String },
    #[error("target `{0}` is not a lean_lib of the root package (only lean_lib targets are supported in M2a)")]
    UnknownTarget(String),
    #[error("{path}: {err}")]
    Io { path: PathBuf, err: String },
    #[error("package `{package}` requires {feature}, which `leanr build` does not support yet (M2b builds lean_lib artifacts only)")]
    Unsupported { package: String, feature: String },
    #[error("building `{module}` ({file}) failed:\n{details}")]
    ModuleBuild {
        module: String,
        file: PathBuf,
        details: String,
    },
}
