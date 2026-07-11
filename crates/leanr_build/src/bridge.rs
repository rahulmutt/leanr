//! translate-config bridge (spec §Architecture, component 2): obtain a
//! declarative TOML config for `lakefile.lean` packages by running pinned
//! official lake once, cached by lakefile content hash. Executing a
//! lakefile is arbitrary code execution by design — identical trust to
//! running lake itself (spec §Error handling & trust).
//!
//! Verified empirically (spec §Architecture): translation works in a bare
//! checkout with no materialized dependencies, so bridging the root
//! config before fetching is sound; lake errors if the out-file exists,
//! so we hand it a fresh temp path and rename into the cache.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use crate::config::{parse_lakefile_toml, ParsedConfig};
use crate::error::BuildError;
use crate::subprocess::{self, RunError};

pub struct LakeInvoker {
    /// The lake executable (PATH-resolved name or explicit path).
    pub program: PathBuf,
    /// elan toolchain override, passed as `+<toolchain>` — pins dependency
    /// bridging to the *root* workspace's toolchain so a dep's own
    /// lean-toolchain file can't trigger a surprise toolchain download.
    pub toolchain: Option<String>,
    pub timeout: Duration,
}

impl Default for LakeInvoker {
    fn default() -> LakeInvoker {
        LakeInvoker {
            program: PathBuf::from("lake"),
            toolchain: None,
            timeout: Duration::from_secs(300),
        }
    }
}

/// Run `lake [+tc] translate-config toml <out>` with cwd `pkg_dir`.
///
/// `lakefile` is the package's config file path (e.g. `<pkg_dir>/lakefile.lean`),
/// used only to name the file in error messages — the subprocess itself never
/// reads it directly (lake finds it via `cwd = pkg_dir`).
pub fn translate_lakefile(
    pkg_dir: &Path,
    lakefile: &Path,
    lake: &LakeInvoker,
    out: &Path,
) -> Result<(), BuildError> {
    let mut cmd = Command::new(&lake.program);
    if let Some(tc) = &lake.toolchain {
        cmd.arg(format!("+{tc}"));
    }
    cmd.arg("translate-config").arg("toml").arg(out);
    cmd.current_dir(pkg_dir);
    let display = format!("{} translate-config toml", lake.program.display());
    let sub = |reason: String, stderr: String| BuildError::Subprocess {
        cmd: display.clone(),
        reason,
        stderr,
    };
    match subprocess::run_with_timeout(&mut cmd, lake.timeout) {
        Ok(finished) => {
            if finished.status.success() {
                Ok(())
            } else {
                Err(sub(
                    format!(
                        "failed for {} (exit status: {}); fix the lakefile or run \
                         `lake translate-config toml` there to reproduce",
                        lakefile.display(),
                        finished.status
                    ),
                    String::from_utf8_lossy(&finished.stderr).into_owned(),
                ))
            }
        }
        Err(RunError::Spawn(e)) => Err(sub(
            format!(
                "failed to start for {} ({e}); check that `lake` is installed and on PATH",
                lakefile.display()
            ),
            String::new(),
        )),
        Err(RunError::TimedOut(stderr)) => Err(sub(
            format!(
                "timed out after {}s translating {}; re-run, and if the machine is \
                 slow this timeout may need raising",
                lake.timeout.as_secs(),
                lakefile.display()
            ),
            String::from_utf8_lossy(&stderr).into_owned(),
        )),
        Err(RunError::Wait(e, stderr)) => Err(sub(
            format!(
                "wait failed for {}: {e}; this is unusual — re-run, and report a leanr \
                 bug if it persists",
                lakefile.display()
            ),
            String::from_utf8_lossy(&stderr).into_owned(),
        )),
    }
}

/// Load a package's config: native parse for `.toml`, bridge for `.lean`
/// (cache: `<cache_dir>/<blake3(lakefile)>.toml`).
pub fn load_config(
    pkg_dir: &Path,
    config_file: &Path,
    cache_dir: &Path,
    lake: &LakeInvoker,
) -> Result<ParsedConfig, BuildError> {
    let config_path = pkg_dir.join(config_file);
    let read = |p: &Path| {
        std::fs::read(p).map_err(|e| BuildError::Io {
            path: p.to_path_buf(),
            err: e.to_string(),
        })
    };
    if config_file.extension().and_then(|e| e.to_str()) == Some("toml") {
        let text = String::from_utf8_lossy(&read(&config_path)?).into_owned();
        return parse_lakefile_toml(&text, &config_path);
    }
    // Known limitation (design spec cache-key definition,
    // docs/superpowers/specs/2026-07-11-m2a-package-model-design.md): the
    // cache key is content-only — it does not fold in the toolchain. A
    // toolchain bump can therefore serve a stale translation until
    // `.leanr/config-cache` is cleared. Deliberate for M2a, where the
    // toolchain is pinned; revisit if the pin ever becomes movable.
    let hash = blake3::hash(&read(&config_path)?).to_hex();
    let cached = cache_dir.join(format!("{hash}.toml"));
    if !cached.is_file() {
        std::fs::create_dir_all(cache_dir).map_err(|e| BuildError::Io {
            path: cache_dir.to_path_buf(),
            err: e.to_string(),
        })?;
        let tmp = cache_dir.join(format!("{hash}.toml.tmp{}", std::process::id()));
        // Stale tmp left behind by a killed run; fine if it's not there.
        let _ = std::fs::remove_file(&tmp);
        // Absolute out path: lake runs with cwd = pkg_dir, not cache_dir.
        let tmp_abs = if tmp.is_absolute() {
            tmp.clone()
        } else {
            std::env::current_dir()
                .map_err(|e| BuildError::Io {
                    path: tmp.clone(),
                    err: e.to_string(),
                })?
                .join(&tmp)
        };
        translate_lakefile(pkg_dir, &config_path, lake, &tmp_abs)?;
        std::fs::rename(&tmp, &cached).map_err(|e| BuildError::Io {
            path: cached.clone(),
            err: e.to_string(),
        })?;
    }
    let text = String::from_utf8_lossy(&read(&cached)?).into_owned();
    // Errors point at the real lakefile, not the cache artifact.
    parse_lakefile_toml(&text, &config_path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};
    use std::time::Duration;

    fn fake(name: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures")
            .join(name)
    }

    fn pkg_with_lakefile_lean() -> tempfile::TempDir {
        let tmp = tempfile::TempDir::new().unwrap();
        std::fs::write(tmp.path().join("lakefile.lean"), "import Lake\n-- v1").unwrap();
        tmp
    }

    #[test]
    fn toml_config_is_parsed_natively_without_invoking_lake() {
        let tmp = tempfile::TempDir::new().unwrap();
        std::fs::write(tmp.path().join("lakefile.toml"), "name = \"native\"").unwrap();
        let lake = LakeInvoker {
            program: PathBuf::from("/definitely/not/a/binary"),
            ..LakeInvoker::default()
        };
        let parsed = load_config(
            tmp.path(),
            Path::new("lakefile.toml"),
            &tmp.path().join("cache"),
            &lake,
        )
        .unwrap();
        assert_eq!(parsed.config.name, "native");
    }

    #[test]
    fn lean_config_is_bridged_and_cached_by_content_hash() {
        let pkg = pkg_with_lakefile_lean();
        let cache = tempfile::TempDir::new().unwrap();
        let cwd_file = cache.path().join("cwd");
        std::env::set_var("FAKE_LAKE_CWD_FILE", &cwd_file);
        let lake = LakeInvoker {
            program: fake("fake-lake-ok.sh"),
            ..LakeInvoker::default()
        };

        let p1 = load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &lake).unwrap();
        assert_eq!(p1.config.name, "fake");
        // Ran in the package directory.
        let ran_in = std::fs::read_to_string(&cwd_file).unwrap();
        assert_eq!(
            Path::new(ran_in.trim()).canonicalize().unwrap(),
            pkg.path().canonicalize().unwrap()
        );
        // Exactly one cache entry, keyed by lakefile hash.
        let entries: Vec<_> = std::fs::read_dir(cache.path())
            .unwrap()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().map(|x| x == "toml").unwrap_or(false))
            .collect();
        assert_eq!(entries.len(), 1);

        // Cache hit: a now-broken lake is never invoked.
        let broken = LakeInvoker {
            program: PathBuf::from("/definitely/not/a/binary"),
            ..LakeInvoker::default()
        };
        let p2 = load_config(
            pkg.path(),
            Path::new("lakefile.lean"),
            cache.path(),
            &broken,
        )
        .unwrap();
        assert_eq!(p2.config.name, "fake");

        // Changing the lakefile misses the cache (and here fails: broken lake).
        std::fs::write(pkg.path().join("lakefile.lean"), "import Lake\n-- v2").unwrap();
        assert!(load_config(
            pkg.path(),
            Path::new("lakefile.lean"),
            cache.path(),
            &broken
        )
        .is_err());
    }

    #[test]
    fn bridge_failure_carries_lakes_stderr() {
        let pkg = pkg_with_lakefile_lean();
        let cache = tempfile::TempDir::new().unwrap();
        let lake = LakeInvoker {
            program: fake("fake-lake-fail.sh"),
            ..LakeInvoker::default()
        };
        let err =
            load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &lake).unwrap_err();
        assert!(err.to_string().contains("ill-formed configuration file"));
    }

    #[test]
    fn bridge_drains_large_stderr_without_waiting_out_the_timeout() {
        let pkg = pkg_with_lakefile_lean();
        let cache = tempfile::TempDir::new().unwrap();
        let lake = LakeInvoker {
            program: fake("fake-lake-big-stderr.sh"),
            // Generous timeout: if the stderr pipe deadlocks the poll loop,
            // the call will not return until this elapses.
            timeout: Duration::from_secs(30),
            ..LakeInvoker::default()
        };
        let start = std::time::Instant::now();
        let err =
            load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &lake).unwrap_err();
        let elapsed = start.elapsed();
        assert!(
            elapsed < Duration::from_secs(10),
            "expected prompt failure, took {elapsed:?}"
        );
        let msg = err.to_string();
        assert!(
            msg.contains("ill-formed configuration file"),
            "error should carry (partial) stderr, got: {msg}"
        );
        assert!(
            !msg.contains("timed out"),
            "this is a fast nonzero exit, not a timeout: {msg}"
        );
    }

    #[test]
    fn bridge_times_out_instead_of_hanging() {
        let pkg = pkg_with_lakefile_lean();
        let cache = tempfile::TempDir::new().unwrap();
        let lake = LakeInvoker {
            program: fake("fake-lake-hang.sh"),
            timeout: Duration::from_millis(300),
            ..LakeInvoker::default()
        };
        let start = std::time::Instant::now();
        let err =
            load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &lake).unwrap_err();
        assert!(start.elapsed() < Duration::from_secs(10));
        assert!(err.to_string().contains("timed out"));
    }
}
