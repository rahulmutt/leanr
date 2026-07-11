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
use std::process::{Child, Command, Stdio};
use std::time::Duration;

#[cfg(unix)]
use std::os::unix::process::CommandExt;

use crate::config::{parse_lakefile_toml, ParsedConfig};
use crate::error::BuildError;

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

/// Kill the child and its whole process-group subtree, then reap it.
/// Plain `Child::kill` only signals the immediate process; if it has
/// spawned children of its own, they keep running and keep any inherited
/// pipe (e.g. stderr) open, which would otherwise hang a reader thread
/// waiting on that pipe to reach EOF.
fn kill_child_tree(child: &mut Child) {
    #[cfg(unix)]
    {
        // SAFETY: signaling a process group by pid is a plain libc call;
        // negating the pid targets the group we created via
        // `process_group(0)` above rather than a single process.
        unsafe {
            libc::kill(-(child.id() as libc::pid_t), libc::SIGKILL);
        }
    }
    #[cfg(not(unix))]
    {
        let _ = child.kill();
    }
    let _ = child.wait();
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
    cmd.stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped());
    // Put the child in its own process group so a timeout kill takes down
    // its whole subtree (lake may itself spawn `lean`/etc.), not just the
    // immediate process. A lone `child.kill()` would leave grandchildren
    // running with the stderr pipe's write end still open, which hangs the
    // reader-thread join below indefinitely instead of returning promptly.
    #[cfg(unix)]
    cmd.process_group(0);
    let display = format!("{} translate-config toml", lake.program.display());
    let sub = |reason: String, stderr: String| BuildError::Subprocess {
        cmd: display.clone(),
        reason,
        stderr,
    };
    let mut child = cmd.spawn().map_err(|e| {
        sub(
            format!(
                "failed to start for {} ({e}); check that `lake` is installed and on PATH",
                lakefile.display()
            ),
            String::new(),
        )
    })?;
    // Take stderr immediately and drain it on a dedicated thread. If we only
    // read it after try_wait observes exit, a child that writes >64KB to
    // stderr blocks on the pipe write and never exits — burning the whole
    // timeout and then reporting "timed out" with an empty stderr, losing
    // the real diagnostic. stdout stays `Stdio::null()`, so it needs no
    // equivalent drain.
    let stderr_pipe = child.stderr.take();
    let stderr_thread = stderr_pipe.map(|mut s| {
        std::thread::spawn(move || {
            use std::io::Read;
            let mut buf = Vec::new();
            let _ = s.read_to_end(&mut buf);
            buf
        })
    });
    let join_stderr = |thread: Option<std::thread::JoinHandle<Vec<u8>>>| -> String {
        thread
            .and_then(|t| t.join().ok())
            .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
            .unwrap_or_default()
    };
    let deadline = std::time::Instant::now() + lake.timeout;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let stderr = join_stderr(stderr_thread);
                if status.success() {
                    return Ok(());
                }
                return Err(sub(
                    format!(
                        "failed for {} (exit status: {status}); fix the lakefile or run \
                         `lake translate-config toml` there to reproduce",
                        lakefile.display()
                    ),
                    stderr,
                ));
            }
            Ok(None) => {
                if std::time::Instant::now() >= deadline {
                    kill_child_tree(&mut child);
                    let stderr = join_stderr(stderr_thread);
                    return Err(sub(
                        format!(
                            "timed out after {}s translating {}; re-run, and if the machine is \
                             slow this timeout may need raising",
                            lake.timeout.as_secs(),
                            lakefile.display()
                        ),
                        stderr,
                    ));
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => {
                kill_child_tree(&mut child);
                let stderr = join_stderr(stderr_thread);
                return Err(sub(
                    format!(
                        "wait failed for {}: {e}; this is unusual — re-run, and report a leanr \
                         bug if it persists",
                        lakefile.display()
                    ),
                    stderr,
                ));
            }
        }
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
