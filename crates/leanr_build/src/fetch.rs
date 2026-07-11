//! Dependency materialization (spec §Architecture, component 4): ensure
//! `.lake/packages/<name>` is a git checkout at exactly the manifest rev.
//! Shells out to the `git` CLI (as lake itself does) with explicit
//! argument vectors and validated URLs; never overwrites local changes.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::error::BuildError;
use crate::manifest::{ManifestPackage, PackageSource};

/// Reject URLs that could be misparsed as git options or drive exotic
/// transports. Allowed: https/http/ssh/git/file schemes, scp-like
/// `user@host:path`, and local paths — none starting with `-`.
pub fn validate_git_url(url: &str) -> Result<(), String> {
    if url.is_empty() {
        return Err("empty git url".into());
    }
    if url.starts_with('-') {
        return Err(format!("git url starts with `-`: `{url}`"));
    }
    if let Some((scheme, _)) = url.split_once("://") {
        return match scheme {
            "https" | "http" | "ssh" | "git" | "file" => Ok(()),
            other => Err(format!("unsupported git url scheme `{other}` in `{url}`")),
        };
    }
    if url.contains("::") {
        return Err(format!("unsupported git transport in `{url}`"));
    }
    Ok(()) // scp-like or local path
}

fn git(args: &[&str], cwd: &Path) -> Result<String, BuildError> {
    let out = Command::new("git")
        .args(args)
        .current_dir(cwd)
        .output()
        .map_err(|e| BuildError::Subprocess {
            cmd: format!("git {}", args.join(" ")),
            reason: format!("failed to start: {e}"),
            stderr: String::new(),
        })?;
    if !out.status.success() {
        return Err(BuildError::Subprocess {
            cmd: format!("git {}", args.join(" ")),
            reason: format!("failed ({})", out.status),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        });
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn ensure_git(name: &str, url: &str, rev: &str, dest: &Path) -> Result<(), BuildError> {
    let ferr = |msg: String| BuildError::Fetch {
        name: name.to_string(),
        msg,
    };
    validate_git_url(url).map_err(ferr)?;
    if !dest.is_dir() {
        let parent = dest.parent().unwrap_or(Path::new("."));
        std::fs::create_dir_all(parent)
            .map_err(|e| ferr(format!("cannot create {}: {e}", parent.display())))?;
        git(
            &[
                "clone",
                "--",
                url,
                dest.to_str().ok_or_else(|| ferr("non-UTF-8 dest".into()))?,
            ],
            parent,
        )
        .map_err(|e| ferr(format!("clone failed: {e}")))?;
    }
    let head = git(&["rev-parse", "HEAD"], dest)?;
    if head == rev {
        return Ok(()); // already pinned; user files (even dirty) untouched
    }
    let dirty = !git(&["status", "--porcelain"], dest)?.is_empty();
    if dirty {
        return Err(ferr(format!(
            "{} has local modifications but is at {head}, not the manifest rev {rev}; \
             commit/stash or remove the directory",
            dest.display()
        )));
    }
    // Fetch only if the rev isn't already present locally.
    if git(
        &[
            "rev-parse",
            "--verify",
            "--quiet",
            &format!("{rev}^{{commit}}"),
        ],
        dest,
    )
    .is_err()
    {
        git(&["fetch", "origin"], dest).map_err(|e| ferr(format!("fetch failed: {e}")))?;
    }
    git(
        &[
            "-c",
            "advice.detachedHead=false",
            "checkout",
            "--detach",
            rev,
        ],
        dest,
    )
    .map_err(|e| ferr(format!("checkout of {rev} failed: {e}")))?;
    Ok(())
}

/// Materialize every manifest package (spec: fresh clones work with no
/// lake invocation). Concurrent across packages; deterministic first
/// error in package order.
pub fn materialize(
    packages: &[ManifestPackage],
    ws_root: &Path,
    packages_dir: &Path,
) -> Result<(), BuildError> {
    let results: Vec<Result<(), BuildError>> = std::thread::scope(|s| {
        let handles: Vec<_> = packages
            .iter()
            .map(|p| {
                s.spawn(move || match &p.source {
                    PackageSource::Git {
                        url,
                        rev,
                        sub_dir: _,
                    } => ensure_git(&p.name, url, rev, &packages_dir.join(&p.name)),
                    PackageSource::Path { dir } => {
                        let full: PathBuf = ws_root.join(dir);
                        if full.is_dir() {
                            Ok(())
                        } else {
                            Err(BuildError::Fetch {
                                name: p.name.clone(),
                                msg: format!("path dependency {} does not exist", full.display()),
                            })
                        }
                    }
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("fetch thread"))
            .collect()
    });
    results.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::{ManifestPackage, PackageSource};
    use std::path::{Path, PathBuf};

    fn sh(dir: &Path, cmd: &str) -> String {
        let out = std::process::Command::new("sh")
            .arg("-c")
            .arg(cmd)
            .current_dir(dir)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{cmd}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    }

    /// A local origin repo with two commits; returns (tempdir, rev1, rev2).
    fn origin() -> (tempfile::TempDir, String, String) {
        let tmp = tempfile::TempDir::new().unwrap();
        sh(tmp.path(), "git init -q -b main && git -c user.email=t@t -c user.name=t commit -q --allow-empty -m one");
        let r1 = sh(tmp.path(), "git rev-parse HEAD");
        sh(
            tmp.path(),
            "git -c user.email=t@t -c user.name=t commit -q --allow-empty -m two",
        );
        let r2 = sh(tmp.path(), "git rev-parse HEAD");
        (tmp, r1, r2)
    }

    fn git_pkg(name: &str, url: String, rev: String) -> ManifestPackage {
        ManifestPackage {
            name: name.into(),
            source: PackageSource::Git {
                url,
                rev,
                sub_dir: None,
            },
            config_file: PathBuf::from("lakefile.toml"),
            inherited: false,
        }
    }

    #[test]
    fn url_validation() {
        assert!(validate_git_url("https://github.com/x/y").is_ok());
        assert!(validate_git_url("ssh://git@github.com/x/y").is_ok());
        assert!(validate_git_url("git@github.com:x/y.git").is_ok());
        assert!(validate_git_url("/abs/path/repo").is_ok());
        assert!(validate_git_url("-oProxyCommand=evil").is_err());
        assert!(validate_git_url("ext::sh -c evil").is_err());
        assert!(validate_git_url("javascript://x").is_err());
        assert!(validate_git_url("").is_err());
    }

    #[test]
    fn clones_at_the_pinned_rev_not_head() {
        let (orig, r1, _r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let pkgs_dir = ws.path().join(".lake/packages");
        let pkg = git_pkg("dep", orig.path().to_str().unwrap().into(), r1.clone());
        materialize(&[pkg], ws.path(), &pkgs_dir).unwrap();
        assert_eq!(sh(&pkgs_dir.join("dep"), "git rev-parse HEAD"), r1);
    }

    #[test]
    fn existing_clean_checkout_at_wrong_rev_is_moved_to_the_pin() {
        let (orig, r1, r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let pkgs_dir = ws.path().join(".lake/packages");
        let url: String = orig.path().to_str().unwrap().into();
        materialize(&[git_pkg("dep", url.clone(), r2)], ws.path(), &pkgs_dir).unwrap();
        materialize(&[git_pkg("dep", url, r1.clone())], ws.path(), &pkgs_dir).unwrap();
        assert_eq!(sh(&pkgs_dir.join("dep"), "git rev-parse HEAD"), r1);
    }

    #[test]
    fn dirty_checkout_is_an_error_never_overwritten() {
        let (orig, r1, r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let pkgs_dir = ws.path().join(".lake/packages");
        let url: String = orig.path().to_str().unwrap().into();
        materialize(&[git_pkg("dep", url.clone(), r1)], ws.path(), &pkgs_dir).unwrap();
        std::fs::write(pkgs_dir.join("dep/local-work.txt"), "precious").unwrap();
        let err = materialize(&[git_pkg("dep", url, r2)], ws.path(), &pkgs_dir).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("dep") && msg.contains("local"), "got: {msg}");
        // The precious file survived.
        assert!(pkgs_dir.join("dep/local-work.txt").exists());
    }

    #[test]
    fn matching_rev_is_a_no_op_even_when_dirty() {
        let (orig, r1, _r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let pkgs_dir = ws.path().join(".lake/packages");
        let url: String = orig.path().to_str().unwrap().into();
        materialize(
            &[git_pkg("dep", url.clone(), r1.clone())],
            ws.path(),
            &pkgs_dir,
        )
        .unwrap();
        std::fs::write(pkgs_dir.join("dep/scratch.txt"), "wip").unwrap();
        // Already at the right rev: leave the user's files alone.
        materialize(&[git_pkg("dep", url, r1)], ws.path(), &pkgs_dir).unwrap();
        assert!(pkgs_dir.join("dep/scratch.txt").exists());
    }

    #[test]
    fn missing_path_dependency_is_a_clear_error() {
        let ws = tempfile::TempDir::new().unwrap();
        let pkg = ManifestPackage {
            name: "local".into(),
            source: PackageSource::Path {
                dir: PathBuf::from("../nope"),
            },
            config_file: PathBuf::from("lakefile.toml"),
            inherited: false,
        };
        let err = materialize(&[pkg], ws.path(), &ws.path().join("pkgs")).unwrap_err();
        assert!(err.to_string().contains("local"));
    }

    #[test]
    fn unknown_rev_reports_the_package() {
        let (orig, _r1, _r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let bad = "0123456789abcdef0123456789abcdef01234567".to_string();
        let pkg = git_pkg("dep", orig.path().to_str().unwrap().into(), bad);
        let err = materialize(&[pkg], ws.path(), &ws.path().join("pkgs")).unwrap_err();
        assert!(err.to_string().contains("dep"));
    }
}
