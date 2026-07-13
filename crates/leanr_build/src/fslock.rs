//! Advisory exclusive file lock shared by the git-source cache (`fetch`)
//! and the artifact CAS (`cache`). Unix `flock`; the `cfg(not(unix))`
//! fallback creates the lock file without holding a lock (same cfg split
//! as `subprocess.rs`'s process-group kill — callers still double-check
//! the guarded invariant after acquisition).

use std::path::Path;

/// Take an advisory exclusive lock on `path` (created if absent),
/// released when the returned file is dropped.
pub(crate) fn lock_exclusive(path: &Path) -> std::io::Result<std::fs::File> {
    let f = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(path)?;
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        // SAFETY: flock on a fd we own; blocks until the lock is granted.
        if unsafe { libc::flock(f.as_raw_fd(), libc::LOCK_EX) } != 0 {
            return Err(std::io::Error::last_os_error());
        }
    }
    Ok(f)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lock_is_created_and_reacquirable_after_drop() {
        let tmp = tempfile::TempDir::new().unwrap();
        let p = tmp.path().join("x.lock");
        {
            let _g = lock_exclusive(&p).unwrap();
            assert!(p.exists());
        }
        // Dropped — a second acquisition must not deadlock.
        let _g2 = lock_exclusive(&p).unwrap();
    }
}
