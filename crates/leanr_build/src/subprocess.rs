//! Shared subprocess machinery for the `lake` bridge (bridge.rs) and the
//! `git` shell-outs (fetch.rs): deadline poll, stdout/stderr-drain threads
//! started at spawn time, and process-group SIGKILL on timeout. Extracted
//! here — see Task 6's `translate_lakefile`, whose hang-proofing this
//! generalizes — so the two callers don't duplicate the same machinery.
//! Not part of the crate's public API: see `mod subprocess;` in lib.rs.

use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

#[cfg(unix)]
use std::os::unix::process::CommandExt;

/// A subprocess that exited (successfully or not) before the deadline.
pub(crate) struct Finished {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

/// Everything that can go wrong *running* the subprocess (as opposed to
/// the subprocess's own nonzero exit, which is a normal `Finished`).
pub(crate) enum RunError {
    /// The process could not be spawned at all.
    Spawn(std::io::Error),
    /// Killed after exceeding the timeout; carries whatever stderr it
    /// managed to write before being killed.
    TimedOut(Vec<u8>),
    /// `try_wait` itself failed (rare); carries partial stderr too.
    Wait(std::io::Error, Vec<u8>),
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
        // `process_group(0)` below rather than a single process.
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

fn drain(
    pipe: Option<impl std::io::Read + Send + 'static>,
) -> Option<std::thread::JoinHandle<Vec<u8>>> {
    pipe.map(|mut p| {
        std::thread::spawn(move || {
            let mut buf = Vec::new();
            let _ = p.read_to_end(&mut buf);
            buf
        })
    })
}

fn join(thread: Option<std::thread::JoinHandle<Vec<u8>>>) -> Vec<u8> {
    thread.and_then(|t| t.join().ok()).unwrap_or_default()
}

/// Spawn `cmd` with stdin closed and stdout/stderr piped and drained from
/// the moment of spawn (so a child that writes more than a pipe buffer
/// can't block on the write end while nothing is reading yet — see
/// bridge.rs's `bridge_drains_large_stderr_without_waiting_out_the_timeout`
/// test for why this matters), killed process-group-wide if it hasn't
/// exited by `timeout`.
pub(crate) fn run_with_timeout(cmd: &mut Command, timeout: Duration) -> Result<Finished, RunError> {
    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    // Put the child in its own process group so a timeout kill takes down
    // its whole subtree, not just the immediate process. A lone
    // `child.kill()` would leave grandchildren running with a pipe's write
    // end still open, which hangs the reader-thread join indefinitely
    // instead of returning promptly.
    #[cfg(unix)]
    cmd.process_group(0);
    let mut child = cmd.spawn().map_err(RunError::Spawn)?;
    let stdout_thread = drain(child.stdout.take());
    let stderr_thread = drain(child.stderr.take());
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                return Ok(Finished {
                    status,
                    stdout: join(stdout_thread),
                    stderr: join(stderr_thread),
                });
            }
            Ok(None) => {
                if Instant::now() >= deadline {
                    kill_child_tree(&mut child);
                    return Err(RunError::TimedOut(join(stderr_thread)));
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => {
                kill_child_tree(&mut child);
                return Err(RunError::Wait(e, join(stderr_thread)));
            }
        }
    }
}
