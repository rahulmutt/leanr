use crate::KernelError;

/// Depth cap for guarded recursion. Far above anything real code
/// produces (the Task 16 stdlib sweep is the arbiter); low enough that
/// adversarial inputs terminate promptly. Hitting it rejects the input
/// — incompleteness, never unsoundness.
pub const MAX_REC_DEPTH: u32 = 1_000_000;

/// Keep at least this much stack headroom; grow in these increments.
/// Values follow rustc's own use of stacker (compiler/rustc_data_structures).
const RED_ZONE: usize = 128 * 1024;
const STACK_CHUNK: usize = 4 * 1024 * 1024;

/// The one sanctioned recursion pattern in this crate (see lib.rs):
/// every recursive kernel function enters frames through `enter`, which
/// (a) counts depth and errors out at `MAX_REC_DEPTH`, and (b) grows
/// the stack segment via `stacker` so the OS stack can never overflow
/// beneath the cap.
#[derive(Debug, Default)]
pub struct RecGuard {
    depth: u32,
}

impl RecGuard {
    pub fn new() -> RecGuard {
        RecGuard { depth: 0 }
    }

    pub fn enter<R>(
        &mut self,
        f: impl FnOnce(&mut RecGuard) -> Result<R, KernelError>,
    ) -> Result<R, KernelError> {
        if self.depth >= MAX_REC_DEPTH {
            return Err(KernelError::DeepRecursion);
        }
        self.depth += 1;
        let r = stacker::maybe_grow(RED_ZONE, STACK_CHUNK, || f(self));
        self.depth -= 1;
        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A recursive function that would blow the OS stack unguarded:
    /// each frame holds a 4 KiB array so 1e5 frames ≈ 400 MiB of stack.
    fn deep(g: &mut RecGuard, n: u64) -> Result<u64, KernelError> {
        let pad = [0u8; 4096];
        std::hint::black_box(&pad);
        if n == 0 {
            return Ok(0);
        }
        g.enter(|g| Ok(deep(g, n - 1)? + 1))
    }

    #[test]
    fn survives_depth_far_beyond_os_stack() {
        let mut g = RecGuard::new();
        assert_eq!(deep(&mut g, 100_000).unwrap(), 100_000);
    }

    #[test]
    fn cap_returns_error_not_panic() {
        let mut g = RecGuard::new();
        fn forever(g: &mut RecGuard) -> Result<(), KernelError> {
            g.enter(forever)
        }
        assert_eq!(forever(&mut g), Err(KernelError::DeepRecursion));
    }

    #[test]
    fn depth_unwinds_after_success() {
        let mut g = RecGuard::new();
        deep(&mut g, 1000).unwrap();
        // Guard is reusable: a second run from depth 0 succeeds.
        assert_eq!(deep(&mut g, 1000).unwrap(), 1000);
    }
}
