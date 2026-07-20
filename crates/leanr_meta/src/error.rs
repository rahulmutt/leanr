//! Every failure `leanr_meta` can report.
//!
//! All of them are INCOMPLETENESS, never unsoundness: the worst case is
//! that elaboration which should have succeeded does not, because the
//! kernel independently re-checks whatever this crate produces (spec
//! § Error handling & edge cases). Same posture as
//! `KernelError::BankExhausted`.

/// A Meta-level failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetaError {
    /// A kernel-level operation failed (bank exhaustion, recursion cap).
    Kernel(leanr_kernel::KernelError),
    /// Decoded `.olean` data was not shaped as this crate expects.
    Olean(String),
    /// A metavariable-context invariant was violated: assigning an
    /// undeclared mvar, or reassigning an assigned one. Not a negative
    /// verdict — a caller bug.
    MVar(String),
    /// The deterministic step budget was exhausted (spec § Determinism).
    /// NOT a negative verdict — the question was never answered.
    StepBudgetExhausted,
    /// The synthesis-reentrancy depth budget was exhausted.
    DepthBudgetExhausted,
}

impl From<leanr_kernel::KernelError> for MetaError {
    fn from(e: leanr_kernel::KernelError) -> MetaError {
        MetaError::Kernel(e)
    }
}

#[cfg(test)]
mod tests {
    use super::MetaError;

    #[test]
    fn kernel_errors_convert() {
        let e: MetaError = leanr_kernel::KernelError::BankExhausted.into();
        assert_eq!(
            e,
            MetaError::Kernel(leanr_kernel::KernelError::BankExhausted)
        );
    }

    // A budget exhaustion must be distinguishable from a negative
    // verdict. This is a type-level guarantee (a distinct variant), but
    // the test pins the intent so a later refactor to `bool` fails here.
    #[test]
    fn budget_exhaustion_is_its_own_variant() {
        assert_ne!(
            MetaError::StepBudgetExhausted,
            MetaError::DepthBudgetExhausted
        );
    }
}
