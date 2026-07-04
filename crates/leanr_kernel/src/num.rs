use std::fmt;

/// Lean `Nat`: arbitrary precision by language semantics (`.olean` files
/// really contain GMP-backed bignums for literals >= 2^63).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Nat(pub num_bigint::BigUint);

impl From<u64> for Nat {
    fn from(v: u64) -> Nat {
        Nat(num_bigint::BigUint::from(v))
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Lean `Int` (only reachable through `Expr` metadata in M1a).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Int(pub num_bigint::BigInt);

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
