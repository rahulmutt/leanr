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

/// Kernel `Nat` arithmetic. Every operation is total (no panic on any
/// input): `sub` truncates at zero, `div`/`mod` follow Lean's `x/0 = 0`
/// and `x%0 = x`, and bit/shift ops never overflow the process. These
/// back `type_checker::reduce_nat` (oracle: src/kernel/type_checker.cpp
/// 609-638), which folds binary/unary `Nat.*` builtins on literals.
impl Nat {
    /// `true` iff this is `0` (oracle: `nat::is_zero`). `BigUint::bits()`
    /// is `0` exactly for zero, and never allocates.
    pub fn is_zero(&self) -> bool {
        self.0.bits() == 0
    }

    /// This value as a machine `usize`, or `None` if it does not fit
    /// (oracle: `nat::is_small` / `get_small_value`, util/nat.h). Never
    /// truncates — used to bound shift/pow amounts against untrusted
    /// bignums without panicking.
    pub fn to_usize(&self) -> Option<usize> {
        let digits = self.0.to_u64_digits();
        if digits.len() > 1 {
            return None;
        }
        let v = digits.first().copied().unwrap_or(0);
        usize::try_from(v).ok()
    }

    /// oracle: `nat_add`.
    pub fn add(&self, other: &Nat) -> Nat {
        Nat(&self.0 + &other.0)
    }

    /// oracle: `nat_sub` — truncated subtraction (`a - b = 0` when
    /// `a < b`); `BigUint`'s `-` would panic on underflow.
    pub fn sub(&self, other: &Nat) -> Nat {
        if self.0 >= other.0 {
            Nat(&self.0 - &other.0)
        } else {
            Nat::from(0)
        }
    }

    /// oracle: `nat_mul`.
    pub fn mul(&self, other: &Nat) -> Nat {
        Nat(&self.0 * &other.0)
    }

    /// oracle: `nat_div` — Lean's `x / 0 = 0`; `BigUint`'s `/` panics on
    /// a zero divisor.
    pub fn div(&self, other: &Nat) -> Nat {
        if other.is_zero() {
            Nat::from(0)
        } else {
            Nat(&self.0 / &other.0)
        }
    }

    /// oracle: `nat_mod` — Lean's `x % 0 = x`; `BigUint`'s `%` panics on
    /// a zero divisor.
    pub fn modulo(&self, other: &Nat) -> Nat {
        if other.is_zero() {
            self.clone()
        } else {
            Nat(&self.0 % &other.0)
        }
    }

    /// oracle: `nat_gcd`. Euclid's algorithm (`gcd(a,0) = a`).
    pub fn gcd(&self, other: &Nat) -> Nat {
        let mut a = self.0.clone();
        let mut b = other.0.clone();
        while b.bits() != 0 {
            let r = &a % &b;
            a = b;
            b = r;
        }
        Nat(a)
    }

    /// oracle: `nat_pow`. `exp` is bounded by the caller (`reduce_pow`'s
    /// `ReducePowMaxExp = 1<<24` guard, type_checker.cpp:586), so it
    /// always fits `u32`.
    pub fn pow(&self, exp: u32) -> Nat {
        Nat(self.0.pow(exp))
    }

    /// oracle: `nat_eq` (used by `Nat.beq`).
    pub fn beq(&self, other: &Nat) -> bool {
        self.0 == other.0
    }

    /// oracle: `nat_le` (used by `Nat.ble`).
    pub fn ble(&self, other: &Nat) -> bool {
        self.0 <= other.0
    }

    /// oracle: `nat_land`.
    pub fn land(&self, other: &Nat) -> Nat {
        Nat(&self.0 & &other.0)
    }

    /// oracle: `nat_lor`.
    pub fn lor(&self, other: &Nat) -> Nat {
        Nat(&self.0 | &other.0)
    }

    /// oracle: `nat_lxor`.
    pub fn lxor(&self, other: &Nat) -> Nat {
        Nat(&self.0 ^ &other.0)
    }

    /// oracle: `lean_nat_shiftl`. `shift` is already narrowed to `usize`
    /// by the caller (a shift amount that does not fit `usize` cannot be
    /// materialized without unbounded memory; `reduce_nat` leaves such an
    /// application un-reduced instead of attempting it).
    pub fn shiftl(&self, shift: usize) -> Nat {
        Nat(&self.0 << shift)
    }

    /// oracle: `lean_nat_shiftr`. A shift wider than the value's bit
    /// length yields `0` (and `BigUint`'s `>>` does so cheaply).
    pub fn shiftr(&self, shift: usize) -> Nat {
        Nat(&self.0 >> shift)
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
