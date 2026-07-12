//! Recursive content-Merkle fingerprint (M2c spec §Fingerprint). A
//! module's key folds in its source, semantic setup inputs, toolchain,
//! leanr's own version, its owning package's provenance (git rev, or
//! declared custom inputs for root/path deps), and the *fingerprints* of
//! its direct imports — so one fixed-size hash captures the whole
//! transitive input closure. Pure content (no mtimes): reproducible
//! across machines and worktrees, which is what a shared CAS needs.

/// Ambient inputs shared by every module in a build.
pub struct FingerprintEnv {
    /// Stable leanr release/commit id (never a per-build nonce) — an
    /// upgrade invalidates the whole cache (spec §Scope decisions).
    pub leanr_version: String,
    /// The pinned `lean-toolchain` string.
    pub toolchain_id: String,
    /// Target platform tag (arch-os).
    pub platform: String,
}

/// Lowercase 64-char blake3 hex.
pub type Fingerprint = String;

/// Domain-separated, length-prefixed field write: `blake3` over a field
/// stream where each field is `len(u64-LE) || bytes`, so no two distinct
/// component tuples can collide by concatenation ambiguity.
#[allow(dead_code)]
fn put(h: &mut blake3::Hasher, field: &[u8]) {
    h.update(&(field.len() as u64).to_le_bytes());
    h.update(field);
}

#[allow(dead_code)]
pub(crate) fn hash_module(
    env: &FingerprintEnv,
    provenance: &[u8],
    source: &[u8],
    setup_inputs: &[u8],
    import_fps: &[String],
) -> Fingerprint {
    let mut h = blake3::Hasher::new();
    put(&mut h, b"leanr-m2c-fingerprint-v1"); // DOMAIN_TAG + FP_SCHEMA_VERSION
    put(&mut h, env.leanr_version.as_bytes());
    put(&mut h, env.toolchain_id.as_bytes());
    put(&mut h, env.platform.as_bytes());
    put(&mut h, provenance);
    put(&mut h, source);
    put(&mut h, setup_inputs);
    put(&mut h, &(import_fps.len() as u64).to_le_bytes());
    for imp in import_fps {
        put(&mut h, imp.as_bytes());
    }
    h.finalize().to_hex().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn env() -> FingerprintEnv {
        FingerprintEnv {
            leanr_version: "0.1.0".into(),
            toolchain_id: "leanprover/lean4:v4.32.0-rc1".into(),
            platform: "x86_64-linux".into(),
        }
    }

    #[test]
    fn deterministic_and_64_hex() {
        let a = hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}ff".into()]);
        let b = hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}ff".into()]);
        assert_eq!(a, b);
        assert_eq!(a.len(), 64);
        assert!(a.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn every_component_changes_the_hash() {
        let base = hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}ff".into()]);
        let mut e2 = env();
        e2.leanr_version = "0.2.0".into();
        assert_ne!(base, hash_module(&e2, b"p", b"src", b"{}", &["A\u{0}ff".into()]));
        let mut e3 = env();
        e3.toolchain_id = "other".into();
        assert_ne!(base, hash_module(&e3, b"p", b"src", b"{}", &["A\u{0}ff".into()]));
        assert_ne!(base, hash_module(&env(), b"q", b"src", b"{}", &["A\u{0}ff".into()]));
        assert_ne!(base, hash_module(&env(), b"p", b"src2", b"{}", &["A\u{0}ff".into()]));
        assert_ne!(base, hash_module(&env(), b"p", b"src", b"{\"x\":1}", &["A\u{0}ff".into()]));
        assert_ne!(base, hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}00".into()]));
    }

    #[test]
    fn length_prefixing_blocks_boundary_collisions() {
        // ("ab","c") must not equal ("a","bc").
        let x = hash_module(&env(), b"ab", b"c", b"{}", &[]);
        let y = hash_module(&env(), b"a", b"bc", b"{}", &[]);
        assert_ne!(x, y);
    }
}
