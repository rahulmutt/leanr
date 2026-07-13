//! Recursive content-Merkle fingerprint (M2c spec §Fingerprint). A
//! module's key folds in its source, semantic setup inputs, toolchain,
//! leanr's own version, its owning package's provenance (git rev, or
//! declared custom inputs for root/path deps), and the *fingerprints* of
//! its direct imports — so one fixed-size hash captures the whole
//! transitive input closure. Pure content (no mtimes): reproducible
//! across machines and worktrees, which is what a shared CAS needs.

use crate::graph::{ModuleId, ModuleInfo};
use crate::setup::Layout;
use crate::{ResolvedPackage, Workspace};

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
fn put(h: &mut blake3::Hasher, field: &[u8]) {
    h.update(&(field.len() as u64).to_le_bytes());
    h.update(field);
}

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

/// Owning-package provenance for a module's fingerprint.
/// - git dep (rev = Some): the pinned rev captures the entire immutable
///   rev-keyed checkout (incl. committed non-`.lean` compile inputs like
///   ProofWidgets' JS) by reference — sound because `fetch::verify_checkout`
///   guarantees rev == checkout bytes.
/// - root / path dep (rev = None): the serialized declared custom inputs
///   (`input_file`/`input_dir`); a lean_lib module's compile otherwise
///   reads only its `.lean` source + imports, both already in the key.
fn owner_provenance(pkg: &ResolvedPackage) -> Vec<u8> {
    match &pkg.rev {
        Some(rev) => {
            let mut v = b"rev\0".to_vec();
            v.extend_from_slice(rev.as_bytes());
            v
        }
        None => {
            let decls = serde_json::to_vec(&(&pkg.config.input_file, &pkg.config.input_dir))
                .unwrap_or_default();
            let mut v = b"inputs\0".to_vec();
            v.extend_from_slice(&decls);
            v
        }
    }
}

/// Canonical semantic setup inputs (spec §Fingerprint): options,
/// isModule, plugins, dynlibs — NOT the machine-specific importArts paths
/// (import identity enters via the recursive import fps instead).
fn setup_inputs_bytes(ws: &Workspace, layout: &Layout, id: ModuleId) -> Vec<u8> {
    let s = crate::setup::module_setup(ws, layout, id);
    serde_json::to_vec(&serde_json::json!({
        "options": s.options,
        "isModule": s.is_module,
        "plugins": s.plugins,
        "dynlibs": s.dynlibs,
    }))
    .expect("setup inputs serialize")
}

pub fn fingerprint_all(
    ws: &Workspace,
    env: &FingerprintEnv,
) -> Result<Vec<Fingerprint>, crate::BuildError> {
    let layout = Layout::new(&ws.root_dir);
    let n = ws.graph.modules.len();
    let mut fps: Vec<Option<Fingerprint>> = vec![None; n];
    // Provenance per package, computed once.
    let provenance_of = |m: &ModuleInfo| -> Vec<u8> {
        let pkg = std::iter::once(&ws.root)
            .chain(ws.deps.iter())
            .find(|p| p.name == m.package);
        pkg.map(owner_provenance)
            .expect("module's package must be root or a declared dep")
    };
    // `waves` is a topological layering: every dep of a wave-k module is
    // in a wave < k, so its fp is already computed.
    for wave in &ws.waves {
        for &id in wave {
            let i = id.0 as usize;
            let m = &ws.graph.modules[i];
            let source = std::fs::read(&m.file).map_err(|e| crate::BuildError::Io {
                path: m.file.clone(),
                err: e.to_string(),
            })?;
            let mut import_fps: Vec<String> = m
                .deps
                .iter()
                .map(|d| {
                    let dm = &ws.graph.modules[d.0 as usize];
                    let fp = fps[d.0 as usize]
                        .as_ref()
                        .expect("import fingerprinted before dependent (topo waves)");
                    format!("{}\u{0}{}", dm.name, fp)
                })
                .collect();
            import_fps.sort();
            let fp = hash_module(
                env,
                &provenance_of(m),
                &source,
                &setup_inputs_bytes(ws, &layout, id),
                &import_fps,
            );
            fps[i] = Some(fp);
        }
    }
    Ok(fps
        .into_iter()
        .map(|f| f.expect("every module in some wave"))
        .collect())
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
        assert_ne!(
            base,
            hash_module(&e2, b"p", b"src", b"{}", &["A\u{0}ff".into()])
        );
        let mut e3 = env();
        e3.toolchain_id = "other".into();
        assert_ne!(
            base,
            hash_module(&e3, b"p", b"src", b"{}", &["A\u{0}ff".into()])
        );
        assert_ne!(
            base,
            hash_module(&env(), b"q", b"src", b"{}", &["A\u{0}ff".into()])
        );
        assert_ne!(
            base,
            hash_module(&env(), b"p", b"src2", b"{}", &["A\u{0}ff".into()])
        );
        assert_ne!(
            base,
            hash_module(&env(), b"p", b"src", b"{\"x\":1}", &["A\u{0}ff".into()])
        );
        assert_ne!(
            base,
            hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}00".into()])
        );
    }

    #[test]
    fn length_prefixing_blocks_boundary_collisions() {
        // ("ab","c") must not equal ("a","bc").
        let x = hash_module(&env(), b"ab", b"c", b"{}", &[]);
        let y = hash_module(&env(), b"a", b"bc", b"{}", &[]);
        assert_ne!(x, y);
    }

    use crate::testws;

    #[test]
    fn leaf_and_dependent_get_distinct_fingerprints() {
        let t = testws::synthetic();
        let fps = fingerprint_all(&t.ws, &env()).unwrap();
        assert_eq!(fps.len(), t.ws.graph.modules.len());
        assert!(fps.iter().all(|f| f.len() == 64));
        // App imports App.Sub — distinct sources ⇒ distinct fingerprints.
        assert_ne!(fps[0], fps[1]);
    }

    #[test]
    fn changing_an_import_changes_the_dependent() {
        // App -> App.Sub. Editing App.Sub's source must change App's fp
        // (Merkle recursion), not just App.Sub's.
        let t1 = testws::synthetic();
        let before = fingerprint_all(&t1.ws, &env()).unwrap();
        let app = t1
            .ws
            .graph
            .id_of(&crate::modules::ModuleName::parse("App").unwrap())
            .unwrap();
        let sub = t1
            .ws
            .graph
            .id_of(&crate::modules::ModuleName::parse("App.Sub").unwrap())
            .unwrap();
        // Rewrite App.Sub.lean in the synthetic workspace, re-resolve.
        std::fs::write(&t1.ws.graph.modules[sub.0 as usize].file, "-- edited\n").unwrap();
        let after = fingerprint_all(&t1.ws, &env()).unwrap();
        assert_ne!(
            before[sub.0 as usize], after[sub.0 as usize],
            "leaf fp changes"
        );
        assert_ne!(
            before[app.0 as usize], after[app.0 as usize],
            "dependent fp changes (Merkle)"
        );
    }

    #[test]
    fn declared_input_file_enters_root_provenance() {
        let t = testws::synthetic();
        let base = fingerprint_all(&t.ws, &env()).unwrap();
        let mut t2 = testws::synthetic();
        t2.ws.root.config.input_file = Some(vec![toml::Value::String("widget.js".into())]);
        let changed = fingerprint_all(&t2.ws, &env()).unwrap();
        // Root package's modules must re-fingerprint when its declared
        // custom inputs change.
        assert_ne!(base[0], changed[0]);
    }
}
