//! Content-addressed artifact store (M2c spec §Layout, §Architecture
//! `cache`). Two levels: a module manifest keyed by fingerprint names the
//! artifact family; each member points at a content blob keyed by the
//! blake3 of its own bytes. Immutable, sharded, flock-guarded, atomic
//! writes. Lives at `$XDG_CACHE_HOME/leanr/cache/` alongside M2b's
//! `src/` and `config-cache/`.

use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

pub struct Cache {
    root: PathBuf,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct ArtifactEntry {
    pub name: String,
    pub blob: String,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct Manifest {
    pub artifacts: Vec<ArtifactEntry>,
}

fn shard(hex: &str) -> &str {
    hex.get(..2).unwrap_or(hex)
}

/// Write `bytes` to `path` atomically (temp sibling + rename), flock-
/// guarded on `path.lock`, leaving the file read-only. A concurrent
/// writer of identical content races safely (rename is atomic).
fn write_atomic_readonly(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let parent = path.parent().expect("cache path has a parent");
    std::fs::create_dir_all(parent)?;
    let lock = path.with_extension("lock");
    let _g = crate::fslock::lock_exclusive(&lock)?;
    if path.exists() {
        return Ok(()); // content-addressed: already present, identical bytes.
    }
    let tmp = path.with_extension("tmp");
    std::fs::write(&tmp, bytes)?;
    let mut perms = std::fs::metadata(&tmp)?.permissions();
    perms.set_readonly(true);
    std::fs::set_permissions(&tmp, perms)?;
    std::fs::rename(&tmp, path)?;
    Ok(())
}

impl Cache {
    pub fn new(cache_root: &Path) -> Cache {
        Cache {
            root: cache_root.join("cache"),
        }
    }

    pub fn blob_path(&self, hex: &str) -> PathBuf {
        self.root.join("blobs").join(shard(hex)).join(hex)
    }

    pub fn store_blob(&self, bytes: &[u8]) -> std::io::Result<String> {
        let hex = blake3::hash(bytes).to_hex().to_string();
        let path = self.blob_path(&hex);
        write_atomic_readonly(&path, bytes)?;
        Ok(hex)
    }

    pub fn manifest_path(&self, fp: &str) -> PathBuf {
        self.root
            .join("modules")
            .join(shard(fp))
            .join(format!("{fp}.json"))
    }

    pub fn insert(&self, fp: &str, artifacts: &[PathBuf]) -> std::io::Result<Manifest> {
        let mut entries = Vec::with_capacity(artifacts.len());
        for art in artifacts {
            let bytes = std::fs::read(art)?;
            let blob = self.store_blob(&bytes)?;
            let name = art
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_default();
            entries.push(ArtifactEntry { name, blob });
        }
        let manifest = Manifest { artifacts: entries };
        let json = serde_json::to_vec(&manifest).expect("manifest serializes");
        write_atomic_readonly(&self.manifest_path(fp), &json)?;
        Ok(manifest)
    }

    pub fn lookup(&self, fp: &str) -> std::io::Result<Option<Manifest>> {
        let path = self.manifest_path(fp);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e),
        };
        // Untrusted-bytes discipline: a malformed manifest is a miss, never a panic.
        let manifest: Manifest = match serde_json::from_slice(&bytes) {
            Ok(m) => m,
            Err(_) => return Ok(None),
        };
        // Guard against a well-formed-JSON-but-malformed `blob` field (e.g. a
        // hex string that's too short, or whose byte offset 2 isn't a char
        // boundary). `shard()` is total, so a malformed blob simply maps to
        // a path that won't exist, and `exists()` catches it here.
        if manifest
            .artifacts
            .iter()
            .any(|a| !self.blob_path(&a.blob).exists())
        {
            return Ok(None);
        }
        Ok(Some(manifest))
    }

    pub fn materialize(&self, manifest: &Manifest, dests: &[PathBuf]) -> std::io::Result<()> {
        assert_eq!(
            manifest.artifacts.len(),
            dests.len(),
            "manifest/dest arity mismatch — caller must pass layout.artifact_paths order"
        );
        for (entry, dest) in manifest.artifacts.iter().zip(dests) {
            let blob = self.blob_path(&entry.blob);
            if let Some(parent) = dest.parent() {
                std::fs::create_dir_all(parent)?;
            }
            // Overwrite: a prior materialization left a read-only hardlink.
            if dest.exists() {
                std::fs::remove_file(dest)?;
            }
            match std::fs::hard_link(&blob, dest) {
                Ok(()) => {}
                // Cross-device (EXDEV) or other link failure: copy instead.
                Err(_) => {
                    std::fs::copy(&blob, dest)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cache() -> (tempfile::TempDir, Cache) {
        let tmp = tempfile::TempDir::new().unwrap();
        let c = Cache::new(tmp.path());
        (tmp, c)
    }

    #[test]
    fn store_blob_is_content_addressed_and_idempotent() {
        let (_t, c) = cache();
        let h1 = c.store_blob(b"hello olean").unwrap();
        let h2 = c.store_blob(b"hello olean").unwrap();
        assert_eq!(h1, h2);
        assert_eq!(h1, blake3::hash(b"hello olean").to_hex().to_string());
        assert_eq!(std::fs::read(c.blob_path(&h1)).unwrap(), b"hello olean");
    }

    #[test]
    fn blob_is_sharded_and_read_only() {
        let (_t, c) = cache();
        let h = c.store_blob(b"x").unwrap();
        let p = c.blob_path(&h);
        assert!(p.parent().unwrap().ends_with(&h[..2]));
        assert!(std::fs::metadata(&p).unwrap().permissions().readonly());
    }

    fn write(p: &Path, b: &[u8]) {
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, b).unwrap();
    }

    #[test]
    fn insert_then_lookup_roundtrips() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        let b = t.path().join("A.ilean");
        write(&a, b"olean-bytes");
        write(&b, b"ilean-bytes");
        let m = c.insert("deadbeef", &[a.clone(), b.clone()]).unwrap();
        assert_eq!(m.artifacts.len(), 2);
        assert_eq!(m.artifacts[0].name, "A.olean");
        let got = c.lookup("deadbeef").unwrap().unwrap();
        assert_eq!(got.artifacts, m.artifacts);
    }

    #[test]
    fn lookup_miss_is_none() {
        let (_t, c) = cache();
        assert!(c.lookup("nope").unwrap().is_none());
    }

    #[test]
    fn lookup_with_a_missing_blob_is_a_self_healing_miss() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        write(&a, b"olean-bytes");
        let m = c.insert("cafe", &[a]).unwrap();
        std::fs::remove_file(c.blob_path(&m.artifacts[0].blob)).unwrap();
        assert!(c.lookup("cafe").unwrap().is_none());
    }

    #[test]
    fn corrupt_manifest_json_is_a_miss_not_a_panic() {
        let (_t, c) = cache();
        let p = c.manifest_path("beef");
        write(&p, b"{ this is not json");
        assert!(c.lookup("beef").unwrap().is_none());
    }

    #[test]
    fn lookup_with_malformed_blob_hex_is_a_miss_not_a_panic() {
        let (_t, c) = cache();
        let p = c.manifest_path("shortblob");
        write(&p, br#"{"artifacts":[{"name":"A","blob":"x"}]}"#);
        assert!(c.lookup("shortblob").unwrap().is_none());
    }

    #[test]
    fn lookup_with_multibyte_blob_hex_is_a_miss_not_a_panic() {
        let (_t, c) = cache();
        let p = c.manifest_path("beef");
        // Valid JSON, but blob is a 3-byte single char straddling byte offset 2.
        // Byte-string literals can't hold non-ASCII directly, so use a \u
        // JSON escape in a normal `str` literal (serde_json decodes it to
        // the 3-byte UTF-8 char '中') and convert to bytes for `write`.
        let json = r#"{"artifacts":[{"name":"A.olean","blob":"中"}]}"#;
        write(&p, json.as_bytes());
        assert!(c.lookup("beef").unwrap().is_none());
    }

    #[test]
    fn materialize_recreates_every_artifact() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        let b = t.path().join("A.ilean");
        write(&a, b"olean-bytes");
        write(&b, b"ilean-bytes");
        let m = c.insert("d00d", &[a.clone(), b.clone()]).unwrap();
        let out = t.path().join("proj");
        let da = out.join("A.olean");
        let db = out.join("A.ilean");
        c.materialize(&m, &[da.clone(), db.clone()]).unwrap();
        assert_eq!(std::fs::read(&da).unwrap(), b"olean-bytes");
        assert_eq!(std::fs::read(&db).unwrap(), b"ilean-bytes");
    }

    #[test]
    #[allow(clippy::cloned_ref_to_slice_refs)]
    fn materialize_overwrites_a_pre_existing_dest() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        write(&a, b"fresh");
        let m = c.insert("f00d", &[a]).unwrap();
        let dest = t.path().join("out/A.olean");
        write(&dest, b"stale-and-readonly");
        let mut perms = std::fs::metadata(&dest).unwrap().permissions();
        perms.set_readonly(true);
        std::fs::set_permissions(&dest, perms).unwrap();
        c.materialize(&m, &[dest.clone()]).unwrap();
        assert_eq!(std::fs::read(&dest).unwrap(), b"fresh");
    }
}
