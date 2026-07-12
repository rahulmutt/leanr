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
    &hex[..2]
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
        // hex string shorter than 2 chars), which would otherwise panic
        // inside `shard()` when `blob_path` is called below.
        if manifest
            .artifacts
            .iter()
            .any(|a| a.blob.len() < 2 || !self.blob_path(&a.blob).exists())
        {
            return Ok(None);
        }
        Ok(Some(manifest))
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
}
