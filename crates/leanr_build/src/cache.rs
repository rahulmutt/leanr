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

    /// All real blob files as (hex, path, len, mtime). Empty if the store
    /// is absent. Filters to entries whose filename is a valid blob key
    /// (64 lowercase hex chars) — `blobs/<shard>/` also contains the
    /// transient `.lock` (flock guard) and `.tmp` (pre-rename) siblings
    /// that `write_atomic_readonly` creates next to each blob, and those
    /// must never be treated as cache content.
    fn walk_blobs(&self) -> std::io::Result<Vec<(String, PathBuf, u64, std::time::SystemTime)>> {
        let blobs_root = self.root.join("blobs");
        let mut out = Vec::new();
        let shards = match std::fs::read_dir(&blobs_root) {
            Ok(rd) => rd,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(out),
            Err(e) => return Err(e),
        };
        for shard in shards {
            let shard = shard?;
            if !shard.file_type()?.is_dir() {
                continue;
            }
            for blob in std::fs::read_dir(shard.path())? {
                let blob = blob?;
                let meta = blob.metadata()?;
                if !meta.is_file() {
                    continue;
                }
                let hex = blob.file_name().to_string_lossy().into_owned();
                if !is_blob_key(&hex) {
                    continue; // skip `.lock`, `.tmp`, and any other stray file.
                }
                let mtime = meta.modified().unwrap_or(std::time::UNIX_EPOCH);
                out.push((hex, blob.path(), meta.len(), mtime));
            }
        }
        Ok(out)
    }

    /// Re-hash every blob (filename must equal the blake3 of its content,
    /// else it's listed in `bad_blobs`) and check that every manifest's
    /// referenced blobs exist (else the manifest is listed in `dangling`).
    pub fn verify(&self) -> std::io::Result<VerifyReport> {
        let mut bad_blobs = Vec::new();
        let blobs = self.walk_blobs()?;
        for (hex, path, _, _) in &blobs {
            let bytes = std::fs::read(path)?;
            if blake3::hash(&bytes).to_hex().to_string() != *hex {
                bad_blobs.push(hex.clone());
            }
        }
        // Dangling manifests: referenced blob missing.
        let mut dangling = Vec::new();
        let modules_root = self.root.join("modules");
        if let Ok(shards) = std::fs::read_dir(&modules_root) {
            for shard in shards {
                let shard = shard?;
                if !shard.file_type()?.is_dir() {
                    continue;
                }
                for man in std::fs::read_dir(shard.path())? {
                    let man = man?;
                    if !man.file_type()?.is_file() {
                        continue;
                    }
                    let bytes = std::fs::read(man.path())?;
                    if let Ok(m) = serde_json::from_slice::<Manifest>(&bytes) {
                        if m.artifacts
                            .iter()
                            .any(|a| !self.blob_path(&a.blob).exists())
                        {
                            dangling.push(man.file_name().to_string_lossy().into_owned());
                        }
                    }
                }
            }
        }
        Ok(VerifyReport {
            blobs: blobs.len(),
            bad_blobs,
            dangling,
        })
    }

    /// LRU eviction by blob mtime: delete the oldest blobs until total
    /// blob bytes are at or under `max_size`.
    pub fn gc(&self, max_size: u64) -> std::io::Result<GcReport> {
        let mut blobs = self.walk_blobs()?;
        let total: u64 = blobs.iter().map(|b| b.2).sum();
        if total <= max_size {
            return Ok(GcReport {
                removed: 0,
                freed: 0,
                kept: total,
            });
        }
        // Oldest first.
        blobs.sort_by_key(|b| b.3);
        let mut kept = total;
        let mut removed = 0;
        let mut freed = 0;
        for (_, path, len, _) in blobs {
            if kept <= max_size {
                break;
            }
            std::fs::remove_file(&path)?;
            kept -= len;
            freed += len;
            removed += 1;
        }
        Ok(GcReport {
            removed,
            freed,
            kept,
        })
    }
}

/// True iff `s` is a valid blob key: exactly 64 lowercase hex chars (a
/// blake3 hex digest). Used by `walk_blobs` to exclude the `.lock` and
/// `.tmp` siblings that `write_atomic_readonly` leaves in `blobs/<shard>/`.
fn is_blob_key(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

#[derive(Debug)]
pub struct VerifyReport {
    pub blobs: usize,
    pub bad_blobs: Vec<String>,
    pub dangling: Vec<String>,
}

#[derive(Debug)]
pub struct GcReport {
    pub removed: usize,
    pub freed: u64,
    pub kept: u64,
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
        c.materialize(&m, std::slice::from_ref(&dest)).unwrap();
        assert_eq!(std::fs::read(&dest).unwrap(), b"fresh");
    }

    #[test]
    fn verify_is_clean_for_a_well_formed_store() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        write(&a, b"bytes");
        c.insert("aa11", &[a]).unwrap();
        let r = c.verify().unwrap();
        assert_eq!(r.bad_blobs.len(), 0);
        assert_eq!(r.dangling.len(), 0);
        assert_eq!(r.blobs, 1);
    }

    #[test]
    fn verify_flags_a_tampered_blob() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        write(&a, b"bytes");
        let m = c.insert("bb22", &[a]).unwrap();
        // Tamper: rewrite the blob's bytes (make it writable first).
        let bp = c.blob_path(&m.artifacts[0].blob);
        // Explicit mode rather than `set_readonly(false)`, which clippy
        // flags: on Unix that clears *all* permission bits (world-writable).
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&bp, std::fs::Permissions::from_mode(0o644)).unwrap();
        std::fs::write(&bp, b"TAMPERED").unwrap();
        let r = c.verify().unwrap();
        assert_eq!(r.bad_blobs, vec![m.artifacts[0].blob.clone()]);
    }

    #[test]
    fn gc_evicts_oldest_until_under_cap() {
        let (_t, c) = cache();
        // Three ~1 KiB blobs; cap at 2 KiB must drop exactly one.
        let a = c.store_blob(&vec![1u8; 1024]).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let b = c.store_blob(&vec![2u8; 1024]).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let cc = c.store_blob(&vec![3u8; 1024]).unwrap();
        let r = c.gc(2048).unwrap();
        assert_eq!(r.removed, 1);
        assert!(!c.blob_path(&a).exists(), "oldest evicted");
        assert!(
            c.blob_path(&b).exists() && c.blob_path(&cc).exists(),
            "newest kept"
        );
    }

    #[test]
    fn walk_blobs_ignores_lock_siblings() {
        // `store_blob` creates a transient flock sibling (`<hex>.lock`)
        // right next to the real blob in the same shard dir. `verify`
        // must not mistake it for a blob: its filename ("<hex>.lock")
        // is not a 64-char hex string, so it would fail the content-hash
        // check and show up as a spurious `bad_blobs` entry, and `gc`
        // would count/evict it as if it were real cached content.
        let (_t, c) = cache();
        let h = c.store_blob(b"lock-sibling-regression").unwrap();
        let lock_sibling = c.blob_path(&h).with_extension("lock");
        assert!(
            lock_sibling.exists(),
            "test assumption: store_blob leaves a .lock sibling in the shard dir"
        );
        let r = c.verify().unwrap();
        assert_eq!(
            r.blobs, 1,
            "only the real blob is counted, not the .lock sibling"
        );
        assert!(
            r.bad_blobs.is_empty(),
            "the .lock sibling must not be flagged as tampered"
        );
    }
}
