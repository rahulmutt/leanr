//! Content-addressed artifact store (M2c spec §Layout, §Architecture
//! `cache`). Two levels: a module manifest keyed by fingerprint names the
//! artifact family; each member points at a content blob keyed by the
//! blake3 of its own bytes. Immutable, sharded, flock-guarded, atomic
//! writes. Lives at `$XDG_CACHE_HOME/leanr/cache/` alongside M2b's
//! `src/` and `config-cache/`.

use std::path::{Path, PathBuf};

pub struct Cache {
    root: PathBuf,
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
}
