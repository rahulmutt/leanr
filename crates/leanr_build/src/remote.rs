//! Remote cache tier (M2d spec §Architecture): a read-through populator
//! of the local CAS over dumb HTTP, plus an explicit S3-presigned pusher
//! and a batch prefetcher. Never touches the project layout — remote
//! bytes only ever enter the local store, after decompress-and-blake3-
//! verify against the content key (§Threat model touch). Remote
//! availability affects speed, never correctness: every failure path
//! degrades to "miss" and the build proceeds via `lean`.

use std::io::Read;

/// Remote manifests are small JSON; anything bigger is hostile or broken.
pub const MAX_MANIFEST_BYTES: u64 = 1 << 20; // 1 MiB
/// Per-artifact decompressed ceiling (largest Mathlib olean is ~100 MiB;
/// 4 GiB is defense-in-depth against decompression bombs, not a tuning
/// knob).
pub const MAX_ARTIFACT_BYTES: u64 = 4 << 30; // 4 GiB

/// zstd level for pushed blobs: 3 is the fast default; ratio-vs-speed
/// retuning is a later measurement, not a correctness matter.
const ZSTD_LEVEL: i32 = 3;

/// Wire key for a module manifest: `v1/modules/<aa>/<fp>.json` —
/// mirrors `Cache::manifest_path` under the versioned prefix.
pub fn remote_manifest_key(fp: &str) -> String {
    format!("v1/modules/{}/{fp}.json", fp.get(..2).unwrap_or(fp))
}

/// Wire key for a content blob: `v1/blobs/<aa>/<hex>` — mirrors
/// `Cache::blob_path` under the versioned prefix. The object's BYTES are
/// zstd-compressed; its NAME is the blake3 of the uncompressed bytes.
pub fn remote_blob_key(hex: &str) -> String {
    format!("v1/blobs/{}/{hex}", hex.get(..2).unwrap_or(hex))
}

pub fn compress(bytes: &[u8]) -> Vec<u8> {
    zstd::encode_all(bytes, ZSTD_LEVEL).expect("zstd encode to Vec never fails")
}

/// Decompress with a hard output cap (bomb defense — spec §Error
/// handling). Errors, never panics, on malformed or oversized input.
pub fn decompress_capped(compressed: &[u8], cap: u64) -> Result<Vec<u8>, String> {
    let dec = zstd::stream::read::Decoder::new(compressed).map_err(|e| e.to_string())?;
    let mut out = Vec::new();
    let n = dec
        .take(cap + 1)
        .read_to_end(&mut out)
        .map_err(|e| e.to_string())?;
    if n as u64 > cap {
        return Err(format!("decompressed size exceeds cap ({cap} bytes)"));
    }
    Ok(out)
}

use crate::cache::{Cache, Manifest};
use std::sync::atomic::{AtomicBool, Ordering};

pub type WarnFn = Box<dyn Fn(&str) + Send + Sync>;

/// Read tier over a dumb-HTTP remote (spec §Wire layout). Failure
/// posture: transport-level errors trip a per-run circuit breaker (one
/// warning, then silent misses); verification failures warn per
/// occurrence and NEVER ingest.
pub struct RemoteCache {
    base: String,
    agent: ureq::Agent,
    tripped: AtomicBool,
    warn: WarnFn,
}

#[derive(Debug, PartialEq)]
pub enum FetchOutcome {
    /// Manifest + all blobs are now in the local CAS.
    Hit { downloaded_blobs: usize },
    /// Remote does not have this fingerprint (or breaker is tripped).
    Miss,
    /// Remote HAS the manifest but something failed to download, parse,
    /// or verify — a miss to the build, distinct for operators.
    Degraded,
}

enum GetError {
    /// Connection-level: refused/timeout/DNS. Trips the breaker.
    Transport(String),
    /// Non-200/404 HTTP status.
    Status(u16),
    /// Body exceeded the caller's cap.
    TooLarge,
}

impl RemoteCache {
    pub fn new(base_url: &str, warn: WarnFn) -> RemoteCache {
        // ureq 3: statuses are NOT errors (we branch on them), connect
        // timeout only (blob downloads may legitimately run long).
        let config = ureq::Agent::config_builder()
            .timeout_connect(Some(std::time::Duration::from_secs(10)))
            .http_status_as_error(false)
            .build();
        RemoteCache {
            base: base_url.trim_end_matches('/').to_string(),
            agent: config.new_agent(),
            tripped: AtomicBool::new(false),
            warn,
        }
    }

    fn trip(&self, why: &str) {
        if !self.tripped.swap(true, Ordering::SeqCst) {
            (self.warn)(&format!(
                "remote cache {}: unreachable ({why}) — disabled for the rest of this run",
                self.base
            ));
        }
    }

    /// GET `{base}/{key}` with a response-size cap. Ok(None) = 404.
    fn get_capped(&self, key: &str, cap: u64) -> Result<Option<Vec<u8>>, GetError> {
        let url = format!("{}/{key}", self.base);
        let mut resp = match self.agent.get(&url).call() {
            Ok(r) => r,
            Err(e) => return Err(GetError::Transport(e.to_string())),
        };
        match resp.status().as_u16() {
            200 => {}
            404 => return Ok(None),
            s => return Err(GetError::Status(s)),
        }
        let body = resp
            .body_mut()
            .with_config()
            .limit(cap)
            .read_to_vec()
            .map_err(|_| GetError::TooLarge)?;
        Ok(Some(body))
    }

    /// Download manifest + missing blobs for `fp` into the local CAS.
    /// Blobs are decompressed (capped) and blake3-verified against their
    /// content key BEFORE `store_blob`; the manifest is written last.
    pub fn fetch(&self, cache: &Cache, fp: &str) -> FetchOutcome {
        if self.tripped.load(Ordering::SeqCst) {
            return FetchOutcome::Miss;
        }
        let mbytes = match self.get_capped(&remote_manifest_key(fp), MAX_MANIFEST_BYTES) {
            Ok(Some(b)) => b,
            Ok(None) => return FetchOutcome::Miss,
            Err(GetError::Transport(e)) => {
                self.trip(&e);
                return FetchOutcome::Miss;
            }
            Err(GetError::Status(s)) => {
                (self.warn)(&format!(
                    "remote cache: HTTP {s} fetching manifest for {fp}"
                ));
                return FetchOutcome::Degraded;
            }
            Err(GetError::TooLarge) => {
                (self.warn)(&format!(
                    "remote cache: manifest for {fp} exceeds {MAX_MANIFEST_BYTES} bytes — rejected"
                ));
                return FetchOutcome::Degraded;
            }
        };
        // Untrusted-bytes discipline: malformed wire manifest is a warned
        // degrade, never a panic; hostile `blob` strings never reach a
        // filesystem path (is_blob_key gates them).
        let manifest: Manifest = match serde_json::from_slice(&mbytes) {
            Ok(m) => m,
            Err(_) => {
                (self.warn)(&format!(
                    "remote cache: malformed manifest for {fp} — rejected"
                ));
                return FetchOutcome::Degraded;
            }
        };
        if manifest
            .artifacts
            .iter()
            .any(|a| !crate::cache::is_blob_key(&a.blob))
        {
            (self.warn)(&format!(
                "remote cache: manifest for {fp} names an invalid blob key — rejected"
            ));
            return FetchOutcome::Degraded;
        }
        let mut downloaded = 0usize;
        for entry in &manifest.artifacts {
            if cache.blob_path(&entry.blob).exists() {
                continue; // wire-level dedup (spec §Scope decisions)
            }
            let compressed =
                match self.get_capped(&remote_blob_key(&entry.blob), MAX_ARTIFACT_BYTES) {
                    Ok(Some(b)) => b,
                    Ok(None) => {
                        (self.warn)(&format!(
                            "remote cache: manifest for {fp} references missing blob {} — degraded",
                            entry.blob
                        ));
                        return FetchOutcome::Degraded;
                    }
                    Err(GetError::Transport(e)) => {
                        self.trip(&e);
                        return FetchOutcome::Degraded;
                    }
                    Err(GetError::Status(s)) => {
                        (self.warn)(&format!(
                            "remote cache: HTTP {s} fetching blob {}",
                            entry.blob
                        ));
                        return FetchOutcome::Degraded;
                    }
                    Err(GetError::TooLarge) => {
                        (self.warn)(&format!(
                            "remote cache: blob {} exceeds {MAX_ARTIFACT_BYTES} bytes — rejected",
                            entry.blob
                        ));
                        return FetchOutcome::Degraded;
                    }
                };
            let bytes = match decompress_capped(&compressed, MAX_ARTIFACT_BYTES) {
                Ok(b) => b,
                Err(e) => {
                    (self.warn)(&format!(
                        "remote cache: blob {} failed decompression ({e}) — rejected",
                        entry.blob
                    ));
                    return FetchOutcome::Degraded;
                }
            };
            // THE ingestion choke point (spec §Threat model touch).
            if blake3::hash(&bytes).to_hex().to_string() != entry.blob {
                (self.warn)(&format!(
                    "remote cache: blob {} failed hash verification — rejected",
                    entry.blob
                ));
                return FetchOutcome::Degraded;
            }
            if let Err(e) = cache.store_blob(&bytes) {
                (self.warn)(&format!(
                    "remote cache: storing blob {} failed ({e})",
                    entry.blob
                ));
                return FetchOutcome::Degraded;
            }
            downloaded += 1;
        }
        // Blobs first, manifest last (crash-safe with lookup self-healing).
        if let Err(e) = cache.insert_manifest(fp, &manifest) {
            (self.warn)(&format!(
                "remote cache: storing manifest for {fp} failed ({e})"
            ));
            return FetchOutcome::Degraded;
        }
        FetchOutcome::Hit {
            downloaded_blobs: downloaded,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_keys_mirror_the_cas_layout_under_v1() {
        let fp = "aabbccdd00112233aabbccdd00112233aabbccdd00112233aabbccdd00112233";
        assert_eq!(remote_manifest_key(fp), format!("v1/modules/aa/{fp}.json"));
        assert_eq!(remote_blob_key(fp), format!("v1/blobs/aa/{fp}"));
        // Total on malformed hex (same posture as cache::shard).
        assert_eq!(remote_blob_key("x"), "v1/blobs/x/x");
    }

    #[test]
    fn compress_roundtrips() {
        let data = b"olean bytes olean bytes olean bytes".repeat(100);
        let c = compress(&data);
        assert!(c.len() < data.len(), "compressible input got smaller");
        assert_eq!(decompress_capped(&c, 1 << 20).unwrap(), data);
    }

    #[test]
    fn decompression_bomb_is_rejected_not_materialized() {
        // 10 MiB of zeros compresses to ~1 KiB; a 1 MiB cap must reject
        // it WITHOUT allocating the full 10 MiB.
        let bomb = compress(&vec![0u8; 10 << 20]);
        assert!(
            bomb.len() < 64 << 10,
            "test premise: bomb is small on the wire"
        );
        let err = decompress_capped(&bomb, 1 << 20).unwrap_err();
        assert!(err.contains("exceeds cap"), "got: {err}");
    }

    #[test]
    fn garbage_input_errors_never_panics() {
        assert!(decompress_capped(b"not zstd at all", 1024).is_err());
        assert!(decompress_capped(&[], 1024).is_err());
    }
}
