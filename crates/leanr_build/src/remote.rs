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
