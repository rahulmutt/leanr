//! M2d remote-cache gate (spec §Testing, hermetic tier): a local static
//! HTTP server stands in for the remote; fetch/push/tamper/offline/
//! build-through-remote scenarios, no toolchain needed.
//! Run via `mise run cache:remote`.

#[path = "support/httpd.rs"]
mod httpd;

use std::io::Read;

/// Minimal std-only HTTP client for smoke-testing the test server itself
/// (the real client under test, ureq, enters in the RemoteCache tests).
fn raw_request(addr: std::net::SocketAddr, req: &str, body: &[u8]) -> (String, Vec<u8>) {
    use std::io::Write;
    let mut s = std::net::TcpStream::connect(addr).unwrap();
    s.write_all(req.as_bytes()).unwrap();
    s.write_all(body).unwrap();
    let mut resp = Vec::new();
    s.read_to_end(&mut resp).unwrap();
    let split = resp
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("response has a header/body split");
    (
        String::from_utf8_lossy(&resp[..split]).into_owned(),
        resp[split + 4..].to_vec(),
    )
}

#[test]
fn httpd_serves_put_then_get_and_404s_missing() {
    let tmp = tempfile::TempDir::new().unwrap();
    let srv = httpd::spawn(tmp.path().to_path_buf());
    let (head, _) = raw_request(
        srv.addr,
        "PUT /v1/blobs/aa/deadbeef?X-Amz-Signature=ignored HTTP/1.1\r\nHost: t\r\nContent-Length: 5\r\n\r\n",
        b"hello",
    );
    assert!(head.starts_with("HTTP/1.1 200"), "{head}");
    // Query string was stripped: the object lives at the bare path.
    let (head, body) = raw_request(
        srv.addr,
        "GET /v1/blobs/aa/deadbeef HTTP/1.1\r\nHost: t\r\n\r\n",
        b"",
    );
    assert!(head.starts_with("HTTP/1.1 200"), "{head}");
    assert_eq!(body, b"hello");
    let (head, _) = raw_request(
        srv.addr,
        "HEAD /v1/blobs/aa/deadbeef HTTP/1.1\r\nHost: t\r\n\r\n",
        b"",
    );
    assert!(head.starts_with("HTTP/1.1 200"), "{head}");
    assert!(head.contains("Content-Length: 5"), "{head}");
    let (head, _) = raw_request(srv.addr, "GET /nope HTTP/1.1\r\nHost: t\r\n\r\n", b"");
    assert!(head.starts_with("HTTP/1.1 404"), "{head}");
}

#[test]
fn httpd_rejects_path_traversal() {
    let tmp = tempfile::TempDir::new().unwrap();
    std::fs::write(tmp.path().join("secret"), b"s").unwrap();
    let srv = httpd::spawn(tmp.path().join("served"));
    let (head, _) = raw_request(srv.addr, "GET /../secret HTTP/1.1\r\nHost: t\r\n\r\n", b"");
    assert!(head.starts_with("HTTP/1.1 400"), "{head}");
}

use leanr_build::cache::{ArtifactEntry, Cache, Manifest};
use leanr_build::remote::{
    compress, remote_blob_key, remote_manifest_key, FetchOutcome, RemoteCache,
};
use std::path::Path;
use std::sync::{Arc, Mutex};

/// A RemoteCache whose warnings land in the returned collector.
fn remote_with_warnings(base: &str) -> (RemoteCache, Arc<Mutex<Vec<String>>>) {
    let warnings: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let w = warnings.clone();
    let rc = RemoteCache::new(
        base,
        Box::new(move |m| w.lock().unwrap().push(m.to_string())),
    );
    (rc, warnings)
}

/// Publish one (fp, artifacts) family into a served-root dir in the wire
/// layout: compressed blobs + plain manifest, blobs first.
fn publish(served: &Path, fp: &str, artifacts: &[(&str, &[u8])]) -> Manifest {
    let mut entries = Vec::new();
    for (name, bytes) in artifacts {
        let hex = blake3::hash(bytes).to_hex().to_string();
        let p = served.join(remote_blob_key(&hex));
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, compress(bytes)).unwrap();
        entries.push(ArtifactEntry {
            name: name.to_string(),
            blob: hex,
        });
    }
    let manifest = Manifest { artifacts: entries };
    let mp = served.join(remote_manifest_key(fp));
    std::fs::create_dir_all(mp.parent().unwrap()).unwrap();
    std::fs::write(mp, serde_json::to_vec(&manifest).unwrap()).unwrap();
    manifest
}

const FP: &str = "1111111111111111111111111111111111111111111111111111111111111111";

#[test]
fn fetch_hit_populates_local_cas_and_lookup_succeeds() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    let expected = publish(
        &served,
        FP,
        &[("A.olean", b"olean-bytes"), ("A.ilean", b"ilean-bytes")],
    );
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    let (rc, warnings) = remote_with_warnings(&format!("http://{}", srv.addr));
    let out = rc.fetch(&cache, FP);
    assert_eq!(
        out,
        FetchOutcome::Hit {
            downloaded_blobs: 2
        }
    );
    assert_eq!(cache.lookup(FP).unwrap().unwrap(), expected);
    assert_eq!(
        std::fs::read(cache.blob_path(&expected.artifacts[0].blob)).unwrap(),
        b"olean-bytes",
        "stored DECOMPRESSED"
    );
    assert!(warnings.lock().unwrap().is_empty());
    // Local integrity holds for remote-sourced entries (spec §Architecture).
    let v = cache.verify().unwrap();
    assert!(v.bad_blobs.is_empty() && v.dangling.is_empty());
}

#[test]
fn fetch_missing_manifest_is_a_quiet_miss() {
    let tmp = tempfile::TempDir::new().unwrap();
    let srv = httpd::spawn(tmp.path().join("empty"));
    let cache = Cache::new(&tmp.path().join("xdg"));
    let (rc, warnings) = remote_with_warnings(&format!("http://{}", srv.addr));
    assert_eq!(rc.fetch(&cache, FP), FetchOutcome::Miss);
    assert!(
        warnings.lock().unwrap().is_empty(),
        "404 is normal, not warned"
    );
}

#[test]
fn fetch_skips_blobs_already_local() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    let m = publish(&served, FP, &[("A.olean", b"shared-bytes")]);
    // Delete the served blob AFTER publishing: if fetch tried to download
    // it, it would 404 and degrade — passing proves no request was made.
    std::fs::remove_file(served.join(remote_blob_key(&m.artifacts[0].blob))).unwrap();
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    cache.store_blob(b"shared-bytes").unwrap(); // already local
    let (rc, _) = remote_with_warnings(&format!("http://{}", srv.addr));
    assert_eq!(
        rc.fetch(&cache, FP),
        FetchOutcome::Hit {
            downloaded_blobs: 0
        }
    );
    assert!(cache.lookup(FP).unwrap().is_some());
}

#[test]
fn tampered_blob_is_rejected_and_local_cas_stays_clean() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    let m = publish(&served, FP, &[("A.olean", b"legit-bytes")]);
    // Server swaps the blob's bytes (still valid zstd, wrong content).
    std::fs::write(
        served.join(remote_blob_key(&m.artifacts[0].blob)),
        compress(b"EVIL-bytes"),
    )
    .unwrap();
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    let (rc, warnings) = remote_with_warnings(&format!("http://{}", srv.addr));
    assert_eq!(rc.fetch(&cache, FP), FetchOutcome::Degraded);
    let w = warnings.lock().unwrap();
    assert!(w.iter().any(|m| m.contains("hash")), "warned: {w:?}");
    assert!(cache.lookup(FP).unwrap().is_none(), "nothing ingested");
    assert!(
        !cache.blob_path(&m.artifacts[0].blob).exists(),
        "no unverified blob stored"
    );
}

#[test]
fn malformed_manifest_and_bad_hex_degrade_without_panic() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    let mp = served.join(remote_manifest_key(FP));
    std::fs::create_dir_all(mp.parent().unwrap()).unwrap();
    std::fs::write(&mp, b"{ not json").unwrap();
    let srv = httpd::spawn(served.clone());
    let cache = Cache::new(&tmp.path().join("xdg"));
    let (rc, warnings) = remote_with_warnings(&format!("http://{}", srv.addr));
    assert_eq!(rc.fetch(&cache, FP), FetchOutcome::Degraded);
    assert_eq!(warnings.lock().unwrap().len(), 1);
    // Well-formed JSON, hostile blob field (path-traversal shaped).
    std::fs::write(
        &mp,
        br#"{"artifacts":[{"name":"A.olean","blob":"../../escape"}]}"#,
    )
    .unwrap();
    assert_eq!(rc.fetch(&cache, FP), FetchOutcome::Degraded);
}

#[test]
fn oversized_manifest_is_rejected() {
    // The blob-side decompression bomb is pinned by remote.rs's
    // `decompression_bomb_is_rejected_not_materialized` unit test (the
    // 4 GiB MAX_ARTIFACT_BYTES cap makes an end-to-end bomb too slow to
    // build here). This test pins the OTHER cap: a manifest response
    // bigger than MAX_MANIFEST_BYTES (1 MiB) degrades, never ingests.
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    let mp = served.join(remote_manifest_key(FP));
    std::fs::create_dir_all(mp.parent().unwrap()).unwrap();
    std::fs::write(&mp, vec![b'x'; 2 << 20]).unwrap(); // 2 MiB > 1 MiB cap
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    let (rc, warnings) = remote_with_warnings(&format!("http://{}", srv.addr));
    assert_eq!(rc.fetch(&cache, FP), FetchOutcome::Degraded);
    assert!(!warnings.lock().unwrap().is_empty());
}

#[test]
fn unreachable_remote_trips_breaker_and_warns_once() {
    let tmp = tempfile::TempDir::new().unwrap();
    let cache = Cache::new(&tmp.path().join("xdg"));
    // Bind-then-drop a listener to get a port that refuses connections.
    let dead = {
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        l.local_addr().unwrap()
    };
    let (rc, warnings) = remote_with_warnings(&format!("http://{dead}"));
    assert_eq!(rc.fetch(&cache, FP), FetchOutcome::Miss);
    assert_eq!(rc.fetch(&cache, FP), FetchOutcome::Miss);
    let w = warnings.lock().unwrap();
    assert_eq!(w.len(), 1, "one warning for the whole run, got {w:?}");
    assert!(w[0].contains("disabled"), "{w:?}");
}
