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

// --- Task 5: build integration (the remote tier in the job body) ---

use leanr_build::compile::{build_workspace, BuildOptions, BuildReport, LeanInvoker};
use leanr_build::fingerprint::{fingerprint_all, FingerprintEnv};
use leanr_build::{resolve, ResolveOptions, Workspace};
use std::path::PathBuf;

fn counting_lean() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/counting-lean.sh")
}

fn write(dir: &Path, rel: &str, text: &str) {
    let p = dir.join(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

/// Same three-module fixture as cache_incremental.rs (Root imports
/// Root.A and Root.B), resolved fresh per test dir.
fn fixture(dir: &Path) -> Workspace {
    write(
        dir,
        "lakefile.toml",
        "name = \"app\"\ndefaultTargets = [\"Root\"]\n\n[[lean_lib]]\nname = \"Root\"\n",
    );
    write(dir, "Root.lean", "import Root.A\nimport Root.B\n");
    write(dir, "Root/A.lean", "-- leaf A\ndef a := 1\n");
    write(dir, "Root/B.lean", "-- leaf B\ndef b := 2\n");
    write(
        dir,
        "lake-manifest.json",
        r#"{"version": "1.2.0", "packages": []}"#,
    );
    let fake_toolchain = dir.join("fake-toolchain");
    std::fs::create_dir_all(&fake_toolchain).unwrap();
    std::fs::write(fake_toolchain.join("Init.olean"), "").unwrap();
    resolve(
        dir,
        &ResolveOptions {
            targets: Vec::new(),
            lake: leanr_build::bridge::LakeInvoker::default(),
            toolchain_olean_dir: fake_toolchain,
            cache_root: dir.join("resolve-cache"),
        },
    )
    .unwrap()
}

fn fp_env() -> FingerprintEnv {
    FingerprintEnv {
        leanr_version: "test".into(),
        toolchain_id: "test-tc".into(),
        platform: "test-plat".into(),
    }
}

// COUNTING_LEAN_LOG is process-wide (same fix as cache_incremental.rs's
// ENV_GUARD): serialize builds that set it.
static ENV_GUARD: Mutex<()> = Mutex::new(());

fn build_with(
    ws: &Workspace,
    xdg: &Path,
    log: &Path,
    remote: Option<RemoteCache>,
    force: bool,
) -> BuildReport {
    let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
    std::env::set_var("COUNTING_LEAN_LOG", log);
    let opts = BuildOptions {
        jobs: 2,
        lean: LeanInvoker {
            program: counting_lean(),
            toolchain: None,
        },
        cache: Some(Cache::new(xdg)),
        force,
        fp_env: fp_env(),
        remote,
    };
    let report = build_workspace(ws, &opts, &|_| {}).unwrap();
    std::env::remove_var("COUNTING_LEAN_LOG");
    report
}

fn lean_runs(log: &Path) -> usize {
    std::fs::read_to_string(log)
        .unwrap_or_default()
        .lines()
        .count()
}

/// Publish machine A's whole local CAS into a served-root dir in the
/// wire layout (compressed blobs, plain manifests). Stand-in for `push`
/// until Task 6; kept afterward as an independent publisher so the
/// fetch tests don't depend on push being correct.
fn publish_cas(xdg: &Path, ws: &Workspace, served: &Path) {
    let cache = Cache::new(xdg);
    let fps = fingerprint_all(ws, &fp_env()).unwrap();
    for fp in &fps {
        let Some(m) = cache.lookup(fp).unwrap() else {
            continue;
        };
        for e in &m.artifacts {
            let dst = served.join(remote_blob_key(&e.blob));
            std::fs::create_dir_all(dst.parent().unwrap()).unwrap();
            std::fs::write(
                dst,
                compress(&std::fs::read(cache.blob_path(&e.blob)).unwrap()),
            )
            .unwrap();
        }
        let mp = served.join(remote_manifest_key(fp));
        std::fs::create_dir_all(mp.parent().unwrap()).unwrap();
        std::fs::write(mp, serde_json::to_vec(&m).unwrap()).unwrap();
    }
}

#[test]
fn fresh_machine_builds_entirely_from_remote_zero_lean() {
    let tmp = tempfile::TempDir::new().unwrap();
    // Machine A: cold build populates CAS A; publish it.
    let dir_a = tmp.path().join("ws-a");
    std::fs::create_dir_all(&dir_a).unwrap();
    let ws_a = fixture(&dir_a);
    let xdg_a = tmp.path().join("xdg-a");
    let cold = build_with(&ws_a, &xdg_a, &tmp.path().join("cold.log"), None, false);
    assert_eq!((cold.built, cold.cached, cold.downloaded), (3, 0, 0));
    let served = tmp.path().join("served");
    publish_cas(&xdg_a, &ws_a, &served);
    let srv = httpd::spawn(served);

    // Machine B: identical sources, EMPTY local CAS, remote configured.
    let dir_b = tmp.path().join("ws-b");
    std::fs::create_dir_all(&dir_b).unwrap();
    let ws_b = fixture(&dir_b);
    let xdg_b = tmp.path().join("xdg-b");
    let log_b = tmp.path().join("b.log");
    let (rc, _) = remote_with_warnings(&format!("http://{}", srv.addr));
    let b = build_with(&ws_b, &xdg_b, &log_b, Some(rc), false);
    assert_eq!(lean_runs(&log_b), 0, "zero lean invocations on machine B");
    assert_eq!((b.built, b.cached, b.downloaded), (0, 0, 3));

    // Artifacts byte-identical across machines (compare every family
    // member via Layout, not hand-built paths).
    let layout_a = leanr_build::setup::Layout::new(&ws_a.root_dir);
    let layout_b = leanr_build::setup::Layout::new(&ws_b.root_dir);
    for (ma, mb) in ws_a.graph.modules.iter().zip(&ws_b.graph.modules) {
        let pa = layout_a.artifact_paths(&ma.package, ma);
        let pb = layout_b.artifact_paths(&mb.package, mb);
        for (a, b) in pa.iter().zip(&pb) {
            assert_eq!(
                std::fs::read(a).unwrap(),
                std::fs::read(b).unwrap(),
                "byte-identical: {} vs {}",
                a.display(),
                b.display()
            );
        }
    }
}

#[test]
fn dead_remote_degrades_to_a_normal_local_build() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = tmp.path().join("ws");
    std::fs::create_dir_all(&dir).unwrap();
    let ws = fixture(&dir);
    let dead = {
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        l.local_addr().unwrap()
    };
    let (rc, warnings) = remote_with_warnings(&format!("http://{dead}"));
    let log = tmp.path().join("dead.log");
    let r = build_with(&ws, &tmp.path().join("xdg"), &log, Some(rc), false);
    assert_eq!((r.built, r.downloaded), (3, 0), "build succeeded via lean");
    assert_eq!(warnings.lock().unwrap().len(), 1, "breaker warned once");
}

#[test]
fn force_runs_lean_even_with_a_populated_remote() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = tmp.path().join("ws");
    std::fs::create_dir_all(&dir).unwrap();
    let ws = fixture(&dir);
    let xdg = tmp.path().join("xdg");
    build_with(&ws, &xdg, &tmp.path().join("c.log"), None, false);
    let served = tmp.path().join("served");
    publish_cas(&xdg, &ws, &served);
    let srv = httpd::spawn(served);
    let (rc, _) = remote_with_warnings(&format!("http://{}", srv.addr));
    let log = tmp.path().join("force.log");
    let r = build_with(&ws, &tmp.path().join("xdg-fresh"), &log, Some(rc), true);
    assert_eq!(lean_runs(&log), 3, "--force always runs lean");
    assert_eq!((r.built, r.downloaded), (3, 0));
}

#[test]
fn local_hit_wins_without_touching_the_remote() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = tmp.path().join("ws");
    std::fs::create_dir_all(&dir).unwrap();
    let ws = fixture(&dir);
    let xdg = tmp.path().join("xdg");
    build_with(&ws, &xdg, &tmp.path().join("c.log"), None, false);
    // Remote is a DEAD endpoint — a warm local build must never contact
    // it (local lookup happens first), so no breaker warning fires.
    let dead = {
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        l.local_addr().unwrap()
    };
    let (rc, warnings) = remote_with_warnings(&format!("http://{dead}"));
    let log = tmp.path().join("warm.log");
    let r = build_with(&ws, &xdg, &log, Some(rc), false);
    assert_eq!(lean_runs(&log), 0);
    assert_eq!((r.built, r.cached, r.downloaded), (0, 3, 0));
    assert!(
        warnings.lock().unwrap().is_empty(),
        "remote never consulted"
    );
}

// --- Task 6: Pusher (S3-presigned upload) ---

use leanr_build::remote::Pusher;

/// Pusher aimed at the test httpd (which ignores sigv4 query params).
/// Path-style: objects land under `<served>/<bucket>/<key>`.
fn test_pusher(addr: std::net::SocketAddr) -> Pusher {
    Pusher::from_parts(
        "s3://cas/team",
        &format!("http://{addr}"),
        "us-east-1",
        "test-key",
        "test-secret",
    )
    .unwrap()
}

#[test]
fn push_uploads_wire_layout_and_is_idempotent() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    std::fs::create_dir_all(&served).unwrap();
    let srv = httpd::spawn(served.clone());
    let cache = Cache::new(&tmp.path().join("xdg"));
    // Local CAS: one module family under FP.
    let a = tmp.path().join("A.olean");
    std::fs::write(&a, b"olean-bytes").unwrap();
    let m = cache.insert(FP, &[a]).unwrap();

    let p = test_pusher(srv.addr);
    let r1 = p.push(&cache, &[FP.to_string()], 2).unwrap();
    assert_eq!(
        (r1.manifests_pushed, r1.manifests_skipped, r1.blobs_pushed),
        (1, 0, 1)
    );
    assert!(r1.bytes_uploaded > 0);
    // Objects at s3-path-style locations: <bucket>/<prefix>/<wire key>.
    let blob_obj = served
        .join("cas/team")
        .join(remote_blob_key(&m.artifacts[0].blob));
    let man_obj = served.join("cas/team").join(remote_manifest_key(FP));
    assert!(
        blob_obj.is_file(),
        "blob object exists: {}",
        blob_obj.display()
    );
    assert!(man_obj.is_file(), "manifest object exists");
    // Blob object is compressed; decompresses to the original bytes.
    assert_eq!(
        leanr_build::remote::decompress_capped(&std::fs::read(&blob_obj).unwrap(), 1 << 20)
            .unwrap(),
        b"olean-bytes"
    );
    // Manifest object is the plain local manifest JSON.
    let remote_m: Manifest = serde_json::from_slice(&std::fs::read(&man_obj).unwrap()).unwrap();
    assert_eq!(remote_m, m);
    // Second push: everything skipped, nothing uploaded.
    let r2 = p.push(&cache, &[FP.to_string()], 2).unwrap();
    assert_eq!(
        (r2.manifests_pushed, r2.manifests_skipped, r2.blobs_pushed),
        (0, 1, 0)
    );
    assert_eq!(r2.bytes_uploaded, 0);
}

#[test]
fn push_then_fetch_roundtrips_end_to_end() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    std::fs::create_dir_all(&served).unwrap();
    let srv = httpd::spawn(served);
    let cache_a = Cache::new(&tmp.path().join("xdg-a"));
    let a = tmp.path().join("A.olean");
    std::fs::write(&a, b"roundtrip-bytes").unwrap();
    cache_a.insert(FP, &[a]).unwrap();
    test_pusher(srv.addr)
        .push(&cache_a, &[FP.to_string()], 1)
        .unwrap();

    // Reads go through the plain-GET base under the same bucket path.
    let cache_b = Cache::new(&tmp.path().join("xdg-b"));
    let (rc, _) = remote_with_warnings(&format!("http://{}/cas/team", srv.addr));
    assert_eq!(
        rc.fetch(&cache_b, FP),
        FetchOutcome::Hit {
            downloaded_blobs: 1
        }
    );
    let got = cache_b.lookup(FP).unwrap().unwrap();
    assert_eq!(
        std::fs::read(cache_b.blob_path(&got.artifacts[0].blob)).unwrap(),
        b"roundtrip-bytes"
    );
}

#[test]
fn pusher_from_parts_rejects_bad_targets() {
    assert!(
        Pusher::from_parts("http://not-s3", "http://e", "r", "k", "s")
            .unwrap_err()
            .contains("s3://")
    );
    assert!(Pusher::from_parts("s3://", "http://e", "r", "k", "s").is_err());
}

#[test]
fn push_skips_fps_with_no_local_manifest() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    std::fs::create_dir_all(&served).unwrap();
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    let r = test_pusher(srv.addr)
        .push(&cache, &[FP.to_string()], 1)
        .unwrap();
    assert_eq!(
        (r.manifests_pushed, r.manifests_skipped, r.blobs_pushed),
        (0, 0, 0)
    );
}

#[test]
fn trailing_slash_only_target_yields_empty_prefix_not_slash() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    std::fs::create_dir_all(&served).unwrap();
    let srv = httpd::spawn(served.clone());
    let cache = Cache::new(&tmp.path().join("xdg"));
    // Local CAS: one module family under FP.
    let a = tmp.path().join("A.olean");
    std::fs::write(&a, b"olean-bytes").unwrap();
    let m = cache.insert(FP, &[a]).unwrap();

    // from_parts("s3://cas/", ...) must behave identically to "s3://cas"
    // (empty prefix after trim, not "/" prefix).
    let p = Pusher::from_parts(
        "s3://cas/",
        &format!("http://{}", srv.addr),
        "us-east-1",
        "test-key",
        "test-secret",
    )
    .unwrap();
    let r = p.push(&cache, &[FP.to_string()], 1).unwrap();
    assert_eq!(
        (r.manifests_pushed, r.manifests_skipped, r.blobs_pushed),
        (1, 0, 1)
    );

    // Objects must land at <served>/cas/v1/... not <served>/cas//v1/...
    let blob_obj = served
        .join("cas")
        .join(remote_blob_key(&m.artifacts[0].blob));
    let man_obj = served.join("cas").join(remote_manifest_key(FP));
    assert!(
        blob_obj.is_file(),
        "blob object exists at correct path (no double slash): {}",
        blob_obj.display()
    );
    assert!(man_obj.is_file(), "manifest object exists at correct path");

    // Verify remote reads work correctly (uses plain-GET base).
    let cache_b = Cache::new(&tmp.path().join("xdg-b"));
    let (rc, _) = remote_with_warnings(&format!("http://{}/cas", srv.addr));
    assert_eq!(
        rc.fetch(&cache_b, FP),
        FetchOutcome::Hit {
            downloaded_blobs: 1
        }
    );
}
