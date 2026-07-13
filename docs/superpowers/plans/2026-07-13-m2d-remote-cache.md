# M2d — Remote Cache Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the M2c local CAS shareable over the network — `leanr build` transparently pulls artifacts from a dumb-HTTP remote, `leanr cache push` publishes to an S3-compatible bucket, and `leanr cache get` prefetches the whole closure.

**Architecture:** One new module `remote.rs` in `leanr_build` acting as a read-through populator of the local CAS (it never touches the project layout; the local `Cache` remains the sole materialization source). The M2c job body in `compile.rs` grows exactly one tier: local miss → `remote.fetch(fp)` → re-`lookup` locally → hit materializes, still-miss runs `lean`. Remote bytes are untrusted: every blob is zstd-decompressed (capped) and blake3-verified against its content key **before** `store_blob`; manifests are parsed defensively.

**Tech Stack:** Rust (workspace pinned rust 1.97.0 via mise), `ureq` (sync HTTP + rustls), `zstd`, `rusty-s3` (sigv4 presigning, no AWS SDK). Test infra: a ~120-line `std::net::TcpListener` static GET/HEAD/PUT server (zero new deps).

Spec: `docs/superpowers/specs/2026-07-13-m2d-remote-cache-design.md`. Read it before starting.

## Global Constraints

- **Remote availability affects speed, never correctness or build success** (spec §Error handling). A dead remote must never fail `leanr build`.
- **Unverified bytes never enter the local CAS**: decompress-then-blake3-verify BEFORE `store_blob`; reject on mismatch (spec §Threat model touch).
- **Untrusted-input rule** (`docs/THREAT_MODEL.md`): remote manifest/blob bytes must never cause a panic — malformed input is a warned miss/degraded, never `unwrap` on wire data.
- **`leanr_cli` holds no build logic** (M2b rule): CLI = argument parsing + printing over `leanr_build` APIs.
- **`leanr_kernel` untouched**; `leanr_build` gains no new *workspace-crate* deps.
- **New external deps limited to**: `ureq`, `zstd`, `rusty-s3` — each already justified in the spec. Nothing else without a spec change.
- **Wire layout is versioned**: all remote paths live under `v1/` (`v1/blobs/<aa>/<hex>`, `v1/modules/<aa>/<fp>.json`). Blob objects are zstd-compressed but **named by the blake3 of the uncompressed bytes**.
- **Upload ordering: blobs before their manifest** (push and fetch-insert both).
- **Never bump the `lean-toolchain` pin** (AGENTS.md).
- Run `mise run fmt` before each commit; `mise run lint` and `mise run test` must be green at every commit. `mise run lint:deps` must pass after the dependency task.

## File Structure

| File | Action | Responsibility |
|---|---|---|
| `crates/leanr_build/Cargo.toml` | Modify | add `ureq`, `zstd`, `rusty-s3` |
| `crates/leanr_build/src/remote.rs` | Create | remote tier: wire keys, compression caps, `RemoteCache::fetch`, `Pusher::push`, `get_all` |
| `crates/leanr_build/src/lib.rs` | Modify | `pub mod remote;` |
| `crates/leanr_build/src/cache.rs` | Modify | `insert_manifest`, `pub(crate) shard`/`is_blob_key` |
| `crates/leanr_build/src/compile.rs` | Modify | remote tier in job body; `BuildOptions.remote`, `BuiltEvent.downloaded`, `BuildReport.downloaded` |
| `crates/leanr_build/tests/support/httpd.rs` | Create | test-only static GET/HEAD/PUT server over `std::net` |
| `crates/leanr_build/examples/cas_httpd.rs` | Create | thin `main()` over `httpd.rs` for the acceptance script |
| `crates/leanr_build/tests/cache_remote.rs` | Create | hermetic M2d gate: fetch/push/tamper/offline/build-through-remote |
| `crates/leanr_cli/src/main.rs` | Modify | `--remote`/`--no-remote`, `cache get`, `cache push`, `downloaded` reporting |
| `mise.toml` | Modify | `cache:remote` task; wire into `ci` |
| `docs/THREAT_MODEL.md` | Modify | make the "Remote cache entries" row concrete |
| `ARCHITECTURE.md` | Modify | one paragraph: M2d remote tier |
| `scripts/remote-cache-acceptance.sh` | Create | recorded full-Mathlib acceptance run |

---

### Task 1: Dependencies + `remote.rs` pure core (wire keys, capped compression)

**Files:**
- Modify: `crates/leanr_build/Cargo.toml`
- Create: `crates/leanr_build/src/remote.rs`
- Modify: `crates/leanr_build/src/lib.rs` (add `pub mod remote;` to the module list, alphabetical: between `pub mod pool;` and `pub mod scanner;`)
- Possibly modify: `deny.toml` (new transitive licenses)

**Interfaces:**
- Produces: `remote::remote_manifest_key(fp: &str) -> String` ("v1/modules/<aa>/<fp>.json"), `remote::remote_blob_key(hex: &str) -> String` ("v1/blobs/<aa>/<hex>"), `remote::compress(bytes: &[u8]) -> Vec<u8>`, `remote::decompress_capped(compressed: &[u8], cap: u64) -> Result<Vec<u8>, String>`, `remote::MAX_MANIFEST_BYTES: u64` (1 MiB), `remote::MAX_ARTIFACT_BYTES: u64` (4 GiB). Consumed by Tasks 4 and 6.
- Consumes: `cache::shard` — not yet public; this task uses a local sharding expression, Task 2 unifies (see note in Step 3).

- [ ] **Step 1: Add the dependencies**

```bash
cd /workspace/crates/leanr_build
cargo add ureq zstd rusty-s3
```

Expected majors: `ureq = "3"`, `zstd = "0.13"`, `rusty-s3 = "0.7"` (accept whatever current stable majors cargo resolves; do NOT pass `--no-default-features` — ureq's default TLS is rustls, which is what we want).

- [ ] **Step 2: Check the dependency gates**

Run: `cargo build -p leanr_build && mise run lint:deps`

If `cargo deny` rejects a new transitive license (rustls pulls `ring`: ISC/MIT/OpenSSL-ish combo), extend the `[licenses] allow` list in `/workspace/deny.toml` with exactly the flagged license identifiers and a `# ureq→rustls→ring (M2d remote cache)` comment. Advisories/sources failures are NOT to be waived — stop and reassess the dep choice if one fires.

- [ ] **Step 3: Write the failing tests** — create `crates/leanr_build/src/remote.rs`:

```rust
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
        assert_eq!(
            remote_manifest_key(fp),
            format!("v1/modules/aa/{fp}.json")
        );
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
        assert!(bomb.len() < 64 << 10, "test premise: bomb is small on the wire");
        let err = decompress_capped(&bomb, 1 << 20).unwrap_err();
        assert!(err.contains("exceeds cap"), "got: {err}");
    }

    #[test]
    fn garbage_input_errors_never_panics() {
        assert!(decompress_capped(b"not zstd at all", 1024).is_err());
        assert!(decompress_capped(&[], 1024).is_err());
    }
}
```

And in `crates/leanr_build/src/lib.rs`, add to the module list:

```rust
pub mod remote;
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p leanr_build remote::`
Expected: 4 passed. (These pass on first implementation since test and code land together; the failing-first checkpoint here is Step 2's build, which fails until `cargo add` and the module exist. If you want a strict red first: create the file with only the tests and `todo!()` bodies, watch them fail, then fill the bodies.)

- [ ] **Step 5: Lint and commit**

```bash
mise run fmt && mise run lint && cargo test -p leanr_build
git add crates/leanr_build/Cargo.toml crates/leanr_build/src/remote.rs crates/leanr_build/src/lib.rs Cargo.lock deny.toml
git commit -m "feat(build): remote cache wire keys + capped zstd (M2d core); deps ureq/zstd/rusty-s3"
```

---

### Task 2: `Cache::insert_manifest` + crate-visible `shard`/`is_blob_key`

**Files:**
- Modify: `crates/leanr_build/src/cache.rs`

**Interfaces:**
- Produces: `Cache::insert_manifest(&self, fp: &str, manifest: &Manifest) -> std::io::Result<()>` (atomic, read-only, blobs-first ordering is the CALLER's contract); `pub(crate) fn shard(hex: &str) -> &str`; `pub(crate) fn is_blob_key(s: &str) -> bool`. Consumed by Task 4 (`fetch` writes the downloaded manifest; validates wire blob hex with `is_blob_key`).
- Consumes: existing `write_atomic_readonly`, `manifest_path`.

- [ ] **Step 1: Write the failing tests** — append to `cache.rs`'s `mod tests`:

```rust
    #[test]
    fn insert_manifest_roundtrips_via_lookup() {
        let (_t, c) = cache();
        // A manifest whose blob actually exists (lookup self-heals
        // otherwise), constructed externally — the remote-ingest path.
        let blob = c.store_blob(b"downloaded-bytes").unwrap();
        let m = Manifest {
            artifacts: vec![ArtifactEntry {
                name: "A.olean".into(),
                blob,
            }],
        };
        c.insert_manifest("feed", &m).unwrap();
        assert_eq!(c.lookup("feed").unwrap().unwrap(), m);
        // Atomic-write hygiene: the manifest file is read-only.
        assert!(std::fs::metadata(c.manifest_path("feed"))
            .unwrap()
            .permissions()
            .readonly());
    }

    #[test]
    fn is_blob_key_accepts_only_64_lowercase_hex() {
        assert!(is_blob_key(&"a".repeat(64)));
        assert!(!is_blob_key(&"A".repeat(64)));
        assert!(!is_blob_key(&"a".repeat(63)));
        assert!(!is_blob_key("../../../../etc/passwd"));
        assert!(!is_blob_key(""));
    }
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build cache::tests::insert_manifest -- --nocapture`
Expected: FAIL — `no method named insert_manifest`.

- [ ] **Step 3: Implement** — in `cache.rs`:

Change the two fn signatures (no body changes):

```rust
pub(crate) fn shard(hex: &str) -> &str {
```

```rust
pub(crate) fn is_blob_key(s: &str) -> bool {
```

Add inside the first `impl Cache` block, after `insert`:

```rust
    /// Store an externally-constructed manifest (the remote-ingest path:
    /// `remote::RemoteCache::fetch` downloads blobs, verifies each
    /// against its content key, `store_blob`s them, THEN calls this —
    /// blobs-first ordering keeps a crash self-healing via `lookup`).
    pub fn insert_manifest(&self, fp: &str, manifest: &Manifest) -> std::io::Result<()> {
        let json = serde_json::to_vec(manifest).expect("manifest serializes");
        write_atomic_readonly(&self.manifest_path(fp), &json)
    }
```

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_build cache::`
Expected: all pass (including the two new ones).

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint
git add crates/leanr_build/src/cache.rs
git commit -m "feat(build): Cache::insert_manifest for remote ingest; crate-visible shard/is_blob_key"
```

---

### Task 3: Hermetic test HTTP server (`tests/support/httpd.rs`) + example wrapper

**Files:**
- Create: `crates/leanr_build/tests/support/httpd.rs`
- Create: `crates/leanr_build/examples/cas_httpd.rs`
- Create: `crates/leanr_build/tests/cache_remote.rs` (server smoke tests only; grows in later tasks)

**Interfaces:**
- Produces: `httpd::Server { pub addr: std::net::SocketAddr }`, `httpd::spawn(root: std::path::PathBuf) -> Server` — serves `root` over GET/HEAD (200/404) and accepts PUT (creating parent dirs), stripping query strings (presigned URLs carry `?X-Amz-...`), rejecting `..` traversal, one request per connection (`Connection: close`). Consumed by every later test task and (via the example) the acceptance script.
- Consumes: nothing from the crate — std only, so the example binary needs no feature gymnastics.

**Design note:** this is TEST INFRASTRUCTURE, deliberately minimal — no keep-alive, no chunked encoding, no TLS. ureq copes with `Connection: close` by reconnecting. It must be correct about the four things the tests rely on: body bytes, status codes, query-string stripping, and traversal rejection.

- [ ] **Step 1: Write the server** — `crates/leanr_build/tests/support/httpd.rs`:

```rust
//! Test-only static HTTP server over std::net (M2d spec §Testing): GET/
//! HEAD serve files under a root dir, PUT writes them (creating parent
//! dirs) — enough to stand in for a dumb HTTP host + S3 PUT endpoint in
//! hermetic tests and the acceptance script. One request per connection
//! (`Connection: close`); query strings (presigned-URL auth params) are
//! ignored; `..`/`.` path segments are rejected.

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::{Path, PathBuf};

pub struct Server {
    pub addr: SocketAddr,
}

pub fn spawn(root: PathBuf) -> Server {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind test server");
    let addr = listener.local_addr().unwrap();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(stream) = stream else { continue };
            let root = root.clone();
            std::thread::spawn(move || {
                let _ = handle(stream, &root);
            });
        }
    });
    Server { addr }
}

fn handle(mut stream: TcpStream, root: &Path) -> std::io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut request_line = String::new();
    reader.read_line(&mut request_line)?;
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("").to_string();
    let target = parts.next().unwrap_or("").to_string();
    let mut content_len = 0usize;
    loop {
        let mut h = String::new();
        if reader.read_line(&mut h)? == 0 {
            break;
        }
        if h == "\r\n" || h == "\n" {
            break;
        }
        if let Some(v) = h.to_ascii_lowercase().strip_prefix("content-length:") {
            content_len = v.trim().parse().unwrap_or(0);
        }
    }
    // Presigned URLs carry `?X-Amz-Signature=...` — the static server
    // ignores auth entirely; the path IS the object identity.
    let path_part = target.split('?').next().unwrap_or("");
    let Some(fs_path) = sanitize(root, path_part) else {
        return respond(&mut stream, "400 Bad Request", None, 0);
    };
    match method.as_str() {
        "GET" => match std::fs::read(&fs_path) {
            Ok(body) => {
                let len = body.len();
                respond(&mut stream, "200 OK", Some(&body), len)
            }
            Err(_) => respond(&mut stream, "404 Not Found", None, 0),
        },
        "HEAD" => match std::fs::metadata(&fs_path) {
            Ok(meta) if meta.is_file() => {
                respond(&mut stream, "200 OK", None, meta.len() as usize)
            }
            _ => respond(&mut stream, "404 Not Found", None, 0),
        },
        "PUT" => {
            let mut body = vec![0u8; content_len];
            reader.read_exact(&mut body)?;
            if let Some(parent) = fs_path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(&fs_path, &body)?;
            respond(&mut stream, "200 OK", None, 0)
        }
        _ => respond(&mut stream, "405 Method Not Allowed", None, 0),
    }
}

/// Root-joined path from URL segments; `None` on any `.`/`..`/empty-path
/// funny business (traversal defense — this serves real temp dirs).
fn sanitize(root: &Path, target: &str) -> Option<PathBuf> {
    let mut p = root.to_path_buf();
    let mut any = false;
    for seg in target.split('/').filter(|s| !s.is_empty()) {
        if seg == "." || seg == ".." || seg.contains('\\') {
            return None;
        }
        p.push(seg);
        any = true;
    }
    if any {
        Some(p)
    } else {
        None
    }
}

fn respond(
    stream: &mut TcpStream,
    status: &str,
    body: Option<&[u8]>,
    content_len: usize,
) -> std::io::Result<()> {
    write!(
        stream,
        "HTTP/1.1 {status}\r\nContent-Length: {content_len}\r\nConnection: close\r\n\r\n"
    )?;
    if let Some(b) = body {
        stream.write_all(b)?;
    }
    stream.flush()
}
```

- [ ] **Step 2: Write the example wrapper** — `crates/leanr_build/examples/cas_httpd.rs`:

```rust
//! Dev/acceptance-only static CAS server (M2d spec §Testing, recorded
//! acceptance run). NOT a shipped server component — the spec rejects
//! one; this is the same test-support httpd exposed as a binary so
//! scripts/remote-cache-acceptance.sh can serve a pushed CAS tree.
//! Usage: cargo run -p leanr_build --example cas_httpd -- <root-dir>
//! Prints the bound `host:port` on stdout, then serves until killed.

#[path = "../tests/support/httpd.rs"]
mod httpd;

fn main() {
    let root = std::env::args()
        .nth(1)
        .expect("usage: cas_httpd <root-dir>");
    let srv = httpd::spawn(std::path::PathBuf::from(root));
    println!("{}", srv.addr);
    loop {
        std::thread::park();
    }
}
```

- [ ] **Step 3: Write the smoke tests** — create `crates/leanr_build/tests/cache_remote.rs`:

```rust
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
    let (head, _) = raw_request(srv.addr, "HEAD /v1/blobs/aa/deadbeef HTTP/1.1\r\nHost: t\r\n\r\n", b"");
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
```

- [ ] **Step 4: Run the tests and the example**

Run: `cargo test -p leanr_build --test cache_remote`
Expected: 2 passed.

Run: `cargo build -p leanr_build --example cas_httpd`
Expected: builds clean (don't run it — it parks forever).

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint
git add crates/leanr_build/tests/support/httpd.rs crates/leanr_build/examples/cas_httpd.rs crates/leanr_build/tests/cache_remote.rs
git commit -m "test(build): hermetic static GET/HEAD/PUT server for the M2d remote gate + cas_httpd example"
```

---

### Task 4: `RemoteCache::fetch` — read-through ingest with verification

**Files:**
- Modify: `crates/leanr_build/src/remote.rs`
- Test: `crates/leanr_build/tests/cache_remote.rs`

**Interfaces:**
- Produces:
  - `remote::WarnFn = Box<dyn Fn(&str) + Send + Sync>`
  - `remote::RemoteCache` with `RemoteCache::new(base_url: &str, warn: WarnFn) -> RemoteCache` and `fetch(&self, cache: &crate::cache::Cache, fp: &str) -> FetchOutcome`
  - `remote::FetchOutcome { Hit { downloaded_blobs: usize }, Miss, Degraded }` (derive `Debug, PartialEq`)
  - `RemoteCache` must be `Send + Sync` (shared by pool worker threads in Task 5).
- Consumes: `cache::Cache::{blob_path, store_blob, insert_manifest}`, `cache::is_blob_key` (Task 2), `remote_manifest_key`/`remote_blob_key`/`decompress_capped`/caps (Task 1), `httpd` (Task 3, tests).

**ureq API note (not a placeholder — an external-crate check):** the code below targets ureq 3.x. Before implementing, open https://docs.rs/ureq (the resolved version) and confirm the three touchpoints: (a) building an `Agent` with a connect timeout and **statuses-not-errors** config, (b) `agent.get(url).call()` return shape, (c) reading a response body with a byte limit. If names drifted, adapt the code — the behavioral contract is pinned by the tests, not by these identifiers.

- [ ] **Step 1: Write the failing tests** — append to `tests/cache_remote.rs`:

```rust
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
    let rc = RemoteCache::new(base, Box::new(move |m| w.lock().unwrap().push(m.to_string())));
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
    let expected = publish(&served, FP, &[("A.olean", b"olean-bytes"), ("A.ilean", b"ilean-bytes")]);
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    let (rc, warnings) = remote_with_warnings(&format!("http://{}", srv.addr));
    let out = rc.fetch(&cache, FP);
    assert_eq!(out, FetchOutcome::Hit { downloaded_blobs: 2 });
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
    assert!(warnings.lock().unwrap().is_empty(), "404 is normal, not warned");
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
    assert_eq!(rc.fetch(&cache, FP), FetchOutcome::Hit { downloaded_blobs: 0 });
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
    assert!(!cache.blob_path(&m.artifacts[0].blob).exists(), "no unverified blob stored");
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
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build --test cache_remote`
Expected: FAIL to compile — `RemoteCache` etc. not found.

- [ ] **Step 3: Implement** — append to `crates/leanr_build/src/remote.rs`:

```rust
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
                (self.warn)(&format!("remote cache: HTTP {s} fetching manifest for {fp}"));
                return FetchOutcome::Degraded;
            }
            Err(GetError::TooLarge) => {
                (self.warn)(&format!("remote cache: manifest for {fp} exceeds {MAX_MANIFEST_BYTES} bytes — rejected"));
                return FetchOutcome::Degraded;
            }
        };
        // Untrusted-bytes discipline: malformed wire manifest is a warned
        // degrade, never a panic; hostile `blob` strings never reach a
        // filesystem path (is_blob_key gates them).
        let manifest: Manifest = match serde_json::from_slice(&mbytes) {
            Ok(m) => m,
            Err(_) => {
                (self.warn)(&format!("remote cache: malformed manifest for {fp} — rejected"));
                return FetchOutcome::Degraded;
            }
        };
        if manifest
            .artifacts
            .iter()
            .any(|a| !crate::cache::is_blob_key(&a.blob))
        {
            (self.warn)(&format!("remote cache: manifest for {fp} names an invalid blob key — rejected"));
            return FetchOutcome::Degraded;
        }
        let mut downloaded = 0usize;
        for entry in &manifest.artifacts {
            if cache.blob_path(&entry.blob).exists() {
                continue; // wire-level dedup (spec §Scope decisions)
            }
            let compressed = match self.get_capped(&remote_blob_key(&entry.blob), MAX_ARTIFACT_BYTES) {
                Ok(Some(b)) => b,
                Ok(None) => {
                    (self.warn)(&format!("remote cache: manifest for {fp} references missing blob {} — degraded", entry.blob));
                    return FetchOutcome::Degraded;
                }
                Err(GetError::Transport(e)) => {
                    self.trip(&e);
                    return FetchOutcome::Degraded;
                }
                Err(GetError::Status(s)) => {
                    (self.warn)(&format!("remote cache: HTTP {s} fetching blob {}", entry.blob));
                    return FetchOutcome::Degraded;
                }
                Err(GetError::TooLarge) => {
                    (self.warn)(&format!("remote cache: blob {} exceeds {MAX_ARTIFACT_BYTES} bytes — rejected", entry.blob));
                    return FetchOutcome::Degraded;
                }
            };
            let bytes = match decompress_capped(&compressed, MAX_ARTIFACT_BYTES) {
                Ok(b) => b,
                Err(e) => {
                    (self.warn)(&format!("remote cache: blob {} failed decompression ({e}) — rejected", entry.blob));
                    return FetchOutcome::Degraded;
                }
            };
            // THE ingestion choke point (spec §Threat model touch).
            if blake3::hash(&bytes).to_hex().to_string() != entry.blob {
                (self.warn)(&format!("remote cache: blob {} failed hash verification — rejected", entry.blob));
                return FetchOutcome::Degraded;
            }
            if let Err(e) = cache.store_blob(&bytes) {
                (self.warn)(&format!("remote cache: storing blob {} failed ({e})", entry.blob));
                return FetchOutcome::Degraded;
            }
            downloaded += 1;
        }
        // Blobs first, manifest last (crash-safe with lookup self-healing).
        if let Err(e) = cache.insert_manifest(fp, &manifest) {
            (self.warn)(&format!("remote cache: storing manifest for {fp} failed ({e})"));
            return FetchOutcome::Degraded;
        }
        FetchOutcome::Hit {
            downloaded_blobs: downloaded,
        }
    }
}
```

Also add `blake3` usage — already a dep. Add `tempfile`/`blake3` to `[dev-dependencies]`? Both already present (`blake3` is a main dep, `tempfile` a dev dep). The integration test also uses `serde_json` — already a main dep, but integration tests need it as a dev-dep too; add if missing:

```bash
cd /workspace/crates/leanr_build && cargo add --dev serde_json blake3
```

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_build --test cache_remote && cargo test -p leanr_build remote::`
Expected: all pass (7 integration + 4 unit).

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint && cargo test -p leanr_build
git add crates/leanr_build/src/remote.rs crates/leanr_build/tests/cache_remote.rs crates/leanr_build/Cargo.toml Cargo.lock
git commit -m "feat(build): RemoteCache::fetch — verified read-through ingest with circuit breaker (M2d)"
```

---

### Task 5: Build integration — the one new tier in the job body

**Files:**
- Modify: `crates/leanr_build/src/compile.rs`
- Modify: `crates/leanr_build/tests/cache_incremental.rs` (one-line: `remote: None` in its `BuildOptions`)
- Test: `crates/leanr_build/tests/cache_remote.rs`

**Interfaces:**
- Produces: `BuildOptions.remote: Option<crate::remote::RemoteCache>`; `BuiltEvent.downloaded: bool`; `BuildReport.downloaded: usize`. Consumed by Task 8 (CLI).
- Consumes: `RemoteCache::fetch` / `FetchOutcome` (Task 4).
- Semantics: remote is consulted ONLY on a local miss, ONLY when `cache` is `Some` and `force` is false. `--no-cache` (cache `None`) therefore implies no remote regardless of the field. A `Downloaded` module is one materialized after a successful remote fetch; `Cached` stays local-hit-only.

- [ ] **Step 1: Write the failing tests** — append to `tests/cache_remote.rs`:

```rust
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
    write(dir, "lake-manifest.json", r#"{"version": "1.2.0", "packages": []}"#);
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
    std::fs::read_to_string(log).unwrap_or_default().lines().count()
}

/// Publish machine A's whole local CAS into a served-root dir in the
/// wire layout (compressed blobs, plain manifests). Stand-in for `push`
/// until Task 6; kept afterward as an independent publisher so the
/// fetch tests don't depend on push being correct.
fn publish_cas(xdg: &Path, ws: &Workspace, served: &Path) {
    let cache = Cache::new(xdg);
    let fps = fingerprint_all(ws, &fp_env()).unwrap();
    for fp in &fps {
        let Some(m) = cache.lookup(fp).unwrap() else { continue };
        for e in &m.artifacts {
            let dst = served.join(remote_blob_key(&e.blob));
            std::fs::create_dir_all(dst.parent().unwrap()).unwrap();
            std::fs::write(dst, compress(&std::fs::read(cache.blob_path(&e.blob)).unwrap())).unwrap();
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
    assert!(warnings.lock().unwrap().is_empty(), "remote never consulted");
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build --test cache_remote`
Expected: FAIL to compile — `BuildOptions` has no field `remote`, `BuildReport` no field `downloaded`.

- [ ] **Step 3: Implement** — in `crates/leanr_build/src/compile.rs`:

Add to `BuildOptions` (after `fp_env`):

```rust
    /// Remote read tier (M2d): consulted only on a local cache miss,
    /// only when `cache` is Some and `force` is false. `None` = local-only.
    pub remote: Option<crate::remote::RemoteCache>,
```

Add to `BuiltEvent` (after `cached`):

```rust
    /// True when this module's artifacts were downloaded from the remote
    /// cache this run (then materialized from the local store).
    pub downloaded: bool,
```

Change `BuildReport`:

```rust
#[derive(Debug)]
pub struct BuildReport {
    pub built: usize,
    pub cached: usize,
    pub downloaded: usize,
}
```

Extend the `Outcome` enum inside `build_workspace`:

```rust
    #[derive(Clone, Copy, PartialEq)]
    enum Outcome {
        Built,
        Cached,
        Downloaded,
    }
```

Replace the cache-lookup block in the job closure (the `if let (Some(cache), Some(fps)) = ... if !opts.force { match cache.lookup(...) }` section) with:

```rust
        if let (Some(cache), Some(fps)) = (opts.cache.as_ref(), fps.as_ref()) {
            if !opts.force {
                let mut hit = match cache.lookup(&fps[i]) {
                    Ok(m) => m.map(|m| (m, Outcome::Cached)),
                    Err(e) => return Err(format!("cache lookup failed: {e}")),
                };
                // M2d read-through tier: local miss → remote fetch →
                // re-lookup. Every fetch failure mode is a miss (remote
                // availability never affects build success).
                if hit.is_none() {
                    if let Some(remote) = &opts.remote {
                        if let crate::remote::FetchOutcome::Hit { .. } =
                            remote.fetch(cache, &fps[i])
                        {
                            hit = match cache.lookup(&fps[i]) {
                                Ok(m) => m.map(|m| (m, Outcome::Downloaded)),
                                Err(e) => return Err(format!("cache lookup failed: {e}")),
                            };
                        }
                    }
                }
                if let Some((manifest, outcome)) = hit {
                    if let Err(e) = cache.materialize(&manifest, &dests) {
                        cleanup();
                        return Err(format!("cache materialize failed: {e}"));
                    }
                    outcomes.lock().unwrap()[i] = outcome;
                    results.lock().unwrap()[i] = Some((0.0, String::new()));
                    return Ok(());
                }
            }
        }
```

In `on_done`, replace the `cached` line with:

```rust
        let outcome = outcomes.lock().unwrap()[i];
        let cached = outcome == Outcome::Cached;
        let downloaded = outcome == Outcome::Downloaded;
```

and pass `downloaded` in the `BuiltEvent { ... }` literal.

Replace the final report construction:

```rust
    Ok(BuildReport {
        built: outs.iter().filter(|o| **o == Outcome::Built).count(),
        cached: outs.iter().filter(|o| **o == Outcome::Cached).count(),
        downloaded: outs.iter().filter(|o| **o == Outcome::Downloaded).count(),
    })
```

Fix the two existing construction sites that now miss the field: the `opts()` helper in `compile.rs`'s `mod tests` and `build_counting_with_env` in `tests/cache_incremental.rs` — add `remote: None,` to each `BuildOptions { ... }` literal.

- [ ] **Step 4: Run the full crate tests**

Run: `cargo test -p leanr_build`
Expected: everything passes — the four new tests, all of `cache_incremental`, all of `compile::tests`.

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint
git add crates/leanr_build/src/compile.rs crates/leanr_build/tests/cache_remote.rs crates/leanr_build/tests/cache_incremental.rs
git commit -m "feat(build): remote read-through tier in the build job body; BuildReport.downloaded"
```

---

### Task 6: `Pusher` — S3-presigned upload

**Files:**
- Modify: `crates/leanr_build/src/remote.rs`
- Test: `crates/leanr_build/tests/cache_remote.rs`

**Interfaces:**
- Produces:
  - `remote::Pusher` with `Pusher::from_env(to: &str) -> Result<Pusher, String>` (`to` = `s3://bucket[/prefix]`; reads `AWS_ENDPOINT_URL` [default `https://s3.<region>.amazonaws.com`], `AWS_REGION`/`AWS_DEFAULT_REGION` [default `us-east-1`], `AWS_ACCESS_KEY_ID` + `AWS_SECRET_ACCESS_KEY` [required — error names the missing var]) and `push(&self, cache: &Cache, fps: &[String], jobs: usize) -> Result<PushReport, String>`
  - `remote::PushReport { manifests_pushed: usize, manifests_skipped: usize, blobs_pushed: usize, bytes_uploaded: u64 }` (derive `Debug`)
  - For testability, split env reading: `Pusher::from_parts(to: &str, endpoint: &str, region: &str, key_id: &str, secret: &str) -> Result<Pusher, String>`, with `from_env` a thin wrapper.
- Consumes: `Cache::{lookup, blob_path}`, `compress`, wire keys (Task 1), `httpd` (tests; its PUT/HEAD ignore the presigned query string).
- Semantics: per fp — no local manifest → skip silently (not built); remote manifest exists (HEAD 200) → `manifests_skipped`; else HEAD each blob, PUT missing ones compressed, PUT manifest LAST, count `manifests_pushed`. Any HTTP/transport error is a hard `Err` (spec: push failures are hard errors). Idempotent by construction.

**rusty-s3 API note:** targets rusty-s3 0.7.x: `Bucket::new(endpoint: Url, UrlStyle::Path, name, region)`, `Credentials::new(key, secret)`, `bucket.put_object(Some(&creds), key).sign(Duration)` / `bucket.head_object(Some(&creds), key).sign(Duration)` → presigned `Url`. Confirm on docs.rs for the resolved version; the tests pin behavior.

- [ ] **Step 1: Write the failing tests** — append to `tests/cache_remote.rs`:

```rust
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
    assert_eq!((r1.manifests_pushed, r1.manifests_skipped, r1.blobs_pushed), (1, 0, 1));
    assert!(r1.bytes_uploaded > 0);
    // Objects at s3-path-style locations: <bucket>/<prefix>/<wire key>.
    let blob_obj = served.join("cas/team").join(remote_blob_key(&m.artifacts[0].blob));
    let man_obj = served.join("cas/team").join(remote_manifest_key(FP));
    assert!(blob_obj.is_file(), "blob object exists: {}", blob_obj.display());
    assert!(man_obj.is_file(), "manifest object exists");
    // Blob object is compressed; decompresses to the original bytes.
    assert_eq!(
        leanr_build::remote::decompress_capped(&std::fs::read(&blob_obj).unwrap(), 1 << 20).unwrap(),
        b"olean-bytes"
    );
    // Manifest object is the plain local manifest JSON.
    let remote_m: Manifest = serde_json::from_slice(&std::fs::read(&man_obj).unwrap()).unwrap();
    assert_eq!(remote_m, m);
    // Second push: everything skipped, nothing uploaded.
    let r2 = p.push(&cache, &[FP.to_string()], 2).unwrap();
    assert_eq!((r2.manifests_pushed, r2.manifests_skipped, r2.blobs_pushed), (0, 1, 0));
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
    test_pusher(srv.addr).push(&cache_a, &[FP.to_string()], 1).unwrap();

    // Reads go through the plain-GET base under the same bucket path.
    let cache_b = Cache::new(&tmp.path().join("xdg-b"));
    let (rc, _) = remote_with_warnings(&format!("http://{}/cas/team", srv.addr));
    assert_eq!(rc.fetch(&cache_b, FP), FetchOutcome::Hit { downloaded_blobs: 1 });
    let got = cache_b.lookup(FP).unwrap().unwrap();
    assert_eq!(
        std::fs::read(cache_b.blob_path(&got.artifacts[0].blob)).unwrap(),
        b"roundtrip-bytes"
    );
}

#[test]
fn pusher_from_parts_rejects_bad_targets() {
    assert!(Pusher::from_parts("http://not-s3", "http://e", "r", "k", "s")
        .unwrap_err()
        .contains("s3://"));
    assert!(Pusher::from_parts("s3://", "http://e", "r", "k", "s").is_err());
}

#[test]
fn push_skips_fps_with_no_local_manifest() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    std::fs::create_dir_all(&served).unwrap();
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    let r = test_pusher(srv.addr).push(&cache, &[FP.to_string()], 1).unwrap();
    assert_eq!((r.manifests_pushed, r.manifests_skipped, r.blobs_pushed), (0, 0, 0));
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build --test cache_remote push`
Expected: FAIL to compile — no `Pusher`.

- [ ] **Step 3: Implement** — append to `remote.rs`:

```rust
/// Explicit upload tier (spec §Scope decisions: push is explicit, CI-
/// side; developer machines never upload implicitly). Presigned sigv4
/// PUT/HEAD via rusty-s3 — works against AWS S3, R2, GCS interop, MinIO,
/// and the test httpd (which ignores the auth query params).
pub struct Pusher {
    bucket: rusty_s3::Bucket,
    creds: rusty_s3::Credentials,
    /// Object-key prefix inside the bucket ("" or "team/").
    prefix: String,
    agent: ureq::Agent,
}

#[derive(Debug)]
pub struct PushReport {
    pub manifests_pushed: usize,
    pub manifests_skipped: usize,
    pub blobs_pushed: usize,
    pub bytes_uploaded: u64,
}

const SIGN_TTL: std::time::Duration = std::time::Duration::from_secs(3600);

impl Pusher {
    /// `to` = `s3://bucket[/prefix]`; endpoint/region/credentials from
    /// the standard AWS env vars (spec §Wire layout & protocol).
    pub fn from_env(to: &str) -> Result<Pusher, String> {
        let region = std::env::var("AWS_REGION")
            .or_else(|_| std::env::var("AWS_DEFAULT_REGION"))
            .unwrap_or_else(|_| "us-east-1".to_string());
        let endpoint = std::env::var("AWS_ENDPOINT_URL")
            .unwrap_or_else(|_| format!("https://s3.{region}.amazonaws.com"));
        let key_id = std::env::var("AWS_ACCESS_KEY_ID")
            .map_err(|_| "AWS_ACCESS_KEY_ID not set (required for cache push)".to_string())?;
        let secret = std::env::var("AWS_SECRET_ACCESS_KEY")
            .map_err(|_| "AWS_SECRET_ACCESS_KEY not set (required for cache push)".to_string())?;
        Pusher::from_parts(to, &endpoint, &region, &key_id, &secret)
    }

    pub fn from_parts(
        to: &str,
        endpoint: &str,
        region: &str,
        key_id: &str,
        secret: &str,
    ) -> Result<Pusher, String> {
        let rest = to
            .strip_prefix("s3://")
            .ok_or_else(|| format!("push target must be s3://bucket[/prefix], got `{to}`"))?;
        let (bucket_name, prefix) = match rest.split_once('/') {
            Some((b, p)) => (b, format!("{}/", p.trim_matches('/'))),
            None => (rest, String::new()),
        };
        if bucket_name.is_empty() {
            return Err(format!("push target must name a bucket, got `{to}`"));
        }
        let endpoint: url::Url = endpoint
            .parse()
            .map_err(|e| format!("bad endpoint `{endpoint}`: {e}"))?;
        let bucket = rusty_s3::Bucket::new(
            endpoint,
            rusty_s3::UrlStyle::Path,
            bucket_name.to_string(),
            region.to_string(),
        )
        .map_err(|e| format!("bad bucket `{bucket_name}`: {e}"))?;
        let config = ureq::Agent::config_builder()
            .timeout_connect(Some(std::time::Duration::from_secs(10)))
            .http_status_as_error(false)
            .build();
        Ok(Pusher {
            bucket,
            creds: rusty_s3::Credentials::new(key_id, secret),
            prefix,
            agent: config.new_agent(),
        })
    }

    fn head(&self, key: &str) -> Result<bool, String> {
        use rusty_s3::S3Action;
        let url = self
            .bucket
            .head_object(Some(&self.creds), &format!("{}{key}", self.prefix))
            .sign(SIGN_TTL);
        let resp = self
            .agent
            .head(url.as_str())
            .call()
            .map_err(|e| format!("HEAD {key}: {e}"))?;
        match resp.status().as_u16() {
            200 => Ok(true),
            404 => Ok(false),
            s => Err(format!("HEAD {key}: HTTP {s}")),
        }
    }

    fn put(&self, key: &str, bytes: &[u8]) -> Result<(), String> {
        use rusty_s3::S3Action;
        let url = self
            .bucket
            .put_object(Some(&self.creds), &format!("{}{key}", self.prefix))
            .sign(SIGN_TTL);
        let resp = self
            .agent
            .put(url.as_str())
            .send(bytes)
            .map_err(|e| format!("PUT {key}: {e}"))?;
        match resp.status().as_u16() {
            200 | 201 | 204 => Ok(()),
            s => Err(format!("PUT {key}: HTTP {s}")),
        }
    }

    /// Upload every locally-cached (fp → manifest) the remote lacks:
    /// HEAD manifest → skip if present; else HEAD+PUT missing blobs
    /// (compressed), then PUT the manifest LAST (spec §Wire layout:
    /// blobs before manifest). Push failures are HARD errors.
    pub fn push(&self, cache: &Cache, fps: &[String], jobs: usize) -> Result<PushReport, String> {
        use std::sync::atomic::AtomicUsize;
        use std::sync::Mutex;
        let idx = AtomicUsize::new(0);
        let report = Mutex::new(PushReport {
            manifests_pushed: 0,
            manifests_skipped: 0,
            blobs_pushed: 0,
            bytes_uploaded: 0,
        });
        let first_err: Mutex<Option<String>> = Mutex::new(None);
        std::thread::scope(|s| {
            for _ in 0..jobs.max(1) {
                s.spawn(|| loop {
                    if first_err.lock().unwrap().is_some() {
                        return;
                    }
                    let i = idx.fetch_add(1, Ordering::SeqCst);
                    let Some(fp) = fps.get(i) else { return };
                    if let Err(e) = self.push_one(cache, fp, &report) {
                        *first_err.lock().unwrap() = Some(e);
                        return;
                    }
                });
            }
        });
        if let Some(e) = first_err.into_inner().unwrap() {
            return Err(e);
        }
        Ok(report.into_inner().unwrap())
    }

    fn push_one(
        &self,
        cache: &Cache,
        fp: &str,
        report: &std::sync::Mutex<PushReport>,
    ) -> Result<(), String> {
        let Some(manifest) = cache.lookup(fp).map_err(|e| format!("lookup {fp}: {e}"))? else {
            return Ok(()); // not built locally — nothing to publish
        };
        if self.head(&remote_manifest_key(fp))? {
            report.lock().unwrap().manifests_skipped += 1;
            return Ok(());
        }
        for entry in &manifest.artifacts {
            let key = remote_blob_key(&entry.blob);
            if self.head(&key)? {
                continue;
            }
            let bytes = std::fs::read(cache.blob_path(&entry.blob))
                .map_err(|e| format!("read blob {}: {e}", entry.blob))?;
            let compressed = compress(&bytes);
            self.put(&key, &compressed)?;
            let mut r = report.lock().unwrap();
            r.blobs_pushed += 1;
            r.bytes_uploaded += compressed.len() as u64;
        }
        let json = serde_json::to_vec(&manifest).expect("manifest serializes");
        self.put(&remote_manifest_key(fp), &json)?;
        let mut r = report.lock().unwrap();
        r.manifests_pushed += 1;
        r.bytes_uploaded += json.len() as u64;
        Ok(())
    }
}
```

`url` is a transitive dep of rusty-s3; add it explicitly since we name its type: `cargo add url` in `crates/leanr_build` (tiny, already in-tree transitively).

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_build --test cache_remote`
Expected: all pass, including `push_then_fetch_roundtrips_end_to_end`.

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint && cargo test -p leanr_build
git add crates/leanr_build/src/remote.rs crates/leanr_build/tests/cache_remote.rs crates/leanr_build/Cargo.toml Cargo.lock
git commit -m "feat(build): Pusher — presigned S3 upload of the local CAS (blobs first, manifest last)"
```

---

### Task 7: `get_all` — batch prefetch driver

**Files:**
- Modify: `crates/leanr_build/src/remote.rs`
- Test: `crates/leanr_build/tests/cache_remote.rs`

**Interfaces:**
- Produces: `remote::get_all(cache: &Cache, remote: &RemoteCache, fps: &[String], jobs: usize) -> GetReport`; `remote::GetReport { fetched: usize, already_local: usize, missing: usize, failed: usize }` (derive `Debug, PartialEq`). Consumed by Task 8 (`leanr cache get`; CLI exits nonzero when `failed > 0`).
- Consumes: `RemoteCache::fetch`, `Cache::lookup`.
- Caller contract: pass DEDUPED fps (CLI sorts+dedups; identical-content modules can share an fp).

- [ ] **Step 1: Write the failing tests** — append to `tests/cache_remote.rs`:

```rust
use leanr_build::remote::{get_all, GetReport};

#[test]
fn get_all_prefetches_misses_and_counts_outcomes() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    let fp_remote = FP; // published below
    let fp_local = "2222222222222222222222222222222222222222222222222222222222222222";
    let fp_absent = "3333333333333333333333333333333333333333333333333333333333333333";
    publish(&served, fp_remote, &[("A.olean", b"remote-bytes")]);
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    let local_art = tmp.path().join("L.olean");
    std::fs::write(&local_art, b"local-bytes").unwrap();
    cache.insert(fp_local, &[local_art]).unwrap();
    let (rc, _) = remote_with_warnings(&format!("http://{}", srv.addr));
    let r = get_all(
        &cache,
        &rc,
        &[fp_remote.to_string(), fp_local.to_string(), fp_absent.to_string()],
        4,
    );
    assert_eq!(
        r,
        GetReport { fetched: 1, already_local: 1, missing: 1, failed: 0 }
    );
    assert!(cache.lookup(fp_remote).unwrap().is_some(), "prefetched into local CAS");
    // Second run: everything already local except the truly absent fp.
    let r2 = get_all(&cache, &rc, &[fp_remote.to_string(), fp_local.to_string()], 4);
    assert_eq!(r2, GetReport { fetched: 0, already_local: 2, missing: 0, failed: 0 });
}

#[test]
fn get_all_counts_degraded_as_failed() {
    let tmp = tempfile::TempDir::new().unwrap();
    let served = tmp.path().join("served");
    let mp = served.join(remote_manifest_key(FP));
    std::fs::create_dir_all(mp.parent().unwrap()).unwrap();
    std::fs::write(&mp, b"{ not json").unwrap();
    let srv = httpd::spawn(served);
    let cache = Cache::new(&tmp.path().join("xdg"));
    let (rc, _) = remote_with_warnings(&format!("http://{}", srv.addr));
    let r = get_all(&cache, &rc, &[FP.to_string()], 1);
    assert_eq!(r, GetReport { fetched: 0, already_local: 0, missing: 0, failed: 1 });
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build --test cache_remote get_all`
Expected: FAIL to compile — no `get_all`.

- [ ] **Step 3: Implement** — append to `remote.rs`:

```rust
#[derive(Debug, PartialEq)]
pub struct GetReport {
    pub fetched: usize,
    pub already_local: usize,
    pub missing: usize,
    pub failed: usize,
}

/// Batch prefetch (spec §Commands: `leanr cache get`): fetch every fp
/// not already a local hit, over `jobs` worker threads. Callers pass
/// deduped fps. Failures don't abort the batch — they're counted, and
/// the CLI turns `failed > 0` into a nonzero exit (fetching is get's
/// whole job).
pub fn get_all(cache: &Cache, remote: &RemoteCache, fps: &[String], jobs: usize) -> GetReport {
    use std::sync::atomic::AtomicUsize;
    let idx = AtomicUsize::new(0);
    let (fetched, already, missing, failed) = (
        AtomicUsize::new(0),
        AtomicUsize::new(0),
        AtomicUsize::new(0),
        AtomicUsize::new(0),
    );
    std::thread::scope(|s| {
        for _ in 0..jobs.max(1) {
            s.spawn(|| loop {
                let i = idx.fetch_add(1, Ordering::SeqCst);
                let Some(fp) = fps.get(i) else { return };
                match cache.lookup(fp) {
                    Ok(Some(_)) => {
                        already.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }
                    Ok(None) => {}
                    Err(_) => {
                        failed.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }
                }
                match remote.fetch(cache, fp) {
                    FetchOutcome::Hit { .. } => fetched.fetch_add(1, Ordering::Relaxed),
                    FetchOutcome::Miss => missing.fetch_add(1, Ordering::Relaxed),
                    FetchOutcome::Degraded => failed.fetch_add(1, Ordering::Relaxed),
                };
            });
        }
    });
    GetReport {
        fetched: fetched.into_inner(),
        already_local: already.into_inner(),
        missing: missing.into_inner(),
        failed: failed.into_inner(),
    }
}
```

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_build --test cache_remote`
Expected: all pass.

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint
git add crates/leanr_build/src/remote.rs crates/leanr_build/tests/cache_remote.rs
git commit -m "feat(build): get_all batch prefetch driver (leanr cache get backend)"
```

---

### Task 8: CLI wiring — `--remote`/`--no-remote`, `cache get`, `cache push`

**Files:**
- Modify: `crates/leanr_cli/src/main.rs`

**Interfaces:**
- Consumes: everything above — `RemoteCache::new`, `Pusher::from_env`, `get_all`, `BuildOptions.remote`, `BuildReport.downloaded`, `BuiltEvent.downloaded`, `fingerprint_all`.
- Produces (user-facing surface, spec §Commands):
  - `leanr build [--remote <url> | --no-remote]` (both conflict with each other; `--remote` also conflicts with `--no-cache`); env fallback `LEANR_REMOTE_CACHE`.
  - `leanr cache get [--remote <url>] [--dir] [--jobs] [--toolchain-dir]` — remote required (flag or env).
  - `leanr cache push --to s3://bucket[/prefix] [--dir] [--jobs] [--toolchain-dir]`.
  - Build lines gain a `(downloaded)` tag; summary becomes `built N modules (C cached, D downloaded) in ...` — the `^built 0 modules (` prefix greps in `scripts/build-fresh-acceptance.sh` keep matching.
- Pure helpers with unit tests (CLI logic stays declarative): `resolve_remote_url(flag: Option<String>, no_remote: bool, env_val: Option<String>) -> Option<String>`; extract the twice-duplicated `FingerprintEnv` construction into `fn fp_env_for(toolchain: &Option<String>) -> leanr_build::fingerprint::FingerprintEnv`.

- [ ] **Step 1: Write the failing unit tests** — append to `main.rs` (new `mod` next to `rel_display_tests`):

```rust
#[cfg(test)]
mod remote_url_tests {
    use super::resolve_remote_url;

    #[test]
    fn flag_wins_over_env() {
        assert_eq!(
            resolve_remote_url(Some("http://flag".into()), false, Some("http://env".into())),
            Some("http://flag".into())
        );
    }

    #[test]
    fn env_applies_when_no_flag() {
        assert_eq!(
            resolve_remote_url(None, false, Some("http://env".into())),
            Some("http://env".into())
        );
    }

    #[test]
    fn no_remote_forces_local_only_even_with_env() {
        assert_eq!(resolve_remote_url(None, true, Some("http://env".into())), None);
    }

    #[test]
    fn nothing_configured_is_none() {
        assert_eq!(resolve_remote_url(None, false, None), None);
    }
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_cli`
Expected: FAIL to compile — no `resolve_remote_url`.

- [ ] **Step 3: Implement.** All edits in `main.rs`:

(a) Helpers (place near `resolve_workspace`):

```rust
/// M2d remote-read config: `--remote` flag > `LEANR_REMOTE_CACHE` env;
/// `--no-remote` forces local-only without disturbing the environment.
fn resolve_remote_url(
    flag: Option<String>,
    no_remote: bool,
    env_val: Option<String>,
) -> Option<String> {
    if no_remote {
        return None;
    }
    flag.or(env_val)
}

fn fp_env_for(toolchain: &Option<String>) -> leanr_build::fingerprint::FingerprintEnv {
    leanr_build::fingerprint::FingerprintEnv {
        leanr_version: env!("CARGO_PKG_VERSION").to_string(),
        toolchain_id: toolchain.clone().unwrap_or_default(),
        platform: format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS),
    }
}

fn remote_cache_for(url: &str) -> leanr_build::remote::RemoteCache {
    leanr_build::remote::RemoteCache::new(url, Box::new(|msg| eprintln!("warning: {msg}")))
}

fn default_jobs(jobs: Option<usize>) -> usize {
    jobs.unwrap_or_else(|| {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    })
}
```

Replace the two existing inline `FingerprintEnv { ... }` constructions (in `build` and in `cache_cmd`'s `--deep` arm) with `fp_env_for(&toolchain_for_lean)` / `fp_env_for(&toolchain)`, and the two inline `jobs.unwrap_or_else(...)` blocks with `default_jobs(jobs)`.

(b) `Command::Build` gains:

```rust
        /// Remote cache URL to read through (env: LEANR_REMOTE_CACHE).
        #[arg(long, conflicts_with_all = ["no_cache", "no_remote"])]
        remote: Option<String>,
        /// Ignore any configured remote cache (local CAS only).
        #[arg(long)]
        no_remote: bool,
```

Thread both through `main()`'s match into `fn build(...)` (add the two parameters), and inside `build`'s `run` closure, after `cache` is computed:

```rust
        let remote = match &cache {
            Some(_) => resolve_remote_url(remote, no_remote, std::env::var("LEANR_REMOTE_CACHE").ok())
                .map(|url| remote_cache_for(&url)),
            None => None, // --no-cache bypasses everything, remote included
        };
```

and `remote` into `BuildOptions { ..., remote }`.

(c) Reporting in `build`: the per-module line adds the downloaded tag —

```rust
            let tag = if e.cached {
                " (cached)"
            } else if e.downloaded {
                " (downloaded)"
            } else {
                ""
            };
```

and the summary line becomes:

```rust
        println!(
            "built {} modules ({} cached, {} downloaded) in {:.1}s ({} jobs)",
            report.built,
            report.cached,
            report.downloaded,
            build_start.elapsed().as_secs_f64(),
            jobs
        );
```

(d) `CacheCommand` gains two variants:

```rust
    /// Prefetch the workspace's whole module closure from a remote cache
    /// into the local store (no lean, no materialization).
    Get {
        /// Remote cache URL (env: LEANR_REMOTE_CACHE).
        #[arg(long)]
        remote: Option<String>,
        /// Workspace dir (default: walk up from cwd).
        #[arg(long)]
        dir: Option<PathBuf>,
        /// Toolchain olean directory (default: `lean --print-libdir`).
        #[arg(long)]
        toolchain_dir: Option<PathBuf>,
        /// Download worker threads (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
    },
    /// Upload the workspace's locally-cached artifacts to an S3-compatible
    /// bucket (credentials via AWS_* env vars; CI-side, explicit only).
    Push {
        /// Target: s3://bucket[/prefix].
        #[arg(long)]
        to: String,
        /// Workspace dir (default: walk up from cwd).
        #[arg(long)]
        dir: Option<PathBuf>,
        /// Toolchain olean directory (default: `lean --print-libdir`).
        #[arg(long)]
        toolchain_dir: Option<PathBuf>,
        /// Upload worker threads (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
    },
```

(e) In `cache_cmd`'s match, add the two arms (note `resolve_workspace(dir, Vec::new(), toolchain_dir)` — same shape as `verify --deep` but honoring the explicit toolchain-dir flag; `resolve_workspace` already takes it):

```rust
            CacheCommand::Get {
                remote,
                dir,
                toolchain_dir,
                jobs,
            } => {
                let url = resolve_remote_url(remote, false, std::env::var("LEANR_REMOTE_CACHE").ok())
                    .ok_or_else(|| {
                        "no remote configured: pass --remote or set LEANR_REMOTE_CACHE".to_string()
                    })?;
                let (ws, toolchain) = resolve_workspace(dir, Vec::new(), toolchain_dir)?;
                let mut fps =
                    leanr_build::fingerprint::fingerprint_all(&ws, &fp_env_for(&toolchain))
                        .map_err(|e| e.to_string())?;
                fps.sort();
                fps.dedup();
                let rc = remote_cache_for(&url);
                let r = leanr_build::remote::get_all(&cache, &rc, &fps, default_jobs(jobs));
                println!(
                    "cache get: {} fetched, {} already local, {} not on remote, {} failed",
                    r.fetched, r.already_local, r.missing, r.failed
                );
                if r.failed > 0 {
                    return Err(format!("{} module(s) failed to fetch", r.failed));
                }
                Ok(())
            }
            CacheCommand::Push {
                to,
                dir,
                toolchain_dir,
                jobs,
            } => {
                let (ws, toolchain) = resolve_workspace(dir, Vec::new(), toolchain_dir)?;
                let mut fps =
                    leanr_build::fingerprint::fingerprint_all(&ws, &fp_env_for(&toolchain))
                        .map_err(|e| e.to_string())?;
                fps.sort();
                fps.dedup();
                let pusher = leanr_build::remote::Pusher::from_env(&to)?;
                let r = pusher.push(&cache, &fps, default_jobs(jobs))?;
                println!(
                    "cache push: {} manifests pushed ({} already remote), {} blobs, {} bytes uploaded",
                    r.manifests_pushed, r.manifests_skipped, r.blobs_pushed, r.bytes_uploaded
                );
                Ok(())
            }
```

`resolve_workspace`'s current signature already accepts `toolchain_dir` as its third parameter — `verify --deep` passes `None`; keep that call as-is.

- [ ] **Step 4: Run the tests and a smoke check**

Run: `cargo test -p leanr_cli && cargo build -p leanr_cli`
Expected: 4 new unit tests pass; builds clean.

Run: `cargo run -p leanr_cli -- cache get 2>&1 | head -3`
Expected: `error: no remote configured: pass --remote or set LEANR_REMOTE_CACHE`

Run: `cargo run -p leanr_cli -- build --help | grep -E "remote"`
Expected: both `--remote <REMOTE>` and `--no-remote` listed.

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint && cargo test --workspace
git add crates/leanr_cli/src/main.rs
git commit -m "feat(cli): build --remote/--no-remote; cache get / cache push (M2d surface)"
```

---

### Task 9: CI gate, threat model, architecture doc

**Files:**
- Modify: `mise.toml`
- Modify: `docs/THREAT_MODEL.md`
- Modify: `ARCHITECTURE.md`

**Interfaces:**
- Produces: `mise run cache:remote` (hermetic, no toolchain, wired into `ci`). Docs made truthful for M2d.

- [ ] **Step 1: Add the mise task** — in `mise.toml`, directly after the `[tasks."cache:incremental"]` block:

```toml
[tasks."cache:remote"]
description = "M2d remote-cache gate: hermetic HTTP CAS — fetch/push/tamper/offline/build-through-remote (fast; no toolchain)"
run = "cargo test --package leanr_build --test cache_remote"
```

and extend the `ci` task's depends list:

```toml
[tasks.ci]
depends = ["lint", "test", "lint:deps", "scan:secrets", "cache:incremental", "cache:remote"]
```

- [ ] **Step 2: Verify the gate runs**

Run: `mise run cache:remote`
Expected: the full cache_remote suite passes.

- [ ] **Step 3: Update `docs/THREAT_MODEL.md`.** Replace the table row

```
| Remote cache entries (M2+) | Cache operator / network | Content-addressed hashes; kernel-check unless signed by a trusted key |
```

with:

```
| Remote cache entries (M2d) | Cache operator / network | Decompress-and-blake3-verify against the content key BEFORE local insertion (single ingestion choke point, `remote.rs`); defensive manifest parsing (size-capped, strict hex, malformed = warned miss); decompression caps (bomb defense). Configuring a remote = trusting its operator with the fp→artifact mapping; signed manifests are the recorded future upgrade |
```

Then append a new section after the M2c/"cache-store integrity" material (search for the last cache-related heading and add below it):

```markdown
## Remote cache ingestion (M2d)

M2d adds a network tier: `leanr build --remote <url>` / `leanr cache
get` download manifests and blobs from an HTTP endpoint, and `leanr
cache push` uploads to an S3-compatible bucket. The wire bytes are
untrusted (THREAT boundary: cache operator / network path):

- **Single ingestion choke point.** Remote bytes enter the local CAS
  only through `remote::RemoteCache::fetch`, which zstd-decompresses
  under a hard cap and blake3-verifies against the content key BEFORE
  `Cache::store_blob`. A mismatch is warned and rejected; unverified
  bytes never land in the store, so every M2c integrity invariant
  (and `leanr cache verify`) covers remote-sourced entries unchanged.
- **Defensive parsing.** Wire manifests are size-capped (1 MiB),
  parsed with serde (malformed = warned degrade, never a panic), and
  every referenced blob key must be 64 lowercase hex chars before it
  touches a filesystem path. Blob decompression enforces a 4 GiB
  output ceiling (bomb defense).
- **Trust boundary, stated.** Content addressing verifies bytes match
  keys; it cannot verify the fp→artifact *mapping*. A compromised
  endpoint can serve self-consistent malicious artifacts for a
  fingerprint. Configuring a remote = trusting its operator — the
  same posture as sccache/bazel/cargo remote caches and `lake exe
  cache`. Signed manifests are the recorded future upgrade; the
  manifest-fetch path is the seam.
- **Availability ≠ correctness.** Every network failure degrades to a
  cache miss (`lean` runs); a connect-level failure trips a per-run
  circuit breaker (one warning, then silence). Push failures are hard
  errors (CI must notice).
```

- [ ] **Step 4: Update `ARCHITECTURE.md`.** In the leanr_build/M2 paragraph (around lines 74–98), after the sentence ending "`leanr cache gc --max-size`. No kernel dependency.", extend with:

```
  M2d adds `remote`, the network tier over the same CAS: `leanr build`
  reads through a dumb-HTTP remote on local miss (blobs verified
  against their content keys before insertion — see
  docs/THREAT_MODEL.md §Remote cache ingestion), `leanr cache push`
  uploads via presigned S3 PUTs, `leanr cache get` prefetches the
  closure. The remote mirrors the CAS layout under `v1/` with
  zstd-compressed blobs; remote availability affects speed, never
  correctness (`--no-remote` / `LEANR_REMOTE_CACHE`).
```

(Adjust indentation/prose to match the surrounding bullet style — read the section first.)

- [ ] **Step 5: Commit**

```bash
mise run ci
git add mise.toml docs/THREAT_MODEL.md ARCHITECTURE.md
git commit -m "chore(build): cache:remote CI gate; M2d threat-model and architecture docs"
```

---

### Task 10: Recorded full-Mathlib acceptance run

**Files:**
- Create: `scripts/remote-cache-acceptance.sh`
- Modify (after the run): `docs/superpowers/specs/2026-07-13-m2d-remote-cache-design.md` (append the recorded results)

**Interfaces:**
- Consumes: the complete M2d surface; `cargo run -p leanr_build --example cas_httpd` (Task 3); precedent structure from `scripts/build-fresh-acceptance.sh`.
- Byte-fidelity argument (spec §Testing): clone A's cold build is the SAME pipeline `scripts/build-fresh-acceptance.sh` already byte-diffs against lake, so this script asserts **strict A↔B byte-identity** (same builder's bytes through the wire — zero tolerance, no nondeterminism excuses) and leaves A↔lake to the standing M2b/M2c gate. Record that reasoning in the results.

- [ ] **Step 1: Write the script** — `scripts/remote-cache-acceptance.sh` (mode 755):

```sh
#!/bin/sh
# M2d acceptance (spec §Testing, recorded run): cold-build pinned Mathlib
# on "machine A" (fresh clone, isolated XDG), push the CAS to a local
# static server, then build on "machine B" (fresh clone, EMPTY XDG,
# --remote) — expect ~zero lean invocations, all modules downloaded, and
# STRICT byte-identity between A's and B's artifacts (A↔lake fidelity is
# scripts/build-fresh-acceptance.sh's standing gate). Finally exercise
# `cache get` on an empty "machine C" XDG. Hours of compute; local only.
# Needs: mathlib:fetch done, elan toolchain.
set -eu

repo_root=$(cd "$(dirname "$0")/.." && pwd)
sha=$(sed -n '3p' "$repo_root/mathlib-pin")
tmp=$(mktemp -d)
server_pid=""
trap 'if [ -n "$server_pid" ]; then kill "$server_pid" 2>/dev/null || true; fi; rm -rf "$tmp"' EXIT INT TERM

echo "acceptance: building leanr + cas_httpd ..." >&2
cargo build --release -p leanr_cli
cargo build --release -p leanr_build --example cas_httpd
leanr="$repo_root/target/release/leanr"
cas_httpd="$repo_root/target/release/examples/cas_httpd"

clone() { # $1 = dest
    git clone -q "$repo_root/.mathlib" "$1"
    git -C "$1" -c advice.detachedHead=false checkout -q --detach "$sha"
}

# --- Machine A: cold build ------------------------------------------------
clone "$tmp/a"
export XDG_CACHE_HOME="$tmp/xdg-a"
echo "acceptance: machine A cold build (hours) ..." >&2
(cd "$tmp/a" && "$leanr" build)

# --- Serve + push ----------------------------------------------------------
served="$tmp/served"; mkdir -p "$served/cas"
"$cas_httpd" "$served" > "$tmp/addr.txt" &
server_pid=$!
sleep 1
addr=$(cat "$tmp/addr.txt")
echo "acceptance: cas_httpd at $addr" >&2

echo "acceptance: cache push (machine A -> local S3 stand-in) ..." >&2
push_out="$tmp/push.txt"
start=$(date +%s)
(cd "$tmp/a" && \
    AWS_ENDPOINT_URL="http://$addr" AWS_ACCESS_KEY_ID=acceptance \
    AWS_SECRET_ACCESS_KEY=acceptance \
    "$leanr" cache push --to s3://cas) | tee "$push_out"
end=$(date +%s)
echo "acceptance: push wall time $((end - start))s" >&2
grep -q '^cache push: ' "$push_out" || { echo "FAIL: no push summary" >&2; exit 1; }

# --- Machine B: fresh XDG, remote-only build --------------------------------
clone "$tmp/b"
export XDG_CACHE_HOME="$tmp/xdg-b"
echo "acceptance: machine B build --remote (expect zero lean runs) ..." >&2
b_out="$tmp/b-build.txt"
start=$(date +%s)
(cd "$tmp/b" && "$leanr" build --remote "http://$addr/cas") > "$b_out"
end=$(date +%s)
echo "acceptance: machine B wall time $((end - start))s" >&2
if ! grep -q '^built 0 modules (' "$b_out"; then
    echo "acceptance: FAIL — machine B ran lean:" >&2
    tail -5 "$b_out" >&2
    exit 1
fi
not_downloaded=$(grep '^\[' "$b_out" | grep -vc ' (downloaded) (' || true)
if [ "$not_downloaded" -ne 0 ]; then
    echo "acceptance: FAIL — $not_downloaded module(s) not tagged (downloaded):" >&2
    grep '^\[' "$b_out" | grep -v ' (downloaded) (' | head -20 >&2
    exit 1
fi
echo "acceptance: PASS — $(grep '^built ' "$b_out")" >&2

echo "acceptance: strict A<->B artifact byte-diff ..." >&2
mismatches="$tmp/ab-mismatches.txt"; : > "$mismatches"
count=0
(cd "$tmp/a/.leanr/build" && find . -type f -path '*/lib/*' | sort) | while IFS= read -r f; do
    cmp -s "$tmp/a/.leanr/build/$f" "$tmp/b/.leanr/build/$f" || echo "$f" >> "$mismatches"
done
count=$(cd "$tmp/a/.leanr/build" && find . -type f -path '*/lib/*' | wc -l)
if [ -s "$mismatches" ]; then
    echo "acceptance: FAIL — $(wc -l < "$mismatches") of $count artifacts differ A<->B:" >&2
    head -50 "$mismatches" >&2
    exit 1
fi
echo "acceptance: PASS — $count artifacts byte-identical A<->B (A<->lake is build-fresh-acceptance.sh's standing gate)" >&2

echo "acceptance: machine B cache verify ..." >&2
"$leanr" cache verify | grep -q '^cache verify: OK (' || { echo "FAIL: cache verify" >&2; exit 1; }
echo "acceptance: PASS — machine B store integrity clean" >&2

# --- Machine C: explicit prefetch ------------------------------------------
clone "$tmp/c"
export XDG_CACHE_HOME="$tmp/xdg-c"
echo "acceptance: machine C cache get (explicit prefetch) ..." >&2
get_out="$tmp/get.txt"
(cd "$tmp/c" && "$leanr" cache get --remote "http://$addr/cas") | tee "$get_out"
grep -q ' 0 failed$' "$get_out" || { echo "FAIL: cache get had failures" >&2; exit 1; }
c_out="$tmp/c-build.txt"
(cd "$tmp/c" && "$leanr" build --no-remote) > "$c_out"
if ! grep -q '^built 0 modules (' "$c_out"; then
    echo "acceptance: FAIL — post-get build ran lean:" >&2
    tail -5 "$c_out" >&2
    exit 1
fi
echo "acceptance: PASS — $(grep '^built ' "$c_out") (prefetch made the build fully local)" >&2

echo "acceptance: PASS — push, remote warm build, A<->B byte-identity, integrity, and cache get all verified" >&2
echo "acceptance: record wall times, module/blob counts, and bytes uploaded in the M2d spec" >&2
```

- [ ] **Step 2: Shellcheck-by-eye + smoke the plumbing cheaply**

Before the hours-long real run, smoke the script's mechanics against the *hermetic fixture* by hand: start `cas_httpd` on a temp dir, run `cache push`/`build --remote`/`cache get` against a small synthetic project (the Task 5 fixture layout works — create it manually in a temp dir with the real `leanr` binary and the real pinned toolchain if available, or rely on `mise run cache:remote` as the mechanics gate). At minimum: `sh -n scripts/remote-cache-acceptance.sh` parses clean.

Run: `sh -n scripts/remote-cache-acceptance.sh`
Expected: no output (syntax OK).

- [ ] **Step 3: Commit the script**

```bash
chmod +x scripts/remote-cache-acceptance.sh
git add scripts/remote-cache-acceptance.sh
git commit -m "test(build): M2d recorded-acceptance script — push, remote warm build, A<->B byte-diff, cache get"
```

- [ ] **Step 4: Run the acceptance (LOCAL ONLY — hours; needs mathlib:fetch + elan)**

Run: `scripts/remote-cache-acceptance.sh`
Expected final line: `acceptance: PASS — push, remote warm build, A<->B byte-identity, integrity, and cache get all verified`

- [ ] **Step 5: Record the results.** Append to `docs/superpowers/specs/2026-07-13-m2d-remote-cache-design.md` a `## Acceptance results (recorded YYYY-MM-DD)` section with: module count, blob count and bytes uploaded (from the push summary), push wall time, machine-B wall time (and that it printed `built 0 modules`), artifact count byte-diffed A↔B, `cache get` summary, and the note that A↔lake fidelity is covered by `scripts/build-fresh-acceptance.sh`. Commit:

```bash
git add docs/superpowers/specs/2026-07-13-m2d-remote-cache-design.md
git commit -m "docs(specs): record M2d remote-cache acceptance results"
```

---

## Plan Self-Review (performed at authoring time)

**Spec coverage:** wire layout & versioned prefix → Task 1; verified ingest, caps, breaker, degraded semantics → Task 4; build tier + `downloaded` reporting → Task 5; S3 push, blobs-before-manifest, idempotence, hard errors → Task 6; `cache get` + nonzero-on-failure → Tasks 7–8; `--remote`/`--no-remote`/env config → Task 8; hermetic gate `mise run cache:remote` (fetch/push/tamper/offline/zero-lean/byte-identity) → Tasks 3–7 + 9; threat-model concretization → Task 9; recorded acceptance → Task 10. Deliberately absent, per spec out-of-scope: signed manifests, bundles, Mathlib-cache interop, server binary, project-config file, remote GC.

**Known API risks (flagged in-task, not placeholders):** exact ureq 3.x builder/body-limit method names (Task 4 note) and rusty-s3 action names (Task 6 note) — both pinned behaviorally by tests, checked against docs.rs at implementation time.

**Type consistency:** `FetchOutcome::{Hit{downloaded_blobs},Miss,Degraded}`, `RemoteCache::new(&str, WarnFn)`, `fetch(&Cache, &str)`, `Pusher::from_parts(to, endpoint, region, key_id, secret)`, `push(&Cache, &[String], usize) -> Result<PushReport,String>`, `get_all(&Cache, &RemoteCache, &[String], usize) -> GetReport`, `BuildOptions.remote`, `BuildReport.downloaded`, `BuiltEvent.downloaded` — used identically across Tasks 4–8. `Cache::insert_manifest(&str, &Manifest)` defined in Task 2, consumed in Task 4.
