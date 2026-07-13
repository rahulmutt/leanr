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
