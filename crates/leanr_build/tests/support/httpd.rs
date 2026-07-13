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
            Ok(meta) if meta.is_file() => respond(&mut stream, "200 OK", None, meta.len() as usize),
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
