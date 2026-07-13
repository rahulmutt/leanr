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
