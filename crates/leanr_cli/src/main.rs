use clap::Parser;

/// A pure-Rust Lean 4 toolchain.
#[derive(Parser)]
#[command(name = "leanr", version)]
struct Cli {}

fn main() {
    let _cli = Cli::parse();
}
