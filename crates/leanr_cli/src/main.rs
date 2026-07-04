use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};

/// A pure-Rust Lean 4 toolchain.
#[derive(Parser)]
#[command(name = "leanr", version)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Inspect official Lean artifacts.
    Olean {
        #[command(subcommand)]
        command: OleanCommand,
    },
}

#[derive(Subcommand)]
enum OleanCommand {
    /// Print the header of an .olean file.
    Info { path: PathBuf },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Command::Olean {
            command: OleanCommand::Info { path },
        } => olean_info(&path),
    }
}

fn olean_info(path: &std::path::Path) -> ExitCode {
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(err) => {
            eprintln!("error: cannot read {}: {err}", path.display());
            return ExitCode::FAILURE;
        }
    };
    match leanr_olean::OleanHeader::parse(&bytes) {
        Ok(header) => {
            println!("githash:      {}", header.githash);
            println!("base address: {:#x}", header.base_addr);
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error: {}: {err}", path.display());
            ExitCode::FAILURE
        }
    }
}
