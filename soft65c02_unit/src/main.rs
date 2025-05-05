use std::path::PathBuf;
use clap::Parser;
use anyhow::Result;
use soft65c02_unit::TestRunner;

/// Run unit tests for 6502 assembly code
#[derive(Parser)]
#[command(version, about)]
struct Args {
    /// Path to the test YAML file
    #[arg(short, long)]
    test: PathBuf,

    /// Enable verbose output
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let runner = TestRunner::from_yaml(&args.test, args.verbose)?;
    runner.run()
}
