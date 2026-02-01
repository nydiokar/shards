use clap::Parser;
use anyhow::Result;
use std::path::PathBuf;

mod frequency;
mod differential;
mod timing;
mod algebraic;

#[derive(Parser)]
#[command(name = "shard-analyzer")]
#[command(about = "71 cryptanalysis methods for build artifacts")]
struct Cli {
    /// Shard number (0-70)
    #[arg(short, long)]
    shard: u8,
    
    /// Target file or directory
    #[arg(short, long)]
    target: PathBuf,
    
    /// Output parquet file
    #[arg(short, long)]
    output: PathBuf,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    
    if cli.shard > 70 {
        anyhow::bail!("Shard must be 0-70");
    }
    
    println!("Running analysis shard {} on {:?}", cli.shard, cli.target);
    
    match cli.shard {
        0..=9 => frequency::analyze(cli.shard, &cli.target, &cli.output)?,
        10..=25 => differential::analyze(cli.shard, &cli.target, &cli.output)?,
        26..=39 => timing::analyze(cli.shard, &cli.target, &cli.output)?,
        40..=70 => algebraic::analyze(cli.shard, &cli.target, &cli.output)?,
        _ => unreachable!(),
    }
    
    println!("Results written to {:?}", cli.output);
    Ok(())
}
