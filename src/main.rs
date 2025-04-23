use anyhow::{Context, Result};
use clap::{Parser, ValueEnum};
use std::fs::File;
use std::io::{self, Read, Write};
use thalamus::{compile_brain_stem, run_program};

#[derive(ValueEnum, Debug, Clone)]
enum IntegerType {
    U8,
    I8,
    U32,
    I32,
}

/// Thalamus - A two-stage Brainfuck compiler (and minimal interpreter).
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input brain_stem file (use - for stdin)
    #[arg(short, long, default_value = "-")]
    input: String,

    /// Output bf code file (use - for stdout)
    #[arg(short, long, default_value = "-")]
    output: String,

    /// Run the generated bf code
    #[arg(short, long)]
    run: bool,

    /// Input for running the bf code (use - for stdin)
    #[arg(short = 'I', long, default_value = "-")]
    run_input: String,

    /// Output file for the run result (use - for stdout)
    #[arg(short = 'O', long, default_value = "-")]
    run_output: String,

    /// Integer type to use for bf execution
    #[arg(short = 't', long, value_enum, default_value = "u32")]
    int_type: IntegerType,

    /// Maximum steps to run (prevents infinite loops)
    #[arg(short = 'M', long)]
    max_steps: Option<usize>,
}

fn main() -> Result<()> {
    let args = if std::env::args().len() <= 1 {
        // Keine Argumente übergeben, Hilfe anzeigen und beenden
        Args::parse_from(["rbfc", "--help"]);
        return Ok(());
    } else {
        Args::parse()
    };

    // Read input brain_stem script
    let mut input_content = String::new();
    if args.input == "-" {
        io::stdin()
            .read_to_string(&mut input_content)
            .context("Failed to read from stdin")?;
    } else {
        let mut file = File::open(&args.input)
            .with_context(|| format!("Failed to open input file: {}", args.input))?;
        file.read_to_string(&mut input_content)
            .with_context(|| format!("Failed to read from input file: {}", args.input))?;
    }

    // Compile brain_stem to bf code
    let bf_code = compile_brain_stem(&input_content).context("Failed to compile bf script")?;

    // Write bf code to output
    if args.output == "-" {
        io::stdout()
            .write_all(bf_code.as_bytes())
            .context("Failed to write to stdout")?;
    } else {
        let mut file = File::create(&args.output)
            .with_context(|| format!("Failed to create output file: {}", args.output))?;
        file.write_all(bf_code.as_bytes())
            .with_context(|| format!("Failed to write to output file: {}", args.output))?;
    }

    // Run the bf code if requested
    if args.run {
        // Prepare input and output objects
        let mut input: Box<dyn Read> = if args.run_input == "-" {
            Box::new(io::stdin())
        } else {
            Box::new(File::open(&args.run_input)
                .with_context(|| format!("Failed to open run input file: {}", args.run_input))?)
        };
        
        let mut output: Box<dyn Write> = if args.run_output == "-" {
            Box::new(io::stdout())
        } else {
            Box::new(File::create(&args.run_output)
                .with_context(|| format!("Failed to create run output file: {}", args.run_output))?)
        };
        
        // Run the program with the configured input/output and integer type
        let _steps = match args.int_type {
            IntegerType::U8 => run_program::<u8>(&bf_code, &mut input, &mut output, args.max_steps)?,
            IntegerType::I8 => run_program::<i8>(&bf_code, &mut input, &mut output, args.max_steps)?,
            IntegerType::U32 => run_program::<u32>(&bf_code, &mut input, &mut output, args.max_steps)?,
            IntegerType::I32 => run_program::<i32>(&bf_code, &mut input, &mut output, args.max_steps)?,
        };
    }

    Ok(())
}
