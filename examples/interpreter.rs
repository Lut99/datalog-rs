//  INTERPRETER.rs
//    by Lut99
//
//  Created:
//    03 May 2024, 14:14:18
//  Last edited:
//    11 Feb 2025, 18:26:44
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements a real-life $Datalog^\neg$ interpreter.
//

use std::fs;
use std::path::PathBuf;

use clap::Parser;
#[cfg(feature = "transitions")]
use datalog::transitions::{ast::TransitionSpec, interpreter::Effect, parser};
#[cfg(not(feature = "transitions"))]
use datalog::{ast::Spec, interpreter::KnowledgeBase, parser};
use error_trace::toplevel;
use humanlog::{DebugMode, HumanLogger};
use log::{debug, error, info};


/***** CONSTANTS *****/
/// The maximum number of files that are supported as input by the interpreter.
pub const MAX_FILES: usize = 64;





/***** ARGUMENTS *****/
/// Defines arguments to the interpreter.
#[derive(Debug, Parser)]
pub struct Arguments {
    /// If given, enables more verbose logging.
    #[clap(long, global = true)]
    debug: bool,

    /// The path(s) to the file(s) to interpret. If more than one is given, they are interpreted as if they are one large file concatenated.
    #[clap(name = "PATHS")]
    paths: Vec<PathBuf>,
}





/***** ENTRYPOINT *****/
fn main() {
    // Parse the CLI arguments
    let args = Arguments::parse();

    // Setup the logger
    if let Err(err) = HumanLogger::terminal(if args.debug { DebugMode::Full } else { DebugMode::HumanFriendly }).init() {
        eprintln!("WARNING: Failed to setup logger: {err} (no logging for this session)");
    }
    info!("datalog {} - v{}", env!("CARGO_BIN_NAME"), env!("CARGO_PKG_VERSION"));

    // Early quit if no files are given
    if args.paths.is_empty() {
        println!("No files are given; nothing to do.");
        std::process::exit(0);
    }
    if args.paths.len() > MAX_FILES {
        error!(
            "The interpreter only supports up to {MAX_FILES} files, but {} files are given.\nPlease merge some files manually and try again.",
            args.paths.len()
        );
        std::process::exit(1);
    }

    // Attempt to load the files
    let mut sources: Vec<(String, String)> = Vec::with_capacity(args.paths.len());
    for path in &args.paths {
        debug!("Reading input file '{}'...", path.display());
        sources.push((path.display().to_string(), match fs::read_to_string(&path) {
            Ok(input) => input,
            Err(err) => {
                error!("{}", toplevel!(("Failed to load input file '{}'", path.display()), err));
                std::process::exit(1);
            },
        }));
    }
    debug!("Loaded {} file(s)", sources.len());

    // Attempt to parse the files
    #[cfg(not(feature = "transitions"))]
    {
        let mut spec: Spec<(&str, &str)> = Spec { rules: Vec::new() };
        for (what, source) in &sources {
            debug!("Parsing file '{what}'...");
            let file_spec: Spec<(&str, &str)> = match parser::parse::<(&str, &str)>((what, source)) {
                Ok(spec) => spec,
                Err(err) => {
                    error!("{err}");
                    error!("Syntax error while parsing input file '{what}' (see output above)");
                    std::process::exit(1);
                },
            };

            // Merge this one with the existing one
            spec.rules.extend(file_spec.rules);
        }

        // Alright, now interpret the file
        debug!("Running interpretation of {} rules...", spec.rules.len());
        let kb: KnowledgeBase<(&str, &str)> = match spec.compile() {
            Ok(spec) => spec.alternating_fixpoint(),
            Err(err) => {
                error!("Failed to compile spec: {err}");
                std::process::exit(1);
            },
        };

        // If we made it, print it
        println!("{kb}");
    }
    #[cfg(feature = "transitions")]
    {
        let mut spec: TransitionSpec<(&str, &str)> = TransitionSpec { phrases: Vec::new() };
        for (what, source) in &sources {
            debug!("Parsing file '{what}'...");
            let file_spec: TransitionSpec<(&str, &str)> = match parser::parse::<(&str, &str)>((what, source)) {
                Ok(spec) => spec,
                Err(err) => {
                    error!("{err}");
                    error!("Syntax error while parsing input file '{what}' (see output above)");
                    std::process::exit(1);
                },
            };

            // Merge this one with the existing one
            spec.phrases.extend(file_spec.phrases);
        }

        // Alright, now interpret the file
        debug!("Running interpretation of {} phrases...", spec.phrases.len());
        let effects: Vec<Effect<(&str, &str)>> = match spec.run() {
            Ok((_, effects)) => effects,
            Err(err) => {
                error!("Failed to run interpretation: {err}");
                std::process::exit(1);
            },
        };

        // If we made it, print it
        println!("Program trace:");
        for effect in effects {
            println!("--> {}", effect.trigger);
            println!("    {}", effect.kb.to_string().replace('\n', "\n    "));
        }
    }
}
