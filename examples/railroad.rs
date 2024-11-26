//  RAILROAD.rs
//    by Lut99
//
//  Created:
//    16 Apr 2024, 17:31:45
//  Last edited:
//    26 Nov 2024, 11:18:30
//  Auto updated?
//    Yes
//
//  Description:
//!   Generates the railroad diagram for the $Datalog^\neg$ AST.
//

use std::path::PathBuf;

use clap::Parser;
use console::style;
use datalog::ast::diagram_to_path;
use error_trace::trace;
use humanlog::{DebugMode, HumanLogger};
use log::error;


/***** ARGUMENTS *****/
/// The arguments to the `railroad`-executable.
#[derive(Debug, Parser)]
struct Arguments {
    /// The path to write the diagram to.
    #[clap(name = "PATH", default_value = concat!(env!("CARGO_MANIFEST_DIR"), "/examples/railroad.svg"), help = "The path to write the railroad diagram of the eFLINT AST to.")]
    path: PathBuf,
}





/***** ENTRYPOINT *****/
fn main() {
    // Read the args
    let args = Arguments::parse();

    // Setup the logger
    if let Err(err) = HumanLogger::terminal(DebugMode::HumanFriendly).init() {
        eprintln!("WARNING: Failed to setup logger: {err} (errors may be lost for this session)");
    }

    // Attempt to write the diagram
    if let Err(err) = diagram_to_path(&args.path) {
        error!("{}", trace!(("Failed to generate railroad diagram for the eFLINT AST"), err));
        std::process::exit(1);
    }

    // Alrighty done (write in orange)
    println!("Successfully written syntax diagram to {}", style(args.path.display()).bold().color256(172));
}
