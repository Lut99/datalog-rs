//  LIB.rs
//    by Lut99
//
//  Created:
//    13 Mar 2024, 16:43:01
//  Last edited:
//    03 Dec 2024, 14:32:29
//  Auto updated?
//    Yes
//
//  Description:
//!   A simple Datalog^\\neg interpreter to support the language as
//!   discussed in the paper.
//

// Declare modules
pub mod ast;
#[cfg(feature = "interpreter")]
pub mod interpreter;
mod log;
#[cfg(feature = "parser")]
pub mod parser;
#[cfg(test)]
mod tests;
#[cfg(feature = "transitions")]
pub mod transitions;
