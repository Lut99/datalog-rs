//  LIB.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 10:47:56
//  Last edited:
//    29 Nov 2024, 16:26:29
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines an overlay on the $Datalog^\\neg$ language that implements
//!   eFLINT-like transitions.
//

// Modules
pub mod ast;
#[cfg(feature = "interpreter")]
pub mod interpreter;
#[cfg(feature = "parser")]
pub mod parser;
