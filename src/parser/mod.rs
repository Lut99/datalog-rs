//  MOD.rs
//    by Lut99
//
//  Created:
//    03 May 2024, 13:42:38
//  Last edited:
//    17 May 2024, 18:17:35
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements a parser for $Datalog^\neg$ using the `ast-toolkit`'s
//!   `snack`-library.
//

// Declare appropriate submodules
pub mod atoms;
pub mod literals;
pub mod rules;
pub mod specs;
pub mod tokens;

// Imports
use ast_toolkit_snack::{Combinator as _, Result as SResult};
use ast_toolkit_span::Span;

use crate::ast::Spec;


/***** ERRORS *****/
/// The concrete error type returned by the [`parse()`] function.
pub type Error<'f, 's> = ast_toolkit_snack::error::Error<'static, &'f str, &'s str, specs::ParseError<&'f str, &'s str>>;





/***** LIBRARY *****/
/// Implements a full parser of some kind of input source to an AST.
///
/// # Arguments
/// - `what`: Some kind of string describing what the input source is, e.g., `<in-memory>` or `/path/to/file`.
/// - `source`: Some kind of `'static` source string. The resulting AST will depent on it for parsing.
///
/// # Returns
/// A parsed $Datalog^\neg$-AST, starting as [`Spec`].
///
/// # Errors
/// This function returns an [`Error`] if the given `input` was not a valid $Datalog^\neg$-program.
#[inline]
pub fn parse<'f, 's>(what: &'f str, source: &'s str) -> Result<Spec<'f, 's>, Error<'f, 's>> {
    // Simply parse as a literal
    match specs::spec().parse(Span::new(what, source)) {
        SResult::Ok(_, res) => Ok(res),
        SResult::Fail(fail) => Err(fail.try_into().unwrap()),
        SResult::Error(err) => Err(err),
    }
}
