//  MOD.rs
//    by Lut99
//
//  Created:
//    03 May 2024, 13:42:38
//  Last edited:
//    06 Feb 2025, 10:19:55
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
pub mod whitespace0;

// Imports
use ast_toolkit::snack::result::SnackError;
use ast_toolkit::span::{Span, SpannableBytes};
pub use whitespace0::whitespace0;

use crate::ast::Spec;


/***** ERRORS *****/
/// The concrete error type returned by the [`parse()`] function.
pub type Error<'s, S> = ast_toolkit::snack::boxed::BoxedParseError<'s, S>;





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
pub fn parse<'s, S>(source: S) -> Result<Spec<S>, Error<'s, S>>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    // Simply parse as a literal
    match specs::spec().parse(Span::new(source)) {
        Ok((_, res)) => Ok(res),
        Err(SnackError::Recoverable(err)) => Err(err),
        Err(SnackError::Fatal(err)) => Err(err),
    }
}
