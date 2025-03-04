//  MOD.rs
//    by Lut99
//
//  Created:
//    03 May 2024, 13:42:38
//  Last edited:
//    04 Mar 2025, 15:59:51
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements a parser for $Datalog^\neg$ using the `ast-toolkit`'s
//!   `snack`-library.
//

// Declare appropriate submodules
pub mod atoms;
pub mod exprs;
pub mod literals;
pub mod rules;
pub mod specs;
pub mod tokens;
pub mod whitespaces;

// Imports
use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{Combinator as _, Result as SResult};
use ast_toolkit::span::{Span, Spannable};

use crate::ast::Spec;


/***** ERRORS *****/
/// The concrete error type returned by the [`parse()`] function.
pub type Error<F, S> = ast_toolkit::snack::error::Error<'static, F, S, specs::ParseError<F, S>>;





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
pub fn parse<F, S>(what: F, source: S) -> Result<Spec<F, S>, Error<F, S>>
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + Spannable + WhileUtf8,
{
    // Simply parse as a literal
    match specs::spec().parse(Span::new(what, source)) {
        SResult::Ok(_, res) => Ok(res),
        SResult::Fail(fail) => Err(fail.try_into().unwrap()),
        SResult::Error(err) => Err(err),
    }
}
