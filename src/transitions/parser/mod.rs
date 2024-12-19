//  MOD.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 17:32:22
//  Last edited:
//    04 Dec 2024, 17:57:14
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements a parser for $Datalog^\neg$ using the `ast-toolkit`'s
//!   `snack`-library.
//

// Declare appropriate submodules
pub mod idents;
pub mod postulations;
pub mod specs;
pub mod tokens;
pub mod transitions;
pub mod triggers;

// Imports
use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{Combinator as _, Result as SResult};
use ast_toolkit::span::{Span, Spannable};

use super::ast::TransitionSpec;


/***** ERRORS *****/
/// The concrete error type returned by the [`parse()`] function.
pub type Error<F, S> = ast_toolkit::snack::error::Error<'static, F, S, specs::ParseError<F, S>>;





/***** LIBRARY *****/
/// Implements a full parser of some kind of input source to an extended datalog AST.
///
/// This parses datalog rules plus transitions and associated triggers and postulations.
///
/// # Arguments
/// - `what`: Some kind of string describing what the input source is, e.g., `<in-memory>` or `/path/to/file`.
/// - `source`: Some kind of source string. The resulting AST will depent on it for parsing.
///
/// # Returns
/// A parsed $Datalog^\neg$-AST, starting as [`TransitionSpec`].
///
/// # Errors
/// This function returns an [`Error`] if the given `input` was not a valid $Datalog^\neg$-program.
#[inline]
pub fn parse<F, S>(what: F, source: S) -> Result<TransitionSpec<F, S>, Error<F, S>>
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + Spannable + WhileUtf8,
{
    // Simply parse as a literal
    match specs::trans_spec().parse(Span::new(what, source)) {
        SResult::Ok(_, res) => Ok(res),
        SResult::Fail(fail) => Err(fail.try_into().unwrap()),
        SResult::Error(err) => Err(err),
    }
}
