//  EXPRS.rs
//    by Lut99
//
//  Created:
//    04 Mar 2025, 15:56:43
//  Last edited:
//    04 Mar 2025, 16:23:49
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for the new integer expressions.
//

use std::fmt::{Display, Formatter, Result as FResult};

use ast_toolkit::snack::error::{Common, Failure};
use ast_toolkit::snack::span::MatchBytes;
use ast_toolkit::snack::{Combinator as _, Result as SResult, comb};
use ast_toolkit::span::Spanning;
use better_derive::Debug;

use super::tokens;
use crate::ast::{self, Span};


/***** ERRORS *****/
/// Errors returned when parsing atoms and related.
#[derive(Debug)]
pub enum ParseError<F, S> {
    /// Failed to parse a parenthesis-wrapped expression.
    ExprParens { err: Common<F, S> },
}
impl<F, S> Display for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ParseError::*;
        match self {
            FactArgs { .. } => write!(f, "{}", FactArgsExpectsFormatter),
        }
    }
}
impl<F, S> std::error::Error for ParseError<F, S> {}
impl<F, S> Spanning<F, S> for ParseError<F, S>
where
    F: Clone,
    S: Clone,
{
    #[inline]
    fn span(&self) -> Span<F, S> {
        use ParseError::*;
        match self {
            FactArgs { span } => span.clone(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        use ParseError::*;
        match self {
            FactArgs { span } => span,
        }
    }
}





/***** LIBRARY *****/
/// Parses an integer expression.
///
/// This implements a
/// [pratt parser](https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html) for
/// dealing with operator precedence and the likes.
///
/// # Returns
/// A combinator capable of parsing [`Expr`](ast::Expr)essions.
///
/// # Fails
/// The given combinator fails if the head of the input is not a valid expression.
#[comb(snack = ::ast_toolkit::snack, expected = "an integer expression", Output = ast::Expr<F, S>, Error = ParseError<F, S>)]
pub fn expr<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes,
{
    // Base case: we always accept parenthesis-wrapped expressions
    match expr_parens().parse(input.clone()) {
        SResult::Ok(rem, res) => return SResult::Ok(rem, ast::Expr::Parens(ast::Ex)),
        SResult::Fail(_) => {},
        SResult::Error(err) => return SResult::Error(err),
    }

    // Parse the start of any expression:

    todo!()
}



/// Parses an integer expression wrapped in parenthesis.
#[comb(snack = ::ast_toolkit::snack, expected = "an integer expression wrapped in parenthesis", Output = ast::ExprParens<F, S>, Error = ParseError<F, S>)]
pub fn expr_parens<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes,
{
    match tokens::parens(expr()).parse(input) {
        SResult::Ok(rem, (expr, paren_tokens)) => SResult::Ok(rem, ast::ExprParens { paren_tokens, expr: Box::new(expr) }),
        SResult::Fail(fail) => SResult::Fail(Failure::Common(Common::Custom(ParseError::ExprParens { err: fail }))),
        SResult::Error(err) => SResult::Error(err),
    }
}
