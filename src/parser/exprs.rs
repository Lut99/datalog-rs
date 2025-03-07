//  EXPRS.rs
//    by Lut99
//
//  Created:
//    04 Mar 2025, 15:56:43
//  Last edited:
//    07 Mar 2025, 11:51:46
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for the new integer expressions.
//

use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::error::{Common, Failure};
use ast_toolkit::snack::span::MatchBytes;
use ast_toolkit::snack::{Combinator as _, Result as SResult, comb};
use ast_toolkit::span::Spanning;

use super::tokens;
use crate::ast::{self, Span};


/***** ERRORS *****/
/// Errors returned when parsing atoms and related.
#[derive(Debug)]
pub enum ParseError<'a, F, S> {
    /// Failed to parse a parenthesis-wrapped expression.
    ExprParens { err: Common<'a, F, S, ast_toolkit::tokens::snack::complete::ParseError<'a, F, S, Box<Self>>> },
    /// The parens()-combinator did not just fail, it failed unrecoverably.
    Parens { err: ast_toolkit::tokens::snack::complete::ParseError<'a, F, S, Box<Self>> },
}
impl<'a, F, S> Display for ParseError<'a, F, S> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExprParens { .. } => write!(f, "{ExprParensExpectsFormatter}"),
            Self::Parens { err } => err.fmt(f),
        }
    }
}
impl<'a, F: Debug, S: Debug> std::error::Error for ParseError<'a, F, S> {}
impl<'a, F, S> Spanning<F, S> for ParseError<'a, F, S>
where
    F: Clone,
    S: Clone,
{
    #[inline]
    fn span(&self) -> Span<F, S> {
        match self {
            Self::ExprParens { err } => err.span(),
            Self::Parens { err } => err.span(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        match self {
            Self::ExprParens { err } => err.into_span(),
            Self::Parens { err } => err.into_span(),
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
#[comb(snack = ::ast_toolkit::snack, expected = "an integer expression", Output = ast::Expr<F, S>, Error = ParseError<'static, F, S>)]
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
#[comb(snack = ::ast_toolkit::snack, expected = "an integer expression wrapped in parenthesis", Output = ast::ExprParens<F, S>, Error = ParseError<'static, F, S>)]
pub fn expr_parens<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes,
{
    match tokens::parens(expr()).parse(input) {
        SResult::Ok(rem, (expr, paren_tokens)) => SResult::Ok(rem, ast::ExprParens { paren_tokens, expr: Box::new(expr) }),
        SResult::Fail(Failure::Common(fail)) => {
            SResult::Fail(Failure::Common(Common::Custom(ParseError::ExprParens { err: fail.map_custom(&mut |err| Box::new(err)) })))
        },
        SResult::Fail(Failure::NotEnough { needed, span }) => SResult::Fail(Failure::NotEnough { needed, span }),
        SResult::Error(err) => SResult::Error(err.map_custom(|err| ParseError::Parens { err })),
    }
}
