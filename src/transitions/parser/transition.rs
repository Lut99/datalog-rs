//  TRANSITION.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 11:01:38
//  Last edited:
//    29 Nov 2024, 11:09:47
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a parser for transitions definitions.
//

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::error::Common;
use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{comb, combinator as comb, error, multi, sequence as seq, utf8};
use ast_toolkit::span::{Span, Spanning};

use super::super::ast;
use super::ident::TransIdentExpectsFormatter;
use super::postulation::PostulationExpectsFormatter;
use super::{ident, postulation, tokens};


/***** ERRORS *****/
/// Errors returned when parsing literals and related.
pub enum ParseError<F, S> {
    /// Failed to parse the closing curly bracket.
    CurlyClose { span: Span<F, S> },
    /// Failed to parse the opening curly bracket.
    CurlyOpen { span: Span<F, S> },
    /// Failed to parse a postulation.
    Postulation { span: Span<F, S> },
    /// Failed to parse the transition identifier.
    TransIdent { span: Span<F, S> },
}
impl<F, S> Debug for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            CurlyClose { span } => {
                let mut fmt = f.debug_struct("ParseError::CurlyClose");
                fmt.field("span", span);
                fmt.finish()
            },
            CurlyOpen { span } => {
                let mut fmt = f.debug_struct("ParseError::CurlyOpen");
                fmt.field("span", span);
                fmt.finish()
            },
            Postulation { span } => {
                let mut fmt = f.debug_struct("ParseError::Postulation");
                fmt.field("span", span);
                fmt.finish()
            },
            TransIdent { span } => {
                let mut fmt = f.debug_struct("ParseError::TransIdent");
                fmt.field("span", span);
                fmt.finish()
            },
        }
    }
}
impl<F, S> Display for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            CurlyClose { .. } => write!(f, "Expected a closing curly bracket"),
            CurlyOpen { .. } => write!(f, "Expected an opening curly bracket"),
            Postulation { .. } => write!(f, "{}", PostulationExpectsFormatter),
            TransIdent { .. } => write!(f, "{}", TransIdentExpectsFormatter),
        }
    }
}
impl<F, S> Error for ParseError<F, S> {}
impl<F, S> Spanning<F, S> for ParseError<F, S>
where
    F: Clone,
    S: Clone,
{
    #[inline]
    fn span(&self) -> Span<F, S> {
        use ParseError::*;
        match self {
            CurlyClose { span } => span.clone(),
            CurlyOpen { span } => span.clone(),
            Postulation { span } => span.clone(),
            TransIdent { span } => span.clone(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        match self {
            Self::CurlyClose { span } => span,
            Self::CurlyOpen { span } => span,
            Self::Postulation { span } => span,
            Self::TransIdent { span } => span,
        }
    }
}





/***** LIBRARY *****/
#[comb(snack = ::ast_toolkit::snack, expected = "a transition definition", Output = ast::Transition<F, S>, Error = ParseError<F, S>)]
pub fn transition<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    comb::map(
        seq::pair(
            comb::map_err(seq::terminated(ident::trans_ident(), error::transmute(utf8::whitespace0())), |err| ParseError::TransIdent {
                span: err.into_span(),
            }),
            comb::map_err(
                tokens::curly(multi::many0(comb::map_err(postulation::postulation(), |err| ParseError::Postulation { span: err.into_span() }))),
                |err| match err {
                    ast_toolkit::tokens::snack::complete::ParseError::Inner { err: Common::Custom(err) } => err,
                    ast_toolkit::tokens::snack::complete::ParseError::Utf8OpenToken { token: _, span } => ParseError::CurlyOpen { span },
                    ast_toolkit::tokens::snack::complete::ParseError::Utf8CloseToken { token: _, span } => ParseError::CurlyClose { span },
                    _ => unreachable!(),
                },
            ),
        ),
        |_| todo!(),
    )
    .parse(input)
}
