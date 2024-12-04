//  TRIGGERS.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 17:55:47
//  Last edited:
//    03 Dec 2024, 17:38:05
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements parsers for the transitions [`Trigger`](ast::Trigger)s.
//

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::error::Common;
use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{comb, combinator as comb, error, multi, sequence as seq};
use ast_toolkit::span::{Span, Spanning};

use super::super::ast;
use super::{idents, tokens};
use crate::parser::whitespaces;
use crate::transitions::parser::idents::TransIdentExpectsFormatter;


/***** ERRORS *****/
/// Errors returned when parsing literals and related.
pub enum ParseError<F, S> {
    /// Failed to parse the closing curly bracket.
    CurlyClose { span: Span<F, S> },
    /// Failed to parse the opening curly bracket.
    CurlyOpen { span: Span<F, S> },
    /// Failed to parse a dot.
    Dot { span: Span<F, S> },
    /// Failed to parse an exclaimation mark.
    Exclaim { span: Span<F, S> },
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
            Dot { span } => {
                let mut fmt = f.debug_struct("ParseError::Dot");
                fmt.field("span", span);
                fmt.finish()
            },
            Exclaim { span } => {
                let mut fmt = f.debug_struct("ParseError::Exclaim");
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
            Dot { .. } => write!(f, "Expected a dot"),
            Exclaim { .. } => write!(f, "Expected an exclaimation mark"),
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
            Dot { span } => span.clone(),
            Exclaim { span } => span.clone(),
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
            Self::Dot { span } => span,
            Self::Exclaim { span } => span,
            Self::TransIdent { span } => span,
        }
    }
}





/***** LIBRARY *****/
/// Parses a transition trigger.
///
/// # Returns
/// A [`Trigger`](ast::Trigger) that represents a trigger of zero or more transitions.
///
/// # Fails
/// This combinator fails if the head of the input does not contains a valid trigger.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Dot, Ident};
/// use datalog::transitions::ast::{Curly, Exclaim, Trigger};
/// use datalog::transitions::parser::triggers::{ParseError, trigger};
///
/// let span1 = Span::new("<example>", "!{ #foo }.");
/// let span2 = Span::new("<example>", "!{}.");
/// let span3 = Span::new("<example>", "!{ #foo #bar }.");
/// let span4 = Span::new("<example>", "{ #foo }.");
/// let span5 = Span::new("<example>", "!{ foo }.");
/// let span6 = Span::new("<example>", "!{ #foo");
///
/// let mut comb = trigger();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(10..), Trigger {
///         exclaim_token: Exclaim { span: span1.slice(..1) },
///         curly_tokens: Curly { open: span1.slice(1..2), close: span1.slice(8..9) },
///         idents: vec![Ident { value: span1.slice(3..7) }],
///         dot: Dot { span: span3.slice(9..10) },
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(4..), Trigger {
///         exclaim_token: Exclaim { span: span2.slice(..1) },
///         curly_tokens: Curly { open: span2.slice(1..2), close: span2.slice(2..3) },
///         idents: vec![],
///         dot: Dot { span: span3.slice(3..4) },
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(15..), Trigger {
///         exclaim_token: Exclaim { span: span3.slice(..1) },
///         curly_tokens: Curly { open: span3.slice(1..2), close: span3.slice(13..14) },
///         idents: vec![Ident { value: span3.slice(3..7) }, Ident { value: span3.slice(8..12) }],
///         dot: Dot { span: span3.slice(14..15) },
///     })
/// );
/// assert!(matches!(
///     comb.parse(span4),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Exclaim { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Error(Error::Common(Common::Custom(ParseError::CurlyClose { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span6),
///     SResult::Error(Error::Common(Common::Custom(ParseError::CurlyClose { .. })))
/// ));
/// ```
#[comb(snack = ::ast_toolkit::snack, expected = "a transition trigger", Output = ast::Trigger<F, S>, Error = ParseError<F, S>)]
pub fn trigger<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    comb::map(
        seq::tuple((
            comb::map_err(tokens::exclaim(), |err| ParseError::Exclaim { span: err.into_span() }),
            error::cut(comb::map_err(
                tokens::curly(seq::preceded(
                    error::transmute(whitespaces::whitespace()),
                    multi::many0(seq::terminated(
                        comb::map_err(idents::trans_ident(), |err| ParseError::TransIdent { span: err.into_span() }),
                        error::transmute(whitespaces::whitespace()),
                    )),
                )),
                |err: ast_toolkit::tokens::snack::complete::ParseError<_, _, ParseError<F, S>>| -> ParseError<F, S> {
                    match err {
                        ast_toolkit::tokens::snack::complete::ParseError::Inner { err: Common::Custom(err) } => err,
                        ast_toolkit::tokens::snack::complete::ParseError::Utf8OpenToken { token: _, span } => ParseError::CurlyOpen { span },
                        ast_toolkit::tokens::snack::complete::ParseError::Utf8CloseToken { token: _, span } => ParseError::CurlyClose { span },
                        _ => unreachable!(),
                    }
                },
            )),
            comb::map_err(crate::parser::tokens::dot(), |err| ParseError::Dot { span: err.into_span() }),
        )),
        |(exclaim_token, (idents, curly_tokens), dot)| ast::Trigger { exclaim_token, curly_tokens, idents, dot },
    )
    .parse(input)
}
