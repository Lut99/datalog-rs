//  TRANSITIONS.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 11:01:38
//  Last edited:
//    29 Nov 2024, 15:44:02
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
use super::idents::TransIdentExpectsFormatter;
use super::postulations::PostulationExpectsFormatter;
use super::{idents, postulations, tokens};


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
/// Parses a transition definition.
///
/// # Returns
/// A [`Transition`](ast::Transition) that represents a definition of a transition.
///
/// # Fails
/// This combinator fails if the head of the input does not contain a valid transition definition.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Arrow, Atom, AtomArg, AtomArgs, Dot, Ident, Literal, Parens, Rule, RuleAntecedents};
/// use datalog::transitions::ast::{Add, Curly, Postulation, PostulationOp, Squiggly, Transition};
/// use datalog::transitions::parser::transitions::{transition, ParseError};
///
/// let span1 = Span::new("<example>", "#foo {}");
/// let span2 = Span::new("<example>", "#bar { +{ foo. } }");
/// let span3 = Span::new("<example>", "#baz { ~{ foo. bar. } +{ baz. } }");
///
/// let mut comb = transition();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(7..), Transition {
///         ident: Ident { value: span1.slice(..4) },
///         curly_tokens: Curly { open: span1.slice(5..6), close: span1.slice(6..7) },
///         postulations: vec![],
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(18..), Transition {
///         ident: Ident { value: span2.slice(..4) },
///         curly_tokens: Curly { open: span2.slice(5..6), close: span2.slice(17..18) },
///         postulations: vec![Postulation {
///             op: PostulationOp::Create(Add { span: span2.slice(7..8) }),
///             curly_tokens: Curly { open: span2.slice(8..9), close: span2.slice(15..16) },
///             rules: vec![Rule {
///                 consequences: punct![v => Atom { ident: Ident { value: span2.slice(10..13) }, args: None }],
///                 tail: None,
///                 dot: Dot { span: span2.slice(13..14) }
///             }],
///         }],
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(33..), Transition {
///         ident: Ident { value: span3.slice(..4) },
///         curly_tokens: Curly { open: span3.slice(5..6), close: span3.slice(32..33) },
///         postulations: vec![
///             Postulation {
///                 op: PostulationOp::Create(Add { span: span3.slice(7..8) }),
///                 curly_tokens: Curly { open: span3.slice(8..9), close: span3.slice(20..21) },
///                 rules: vec![
///                     Rule {
///                         consequences: punct![v => Atom { ident: Ident { value: span3.slice(10..13) }, args: None }],
///                         tail: None,
///                         dot: Dot { span: span3.slice(13..14) }
///                     },
///                     Rule {
///                         consequences: punct![v => Atom { ident: Ident { value: span3.slice(15..18) }, args: None }],
///                         tail: None,
///                         dot: Dot { span: span3.slice(18..19) }
///                     },
///                 ],
///             },
///             Postulation {
///                 op: PostulationOp::Create(Add { span: span3.slice(22..23) }),
///                 curly_tokens: Curly { open: span3.slice(23..24), close: span3.slice(30..31) },
///                 rules: vec![Rule {
///                     consequences: punct![v => Atom { ident: Ident { value: span3.slice(25..28) }, args: None }],
///                     tail: None,
///                     dot: Dot { span: span3.slice(28..29) }
///                 }],
///             },
///         ],
///     })
/// );
/// ```
#[comb(snack = ::ast_toolkit::snack, expected = "a transition definition", Output = ast::Transition<F, S>, Error = ParseError<F, S>)]
pub fn transition<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    comb::map(
        seq::pair(
            comb::map_err(seq::terminated(idents::trans_ident(), error::transmute(utf8::whitespace0())), |err| ParseError::TransIdent {
                span: err.into_span(),
            }),
            comb::map_err(
                tokens::curly(seq::preceded(
                    error::transmute(utf8::whitespace0()),
                    multi::many0(seq::terminated(
                        comb::map_err(postulations::postulation(), |err| ParseError::Postulation { span: err.into_span() }),
                        error::transmute(utf8::whitespace0()),
                    )),
                )),
                |err| match err {
                    ast_toolkit::tokens::snack::complete::ParseError::Inner { err: Common::Custom(err) } => err,
                    ast_toolkit::tokens::snack::complete::ParseError::Utf8OpenToken { token: _, span } => ParseError::CurlyOpen { span },
                    ast_toolkit::tokens::snack::complete::ParseError::Utf8CloseToken { token: _, span } => ParseError::CurlyClose { span },
                    _ => unreachable!(),
                },
            ),
        ),
        |(ident, (postulations, curly_tokens))| ast::Transition { ident, curly_tokens, postulations },
    )
    .parse(input)
}