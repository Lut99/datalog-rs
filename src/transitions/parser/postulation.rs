//  POSTULATION.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 11:10:12
//  Last edited:
//    29 Nov 2024, 14:11:03
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for postulations.
//

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::error::Common;
use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{branch, comb, combinator as comb, error, multi, sequence as seq, utf8};
use ast_toolkit::span::{Span, Spanning};

use super::super::ast;
use super::tokens;
use crate::parser::rules::{self, RuleExpectsFormatter};


/***** ERRORS *****/
/// Errors returned when parsing postulations and related.
pub enum ParseError<F, S> {
    /// Failed to parse the closing curly bracket.
    CurlyClose { span: Span<F, S> },
    /// Failed to parse the opening curly bracket.
    CurlyOpen { span: Span<F, S> },
    /// Failed to parse a [`PostulationOp`](ast::PostulationOp).
    PostulationOp { span: Span<F, S> },
    /// Failed to parse a [`Rule`](crate::ast::Rule).
    Rule { span: Span<F, S> },
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
            PostulationOp { span } => {
                let mut fmt = f.debug_struct("ParseError::PostulationOp");
                fmt.field("span", span);
                fmt.finish()
            },
            Rule { span } => {
                let mut fmt = f.debug_struct("ParseError::Rule");
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
            PostulationOp { .. } => write!(f, "{}", PostulationOpExpectsFormatter),
            Rule { .. } => write!(f, "{}", RuleExpectsFormatter),
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
        match self {
            Self::CurlyClose { span } => span.clone(),
            Self::CurlyOpen { span } => span.clone(),
            Self::PostulationOp { span } => span.clone(),
            Self::Rule { span } => span.clone(),
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
            Self::PostulationOp { span } => span,
            Self::Rule { span } => span,
        }
    }
}





/***** LIBRARY *****/
/// Parses a postulation.
///
/// # Returns
/// A [`Postulation`](ast::Postulation) that represents a shorthand transition and trigger.
///
/// # Fails
/// This combinator fails if the head of the input does not contain a valid postulation.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Arrow, Ident, Rule, RuleAntecedents, Dot, Atom, Literal};
/// use datalog::transitions::ast::{Add, Curly, Postulation, PostulationOp, Squiggly};
/// use datalog::transitions::parser::postulation::{postulation, ParseError};
///
/// let span1 = Span::new("<example>", "+{ foo. }");
/// let span2 = Span::new("<example>", "~{ bar :- baz(quz). }");
/// let span3 = Span::new("<example>", "+{}");
/// let span4 = Span::new("<example>", "~{ foo. bar. }");
/// let span5 = Span::new("<example>", "{ foo. }");
/// let span6 = Span::new("<example>", "~{ bar :- baz(quz).");
///
/// let mut comb = postulation();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(9..), Postulation {
///         op: PostulationOp::Create(Add { span: span1.slice(..1) }),
///         curly_tokens: Curly { open: span1.slice(1..2), close: span1.slice(8..9) },
///         rules: vec![Rule {
///             consequences: punct![v => Atom { ident: Ident { value: span1.slice(3..6) }, args: None }],
///             tail: None,
///             dot: Dot { span: span1.slice(6..7) }
///         }],
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(21..), Postulation {
///         op: PostulationOp::Obfuscate(AddSquiggly { span: span2.slice(..1) }),
///         curly_tokens: Curly { open: span2.slice(1..2), close: span2.slice(20..21) },
///         rules: vec![Rule {
///             consequences: punct![v => Atom { ident: Ident { value: span2.slice(3..6) }, args: None }],
///             tail: Some(RuleAntecedents {
///                 arrow_token: Arrow { span: span1.slice(7..9) },
///                 antecedents: punct![v => Literal {  }]
///             }),
///             dot: Dot { span: span2.slice(18..19) }
///         }],
///     })
/// );
/// // assert_eq!(
/// //     comb.parse(span2).unwrap(),
/// //     (span2.slice(1..), PostulationOp::Obfuscate(Squiggly { span: span2.slice(..1) }))
/// // );
/// // assert!(matches!(comb.parse(span3), SResult::Fail(Failure::Common(Common::Alt { .. }))));
/// // assert!(matches!(comb.parse(span4), SResult::Fail(Failure::Common(Common::Alt { .. }))));
/// ```
#[comb(snack = ::ast_toolkit::snack, expected = "a transition definition", Output = ast::Postulation<F, S>, Error = ParseError<F, S>)]
pub fn postulation<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    comb::map(
        seq::pair(
            seq::terminated(postulation_op(), error::transmute(utf8::whitespace0())),
            error::cut(comb::map_err(
                tokens::curly(seq::preceded(
                    error::transmute(utf8::whitespace0()),
                    multi::many0(comb::map_err(seq::terminated(rules::rule(), error::transmute(utf8::whitespace0())), |err| ParseError::Rule {
                        span: err.into_span(),
                    })),
                )),
                |err| match err {
                    ast_toolkit::tokens::snack::complete::ParseError::Inner { err: Common::Custom(err) } => err,
                    ast_toolkit::tokens::snack::complete::ParseError::Utf8OpenToken { token: _, span } => ParseError::CurlyOpen { span },
                    ast_toolkit::tokens::snack::complete::ParseError::Utf8CloseToken { token: _, span } => ParseError::CurlyClose { span },
                    _ => unreachable!(),
                },
            )),
        ),
        |(op, (rules, curly_tokens))| ast::Postulation { op, curly_tokens, rules },
    )
    .parse(input)
}



/// Parses a postulation operator.
///
/// # Returns
/// A [`PostulationOp`](ast::PostulationOp) that represents either `+` or `~`.
///
/// # Fails
/// This combinator fails if the head of the input does not contain `+` or `~`.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::Ident;
/// use datalog::transitions::ast::{Add, PostulationOp, Squiggly};
/// use datalog::transitions::parser::postulation::{postulation_op, ParseError};
///
/// let span1 = Span::new("<example>", "+");
/// let span2 = Span::new("<example>", "~");
/// let span3 = Span::new("<example>", "a");
/// let span4 = Span::new("<example>", "");
///
/// let mut comb = postulation_op();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(1..), PostulationOp::Create(Add { span: span1.slice(..1) }))
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(1..), PostulationOp::Obfuscate(Squiggly { span: span2.slice(..1) }))
/// );
/// assert!(matches!(comb.parse(span3), SResult::Fail(Failure::Common(Common::Alt { .. }))));
/// assert!(matches!(comb.parse(span4), SResult::Fail(Failure::Common(Common::Alt { .. }))));
/// ```
#[comb(snack = ::ast_toolkit::snack, expected = "a postulation operator (\"+\" or \"~\")", Output = ast::PostulationOp<F, S>, Error = ParseError<F, S>)]
pub fn postulation_op<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + WhileUtf8,
{
    comb::map_err(
        branch::alt((
            comb::map(tokens::add(), |add| ast::PostulationOp::Create(add)),
            comb::map(tokens::squiggly(), |squiggly| ast::PostulationOp::Obfuscate(squiggly)),
        )),
        |err| ParseError::PostulationOp { span: err.into_span() },
    )
    .parse(input)
}