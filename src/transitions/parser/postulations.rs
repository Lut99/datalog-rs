//  POSTULATIONS.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 11:10:12
//  Last edited:
//    03 Dec 2024, 17:20:24
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
use ast_toolkit::snack::{branch, comb, combinator as comb, error, multi, sequence as seq};
use ast_toolkit::span::{Span, Spanning};

use super::super::ast;
use super::tokens;
use crate::parser::atoms::{self, AtomExpectsFormatter};
use crate::parser::rules::{self, RuleAntecedentsExpectsFormatter};
use crate::parser::whitespaces;


/***** ERRORS *****/
/// Errors returned when parsing postulations and related.
pub enum ParseError<F, S> {
    /// Failed to parse an [`Atom`](crate::ast::Atom).
    Atom { span: Span<F, S> },
    /// Failed to parse a comma.
    Comma { span: Span<F, S> },
    /// Failed to parse the closing curly bracket.
    CurlyClose { span: Span<F, S> },
    /// Failed to parse the opening curly bracket.
    CurlyOpen { span: Span<F, S> },
    /// Failed to parse the ending dot of a postulation.
    Dot { span: Span<F, S> },
    /// Failed to parse a [`PostulationOp`](ast::PostulationOp).
    PostulationOp { span: Span<F, S> },
    /// Failed to parse a [`RuleAntecedents`](crate::ast::RuleAntecedents).
    RuleAntecedents { span: Span<F, S> },
}
impl<F, S> Debug for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Atom { span } => {
                let mut fmt = f.debug_struct("ParseError::Atom");
                fmt.field("span", span);
                fmt.finish()
            },
            Comma { span } => {
                let mut fmt = f.debug_struct("ParseError::Comma");
                fmt.field("span", span);
                fmt.finish()
            },
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
            PostulationOp { span } => {
                let mut fmt = f.debug_struct("ParseError::PostulationOp");
                fmt.field("span", span);
                fmt.finish()
            },
            RuleAntecedents { span } => {
                let mut fmt = f.debug_struct("ParseError::RuleAntecedents");
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
            Atom { .. } => write!(f, "{}", AtomExpectsFormatter),
            Comma { .. } => write!(f, "Expected a comma"),
            CurlyClose { .. } => write!(f, "Expected a closing curly bracket"),
            CurlyOpen { .. } => write!(f, "Expected an opening curly bracket"),
            Dot { .. } => write!(f, "Expected a dot"),
            PostulationOp { .. } => write!(f, "{}", PostulationOpExpectsFormatter),
            RuleAntecedents { .. } => write!(f, "{}", RuleAntecedentsExpectsFormatter),
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
            Self::Atom { span } => span.clone(),
            Self::Comma { span } => span.clone(),
            Self::CurlyClose { span } => span.clone(),
            Self::CurlyOpen { span } => span.clone(),
            Self::Dot { span } => span.clone(),
            Self::PostulationOp { span } => span.clone(),
            Self::RuleAntecedents { span } => span.clone(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        match self {
            Self::Atom { span } => span,
            Self::Comma { span } => span,
            Self::CurlyClose { span } => span,
            Self::CurlyOpen { span } => span,
            Self::Dot { span } => span,
            Self::PostulationOp { span } => span,
            Self::RuleAntecedents { span } => span,
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
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Arrow, Atom, AtomArg, AtomArgs, Comma, Dot, Ident, Literal, Parens, Rule, RuleAntecedents};
/// use datalog::transitions::ast::{Add, Curly, Postulation, PostulationOp, Squiggly};
/// use datalog::transitions::parser::postulations::{postulation, ParseError};
///
/// let span1 = Span::new("<example>", "+{ foo }.");
/// let span2 = Span::new("<example>", "~{ bar } :- baz(quz).");
/// let span3 = Span::new("<example>", "+{}.");
/// let span4 = Span::new("<example>", "~{ foo, bar }.");
/// let span5 = Span::new("<example>", "{ foo }.");
/// let span6 = Span::new("<example>", "~{ bar :- baz(quz).");
///
/// let mut comb = postulation();
/// println!("{:?}", comb.parse(span1));
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(9..), Postulation {
///         op: PostulationOp::Create(Add { span: span1.slice(..1) }),
///         curly_tokens: Curly { open: span1.slice(1..2), close: span1.slice(7..8) },
///         consequents: punct![v => Atom { ident: Ident { value: span1.slice(3..6) }, args: None }],
///         tail: None,
///         dot: Dot { span: span1.slice(8..9) },
///     })
/// );
/// println!("{:?}", comb.parse(span2));
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(21..), Postulation {
///         op: PostulationOp::Obfuscate(Squiggly { span: span2.slice(..1) }),
///         curly_tokens: Curly { open: span2.slice(1..2), close: span2.slice(7..8) },
///         consequents: punct![v => Atom { ident: Ident { value: span2.slice(3..6) }, args: None }],
///         tail: Some(RuleAntecedents {
///             arrow_token: Arrow { span: span2.slice(9..11) },
///             antecedents: punct![v => Literal::Atom(Atom {
///                 ident: Ident { value: span2.slice(12..15) },
///                 args: Some(AtomArgs {
///                     paren_tokens: Parens { open: span2.slice(15..16), close: span2.slice(19..20) },
///                     args: punct![v => AtomArg::Atom(Ident { value: span2.slice(16..19) })]
///                 })
///             })]
///         }),
///         dot: Dot { span: span2.slice(20..21) }
///     })
/// );
/// println!("{:?}", comb.parse(span3));
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(4..), Postulation {
///         op: PostulationOp::Create(Add { span: span3.slice(..1) }),
///         curly_tokens: Curly { open: span3.slice(1..2), close: span3.slice(2..3) },
///         consequents: punct![],
///         tail: None,
///         dot: Dot { span: span3.slice(3..4) },
///     })
/// );
/// println!("{:?}", comb.parse(span4));
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (span4.slice(14..), Postulation {
///         op: PostulationOp::Create(Add { span: span4.slice(..1) }),
///         curly_tokens: Curly { open: span4.slice(1..2), close: span4.slice(12..13) },
///         consequents: punct![
///             v => Atom { ident: Ident { value: span4.slice(3..6) }, args: None },
///             p => Comma { span: span4.slice(6..7) },
///             v => Atom { ident: Ident { value: span4.slice(8..11) }, args: None }
///         ],
///         tail: None,
///         dot: Dot { span: span4.slice(13..14) }
///     })
/// );
/// assert!(matches!(comb.parse(span5), SResult::Fail(Failure::Common(Common::Alt { .. }))));
/// assert!(matches!(comb.parse(span6), SResult::Error(Error::Common(Common::Custom(ParseError::CurlyClose { .. })))));
/// ```
#[comb(snack = ::ast_toolkit::snack, expected = "a transition definition", Output = ast::Postulation<F, S>, Error = ParseError<F, S>)]
pub fn postulation<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    comb::map(
        seq::pair(
            seq::terminated(postulation_op(), error::transmute(whitespaces::whitespace())),
            error::cut(seq::tuple((
                comb::map_err(
                    tokens::curly(multi::punctuated0(
                        seq::delimited(
                            error::transmute(whitespaces::whitespace()),
                            comb::map_err(atoms::atom(), |err| ParseError::Atom { span: err.span() }),
                            error::transmute(whitespaces::whitespace()),
                            // error::transmute(comb::not(utf8::complete::while1(|c| {
                            //     if c.len() != 1 {
                            //         return false;
                            //     }
                            //     let c: char = c.chars().next().unwrap();
                            //     (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_'
                            // }))),
                        ),
                        comb::map_err(crate::parser::tokens::comma(), |err| ParseError::Comma { span: err.into_span() }),
                    )),
                    |err| match err {
                        ast_toolkit::tokens::snack::complete::ParseError::Inner { err: Common::Custom(err) } => err,
                        ast_toolkit::tokens::snack::complete::ParseError::Utf8OpenToken { token: _, span } => ParseError::CurlyOpen { span },
                        ast_toolkit::tokens::snack::complete::ParseError::Utf8CloseToken { token: _, span } => ParseError::CurlyClose { span },
                        _ => unreachable!(),
                    },
                ),
                error::transmute(whitespaces::whitespace()),
                comb::map_err(comb::opt(rules::rule_antecedents()), |err| ParseError::RuleAntecedents { span: err.into_span() }),
                error::transmute(whitespaces::whitespace()),
                comb::map_err(crate::parser::tokens::dot(), |err| ParseError::Dot { span: err.into_span() }),
            ))),
        ),
        |(op, ((consequents, curly_tokens), _, tail, _, dot))| ast::Postulation { op, curly_tokens, consequents, tail, dot },
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
/// use datalog::transitions::parser::postulations::{ParseError, postulation_op};
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
