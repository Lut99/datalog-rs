//  POSTULATIONS.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 11:10:12
//  Last edited:
//    07 Feb 2025, 17:46:05
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for postulations.
//

use ast_toolkit::punctuated::snack as punctuated;
use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{branch, combinator as comb, error, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use super::super::ast;
use super::tokens;
use crate::parser::{atoms, rules, whitespace0};


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
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, Parens, Rule, RuleBody,
/// };
/// use datalog::transitions::ast::{Add, Curly, Postulation, PostulationOp, Squiggly};
/// use datalog::transitions::parser::postulations::postulation;
///
/// let span1 = Span::new(("<example>", "+{ foo }."));
/// let span2 = Span::new(("<example>", "~{ bar } :- baz(quz)."));
/// let span3 = Span::new(("<example>", "+{}."));
/// let span4 = Span::new(("<example>", "~{ foo, bar }."));
/// let span5 = Span::new(("<example>", "{ foo }."));
/// let span6 = Span::new(("<example>", "~{ bar :- baz(quz)."));
///
/// let mut comb = postulation();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(9..), Postulation {
///         op: PostulationOp::Create(Add::from(span1.slice(..1))),
///         curly_tokens: Curly {
///             open:  span1.slice(1..2).into(),
///             close: span1.slice(7..8).into(),
///         },
///         consequents: punct![Atom::Fact(Fact {
///             ident: Ident { value: "foo".into(), span: Some(span1.slice(3..6)) },
///             args:  None,
///         })],
///         tail: None,
///         dot: span1.slice(8..9).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(21..), Postulation {
///         op: PostulationOp::Obfuscate(Squiggly::from(span2.slice(..1))),
///         curly_tokens: Curly {
///             open:  span2.slice(1..2).into(),
///             close: span2.slice(7..8).into(),
///         },
///         consequents: punct![Atom::Fact(Fact {
///             ident: Ident { value: "bar".into(), span: Some(span2.slice(3..6)) },
///             args:  None,
///         })],
///         tail: Some(RuleBody {
///             arrow_token: span2.slice(9..11).into(),
///             antecedents: punct![Literal::Atom(Atom::Fact(Fact {
///                 ident: Ident { value: "baz".into(), span: Some(span2.slice(12..15)) },
///                 args:  Some(FactArgs {
///                     paren_tokens: Parens {
///                         open:  span2.slice(15..16).into(),
///                         close: span2.slice(19..20).into(),
///                     },
///                     args: punct![Atom::Fact(Fact {
///                         ident: Ident { value: "quz".into(), span: Some(span2.slice(16..19)) },
///                         args:  None,
///                     })],
///                 }),
///             }))],
///         }),
///         dot: span2.slice(20..21).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(4..), Postulation {
///         op: PostulationOp::Create(Add::from(span3.slice(..1))),
///         curly_tokens: Curly {
///             open:  span3.slice(1..2).into(),
///             close: span3.slice(2..3).into(),
///         },
///         consequents: Punctuated::new(),
///         tail: None,
///         dot: span3.slice(3..4).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (span4.slice(14..), Postulation {
///         op: PostulationOp::Obfuscate(Squiggly::from(span4.slice(..1))),
///         curly_tokens: Curly {
///             open:  span4.slice(1..2).into(),
///             close: span4.slice(12..13).into(),
///         },
///         consequents: punct![
///             Atom::Fact(Fact {
///                 ident: Ident { value: "foo".into(), span: Some(span4.slice(3..6)) },
///                 args:  None,
///             }),
///             Comma::from(span4.slice(6..7)),
///             Atom::Fact(Fact {
///                 ident: Ident { value: "bar".into(), span: Some(span4.slice(8..11)) },
///                 args:  None,
///             })
///         ],
///         tail: None,
///         dot: span4.slice(13..14).into(),
///     })
/// );
/// assert!(matches!(comb.parse(span5), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span6), Err(SnackError::Fatal(_))));
/// ```
pub fn postulation<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Postulation<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        seq::pair(
            seq::terminated(postulation_op(), whitespace0()),
            error::cut(seq::tuple((
                tokens::curly(punctuated::punctuated_nontrailing_many0(
                    seq::delimited(whitespace0(), atoms::atom(), whitespace0()),
                    crate::parser::tokens::comma(),
                )),
                whitespace0(),
                comb::opt(rules::rule_body()),
                whitespace0(),
                crate::parser::tokens::dot(),
            ))),
        ),
        |(op, ((curly_tokens, consequents), _, tail, _, dot))| ast::Postulation { op, curly_tokens, consequents, tail, dot },
    )
    .boxed()
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
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::Ident;
/// use datalog::transitions::ast::{Add, PostulationOp, Squiggly};
/// use datalog::transitions::parser::postulations::postulation_op;
///
/// let span1 = Span::new(("<example>", "+"));
/// let span2 = Span::new(("<example>", "~"));
/// let span3 = Span::new(("<example>", "a"));
/// let span4 = Span::new(("<example>", ""));
///
/// let mut comb = postulation_op();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(1..), PostulationOp::Create(Add::from(span1.slice(..1))))
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(1..), PostulationOp::Obfuscate(Squiggly::from(span2.slice(..1))))
/// );
/// assert!(matches!(comb.parse(span3), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span4), Err(SnackError::Recoverable(_))));
/// ```
pub fn postulation_op<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::PostulationOp<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    branch::alt((
        comb::map(tokens::add(), |add| ast::PostulationOp::Create(add)),
        comb::map(tokens::squiggly(), |squiggly| ast::PostulationOp::Obfuscate(squiggly)),
    ))
    .boxed()
}
