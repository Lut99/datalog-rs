//  TRANSITIONS.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 11:01:38
//  Last edited:
//    07 Feb 2025, 17:44:45
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a parser for transitions definitions.
//

use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{combinator as comb, multi, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use super::super::ast;
use super::{idents, postulations, tokens};
use crate::parser::whitespace0;


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
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Arrow, Atom, Comma, Dot, Fact, Ident, Literal, Parens, Rule, RuleBody};
/// use datalog::transitions::ast::{Add, Curly, Postulation, PostulationOp, Squiggly, Transition};
/// use datalog::transitions::parser::transitions::transition;
///
/// let span1 = Span::new(("<example>", "#foo {}."));
/// let span2 = Span::new(("<example>", "#bar { +{ foo }. }."));
/// let span3 = Span::new(("<example>", "#baz { ~{ foo, bar }. +{ baz }. }."));
///
/// let mut comb = transition();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(8..), Transition {
///         ident: Ident { value: "#foo".into(), span: Some(span1.slice(..4)) },
///         curly_tokens: Curly {
///             open:  span1.slice(5..6).into(),
///             close: span1.slice(6..7).into(),
///         },
///         postulations: vec![],
///         dot: span3.slice(7..8).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(19..), Transition {
///         ident: Ident { value: "#bar".into(), span: Some(span2.slice(..4)) },
///         curly_tokens: Curly {
///             open:  span2.slice(5..6).into(),
///             close: span2.slice(17..18).into(),
///         },
///         postulations: vec![Postulation {
///             op: PostulationOp::Create(Add::from(span2.slice(7..8))),
///             curly_tokens: Curly {
///                 open:  span2.slice(8..9).into(),
///                 close: span2.slice(14..15).into(),
///             },
///             consequents: punct![Atom::Fact(Fact {
///                 ident: Ident { value: "foo".into(), span: Some(span2.slice(10..13)) },
///                 args:  None,
///             })],
///             tail: None,
///             dot: span2.slice(15..16).into(),
///         }],
///         dot: span3.slice(18..19).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(34..), Transition {
///         ident: Ident { value: "#baz".into(), span: Some(span3.slice(..4)) },
///         curly_tokens: Curly {
///             open:  span3.slice(5..6).into(),
///             close: span3.slice(32..33).into(),
///         },
///         postulations: vec![
///             Postulation {
///                 op: PostulationOp::Obfuscate(Squiggly::from(span3.slice(7..8))),
///                 curly_tokens: Curly {
///                     open:  span3.slice(8..9).into(),
///                     close: span3.slice(19..20).into(),
///                 },
///                 consequents: punct![
///                     Atom::Fact(Fact {
///                         ident: Ident { value: "foo".into(), span: Some(span3.slice(10..13)) },
///                         args:  None,
///                     }),
///                     Comma::from(span3.slice(13..14)),
///                     Atom::Fact(Fact {
///                         ident: Ident { value: "bar".into(), span: Some(span3.slice(15..18)) },
///                         args:  None,
///                     })
///                 ],
///                 tail: None,
///                 dot: span3.slice(20..21).into(),
///             },
///             Postulation {
///                 op: PostulationOp::Create(Add::from(span3.slice(22..23))),
///                 curly_tokens: Curly {
///                     open:  span3.slice(23..24).into(),
///                     close: span3.slice(29..30).into(),
///                 },
///                 consequents: punct![Atom::Fact(Fact {
///                     ident: Ident { value: "baz".into(), span: Some(span3.slice(25..28)) },
///                     args:  None,
///                 })],
///                 tail: None,
///                 dot: span3.slice(30..31).into(),
///             },
///         ],
///         dot: span3.slice(33..34).into(),
///     })
/// );
/// ```
pub fn transition<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Transition<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        seq::tuple((
            seq::terminated(idents::trans_ident(), whitespace0()),
            tokens::curly(seq::preceded(whitespace0(), multi::many0(seq::terminated(postulations::postulation(), whitespace0())))),
            crate::parser::tokens::dot(),
        )),
        |(ident, (curly_tokens, postulations), dot)| ast::Transition { ident, curly_tokens, postulations, dot },
    )
    .boxed()
}
