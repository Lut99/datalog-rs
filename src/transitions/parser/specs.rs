//  SPECS.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 15:45:02
//  Last edited:
//    07 Feb 2025, 17:44:40
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines the toplevel parsers of the transition.
//

use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{branch, combinator as comb, multi, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use super::super::ast;
use super::{postulations, transitions, triggers};
use crate::parser::{rules, whitespace0};


/***** LIBRARY *****/
/// Parses a whole specification with both transitions and rules.
///
/// # Returns
/// A [`TransitionSpec`](ast::TransitionSpec) that represents rules and transitions.
///
/// # Fails
/// This combinator fails if the head of the input as a whole does not contain valid datalog.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, Parens, Rule, RuleBody,
/// };
/// use datalog::transitions::ast::{
///     Add, Curly, Exclaim, Phrase, Postulation, PostulationOp, Squiggly, Transition,
///     TransitionSpec, Trigger,
/// };
/// use datalog::transitions::parser::specs::trans_spec;
///
/// let span1 = Span::new((
///     "<example>",
///     r#"#foo {
///     +{ foo }.
///     ~{ bar } :- baz(quz).
/// }.
/// !{ #foo }.
/// +{ foo }.
/// foo :- bar, baz(quz)."#,
/// ));
///
/// let mut comb = trans_spec();
/// println!("{:?}", comb.parse(span1));
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(92..), TransitionSpec {
///         phrases: vec![
///             Phrase::Transition(Transition {
///                 ident: Ident { value: "#foo".into(), span: Some(span1.slice(..4)) },
///                 curly_tokens: Curly {
///                     open:  span1.slice(5..6).into(),
///                     close: span1.slice(47..48).into(),
///                 },
///                 postulations: vec![
///                     Postulation {
///                         op: PostulationOp::Create(Add::from(span1.slice(11..12))),
///                         curly_tokens: Curly {
///                             open:  span1.slice(12..13).into(),
///                             close: span1.slice(18..19).into(),
///                         },
///                         consequents: punct![Atom::Fact(Fact {
///                             ident: Ident {
///                                 value: "foo".into(),
///                                 span:  Some(span1.slice(14..17)),
///                             },
///                             args:  None,
///                         })],
///                         tail: None,
///                         dot: span1.slice(19..20).into(),
///                     },
///                     Postulation {
///                         op: PostulationOp::Obfuscate(Squiggly::from(span1.slice(25..26))),
///                         curly_tokens: Curly {
///                             open:  span1.slice(26..27).into(),
///                             close: span1.slice(32..33).into(),
///                         },
///                         consequents: punct![Atom::Fact(Fact {
///                             ident: Ident {
///                                 value: "bar".into(),
///                                 span:  Some(span1.slice(28..31)),
///                             },
///                             args:  None,
///                         })],
///                         tail: Some(RuleBody {
///                             arrow_token: span1.slice(34..36).into(),
///                             antecedents: punct![Literal::Atom(Atom::Fact(Fact {
///                                 ident: Ident {
///                                     value: "baz".into(),
///                                     span:  Some(span1.slice(37..40)),
///                                 },
///                                 args:  Some(FactArgs {
///                                     paren_tokens: Parens {
///                                         open:  span1.slice(40..41).into(),
///                                         close: span1.slice(44..45).into(),
///                                     },
///                                     args: punct![Atom::Fact(Fact {
///                                         ident: Ident {
///                                             value: "quz".into(),
///                                             span:  Some(span1.slice(41..44)),
///                                         },
///                                         args:  None,
///                                     })],
///                                 }),
///                             }))],
///                         }),
///                         dot: span1.slice(45..46).into(),
///                     },
///                 ],
///                 dot: span1.slice(48..49).into(),
///             }),
///             Phrase::Trigger(Trigger {
///                 exclaim_token: span1.slice(50..51).into(),
///                 curly_tokens: Curly {
///                     open:  span1.slice(51..52).into(),
///                     close: span1.slice(58..59).into(),
///                 },
///                 idents: vec![Ident { value: "#foo".into(), span: Some(span1.slice(53..57)) }],
///                 dot: span1.slice(59..60).into(),
///             }),
///             Phrase::Postulation(Postulation {
///                 op: PostulationOp::Create(Add::from(span1.slice(61..62))),
///                 curly_tokens: Curly {
///                     open:  span1.slice(62..63).into(),
///                     close: span1.slice(68..69).into(),
///                 },
///                 consequents: punct![Atom::Fact(Fact {
///                     ident: Ident { value: "foo".into(), span: Some(span1.slice(64..67)) },
///                     args:  None,
///                 })],
///                 tail: None,
///                 dot: span1.slice(69..70).into(),
///             }),
///             Phrase::Rule(Rule {
///                 consequents: punct![Atom::Fact(Fact {
///                     ident: Ident { value: "foo".into(), span: Some(span1.slice(71..74)) },
///                     args:  None,
///                 })],
///                 tail: Some(RuleBody {
///                     arrow_token: span1.slice(75..77).into(),
///                     antecedents: punct![
///                         Literal::Atom(Atom::Fact(Fact {
///                             ident: Ident {
///                                 value: "bar".into(),
///                                 span:  Some(span1.slice(78..81)),
///                             },
///                             args:  None,
///                         })),
///                         Comma::from(span1.slice(81..82)),
///                         Literal::Atom(Atom::Fact(Fact {
///                             ident: Ident {
///                                 value: "baz".into(),
///                                 span:  Some(span1.slice(83..86)),
///                             },
///                             args:  Some(FactArgs {
///                                 paren_tokens: Parens {
///                                     open:  span1.slice(86..87).into(),
///                                     close: span1.slice(90..91).into(),
///                                 },
///                                 args: punct![Atom::Fact(Fact {
///                                     ident: Ident {
///                                         value: "quz".into(),
///                                         span:  Some(span1.slice(87..90)),
///                                     },
///                                     args:  None,
///                                 })],
///                             }),
///                         }))
///                     ],
///                 }),
///                 dot: span1.slice(91..92).into(),
///             }),
///         ],
///     })
/// );
/// ```
#[inline]
pub fn trans_spec<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::TransitionSpec<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(comb::consume(multi::many0(seq::delimited(whitespace0(), phrase(), whitespace0()))), |phrases| ast::TransitionSpec { phrases }).boxed()
}



/// Parses a phrase.
///
/// # Returns
/// A [`Phrase`](ast::Phrase) that represents one of the possible phrases at the toplevel.
///
/// # Fails
/// This combinator fails if the head of the input does not contain a valid phrase.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, Parens, Rule, RuleBody,
/// };
/// use datalog::transitions::ast::{
///     Add, Curly, Exclaim, Phrase, Postulation, PostulationOp, Squiggly, Transition, Trigger,
/// };
/// use datalog::transitions::parser::specs::phrase;
///
/// let span1 = Span::new(("<example>", "#foo {\n    +{ foo }.\n    ~{ bar } :- baz(quz).\n}."));
/// let span2 = Span::new(("<example>", "!{ #foo }."));
/// let span3 = Span::new(("<example>", "+{ foo }."));
/// let span4 = Span::new(("<example>", "foo :- bar, baz(quz)."));
///
/// let mut comb = phrase();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (
///         span1.slice(49..),
///         Phrase::Transition(Transition {
///             ident: Ident { value: "#foo".into(), span: Some(span1.slice(..4)) },
///             curly_tokens: Curly {
///                 open:  span1.slice(5..6).into(),
///                 close: span1.slice(47..48).into(),
///             },
///             postulations: vec![
///                 Postulation {
///                     op: PostulationOp::Create(Add::from(span1.slice(11..12))),
///                     curly_tokens: Curly {
///                         open:  span1.slice(12..13).into(),
///                         close: span1.slice(18..19).into(),
///                     },
///                     consequents: punct![Atom::Fact(Fact {
///                         ident: Ident { value: "foo".into(), span: Some(span1.slice(14..17)) },
///                         args:  None,
///                     })],
///                     tail: None,
///                     dot: span1.slice(19..20).into(),
///                 },
///                 Postulation {
///                     op: PostulationOp::Obfuscate(Squiggly::from(span1.slice(25..26))),
///                     curly_tokens: Curly {
///                         open:  span1.slice(26..27).into(),
///                         close: span1.slice(32..33).into(),
///                     },
///                     consequents: punct![Atom::Fact(Fact {
///                         ident: Ident { value: "bar".into(), span: Some(span1.slice(28..31)) },
///                         args:  None,
///                     })],
///                     tail: Some(RuleBody {
///                         arrow_token: span1.slice(34..36).into(),
///                         antecedents: punct![Literal::Atom(Atom::Fact(Fact {
///                             ident: Ident {
///                                 value: "baz".into(),
///                                 span:  Some(span1.slice(37..40)),
///                             },
///                             args:  Some(FactArgs {
///                                 paren_tokens: Parens {
///                                     open:  span1.slice(40..41).into(),
///                                     close: span1.slice(44..45).into(),
///                                 },
///                                 args: punct![Atom::Fact(Fact {
///                                     ident: Ident {
///                                         value: "quz".into(),
///                                         span:  Some(span1.slice(41..44)),
///                                     },
///                                     args:  None,
///                                 })],
///                             }),
///                         }))],
///                     }),
///                     dot: span1.slice(45..46).into(),
///                 },
///             ],
///             dot: span3.slice(48..49).into(),
///         })
///     )
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (
///         span2.slice(10..),
///         Phrase::Trigger(Trigger {
///             exclaim_token: span2.slice(..1).into(),
///             curly_tokens: Curly {
///                 open:  span2.slice(1..2).into(),
///                 close: span2.slice(8..9).into(),
///             },
///             idents: vec![Ident { value: "#foo".into(), span: Some(span2.slice(3..7)) }],
///             dot: span3.slice(9..10).into(),
///         })
///     )
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (
///         span3.slice(9..),
///         Phrase::Postulation(Postulation {
///             op: PostulationOp::Create(Add::from(span3.slice(..1))),
///             curly_tokens: Curly {
///                 open:  span3.slice(1..2).into(),
///                 close: span3.slice(7..8).into(),
///             },
///             consequents: punct![Atom::Fact(Fact {
///                 ident: Ident { value: "foo".into(), span: Some(span3.slice(3..6)) },
///                 args:  None,
///             })],
///             tail: None,
///             dot: span3.slice(8..9).into(),
///         })
///     )
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (
///         span4.slice(21..),
///         Phrase::Rule(Rule {
///             consequents: punct![Atom::Fact(Fact {
///                 ident: Ident { value: "foo".into(), span: Some(span4.slice(..3)) },
///                 args:  None,
///             })],
///             tail: Some(RuleBody {
///                 arrow_token: span4.slice(4..6).into(),
///                 antecedents: punct![
///                     Literal::Atom(Atom::Fact(Fact {
///                         ident: Ident { value: "bar".into(), span: Some(span4.slice(7..10)) },
///                         args:  None,
///                     })),
///                     Comma::from(span4.slice(10..11)),
///                     Literal::Atom(Atom::Fact(Fact {
///                         ident: Ident { value: "baz".into(), span: Some(span4.slice(12..15)) },
///                         args:  Some(FactArgs {
///                             paren_tokens: Parens {
///                                 open:  span4.slice(15..16).into(),
///                                 close: span4.slice(19..20).into(),
///                             },
///                             args: punct![Atom::Fact(Fact {
///                                 ident: Ident {
///                                     value: "quz".into(),
///                                     span:  Some(span4.slice(16..19)),
///                                 },
///                                 args:  None,
///                             })],
///                         }),
///                     }))
///                 ],
///             }),
///             dot: span4.slice(20..21).into(),
///         })
///     )
/// );
/// ```
pub fn phrase<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Phrase<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    branch::alt((
        comb::map(postulations::postulation(), ast::Phrase::Postulation),
        comb::map(rules::rule(), ast::Phrase::Rule),
        comb::map(transitions::transition(), ast::Phrase::Transition),
        comb::map(triggers::trigger(), ast::Phrase::Trigger),
    ))
    .boxed()
}
