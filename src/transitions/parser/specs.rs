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

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{branch, comb, combinator as comb, error, multi, sequence as seq};
use ast_toolkit::span::{Span, Spannable, Spanning};

use super::super::ast;
use super::postulations::PostulationExpectsFormatter;
use super::transitions::TransitionExpectsFormatter;
use super::triggers::TriggerExpectsFormatter;
use super::{postulations, transitions, triggers};
use crate::parser::rules::RuleExpectsFormatter;
use crate::parser::{rules, whitespace0};


/***** ERRORS *****/
/// Errors returned when parsing literals and related.
pub enum ParseError<F, S> {
    /// Failed to parse a [`Postulation`](ast::Postulation).
    Postulation { span: Span<F, S> },
    /// Failed to parse a [`Rule`](crate::ast::Rule).
    Rule { span: Span<F, S> },
    /// Failed to parse a [`Transition`](ast::Transition).
    Transition { span: Span<F, S> },
    /// Failed to parse a [`Trigger`](ast::Trigger).
    Trigger { span: Span<F, S> },
}
impl<F, S> Debug for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Postulation { span } => {
                let mut fmt = f.debug_struct("ParseError::Postulation");
                fmt.field("span", span);
                fmt.finish()
            },
            Rule { span } => {
                let mut fmt = f.debug_struct("ParseError::Rule");
                fmt.field("span", span);
                fmt.finish()
            },
            Transition { span } => {
                let mut fmt = f.debug_struct("ParseError::Transition");
                fmt.field("span", span);
                fmt.finish()
            },
            Trigger { span } => {
                let mut fmt = f.debug_struct("ParseError::Trigger");
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
            Postulation { .. } => write!(f, "{}", PostulationExpectsFormatter),
            Rule { .. } => write!(f, "{}", RuleExpectsFormatter),
            Transition { .. } => write!(f, "{}", TransitionExpectsFormatter),
            Trigger { .. } => write!(f, "{}", TriggerExpectsFormatter),
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
            Postulation { span } => span.clone(),
            Rule { span } => span.clone(),
            Transition { span } => span.clone(),
            Trigger { span } => span.clone(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        use ParseError::*;
        match self {
            Postulation { span } => span,
            Rule { span } => span,
            Transition { span } => span,
            Trigger { span } => span,
        }
    }
}





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
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Arrow, Atom, Fact, FactArgs, Comma, Dot, Ident, Literal, Parens, Rule, RuleBody};
/// use datalog::transitions::ast::{Add, Curly, Exclaim, Phrase, Postulation, PostulationOp, Squiggly, Transition, TransitionSpec, Trigger};
/// use datalog::transitions::parser::specs::{ParseError, trans_spec};
///
/// let span1 = Span::new("<example>", r#"#foo {
///     +{ foo }.
///     ~{ bar } :- baz(quz).
/// }.
/// !{ #foo }.
/// +{ foo }.
/// foo :- bar, baz(quz)."#);
///
/// let mut comb = trans_spec();
/// println!("{:?}", comb.parse(span1));
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (
///         span1.slice(92..),
///         TransitionSpec {
///             phrases: vec![
///                 Phrase::Transition(Transition {
///                     ident: Ident { value: span1.slice(..4) },
///                     curly_tokens: Curly { open: span1.slice(5..6), close: span1.slice(47..48) },
///                     postulations: vec![
///                         Postulation {
///                             op: PostulationOp::Create(Add { span: span1.slice(11..12) }),
///                             curly_tokens: Curly { open: span1.slice(12..13), close: span1.slice(18..19) },
///                             consequents: punct![v => Atom::Fact(Fact { ident: Ident { value: span1.slice(14..17) }, args: None })],
///                             tail: None,
///                             dot: Dot { span: span1.slice(19..20) },
///                         },
///                         Postulation {
///                             op: PostulationOp::Obfuscate(Squiggly { span: span1.slice(25..26) }),
///                             curly_tokens: Curly { open: span1.slice(26..27), close: span1.slice(32..33) },
///                             consequents: punct![v => Atom::Fact(Fact { ident: Ident { value: span1.slice(28..31) }, args: None })],
///                             tail: Some(RuleBody {
///                                 arrow_token: Arrow { span: span1.slice(34..36) },
///                                 antecedents: punct![v => Literal::Atom(Atom::Fact(Fact {
///                                     ident: Ident { value: span1.slice(37..40) },
///                                     args: Some(FactArgs {
///                                         paren_tokens: Parens { open: span1.slice(40..41), close: span1.slice(44..45) },
///                                         args: punct![v => Atom::Fact(Fact {
///                                             ident: Ident { value: span1.slice(41..44) },
///                                             args: None,
///                                         })],
///                                     }),
///                                 }))],
///                             }),
///                             dot: Dot { span: span1.slice(45..46) },
///                         },
///                     ],
///                     dot: Dot { span: span1.slice(48..49) },
///                 }),
///                 Phrase::Trigger(Trigger {
///                     exclaim_token: Exclaim { span: span1.slice(50..51) },
///                     curly_tokens: Curly { open: span1.slice(51..52), close: span1.slice(58..59) },
///                     idents: vec![Ident { value: span1.slice(53..57) }],
///                     dot: Dot { span: span1.slice(59..60) },
///                 }),
///                 Phrase::Postulation(Postulation {
///                     op: PostulationOp::Create(Add { span: span1.slice(61..62) }),
///                     curly_tokens: Curly { open: span1.slice(62..63), close: span1.slice(68..69) },
///                     consequents: punct![v => Atom::Fact(Fact { ident: Ident { value: span1.slice(64..67) }, args: None })],
///                     tail: None,
///                     dot: Dot { span: span1.slice(69..70) },
///                 }),
///                 Phrase::Rule(Rule {
///                     consequents: punct![v => Atom::Fact(Fact { ident: Ident { value: span1.slice(71..74) }, args: None })],
///                     tail: Some(RuleBody {
///                         arrow_token: Arrow { span: span1.slice(75..77) },
///                         antecedents: punct![
///                             v => Literal::Atom(Atom::Fact(Fact {
///                                 ident: Ident { value: span1.slice(78..81) },
///                                 args: None,
///                             })),
///                             p => Comma { span: span1.slice(81..82) },
///                             v => Literal::Atom(Atom::Fact(Fact {
///                                 ident: Ident { value: span1.slice(83..86) },
///                                 args: Some(FactArgs {
///                                     paren_tokens: Parens { open: span1.slice(86..87), close: span1.slice(90..91) },
///                                     args: punct![v => Atom::Fact(Fact {
///                                         ident: Ident { value: span1.slice(87..90) },
///                                         args: None,
///                                     })],
///                                 }),
///                             }))
///                         ],
///                     }),
///                     dot: Dot { span: span1.slice(91..92) },
///                 }),
///             ]
///         }
///     )
/// );
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "zero or more postulations, rules, transition definitions or triggers", Output = ast::TransitionSpec<F, S>, Error = ParseError<F, S>)]
pub fn trans_spec<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + Spannable + WhileUtf8,
{
    comb::map(
        comb::all(multi::many0(seq::delimited(error::transmute(whitespace0::whitespace()), phrase(), error::transmute(whitespace0::whitespace())))),
        |phrases| ast::TransitionSpec { phrases },
    )
    .parse(input)
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
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Arrow, Atom, Fact, FactArgs, Comma, Dot, Ident, Literal, Parens, Rule, RuleBody};
/// use datalog::transitions::ast::{Add, Curly, Exclaim, Phrase, Postulation, PostulationOp, Squiggly, Transition, Trigger};
/// use datalog::transitions::parser::specs::{ParseError, phrase};
///
/// let span1 = Span::new("<example>", "#foo {\n    +{ foo }.\n    ~{ bar } :- baz(quz).\n}.");
/// let span2 = Span::new("<example>", "!{ #foo }.");
/// let span3 = Span::new("<example>", "+{ foo }.");
/// let span4 = Span::new("<example>", "foo :- bar, baz(quz).");
///
/// let mut comb = phrase();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (
///         span1.slice(49..),
///         Phrase::Transition(Transition {
///             ident: Ident { value: span1.slice(..4) },
///             curly_tokens: Curly { open: span1.slice(5..6), close: span1.slice(47..48) },
///             postulations: vec![
///                 Postulation {
///                     op: PostulationOp::Create(Add { span: span1.slice(11..12) }),
///                     curly_tokens: Curly { open: span1.slice(12..13), close: span1.slice(18..19) },
///                     consequents: punct![v => Atom::Fact(Fact { ident: Ident { value: span1.slice(14..17) }, args: None })],
///                     tail: None,
///                     dot: Dot { span: span1.slice(19..20) },
///                 },
///                 Postulation {
///                     op: PostulationOp::Obfuscate(Squiggly { span: span1.slice(25..26) }),
///                     curly_tokens: Curly { open: span1.slice(26..27), close: span1.slice(32..33) },
///                     consequents: punct![v => Atom::Fact(Fact { ident: Ident { value: span1.slice(28..31) }, args: None })],
///                     tail: Some(RuleBody {
///                         arrow_token: Arrow { span: span1.slice(34..36) },
///                         antecedents: punct![v => Literal::Atom(Atom::Fact(Fact {
///                             ident: Ident { value: span1.slice(37..40) },
///                             args: Some(FactArgs {
///                                 paren_tokens: Parens { open: span1.slice(40..41), close: span1.slice(44..45) },
///                                 args: punct![v => Atom::Fact(Fact {
///                                     ident: Ident { value: span1.slice(41..44) },
///                                     args: None,
///                                 })],
///                             }),
///                         }))],
///                     }),
///                     dot: Dot { span: span1.slice(45..46) },
///                 },
///             ],
///             dot: Dot { span: span3.slice(48..49) },
///         })
///     )
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(10..), Phrase::Trigger(Trigger {
///         exclaim_token: Exclaim { span: span2.slice(..1) },
///         curly_tokens: Curly { open: span2.slice(1..2), close: span2.slice(8..9) },
///         idents: vec![Ident { value: span2.slice(3..7) }],
///         dot: Dot { span: span3.slice(9..10) },
///     }))
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(9..), Phrase::Postulation(Postulation {
///         op: PostulationOp::Create(Add { span: span3.slice(..1) }),
///         curly_tokens: Curly { open: span3.slice(1..2), close: span3.slice(7..8) },
///         consequents: punct![v => Atom::Fact(Fact { ident: Ident { value: span3.slice(3..6) }, args: None })],
///         tail: None,
///         dot: Dot { span: span3.slice(8..9) }
///     }))
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (span4.slice(21..), Phrase::Rule(Rule {
///         consequents: punct![v => Atom::Fact(Fact { ident: Ident { value: span4.slice(..3) }, args: None })],
///         tail: Some(RuleBody {
///             arrow_token: Arrow { span: span4.slice(4..6) },
///             antecedents: punct![
///                 v => Literal::Atom(Atom::Fact(Fact {
///                     ident: Ident { value: span4.slice(7..10) },
///                     args: None,
///                 })),
///                 p => Comma { span: span4.slice(10..11) },
///                 v => Literal::Atom(Atom::Fact(Fact {
///                     ident: Ident { value: span4.slice(12..15) },
///                     args: Some(FactArgs {
///                         paren_tokens: Parens { open: span4.slice(15..16), close: span4.slice(19..20) },
///                         args: punct![v => Atom::Fact(Fact {
///                             ident: Ident { value: span4.slice(16..19) },
///                             args: None,
///                         })],
///                     }),
///                 }))
///             ],
///         }),
///         dot: Dot { span: span4.slice(20..21) },
///     }))
/// );
/// ```
#[comb(snack = ::ast_toolkit::snack, expected = "a postulation, rule, transition definition or trigger", Output = ast::Phrase<F, S>, Error = ParseError<F, S>)]
pub fn phrase<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    branch::alt((
        comb::map_err(comb::map(postulations::postulation(), ast::Phrase::Postulation), |err| ParseError::Postulation { span: err.into_span() }),
        comb::map_err(comb::map(rules::rule(), ast::Phrase::Rule), |err| ParseError::Rule { span: err.into_span() }),
        comb::map_err(comb::map(transitions::transition(), ast::Phrase::Transition), |err| ParseError::Transition { span: err.into_span() }),
        comb::map_err(comb::map(triggers::trigger(), ast::Phrase::Trigger), |err| ParseError::Trigger { span: err.into_span() }),
    ))
    .parse(input)
}
