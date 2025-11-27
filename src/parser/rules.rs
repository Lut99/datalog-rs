//  RULES.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 16:38:16
//  Last edited:
//    07 Feb 2025, 17:19:28
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements combinators for parsing $Datalog^\neg$ rules.
//

use ast_toolkit::punctuated::snack as punctuated;
use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{combinator as comb, error, scan, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use super::{atoms, literals, tokens, whitespace0};
use crate::ast;


/***** LIBRARY *****/
/// Parses $Datalog^\neg$ rules.
///
/// # Returns
/// A combinator that parses a punctuated list of consequences, then `:-`, and then a punctuated list of antecedents, finalized by a dot.
///
/// # Fails
/// This combinator fails if the input was not an arrow followed by comma-separated atoms.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, NegAtom, Not, Parens, Rule,
///     RuleBody,
/// };
/// use datalog::parser::rules::rule;
///
/// let span1 = Span::new(("<example>", "foo :- bar."));
/// let span2 = Span::new(("<example>", "foo, bar."));
/// let span3 = Span::new(("<example>", "bar(foo) :- baz(Qux)."));
/// let span4 = Span::new(("<example>", "."));
/// let span5 = Span::new(("<example>", ":-"));
///
/// let mut comb = rule();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(11..), Rule {
///         consequents: punct![Atom::Fact(Fact {
///             ident: Ident { value: span1.slice(..3) },
///             args:  None,
///         })],
///         tail: Some(RuleBody {
///             arrow_token: span1.slice(4..6).into(),
///             antecedents: punct![Literal::Atom(Atom::Fact(Fact {
///                 ident: Ident { value: span1.slice(7..10) },
///                 args:  None,
///             }))],
///         }),
///         dot: span1.slice(10..11).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(9..), Rule {
///         consequents: punct![
///             Atom::Fact(Fact { ident: Ident { value: span2.slice(..3) }, args: None }),
///             Comma::from(span2.slice(3..4)),
///             Atom::Fact(Fact { ident: Ident { value: span2.slice(5..8) }, args: None })
///         ],
///         tail: None,
///         dot: span2.slice(8..9).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(21..), Rule {
///         consequents: punct![Atom::Fact(Fact {
///             ident: Ident { value: span3.slice(..3) },
///             args:  Some(FactArgs {
///                 paren_tokens: Parens {
///                     open:  span3.slice(3..4).into(),
///                     close: span3.slice(7..8).into(),
///                 },
///                 args: punct![Atom::Fact(Fact {
///                     ident: Ident { value: span3.slice(4..7) },
///                     args:  None,
///                 })],
///             }),
///         })],
///         tail: Some(RuleBody {
///             arrow_token: span3.slice(9..11).into(),
///             antecedents: punct![Literal::Atom(Atom::Fact(Fact {
///                 ident: Ident { value: span3.slice(12..15) },
///                 args:  Some(FactArgs {
///                     paren_tokens: Parens {
///                         open:  span3.slice(15..16).into(),
///                         close: span3.slice(19..20).into(),
///                     },
///                     args: punct![Atom::Var(Ident { value: span3.slice(16..19) })],
///                 }),
///             }))],
///         }),
///         dot: span3.slice(20..21).into(),
///     })
/// );
/// assert!(matches!(comb.parse(span4), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span5), Err(SnackError::Recoverable(_))));
/// ```
#[inline]
pub fn rule<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Rule<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        seq::tuple((
            punctuated::punctuated_nontrailing_many1(
                seq::delimited(
                    whitespace0(),
                    atoms::atom(),
                    comb::not(scan::while1("an identifier", |&b| (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-' || b == b'_')),
                ),
                tokens::comma(),
            ),
            whitespace0(),
            comb::opt(rule_body()),
            whitespace0(),
            tokens::dot(),
        )),
        |(consequents, _, tail, _, dot)| ast::Rule { consequents, tail, dot },
    )
    .boxed()
}

/// Parses the body-part of a rule.
///
/// # Returns
/// A combinator that parses `:-`, then a punctuated list of atoms.
///
/// # Fails
/// This combinator fails if the input was not an arrow followed by comma-separated atoms.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Comma, Fact, FactArgs, Ident, Literal, NegAtom, Not, Parens, RuleBody,
/// };
/// use datalog::parser::rules::rule_body;
///
/// let span1 = Span::new(("<example>", ":- foo"));
/// let span2 = Span::new(("<example>", ":- not foo(), bar(baz)"));
/// let span3 = Span::new(("<example>", "foo"));
/// let span4 = Span::new(("<example>", ":-"));
///
/// let mut comb = rule_body();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(6..), RuleBody {
///         arrow_token: span1.slice(..2).into(),
///         antecedents: punct![Literal::Atom(Atom::Fact(Fact {
///             ident: Ident { value: span1.slice(3..6) },
///             args:  None,
///         }))],
///     }),
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(22..), RuleBody {
///         arrow_token: span2.slice(..2).into(),
///         antecedents: punct![
///             Literal::NegAtom(NegAtom {
///                 not_token: span2.slice(3..6).into(),
///                 atom:      Atom::Fact(Fact {
///                     ident: Ident { value: span2.slice(7..10) },
///                     args:  Some(FactArgs {
///                         paren_tokens: Parens {
///                             open:  span2.slice(10..11).into(),
///                             close: span2.slice(11..12).into(),
///                         },
///                         args: Punctuated::new(),
///                     }),
///                 }),
///             }),
///             Comma::from(span2.slice(12..13)),
///             Literal::Atom(Atom::Fact(Fact {
///                 ident: Ident { value: span2.slice(14..17) },
///                 args:  Some(FactArgs {
///                     paren_tokens: Parens {
///                         open:  span2.slice(17..18).into(),
///                         close: span2.slice(21..22).into(),
///                     },
///                     args: punct![Atom::Fact(Fact {
///                         ident: Ident { value: span2.slice(18..21) },
///                         args:  None,
///                     })],
///                 }),
///             }))
///         ],
///     }),
/// );
/// assert!(matches!(comb.parse(span3), Err(SnackError::Recoverable(_)),));
/// assert!(matches!(comb.parse(span4), Err(SnackError::Fatal(_)),));
/// ```
#[inline]
pub fn rule_body<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::RuleBody<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        seq::pair(
            tokens::arrow(),
            error::cut(punctuated::punctuated_nontrailing_many1(
                seq::delimited(
                    whitespace0(),
                    literals::literal(),
                    comb::not(scan::while1("an identifier", |&b| (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-' || b == b'_')),
                ),
                tokens::comma(),
            )),
        ),
        |(arrow_token, antecedents)| ast::RuleBody { arrow_token, antecedents },
    )
    .boxed()
}
