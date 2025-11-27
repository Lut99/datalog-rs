//  SPECS.rs
//    by Lut99
//
//  Created:
//    08 May 2024, 11:12:42
//  Last edited:
//    07 Feb 2025, 17:43:27
//  Auto updated?
//    Yes
//
//  Description:
//!   Parses the toplevel $Datalog^\neg$ program.
//

use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{combinator as comb, multi, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use super::{rules, whitespace0};
use crate::ast;


/***** LIBRARY *****/
/// Parses $Datalog^\neg$ program.
///
/// # Returns
/// A combinator that parses list of rules.
///
/// # Fails
/// This combinator fails if the input was not solidly consisting of $Datalog^\neg$ rules.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Comma, Dot, Fact, Ident, Literal, NegAtom, Not, Parens, Rule, RuleBody, Spec,
/// };
/// use datalog::parser::specs::spec;
///
/// let span1 = Span::new(("<example>", ""));
/// let span2 = Span::new(("<example>", "foo :- bar."));
/// let span3 = Span::new(("<example>", "foo :- bar. foo, bar."));
/// let span4 = Span::new(("<example>", "foo :- bar. foo, bar. baz"));
///
/// let mut comb = spec();
/// assert_eq!(comb.parse(span1).unwrap(), (span1, Spec { rules: Vec::new() }));
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(11..), Spec {
///         rules: vec![Rule {
///             consequents: punct![Atom::Fact(Fact {
///                 ident: Ident { value: "foo".into(), span: Some(span2.slice(..3)) },
///                 args:  None,
///             })],
///             tail: Some(RuleBody {
///                 arrow_token: span2.slice(4..6).into(),
///                 antecedents: punct![Literal::Atom(Atom::Fact(Fact {
///                     ident: Ident { value: "bar".into(), span: Some(span2.slice(7..10)) },
///                     args:  None,
///                 }))],
///             }),
///             dot: span2.slice(10..11).into(),
///         }],
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(21..), Spec {
///         rules: vec![
///             Rule {
///                 consequents: punct![Atom::Fact(Fact {
///                     ident: Ident { value: "foo".into(), span: Some(span2.slice(..3)) },
///                     args:  None,
///                 })],
///                 tail: Some(RuleBody {
///                     arrow_token: span2.slice(4..6).into(),
///                     antecedents: punct![Literal::Atom(Atom::Fact(Fact {
///                         ident: Ident { value: "bar".into(), span: Some(span2.slice(7..10)) },
///                         args:  None,
///                     }))],
///                 }),
///                 dot: span2.slice(10..11).into(),
///             },
///             Rule {
///                 consequents: punct![
///                     Atom::Fact(Fact {
///                         ident: Ident { value: "foo".into(), span: Some(span3.slice(12..15)) },
///                         args:  None,
///                     }),
///                     Comma::from(span3.slice(15..16)),
///                     Atom::Fact(Fact {
///                         ident: Ident { value: "bar".into(), span: Some(span3.slice(17..20)) },
///                         args:  None,
///                     })
///                 ],
///                 tail: None,
///                 dot: span3.slice(20..21).into(),
///             },
///         ],
///     })
/// );
/// assert!(matches!(comb.parse(span4), Err(SnackError::Recoverable(_))));
/// ```
#[inline]
pub fn spec<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Spec<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(comb::consume(multi::many0(seq::delimited(whitespace0(), rules::rule(), whitespace0()))), |rules| ast::Spec { rules }).boxed()
}
