//  LITERALS.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 14:20:04
//  Last edited:
//    06 Feb 2025, 10:19:43
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements combinators for parsing literals.
//

use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{branch, combinator as comb, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use super::{atoms, tokens, whitespace0};
use crate::ast;


/***** LIBRARY *****/
/// Parses a literal, either positive or negative.
///
/// # Returns
/// A combinator that either an [`ast::Atom`] or an [`ast::NegAtom`], both as [`ast::Literal`]s.
///
/// # Fails
/// This combinator fails if the input was not a literal.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, Comma, Fact, FactArgs, Ident, Literal, NegAtom, Not, Parens};
/// use datalog::parser::literals::literal;
///
/// let span2 = Span::new(("<example>", "not foo()"));
/// let span1 = Span::new(("<example>", "not foo"));
/// let span3 = Span::new(("<example>", "not foo(bar)"));
/// let span4 = Span::new(("<example>", "foo"));
/// let span5 = Span::new(("<example>", ""));
///
/// let mut comb = literal();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (
///         span1.slice(7..),
///         Literal::NegAtom(NegAtom {
///             not_token: span1.slice(..3).into(),
///             atom:      Atom::Fact(Fact {
///                 ident: Ident { value: span1.slice(4..7) },
///                 args:  None,
///             }),
///         })
///     ),
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (
///         span2.slice(9..),
///         Literal::NegAtom(NegAtom {
///             not_token: span2.slice(..3).into(),
///             atom:      Atom::Fact(Fact {
///                 ident: Ident { value: span2.slice(4..7) },
///                 args:  Some(FactArgs {
///                     paren_tokens: Parens {
///                         open:  span2.slice(7..8).into(),
///                         close: span2.slice(8..9).into(),
///                     },
///                     args: Punctuated::new(),
///                 }),
///             }),
///         })
///     ),
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (
///         span3.slice(12..),
///         Literal::NegAtom(NegAtom {
///             not_token: span3.slice(..3).into(),
///             atom:      Atom::Fact(Fact {
///                 ident: Ident { value: span3.slice(4..7) },
///                 args:  Some(FactArgs {
///                     paren_tokens: Parens {
///                         open:  span3.slice(7..8).into(),
///                         close: span3.slice(11..12).into(),
///                     },
///                     args: punct![Atom::Fact(Fact {
///                         ident: Ident { value: span3.slice(8..11) },
///                         args:  None,
///                     })],
///                 }),
///             }),
///         })
///     ),
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (
///         span4.slice(3..),
///         Literal::Atom(Atom::Fact(Fact {
///             ident: Ident { value: span4.slice(..3) },
///             args:  None,
///         }))
///     ),
/// );
/// assert!(matches!(comb.parse(span5), Err(SnackError::Recoverable(_))));
/// ```
#[inline]
pub fn literal<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Literal<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    branch::alt((comb::map(neg_atom(), ast::Literal::NegAtom), comb::map(atoms::atom(), ast::Literal::Atom))).boxed()
}

/// Parses a negated literal, which can only occur as antecedent.
///
/// # Returns
/// A combinator that parses `not`, then an atom.
///
/// # Fails
/// This combinator fails if the input was not a negated atom.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, Comma, Fact, FactArgs, Ident, NegAtom, Not, Parens};
/// use datalog::parser::literals::neg_atom;
///
/// let span1 = Span::new(("<example>", "not foo"));
/// let span2 = Span::new(("<example>", "not foo()"));
/// let span3 = Span::new(("<example>", "not foo(bar)"));
/// let span4 = Span::new(("<example>", "foo"));
/// let span5 = Span::new(("<example>", ""));
///
/// let mut comb = neg_atom();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(7..), NegAtom {
///         not_token: span1.slice(..3).into(),
///         atom:      Atom::Fact(Fact { ident: Ident { value: span1.slice(4..7) }, args: None }),
///     }),
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(9..), NegAtom {
///         not_token: span2.slice(..3).into(),
///         atom:      Atom::Fact(Fact {
///             ident: Ident { value: span2.slice(4..7) },
///             args:  Some(FactArgs {
///                 paren_tokens: Parens {
///                     open:  span2.slice(7..8).into(),
///                     close: span2.slice(8..9).into(),
///                 },
///                 args: Punctuated::new(),
///             }),
///         }),
///     }),
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(12..), NegAtom {
///         not_token: span3.slice(..3).into(),
///         atom:      Atom::Fact(Fact {
///             ident: Ident { value: span3.slice(4..7) },
///             args:  Some(FactArgs {
///                 paren_tokens: Parens {
///                     open:  span3.slice(7..8).into(),
///                     close: span3.slice(11..12).into(),
///                 },
///                 args: punct![Atom::Fact(Fact {
///                     ident: Ident { value: span3.slice(8..11) },
///                     args:  None,
///                 })],
///             }),
///         }),
///     }),
/// );
/// assert!(matches!(comb.parse(span4), Err(SnackError::Recoverable(_)),));
/// assert!(matches!(comb.parse(span5), Err(SnackError::Recoverable(_)),));
/// ```
#[inline]
pub fn neg_atom<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::NegAtom<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(seq::separated_pair(tokens::not(), whitespace0(), atoms::atom()), |(not_token, atom)| ast::NegAtom { not_token, atom }).boxed()
}
