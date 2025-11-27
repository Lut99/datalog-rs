//  ATOMS.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 10:29:41
//  Last edited:
//    03 Feb 2025, 19:22:56
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements parsers to parse [`Atom`]s.
//

use ast_toolkit::punctuated::snack as punctuated;
use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{branch, combinator as comb, scan, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use super::{tokens, whitespace0};
use crate::ast;


/***** LIBRARY *****/
/// Parses a full atom definition.
///
/// This is an identifier, with an optional list of arguments to that identifier.
///
/// # Returns
/// A combinator that can parse the input to an [`FactArgs`](ast::FactArgs).
///
/// # Fails
/// The returned combinator fails if the input is not a list of atom arguments wrapped in parenthesis.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::{Result as SResult, SnackError};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, Comma, Fact, FactArgs, Ident, Parens};
/// use datalog::parser::atoms::atom;
///
/// let span1 = Span::new(("<example>", "qux()"));
/// let span2 = Span::new(("<example>", "qux(foo)"));
/// let span3 = Span::new(("<example>", "qux(Bar, baz)"));
/// let span4 = Span::new(("<example>", "foo"));
/// let span5 = Span::new(("<example>", "(foo bar)"));
/// let span6 = Span::new(("<example>", "foo(#)"));
/// let span7 = Span::new(("<example>", "Bar"));
///
/// let mut comb = atom();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (
///         span1.slice(5..),
///         Atom::Fact(Fact {
///             ident: Ident { value: "qux".into(), span: Some(span1.slice(..3)) },
///             args:  Some(FactArgs {
///                 paren_tokens: Parens {
///                     open:  span1.slice(3..4).into(),
///                     close: span1.slice(4..5).into(),
///                 },
///                 args: Punctuated::new(),
///             }),
///         })
///     )
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (
///         span2.slice(8..),
///         Atom::Fact(Fact {
///             ident: Ident { value: "qux".into(), span: Some(span2.slice(..3)) },
///             args:  Some(FactArgs {
///                 paren_tokens: Parens {
///                     open:  span2.slice(3..4).into(),
///                     close: span2.slice(7..8).into(),
///                 },
///                 args: punct![Atom::Fact(Fact {
///                     ident: Ident { value: "foo".into(), span: Some(span2.slice(4..7)) },
///                     args:  None,
///                 })],
///             }),
///         })
///     )
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (
///         span3.slice(13..),
///         Atom::Fact(Fact {
///             ident: Ident { value: "qux".into(), span: Some(span3.slice(..3)) },
///             args:  Some(FactArgs {
///                 paren_tokens: Parens {
///                     open:  span3.slice(3..4).into(),
///                     close: span3.slice(12..13).into(),
///                 },
///                 args: punct![
///                     Atom::Var(Ident { value: "Bar".into(), span: Some(span3.slice(4..7)) }),
///                     Comma::from(span3.slice(7..8)),
///                     Atom::Fact(Fact {
///                         ident: Ident { value: "baz".into(), span: Some(span3.slice(9..12)) },
///                         args:  None,
///                     })
///                 ],
///             }),
///         })
///     )
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (
///         span4.slice(3..),
///         Atom::Fact(Fact {
///             ident: Ident { value: "foo".into(), span: Some(span4.slice(..3)) },
///             args:  None,
///         })
///     )
/// );
/// assert!(matches!(comb.parse(span5), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span6), Err(SnackError::Fatal(_))));
/// assert_eq!(
///     comb.parse(span7).unwrap(),
///     (span7.slice(3..), Atom::Var(Ident { value: "Bar".into(), span: Some(span7.slice(..3)) })),
/// );
/// ```
#[inline]
pub fn atom<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Atom<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    branch::alt((comb::map(fact(), ast::Atom::Fact), comb::map(var(), ast::Atom::Var))).boxed()
}



/// Parses a fact (i.e., a non-variable [`Atom`]).
///
/// # Returns
/// A combinator that can parse the input to a [`Fact`](ast::Fact).
///
/// # Fails
/// The returned combinator fails if the input is not an identifier followed by optional [`fact_args()`].
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::{Result as SResult, SnackError};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, Comma, Fact, FactArgs, Ident, Parens};
/// use datalog::parser::atoms::fact;
///
/// let span1 = Span::new(("<example>", "qux()"));
/// let span2 = Span::new(("<example>", "qux(foo)"));
/// let span3 = Span::new(("<example>", "qux(Bar, baz)"));
/// let span4 = Span::new(("<example>", "foo"));
/// let span5 = Span::new(("<example>", "(foo bar)"));
/// let span6 = Span::new(("<example>", "foo(#)"));
/// let span7 = Span::new(("<example>", "Bar"));
///
/// let mut comb = fact();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(5..), Fact {
///         ident: Ident { value: "qux".into(), span: Some(span1.slice(..3)) },
///         args:  Some(FactArgs {
///             paren_tokens: Parens {
///                 open:  span1.slice(3..4).into(),
///                 close: span1.slice(4..5).into(),
///             },
///             args: Punctuated::new(),
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(8..), Fact {
///         ident: Ident { value: "qux".into(), span: Some(span2.slice(..3)) },
///         args:  Some(FactArgs {
///             paren_tokens: Parens {
///                 open:  span2.slice(3..4).into(),
///                 close: span2.slice(7..8).into(),
///             },
///             args: punct![Atom::Fact(Fact {
///                 ident: Ident { value: "foo".into(), span: Some(span2.slice(4..7)) },
///                 args:  None,
///             })],
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(13..), Fact {
///         ident: Ident { value: "qux".into(), span: Some(span3.slice(..3)) },
///         args:  Some(FactArgs {
///             paren_tokens: Parens {
///                 open:  span3.slice(3..4).into(),
///                 close: span3.slice(12..13).into(),
///             },
///             args: punct![
///                 Atom::Var(Ident { value: "Bar".into(), span: Some(span3.slice(4..7)) }),
///                 Comma::from(span3.slice(7..8)),
///                 Atom::Fact(Fact {
///                     ident: Ident { value: "baz".into(), span: Some(span3.slice(9..12)) },
///                     args:  None,
///                 })
///             ],
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (span4.slice(3..), Fact {
///         ident: Ident { value: "foo".into(), span: Some(span4.slice(..3)) },
///         args:  None,
///     })
/// );
/// assert!(matches!(comb.parse(span5), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span6), Err(SnackError::Fatal(_))));
/// assert!(matches!(comb.parse(span7), Err(SnackError::Recoverable(_))));
/// ```
#[inline]
pub fn fact<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Fact<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    // Parse the identifier first; then the optional arguments
    comb::map(seq::separated_pair(ident(), whitespace0(), comb::opt(fact_args())), |(ident, args)| ast::Fact { ident, args }).boxed()
}

/// Parses a list of fact arguments.
///
/// # Returns
/// A combinator that can parse the input to an [`FactArgs`](ast::FactArgs).
///
/// # Fails
/// The returned combinator fails if the input is not a list of fact arguments wrapped in parenthesis.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::{Punctuated, punct};
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::{Result as SResult, SnackError};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, Comma, Fact, FactArgs, Ident, Parens, ParensClose, ParensOpen};
/// use datalog::parser::atoms::fact_args;
///
/// let span1 = Span::new(("<example>", "()"));
/// let span2 = Span::new(("<example>", "(foo)"));
/// let span3 = Span::new(("<example>", "(Bar, baz)"));
/// let span4 = Span::new(("<example>", "foo"));
/// let span5 = Span::new(("<example>", "(foo bar)"));
/// let span6 = Span::new(("<example>", "(#)"));
///
/// let mut comb = fact_args();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(2..), FactArgs {
///         paren_tokens: Parens {
///             open:  ParensOpen::from(span1.slice(..1)),
///             close: ParensClose::from(span1.slice(1..2)),
///         },
///         args: Punctuated::new(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(5..), FactArgs {
///         paren_tokens: Parens {
///             open:  span2.slice(0..1).into(),
///             close: span2.slice(4..5).into(),
///         },
///         args: punct![Atom::Fact(Fact {
///             ident: Ident { value: "foo".into(), span: Some(span2.slice(1..4)) },
///             args:  None,
///         })],
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(10..), FactArgs {
///         paren_tokens: Parens {
///             open:  span3.slice(..1).into(),
///             close: span3.slice(9..10).into(),
///         },
///         args: punct![
///             Atom::Var(Ident { value: "Bar".into(), span: Some(span3.slice(1..4)) }),
///             Comma::from(span3.slice(4..5)),
///             Atom::Fact(Fact {
///                 ident: Ident { value: "baz".into(), span: Some(span3.slice(6..9)) },
///                 args:  None,
///             })
///         ],
///     })
/// );
/// assert!(matches!(comb.parse(span4), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span5), Err(SnackError::Fatal(_))));
/// assert!(matches!(comb.parse(span6), Err(SnackError::Fatal(_))));
/// ```
#[inline]
pub fn fact_args<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::FactArgs<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        tokens::parens(punctuated::punctuated_nontrailing_many0(
            // NOTE: Closure here is to prevent recursion. Remember that these functions are called at construction time, not parse time (so there's no lazy evaluation, as it were).
            // The closure makes it lazy.
            seq::delimited(whitespace0(), comb::closure("an atom", |input| atom().parse(input)), whitespace0()),
            tokens::comma(),
        )),
        |(paren_tokens, args)| ast::FactArgs { paren_tokens, args },
    )
    .boxed()
}



/// Parses a $Datalog^\neg$ identifier.
///
/// This is _not_ a variable. I.e., it cannot start with an uppercase letter.
///
/// # Returns
/// A combinator that can parse the input to an [`Ident`](ast::Ident).
///
/// # Fails
/// The returned combinator fails if the input is not an identifier.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::{Result as SResult, SnackError};
/// use ast_toolkit::span::Span;
/// use datalog::ast::Ident;
/// use datalog::parser::atoms::ident;
///
/// let span1 = Span::new(("<example>", "foo"));
/// let span2 = Span::new(("<example>", "Bar"));
/// let span3 = Span::new(("<example>", "()"));
///
/// let mut comb = ident();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(3..), Ident { value: "foo".into(), span: Some(span1.slice(..3)) })
/// );
/// assert!(matches!(comb.parse(span2), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span3), Err(SnackError::Recoverable(_))));
/// ```
#[inline]
pub fn ident<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Ident<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        comb::recognize(seq::pair(
            scan::elem("a lowercase letter or underscore", |&b| (b >= b'a' && b <= b'z') || b == b'_'),
            scan::while0("zero or more lowercase alphanumeric characters, dashes or underscores", |&b| {
                (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-' || b == b'_'
            }),
        )),
        |span| ast::Ident {
            value: String::from_utf8(span.as_bytes().into()).unwrap_or_else(|err| panic!("Parsed identifier should only be valid UTF-8: {err}")),
            span:  Some(span),
        },
    )
    .boxed()
}

/// Parses a $Datalog^\neg$ variable.
///
/// It is essentially an identifier with uppercase letter.
///
/// # Returns
/// A combinator that can parse the input to an [`Ident`](ast::Ident).
///
/// # Fails
/// The returned combinator fails if the input is not a variable.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::{Result as SResult, SnackError};
/// use ast_toolkit::span::Span;
/// use datalog::ast::Ident;
/// use datalog::parser::atoms::var;
///
/// let span1 = Span::new(("<example>", "foo"));
/// let span2 = Span::new(("<example>", "Bar"));
/// let span3 = Span::new(("<example>", "()"));
///
/// let mut comb = var();
/// assert!(matches!(comb.parse(span1), Err(SnackError::Recoverable(_))));
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(3..), Ident { value: "Bar".into(), span: Some(span2.slice(..3)) })
/// );
/// assert!(matches!(comb.parse(span3), Err(SnackError::Recoverable(_))));
/// ```
#[inline]
pub fn var<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Ident<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        comb::recognize(seq::pair(
            scan::elem("an uppercase letter or underscore", |&b| (b >= b'A' && b <= b'Z') || b == b'_'),
            scan::while0("zero or more lowercase alphanumeric characters, dashes or underscores", |&b| {
                (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-' || b == b'_'
            }),
        )),
        |span| ast::Ident {
            value: String::from_utf8(span.as_bytes().into()).unwrap_or_else(|err| panic!("Parsed variable should only be valid UTF-8: {err}")),
            span:  Some(span),
        },
    )
    .boxed()
}
