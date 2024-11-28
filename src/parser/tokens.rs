//  TOKENS.rs
//    by Lut99
//
//  Created:
//    18 Mar 2024, 12:04:42
//  Last edited:
//    28 Nov 2024, 17:00:01
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for $Datalog^\neg$ keywords.
//

use ast_toolkit::snack::combinator::{self as comb};
use ast_toolkit::snack::span::{LenBytes, MatchBytes, WhileUtf8};
use ast_toolkit::snack::utf8::complete::{self as utf8};
use ast_toolkit::snack::{comb, Combinator};
use ast_toolkit::span::Span;
use ast_toolkit::tokens::snack::complete::{utf8_delimiter, utf8_token, Utf8Delimiter, Utf8Token};

use crate::ast::{Arrow, Comma, Dot, Not, Parens};


/***** HELPER FUNCTIONS *****/
/// Combinator that we use to match the end of a token.
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "the end of a token")]
pub fn token_end<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + LenBytes + WhileUtf8,
{
    comb::not(utf8::while1(|c: &str| -> bool {
        if c.len() != 1 {
            return false;
        }
        let c: char = c.chars().next().unwrap();
        (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_'
    }))
    .parse(input)
}





/***** LIBRARY FUNCTIONS *****/
/// Combinator for parsing a `:-`.
///
/// # Returns
/// A combinator that parses [`Arrow`]s.
///
/// # Fails
/// The returned combinator fails if the input is not `,`.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::ast::Arrow;
/// use datalog::parser::tokens::arrow;
///
/// let span1 = Span::new("<example>", ":-");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = arrow();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(2..), Arrow { span: span1.slice(..2) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8Token { .. })))
/// ));
/// ```
#[inline]
pub const fn arrow<'t, F, S>() -> Utf8Token<F, S, Arrow<F, S>, TokenEnd<F, S>>
where
    F: Clone,
    S: Clone + LenBytes + MatchBytes + WhileUtf8,
{
    utf8_token(token_end())
}

/// Combinator for parsing a `,`.
///
/// # Returns
/// A combinator that parses [`Comma`]s.
///
/// # Fails
/// The returned combinator fails if the input is not `,`.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::ast::Comma;
/// use datalog::parser::tokens::comma;
///
/// let span1 = Span::new("<example>", ",");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = comma();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(1..), Comma { span: span1.slice(..1) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8Token { .. })))
/// ));
/// ```
#[inline]
pub const fn comma<'t, F, S>() -> Utf8Token<F, S, Comma<F, S>, TokenEnd<F, S>>
where
    F: Clone,
    S: Clone + LenBytes + MatchBytes + WhileUtf8,
{
    utf8_token(token_end())
}

/// Combinator for parsing a `.`.
///
/// # Returns
/// A combinator that parses [`Dot`]s.
///
/// # Fails
/// The returned combinator fails if the input is not `.`.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::ast::Dot;
/// use datalog::parser::tokens::dot;
///
/// let span1 = Span::new("<example>", ".");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = dot();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(1..), Dot { span: span1.slice(..1) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8Token { .. })))
/// ));
/// ```
#[inline]
pub const fn dot<'t, F, S>() -> Utf8Token<F, S, Dot<F, S>, TokenEnd<F, S>>
where
    F: Clone,
    S: Clone + LenBytes + MatchBytes + WhileUtf8,
{
    utf8_token(token_end())
}

/// Combinator for parsing a `not`-keyword.
///
/// # Returns
/// A combinator that parses [`Not`]s.
///
/// # Fails
/// The returned combinator fails if the input is not `not`.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::ast::Not;
/// use datalog::parser::tokens::not;
///
/// let span1 = Span::new("<example>", "not");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = not();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(3..), Not { span: span1.slice(..3) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8Token { .. })))
/// ));
/// ```
#[inline]
pub const fn not<'t, F, S>() -> Utf8Token<F, S, Not<F, S>, TokenEnd<F, S>>
where
    F: Clone,
    S: Clone + LenBytes + MatchBytes + WhileUtf8,
{
    utf8_token(token_end())
}

/// Combinator for parsing parenthesis with something else in between.
///
/// # Arguments
/// - `comb`: Some other combinator that is found in between the parenthesis.
///
/// # Returns
/// A combinator that parses the parenthesis with the given `comb` in between them. Returns it as a tuple of the [`Parens`] and the result of `comb`.
///
/// # Fails
/// The returned combinator fails if the input is not parenthesis, or `comb` fails.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::combinator::nop;
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::ast::Parens;
/// use datalog::parser::tokens::parens;
///
/// let span1 = Span::new("<example>", "()");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = parens(nop());
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(2..), ((), Parens { open: span1.slice(..1), close: span1.slice(1..2) }))
/// );
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8OpenToken { .. })))
/// ));
/// ```
#[inline]
pub const fn parens<'t, F, S, C>(comb: C) -> Utf8Delimiter<F, S, Parens<F, S>, C>
where
    F: Clone,
    S: Clone + MatchBytes,
    C: Combinator<'t, F, S>,
{
    utf8_delimiter(comb)
}
