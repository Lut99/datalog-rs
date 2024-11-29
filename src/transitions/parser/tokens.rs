//  TOKENS.rs
//    by Lut99
//
//  Created:
//    18 Mar 2024, 12:04:42
//  Last edited:
//    29 Nov 2024, 11:23:50
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for additional keywords introduced by the transitions.
//

use ast_toolkit::snack::span::{LenBytes, MatchBytes, WhileUtf8};
use ast_toolkit::snack::Combinator;
use ast_toolkit::tokens::snack::complete::{utf8_delimiter, utf8_token, Utf8Delimiter, Utf8Token};

use super::super::ast::{Add, Curly, Exclaim, Squiggly};
use crate::parser::tokens::{token_end, TokenEnd};


/***** LIBRARY FUNCTIONS *****/
/// Combinator for parsing a `+`.
///
/// # Returns
/// A combinator that parses [`Add`]s.
///
/// # Fails
/// The returned combinator fails if the input is not `+`.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::transitions::ast::Add;
/// use datalog::transitions::parser::tokens::add;
///
/// let span1 = Span::new("<example>", "+");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = add();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(1..), Add { span: span1.slice(..1) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8Token { .. })))
/// ));
/// ```
#[inline]
pub const fn add<'t, F, S>() -> Utf8Token<F, S, Add<F, S>, TokenEnd<F, S>>
where
    F: Clone,
    S: Clone + LenBytes + MatchBytes + WhileUtf8,
{
    utf8_token(token_end())
}

/// Combinator for parsing a `~`.
///
/// # Returns
/// A combinator that parses [`Squiggly`]s.
///
/// # Fails
/// The returned combinator fails if the input is not `~`.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::transitions::ast::Squiggly;
/// use datalog::transitions::parser::tokens::squiggly;
///
/// let span1 = Span::new("<example>", "~");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = squiggly();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(1..), Squiggly { span: span1.slice(..1) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8Token { .. })))
/// ));
/// ```
#[inline]
pub const fn squiggly<'t, F, S>() -> Utf8Token<F, S, Squiggly<F, S>, TokenEnd<F, S>>
where
    F: Clone,
    S: Clone + LenBytes + MatchBytes + WhileUtf8,
{
    utf8_token(token_end())
}

/// Combinator for parsing a `!`.
///
/// # Returns
/// A combinator that parses [`Exclaim`]s.
///
/// # Fails
/// The returned combinator fails if the input is not `!`.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::transitions::ast::Exclaim;
/// use datalog::transitions::parser::tokens::exclaim;
///
/// let span1 = Span::new("<example>", "!");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = exclaim();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(1..), Exclaim { span: span1.slice(..1) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8Token { .. })))
/// ));
/// ```
#[inline]
pub const fn exclaim<'t, F, S>() -> Utf8Token<F, S, Exclaim<F, S>, TokenEnd<F, S>>
where
    F: Clone,
    S: Clone + LenBytes + MatchBytes + WhileUtf8,
{
    utf8_token(token_end())
}

/// Combinator for parsing curly brackets with something else in between.
///
/// # Arguments
/// - `comb`: Some other combinator that is found in between the curly brackets.
///
/// # Returns
/// A combinator that parses the curly brackets with the given `comb` in between them. Returns it
/// as a tuple of the [`Parens`] and the result of `comb`.
///
/// # Fails
/// The returned combinator fails if the input is not curly brackets, or `comb` fails.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::combinator::nop;
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use ast_toolkit::tokens::snack::complete::ParseError;
/// use datalog::transitions::ast::Curly;
/// use datalog::transitions::parser::tokens::curly;
///
/// let span1 = Span::new("<example>", "{}");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = curly(nop());
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(2..), ((), Curly { open: span1.slice(..1), close: span1.slice(1..2) }))
/// );
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Utf8OpenToken { .. })))
/// ));
/// ```
#[inline]
pub const fn curly<'t, F, S, C>(comb: C) -> Utf8Delimiter<F, S, Curly<F, S>, C>
where
    F: Clone,
    S: Clone + MatchBytes,
    C: Combinator<'t, F, S>,
{
    utf8_delimiter(comb)
}
