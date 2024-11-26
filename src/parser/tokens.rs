//  TOKENS.rs
//    by Lut99
//
//  Created:
//    18 Mar 2024, 12:04:42
//  Last edited:
//    08 May 2024, 11:25:19
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for $Datalog^\neg$ keywords.
//

use ast_toolkit_snack::combinator::{self as comb, Map};
use ast_toolkit_snack::error::{self, Transmute};
use ast_toolkit_snack::sequence::{self as seq, Delim};
use ast_toolkit_snack::utf8::complete::{self as utf8, Tag};
use ast_toolkit_snack::Combinator;

use crate::ast;


/***** TYPE ALIASES *****/
/// The returned type of various token combinators.
pub type Token<'f, 's, T> = Map<&'f str, &'s str, Tag<'static, &'f str, &'s str>, fn(Span<'f, 's>) -> T>;

/// The returned type of the [`parens()`]-combinator.
pub type Parens<'t, 'f, 's, C> = Map<
    &'f str,
    &'s str,
    Delim<
        &'f str,
        &'s str,
        Transmute<&'f str, &'s str, Tag<'static, &'f str, &'s str>, <C as Combinator<'t, &'f str, &'s str>>::Error>,
        C,
        Transmute<&'f str, &'s str, Tag<'static, &'f str, &'s str>, <C as Combinator<'t, &'f str, &'s str>>::Error>,
    >,
    fn(
        (Span<'f, 's>, <C as Combinator<'t, &'f str, &'s str>>::Output, Span<'f, 's>),
    ) -> (ast::Parens<'f, 's>, <C as Combinator<'t, &'f str, &'s str>>::Output),
>;

/// Convenience alias for a [`Span`](ast_toolkit_span::Span) over static strings.
type Span<'f, 's> = ast_toolkit_span::Span<&'f str, &'s str>;





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
/// use ast_toolkit_snack::error::{Common, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
/// use datalog::ast::Arrow;
/// use datalog::parser::tokens::arrow;
///
/// let span1 = Span::new("<example>", ":-");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = arrow();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(2..), Arrow { span: span1.slice(..2) }));
/// assert!(matches!(comb.parse(span2), SResult::Fail(Failure::Common(Common::TagUtf8 { .. }))));
/// ```
pub const fn arrow<'f, 's>() -> Token<'f, 's, ast::Arrow<'f, 's>> { comb::map(utf8::tag(":-"), |span| ast::Arrow { span }) }

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
/// use ast_toolkit_snack::error::{Common, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
/// use datalog::ast::Comma;
/// use datalog::parser::tokens::comma;
///
/// let span1 = Span::new("<example>", ",");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = comma();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(1..), Comma { span: span1.slice(..1) }));
/// assert!(matches!(comb.parse(span2), SResult::Fail(Failure::Common(Common::TagUtf8 { .. }))));
/// ```
pub const fn comma<'f, 's>() -> Token<'f, 's, ast::Comma<'f, 's>> { comb::map(utf8::tag(","), |span| ast::Comma { span }) }

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
/// use ast_toolkit_snack::error::{Common, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
/// use datalog::ast::Dot;
/// use datalog::parser::tokens::dot;
///
/// let span1 = Span::new("<example>", ".");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = dot();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(1..), Dot { span: span1.slice(..1) }));
/// assert!(matches!(comb.parse(span2), SResult::Fail(Failure::Common(Common::TagUtf8 { .. }))));
/// ```
pub const fn dot<'f, 's>() -> Token<'f, 's, ast::Dot<'f, 's>> { comb::map(utf8::tag("."), |span| ast::Dot { span }) }

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
/// use ast_toolkit_snack::error::{Common, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
/// use datalog::ast::Not;
/// use datalog::parser::tokens::not;
///
/// let span1 = Span::new("<example>", "not");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = not();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(3..), Not { span: span1.slice(..3) }));
/// assert!(matches!(comb.parse(span2), SResult::Fail(Failure::Common(Common::TagUtf8 { .. }))));
/// ```
pub const fn not<'f, 's>() -> Token<'f, 's, ast::Not<'f, 's>> { comb::map(utf8::tag("not"), |span| ast::Not { span }) }

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
/// use ast_toolkit_snack::combinator::nop;
/// use ast_toolkit_snack::error::{Common, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
/// use datalog::ast::Parens;
/// use datalog::parser::tokens::parens;
///
/// let span1 = Span::new("<example>", "()");
/// let span2 = Span::new("<example>", "foo");
///
/// let mut comb = parens(nop());
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(2..), (Parens { open: span1.slice(..1), close: span1.slice(1..2) }, ()))
/// );
/// assert!(matches!(comb.parse(span2), SResult::Fail(Failure::Common(Common::DelimOpen { .. }))));
/// ```
pub const fn parens<'t, 'f, 's, C>(comb: C) -> Parens<'t, 'f, 's, C>
where
    C: Combinator<'t, &'f str, &'s str>,
{
    comb::map(seq::delim(error::transmute(utf8::tag("(")), comb, error::transmute(utf8::tag(")"))), |(open, middle, close)| {
        (ast::Parens { open, close }, middle)
    })
}
