//  IDENTS.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 17:39:56
//  Last edited:
//    29 Nov 2024, 15:34:23
//  Auto updated?
//    Yes
//
//  Description:
//!   Parses the transition identifier.
//

use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::error::{Common, Failure};
use ast_toolkit::snack::span::WhileUtf8;
use ast_toolkit::snack::utf8::complete as utf8;
use ast_toolkit::snack::{Result as SResult, comb};
use ast_toolkit::span::{Span, Spanning};

use crate::ast;


/***** ERRORS *****/
/// Error returned when parsing atoms and related.
pub struct ParseError<F, S> {
    pub span: Span<F, S>,
}
impl<F, S> Debug for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        let mut fmt = f.debug_struct("ParseError");
        fmt.field("span", &self.span);
        fmt.finish()
    }
}
impl<F, S> Display for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { write!(f, "{}", TransIdentExpectsFormatter) }
}
impl<F, S> std::error::Error for ParseError<F, S> {}
impl<F, S> Spanning<F, S> for ParseError<F, S>
where
    F: Clone,
    S: Clone,
{
    #[inline]
    fn span(&self) -> Span<F, S> { self.span.clone() }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        self.span
    }
}





/***** LIBRARY *****/
/// Parses a transition identifier.
///
/// This is like a normal identifier, but with a hashtag preceding it instead of a lowercase letter
/// or underscore.
///
/// # Returns
/// A [`Ident`](ast::Ident) that represents the parsed identifier.
///
/// # Fails
/// This combinator fails if the head of the input does not contains a valid transition identifier.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::Ident;
/// use datalog::transitions::parser::idents::{ParseError, trans_ident};
///
/// let span1 = Span::new("<example>", "#foo");
/// let span2 = Span::new("<example>", "bar");
/// let span3 = Span::new("<example>", "Bar");
/// let span4 = Span::new("<example>", "()");
///
/// let mut comb = trans_ident();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(4..), Ident { value: span1.slice(..4) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span3),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span4),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError { .. })))
/// ));
/// ```
#[comb(snack = ::ast_toolkit::snack, expected = "a lowercase, alphanumerical identifier preceded by a pound", Output = ast::Ident<F, S>, Error = ParseError<F, S>)]
pub fn trans_ident<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + WhileUtf8,
{
    let mut first: bool = true;
    match utf8::while1(|c: &str| -> bool {
        if c.len() != 1 {
            return false;
        }
        let c: char = c.chars().next().unwrap();
        if first {
            first = false;
            c == '#'
        } else {
            (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_'
        }
    })
    .parse(input)
    {
        SResult::Ok(rem, value) => SResult::Ok(rem, ast::Ident { value }),
        SResult::Fail(fail) => SResult::Fail(Failure::Common(Common::Custom(ParseError { span: fail.into_span() }))),
        SResult::Error(_) => unreachable!(),
    }
}
