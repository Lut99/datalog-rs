//  WHITESPACES.rs
//    by Lut99
//
//  Created:
//    04 Dec 2024, 17:43:01
//  Last edited:
//    04 Dec 2024, 18:01:04
//  Auto updated?
//    Yes
//
//  Description:
//!   Parses comments.
//

use std::convert::Infallible;
use std::marker::PhantomData;

use ast_toolkit::snack::result::{Expected, Result as SResult, SnackError};
use ast_toolkit::snack::{Combinator, ascii, branch, combinator as comb, multi, scan, sequence as seq};
use ast_toolkit::span::{Span, Spannable, SpannableBytes};


/***** COMBINATORS *****/
/// Implements a combinator looking for end-of-file.
pub struct Eof<S> {
    _s: PhantomData<S>,
}
impl<'s, S: Clone + Spannable<'s>> Combinator<'static, 's, S> for Eof<S> {
    type Output = ();
    type ExpectsFormatter = &'static str;
    type Recoverable = Expected<&'static str, S>;
    type Fatal = Infallible;

    #[inline]
    fn expects(&self) -> Self::ExpectsFormatter { "Expected end-of-input" }

    #[inline]
    fn parse(&mut self, input: Span<S>) -> SResult<Self::Output, Self::Recoverable, Self::Fatal, S> {
        if input.is_empty() {
            Ok((input, ()))
        } else {
            Err(SnackError::Recoverable(Expected { fmt: self.expects(), fixable: Some(Some(1)), span: input }))
        }
    }
}



/// Implements the [`whitespace0()`]-combinator.
pub struct Whitespace0<S> {
    _s: PhantomData<S>,
}

impl<'s, S: Clone + SpannableBytes<'s>> Combinator<'static, 's, S> for Whitespace0<S> {
    type Output = Span<S>;
    type ExpectsFormatter = &'static str;
    type Recoverable = Infallible;
    type Fatal = Infallible;

    #[inline]
    fn expects(&self) -> Self::ExpectsFormatter { "Expected whitespace or comments" }

    #[inline]
    fn parse(&mut self, input: Span<S>) -> SResult<Self::Output, Self::Recoverable, Self::Fatal, S> {
        match comb::recognize(multi::many0(branch::alt((
            ascii::whitespace1(),
            comb::recognize(seq::tuple((
                scan::tag(b"//"),
                scan::while0("comment", |&b| b != b'\n'),
                branch::alt((comb::discard(scan::elem("newline", |&b| b == b'\n')), Eof { _s: PhantomData })),
            ))),
        ))))
        .parse(input)
        {
            Ok(res) => Ok(res),
            Err(_) => unreachable!(),
        }
    }
}





/***** LIBRARY *****/
/// Parses Datalog whitespace.
///
/// Besides from the [usual suspects](ascii::whitespace0()), this also parses and ignores comments.
///
/// Datalog only supports double-slash, single-line comments for now.
///
/// # Returns
/// A [`Whitespace0`]-combinator that will pop comments from the input.
///
/// # Fails
/// This combinator never fails.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::span::Span;
/// use datalog::parser::whitespace0::whitespace0;
///
/// let span1 = Span::new(("<example>", "// Test\n"));
/// let span2 = Span::new(("<example>", "// Test\r\n"));
/// let span3 = Span::new(("<example>", "// Test"));
/// let span4 = Span::new(("<example>", "  \t  \r\n  \n\r"));
/// let span5 = Span::new(("<example>", "Test  \t"));
/// let span6 = Span::new(("<example>", ""));
///
/// let mut comb = whitespace0();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(8..), span1.slice(..8)));
/// assert_eq!(comb.parse(span2).unwrap(), (span2.slice(9..), span2.slice(..9)));
/// assert_eq!(comb.parse(span3).unwrap(), (span3.slice(7..), span3.slice(..7)));
/// assert_eq!(comb.parse(span4).unwrap(), (span4.slice(11..), span4.slice(..11)));
/// assert_eq!(comb.parse(span5).unwrap(), (span5, span5.slice(())));
/// assert_eq!(comb.parse(span6).unwrap(), (span6, span6.slice(())));
/// ```
#[inline]
pub const fn whitespace0<'s, S: Clone + SpannableBytes<'s>>() -> Whitespace0<S> { Whitespace0 { _s: PhantomData } }
