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

use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{branch, comb, combinator as comb, multi, sequence as seq, utf8};
use ast_toolkit::span::Span;


/***** LIBRARY *****/
/// Parses Datalog whitespace.
///
/// Besides from the [usual suspects](utf8::whitespace0()), this also parses and ignores comments.
///
/// Datalog only supports double-slash, single-line comments for now.
///
/// # Returns
/// A [`Whitespace`]-combinator that will pop comments from the input.
///
/// # Fails
/// This combinator never fails.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::span::Span;
/// use datalog::parser::whitespaces::whitespace;
///
/// let span1 = Span::new("<example>", "// Test\n");
/// let span2 = Span::new("<example>", "// Test\r\n");
/// let span3 = Span::new("<example>", "// Test");
/// let span4 = Span::new("<example>", "  \t  \r\n  \n\r");
/// let span5 = Span::new("<example>", "Test  \t");
/// let span6 = Span::new("<example>", "");
///
/// let mut comb = whitespace();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(8..), span1.slice(..8)));
/// assert_eq!(comb.parse(span2).unwrap(), (span2.slice(9..), span2.slice(..9)));
/// assert_eq!(comb.parse(span3).unwrap(), (span3.slice(7..), span3.slice(..7)));
/// assert_eq!(comb.parse(span4).unwrap(), (span4.slice(11..), span4.slice(..11)));
/// assert_eq!(comb.parse(span5).unwrap(), (span5, span5.slice(..0)));
/// assert_eq!(comb.parse(span6).unwrap(), (span6, span6.slice(..0)));
/// ```
#[comb(snack = ::ast_toolkit::snack, expected = "a whitespace (space, tab, carriage return or newline) or a single-line comment starting with a double slash", Output = Span<F, S>)]
pub fn whitespace<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    comb::recognize(multi::many0(branch::alt((
        utf8::complete::whitespace1(),
        comb::recognize(seq::tuple((
            utf8::complete::tag("//"),
            utf8::while0(|c: &str| c != "\n" && c != "\r\n"),
            comb::opt(branch::alt((utf8::complete::tag("\n"), utf8::complete::tag("\r\n")))),
        ))),
    ))))
    .parse(input)
}
