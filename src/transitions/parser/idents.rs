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

use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{combinator as comb, scan, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use crate::ast;


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
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::Ident;
/// use datalog::transitions::parser::idents::trans_ident;
///
/// let span1 = Span::new(("<example>", "#foo"));
/// let span2 = Span::new(("<example>", "bar"));
/// let span3 = Span::new(("<example>", "Bar"));
/// let span4 = Span::new(("<example>", "()"));
///
/// let mut comb = trans_ident();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(4..), Ident { value: "#foo".into(), span: Some(span1.slice(..4)) })
/// );
/// assert!(matches!(comb.parse(span2), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span3), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span4), Err(SnackError::Recoverable(_))));
/// ```
pub fn trans_ident<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Ident<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        comb::recognize(seq::pair(
            scan::elem("a pound", |&b| b == b'#'),
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
