//  TRIGGERS.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 17:55:47
//  Last edited:
//    03 Dec 2024, 17:38:05
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements parsers for the transitions [`Trigger`](ast::Trigger)s.
//

use ast_toolkit::snack::boxed::{BoxableCombinator as _, BoxedCombinator};
use ast_toolkit::snack::{combinator as comb, error, multi, sequence as seq};
use ast_toolkit::span::SpannableBytes;

use super::super::ast;
use super::{idents, tokens};
use crate::parser::whitespace0;


/***** LIBRARY *****/
/// Parses a transition trigger.
///
/// # Returns
/// A [`Trigger`](ast::Trigger) that represents a trigger of zero or more transitions.
///
/// # Fails
/// This combinator fails if the head of the input does not contains a valid trigger.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::Combinator as _;
/// use ast_toolkit::snack::result::SnackError;
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Dot, Ident};
/// use datalog::transitions::ast::{Curly, Trigger};
/// use datalog::transitions::parser::triggers::trigger;
///
/// let span1 = Span::new(("<example>", "!{ #foo }."));
/// let span2 = Span::new(("<example>", "!{}."));
/// let span3 = Span::new(("<example>", "!{ #foo #bar }."));
/// let span4 = Span::new(("<example>", "{ #foo }."));
/// let span5 = Span::new(("<example>", "!{ foo }."));
/// let span6 = Span::new(("<example>", "!{ #foo"));
///
/// let mut comb = trigger();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(10..), Trigger {
///         exclaim_token: span1.slice(..1).into(),
///         curly_tokens: Curly {
///             open:  span1.slice(1..2).into(),
///             close: span1.slice(8..9).into(),
///         },
///         idents: vec![Ident { value: "#foo".into(), span: Some(span1.slice(3..7)) }],
///         dot: span3.slice(9..10).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(4..), Trigger {
///         exclaim_token: span2.slice(..1).into(),
///         curly_tokens: Curly {
///             open:  span2.slice(1..2).into(),
///             close: span2.slice(2..3).into(),
///         },
///         idents: Vec::new(),
///         dot: span3.slice(3..4).into(),
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(15..), Trigger {
///         exclaim_token: span3.slice(..1).into(),
///         curly_tokens: Curly {
///             open:  span3.slice(1..2).into(),
///             close: span3.slice(13..14).into(),
///         },
///         idents: vec![Ident { value: "#foo".into(), span: Some(span3.slice(3..7)) }, Ident {
///             value: "#bar".into(),
///             span:  Some(span3.slice(8..12)),
///         }],
///         dot: span3.slice(14..15).into(),
///     })
/// );
/// assert!(matches!(comb.parse(span4), Err(SnackError::Recoverable(_))));
/// assert!(matches!(comb.parse(span5), Err(SnackError::Fatal(_))));
/// assert!(matches!(comb.parse(span6), Err(SnackError::Fatal(_))));
/// ```
pub fn trigger<'s, S>() -> BoxedCombinator<'s, 's, 's, 's, 'static, 's, ast::Trigger<S>, S>
where
    S: 's + Clone + SpannableBytes<'s>,
{
    comb::map(
        seq::tuple((
            tokens::exclaim(),
            error::cut(tokens::curly(seq::preceded(whitespace0(), multi::many0(seq::terminated(idents::trans_ident(), whitespace0()))))),
            crate::parser::tokens::dot(),
        )),
        |(exclaim_token, (curly_tokens, idents), dot)| ast::Trigger { exclaim_token, curly_tokens, idents, dot },
    )
    .boxed()
}
