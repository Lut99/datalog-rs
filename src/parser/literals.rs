//  LITERALS.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 14:20:04
//  Last edited:
//    28 Nov 2024, 17:13:28
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements combinators for parsing literals.
//

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::utf8::complete as utf8;
use ast_toolkit::snack::{branch, comb, combinator as comb, error, sequence as seq, Result as SResult};
use ast_toolkit::span::{Span, Spanning};

use super::{atoms, tokens};
use crate::ast;


/***** ERRORS *****/
/// Errors returned when parsing literals and related.
pub enum ParseError<F, S> {
    /// Failed to parse an atom.
    Atom { span: Span<F, S> },
    /// Failed to parse a `not`-keyword.
    Not { span: Span<F, S> },
}
impl<F, S> Debug for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Atom { span } => {
                let mut fmt = f.debug_struct("ParseError::Atom");
                fmt.field("span", span);
                fmt.finish()
            },
            Not { span } => {
                let mut fmt = f.debug_struct("ParseError::Not");
                fmt.field("span", span);
                fmt.finish()
            },
        }
    }
}
impl<F, S> Display for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Atom { .. } => write!(f, "Expected an atom"),
            Not { .. } => write!(f, "Expected a \"not\""),
        }
    }
}
impl<F, S> Error for ParseError<F, S> {}
impl<F, S> Spanning<F, S> for ParseError<F, S>
where
    F: Clone,
    S: Clone,
{
    #[inline]
    fn span(&self) -> Span<F, S> {
        use ParseError::*;
        match self {
            Atom { span } => span.clone(),
            Not { span } => span.clone(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        match self {
            Self::Atom { span } => span,
            Self::Not { span } => span,
        }
    }
}





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
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Literal, Atom, AtomArg, AtomArgs, Comma, Ident, NegAtom, Not, Parens};
/// use datalog::parser::literals::{literal, ParseError};
///
/// let span1 = Span::new("<example>", "not foo");
/// let span2 = Span::new("<example>", "not foo()");
/// let span3 = Span::new("<example>", "not foo(bar)");
/// let span4 = Span::new("<example>", "foo");
/// let span5 = Span::new("<example>", "");
///
/// let mut comb = literal();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(7..), Literal::NegAtom(NegAtom {
///         not_token: Not { span: span1.slice(..3) },
///         atom:      Atom { ident: Ident { value: span1.slice(4..7) }, args: None },
///     })),
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(9..), Literal::NegAtom(NegAtom {
///         not_token: Not { span: span2.slice(..3) },
///         atom:      Atom {
///             ident: Ident { value: span2.slice(4..7) },
///             args:  Some(AtomArgs {
///                 paren_tokens: Parens { open: span2.slice(7..8), close: span2.slice(8..9) },
///                 args: punct![],
///             }),
///         },
///     })),
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(12..), Literal::NegAtom(NegAtom {
///         not_token: Not { span: span3.slice(..3) },
///         atom:      Atom {
///             ident: Ident { value: span3.slice(4..7) },
///             args:  Some(AtomArgs {
///                 paren_tokens: Parens { open: span3.slice(7..8), close: span3.slice(11..12) },
///                 args: punct![v => AtomArg::Atom(Ident { value: span3.slice(8..11) })],
///             }),
///         },
///     })),
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (span4.slice(3..), Literal::Atom(Atom {
///         ident: Ident { value: span4.slice(..3) },
///         args:  None,
///     })),
/// );
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Fail(Failure::Common(Common::Alt { .. })),
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "either a positive or negative atom", Output = ast::Literal<F, S>, Error = ParseError<F, S>)]
pub fn literal<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    branch::alt((
        comb::map(neg_atom(), ast::Literal::NegAtom),
        comb::map(comb::map_err(atoms::atom(), |err| ParseError::Atom { span: err.into_span() }), ast::Literal::Atom),
    ))
    .parse(input)
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
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, AtomArg, AtomArgs, Comma, Ident, NegAtom, Not, Parens};
/// use datalog::parser::literals::{neg_atom, ParseError};
///
/// let span1 = Span::new("<example>", "not foo");
/// let span2 = Span::new("<example>", "not foo()");
/// let span3 = Span::new("<example>", "not foo(bar)");
/// let span4 = Span::new("<example>", "foo");
/// let span5 = Span::new("<example>", "");
///
/// let mut comb = neg_atom();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(7..), NegAtom {
///         not_token: Not { span: span1.slice(..3) },
///         atom:      Atom { ident: Ident { value: span1.slice(4..7) }, args: None },
///     }),
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(9..), NegAtom {
///         not_token: Not { span: span2.slice(..3) },
///         atom:      Atom {
///             ident: Ident { value: span2.slice(4..7) },
///             args:  Some(AtomArgs {
///                 paren_tokens: Parens { open: span2.slice(7..8), close: span2.slice(8..9) },
///                 args: punct![],
///             }),
///         },
///     }),
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(12..), NegAtom {
///         not_token: Not { span: span3.slice(..3) },
///         atom:      Atom {
///             ident: Ident { value: span3.slice(4..7) },
///             args:  Some(AtomArgs {
///                 paren_tokens: Parens { open: span3.slice(7..8), close: span3.slice(11..12) },
///                 args: punct![v => AtomArg::Atom(Ident { value: span3.slice(8..11) })],
///             }),
///         },
///     }),
/// );
/// assert!(matches!(
///     comb.parse(span4),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Not { .. }))),
/// ));
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Not { .. }))),
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "a negated atom", Output = ast::NegAtom<F, S>, Error = ParseError<F, S>)]
pub fn neg_atom<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    match seq::separated_pair(
        comb::map_err(tokens::not(), |err| ParseError::Not { span: err.into_span() }),
        error::transmute(utf8::whitespace1()),
        comb::map_err(atoms::atom(), |err| ParseError::Atom { span: err.into_span() }),
    )
    .parse(input)
    {
        SResult::Ok(rem, (not_token, atom)) => SResult::Ok(rem, ast::NegAtom { not_token, atom }),
        SResult::Fail(fail) => SResult::Fail(fail),
        SResult::Error(err) => SResult::Error(err),
    }
}
