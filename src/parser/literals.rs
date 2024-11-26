//  LITERALS.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 14:20:04
//  Last edited:
//    08 May 2024, 11:25:47
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements combinators for parsing literals.
//

use std::error::Error;
use std::fmt::{Display, Formatter, Result as FResult};
use std::marker::PhantomData;

use ast_toolkit_snack::utf8::complete as utf8;
use ast_toolkit_snack::{branch, combinator as comb, error, sequence as seq, Combinator, Expects, ExpectsFormatter, Result as SResult};
use ast_toolkit_span::Spanning;

use super::{atoms, tokens};
use crate::ast;


/***** TYPE ALIASES *****/
/// Convenience alias for a [`Span`](ast_toolkit_span::Span) over static strings.
type Span<'f, 's> = ast_toolkit_span::Span<&'f str, &'s str>;





/***** ERRORS *****/
/// Errors returned when parsing literals and related.
#[derive(Debug)]
pub enum ParseError<'f, 's> {
    /// Failed to parse an atom.
    Atom { span: Span<'f, 's> },
}
impl<'f, 's> Display for ParseError<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Atom { .. } => write!(f, "Expected an atom"),
        }
    }
}
impl<'f, 's> Error for ParseError<'f, 's> {}
impl<'f, 's> Spanning<&'f str, &'s str> for ParseError<'f, 's> {
    #[inline]
    fn span(&self) -> Span<'f, 's> {
        use ParseError::*;
        match self {
            Atom { span } => *span,
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
/// use ast_toolkit_punctuated::punct;
/// use ast_toolkit_snack::error::{Common, Error, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
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
pub const fn literal<'f, 's>() -> Literal<'f, 's> { Literal { _f: PhantomData, _s: PhantomData } }

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
/// use ast_toolkit_punctuated::punct;
/// use ast_toolkit_snack::error::{Common, Error, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
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
///     SResult::Fail(Failure::Common(Common::TagUtf8 { .. })),
/// ));
/// println!("{:?}", comb.parse(span5));
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Fail(Failure::Common(Common::TagUtf8 { .. })),
/// ));
/// ```
#[inline]
pub const fn neg_atom<'f, 's>() -> NegAtom<'f, 's> { NegAtom { _f: PhantomData, _s: PhantomData } }





/***** LIBRARY EXPECTS *****/
/// ExpectsForamtter for the [`Literal`] combinator.
#[derive(Debug)]
pub struct LiteralExpects;
impl Display for LiteralExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for LiteralExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "either a positive or a negative atom") }
}

/// ExpectsForamtter for the [`NegAtom`] combinator.
#[derive(Debug)]
pub struct NegAtomExpects;
impl Display for NegAtomExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for NegAtomExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "a negated atom") }
}





/***** LIBRARY COMBINATORS *****/
/// Combinator returned by [`literal()`].
pub struct Literal<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for Literal<'f, 's> {
    type Formatter = LiteralExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { LiteralExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for Literal<'f, 's> {
    type Output = ast::Literal<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: Span<'f, 's>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
        branch::alt((
            comb::map(neg_atom(), ast::Literal::NegAtom),
            comb::map(comb::map_err(atoms::atom(), |err| ParseError::Atom { span: err.span() }), ast::Literal::Atom),
        ))
        .parse(input)
    }
}

/// Combinator returned by [`neg_atom()`].
pub struct NegAtom<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for NegAtom<'f, 's> {
    type Formatter = NegAtomExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { NegAtomExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for NegAtom<'f, 's> {
    type Output = ast::NegAtom<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: Span<'f, 's>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
        match seq::separated_pair(
            error::transmute(tokens::not()),
            error::transmute(utf8::whitespace1()),
            comb::map_err(atoms::atom(), |err| ParseError::Atom { span: err.span() }),
        )
        .parse(input)
        {
            SResult::Ok(rem, (not_token, atom)) => SResult::Ok(rem, ast::NegAtom { not_token, atom }),
            SResult::Fail(fail) => SResult::Fail(fail),
            SResult::Error(err) => SResult::Error(err),
        }
    }
}
