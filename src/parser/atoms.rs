//  ATOMS.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 10:29:41
//  Last edited:
//    28 Nov 2024, 17:17:15
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements parsers to parse [`Atom`]s.
//

use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::error::{Common, Error, Failure};
use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::utf8::complete::while1;
use ast_toolkit::snack::{branch, comb, combinator as comb, error, multi, sequence as seq, utf8, Result as SResult};
use ast_toolkit::span::{Span, Spanning};

use super::tokens;
use crate::ast;


/***** ERRORS *****/
/// Errors returned when parsing atoms and related.
pub enum ParseError<F, S> {
    /// Failed to parse the argument to an atom.
    AtomArgs { span: Span<F, S> },
    /// Failed to parse an identifier.
    Ident { span: Span<F, S> },
    /// Failed to parse a variable.
    Var { span: Span<F, S> },
    /// Failed to parse a comma.
    Comma { span: Span<F, S> },
}
impl<F, S> Debug for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::AtomArgs { span } => {
                let mut fmt = f.debug_struct("ParseError::AtomArgs");
                fmt.field("span", span);
                fmt.finish()
            },
            Self::Ident { span } => {
                let mut fmt = f.debug_struct("ParseError::Ident");
                fmt.field("span", span);
                fmt.finish()
            },
            Self::Var { span } => {
                let mut fmt = f.debug_struct("ParseError::Var");
                fmt.field("span", span);
                fmt.finish()
            },
            Self::Comma { span } => {
                let mut fmt = f.debug_struct("ParseError::Comma");
                fmt.field("span", span);
                fmt.finish()
            },
        }
    }
}
impl<F, S> Display for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ParseError::*;
        match self {
            AtomArgs { .. } => write!(f, "{}", AtomArgsExpectsFormatter),
            Ident { .. } => write!(f, "{}", IdentExpectsFormatter),
            Var { .. } => write!(f, "{}", VarExpectsFormatter),
            Comma { .. } => write!(f, "Expected a comma"),
        }
    }
}
impl<F, S> std::error::Error for ParseError<F, S> {}
impl<F, S> Spanning<F, S> for ParseError<F, S>
where
    F: Clone,
    S: Clone,
{
    #[inline]
    fn span(&self) -> Span<F, S> {
        use ParseError::*;
        match self {
            AtomArgs { span } => span.clone(),
            Ident { span } => span.clone(),
            Var { span } => span.clone(),
            Comma { span } => span.clone(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        use ParseError::*;
        match self {
            AtomArgs { span } => span,
            Ident { span } => span,
            Var { span } => span,
            Comma { span } => span,
        }
    }
}





/***** LIBRARY *****/
/// Parses a full atom definition.
///
/// This is an identifier, with an optional list of arguments to that identifier.
///
/// # Returns
/// A combinator that can parse the input to an [`AtomArgs`](ast::AtomArgs).
///
/// # Fails
/// The returned combinator fails if the input is not a list of atom arguments wrapped in parenthesis.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, AtomArg, AtomArgs, Comma, Parens, Ident};
/// use datalog::parser::atoms::{atom, ParseError};
///
/// let span1 = Span::new("<example>", "qux()");
/// let span2 = Span::new("<example>", "qux(foo)");
/// let span3 = Span::new("<example>", "qux(Bar, baz)");
/// let span4 = Span::new("<example>", "foo");
/// let span5 = Span::new("<example>", "(foo bar)");
/// let span6 = Span::new("<example>", "foo(#)");
///
/// let mut comb = atom();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(5..), Atom {
///         ident: Ident { value: span1.slice(..3) },
///         args: Some(AtomArgs {
///             paren_tokens: Parens { open: span1.slice(3..4), close: span1.slice(4..5) },
///             args: punct![],
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(8..), Atom {
///         ident: Ident { value: span2.slice(..3) },
///         args: Some(AtomArgs {
///             paren_tokens: Parens { open: span2.slice(3..4), close: span2.slice(7..8) },
///             args: punct![v => AtomArg::Atom(Ident { value: span2.slice(4..7) })],
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(13..), Atom {
///         ident: Ident { value: span3.slice(..3) },
///         args: Some(AtomArgs {
///             paren_tokens: Parens { open: span3.slice(3..4), close: span3.slice(12..13) },
///             args: punct![
///                 v => AtomArg::Var(Ident { value: span3.slice(4..7) }),
///                 p => Comma { span: span3.slice(7..8) },
///                 v => AtomArg::Atom(Ident { value: span3.slice(9..12) })
///             ],
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (span4.slice(3..), Atom {
///         ident: Ident { value: span4.slice(..3) },
///         args: None,
///     })
/// );
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Ident { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span6),
///     SResult::Error(Error::Common(Common::Custom(ParseError::AtomArgs { .. })))
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "an atom", Output = ast::Atom<F, S>, Error = ParseError<F, S>)]
pub fn atom<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    match seq::pair(ident(), comb::opt(atom_args())).parse(input) {
        SResult::Ok(rem, (ident, args)) => SResult::Ok(rem, ast::Atom { ident, args }),
        SResult::Fail(fail) => SResult::Fail(fail),
        SResult::Error(err) => SResult::Error(err),
    }
}



/// Parses a list of atom arguments.
///
/// # Returns
/// A combinator that can parse the input to an [`AtomArgs`](ast::AtomArgs).
///
/// # Fails
/// The returned combinator fails if the input is not a list of atom arguments wrapped in parenthesis.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{AtomArg, AtomArgs, Comma, Parens, Ident};
/// use datalog::parser::atoms::{atom_args, ParseError};
///
/// let span1 = Span::new("<example>", "()");
/// let span2 = Span::new("<example>", "(foo)");
/// let span3 = Span::new("<example>", "(Bar, baz)");
/// let span4 = Span::new("<example>", "foo");
/// let span5 = Span::new("<example>", "(foo bar)");
/// let span6 = Span::new("<example>", "(#)");
///
/// let mut comb = atom_args();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(2..), AtomArgs {
///         paren_tokens: Parens { open: span1.slice(0..1), close: span1.slice(1..2) },
///         args: punct![],
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(5..), AtomArgs {
///         paren_tokens: Parens { open: span2.slice(0..1), close: span2.slice(4..5) },
///         args: punct![v => AtomArg::Atom(Ident { value: span2.slice(1..4) })],
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(10..), AtomArgs {
///         paren_tokens: Parens { open: span3.slice(..1), close: span3.slice(9..10) },
///         args: punct![
///             v => AtomArg::Var(Ident { value: span3.slice(1..4) }),
///             p => Comma { span: span3.slice(4..5) },
///             v => AtomArg::Atom(Ident { value: span3.slice(6..9) })
///         ],
///     })
/// );
/// assert!(matches!(
///     comb.parse(span4),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::AtomArgs { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Error(Error::Common(Common::Custom(ParseError::AtomArgs { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span6),
///     SResult::Error(Error::Common(Common::Custom(ParseError::AtomArgs { .. })))
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "zero or more arguments", Output = ast::AtomArgs<F, S>, Error = ParseError<F, S>)]
pub fn atom_args<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    match tokens::parens(multi::punctuated0(
        seq::delimited(error::transmute(utf8::whitespace0()), atom_arg(), error::transmute(utf8::whitespace0())),
        comb::map_err(tokens::comma(), |err| ParseError::Comma { span: err.into_span() }),
    ))
    .parse(input)
    {
        SResult::Ok(rem, (args, parens)) => SResult::Ok(rem, ast::AtomArgs { paren_tokens: parens, args }),
        SResult::Fail(fail) => SResult::Fail(Failure::Common(Common::Custom(ParseError::AtomArgs { span: fail.into_span() }))),
        SResult::Error(err) => SResult::Error(Error::Common(Common::Custom(ParseError::AtomArgs { span: err.into_span() }))),
    }
}

/// Parses an argument to an atom.
///
/// This is either a regular ol' identifier, _or_ a variable.
///
/// # Returns
/// A combinator that can parse the input to an [`AtomArg`](ast::AtomArg).
///
/// # Fails
/// The returned combinator fails if the input is not an identifier or a variable.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{AtomArg, Ident};
/// use datalog::parser::atoms::{atom_arg, ParseError};
///
/// let span1 = Span::new("<example>", "foo");
/// let span2 = Span::new("<example>", "Bar");
/// let span3 = Span::new("<example>", "()");
///
/// let mut comb = atom_arg();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(3..), AtomArg::Atom(Ident { value: span1.slice(..3) }))
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(3..), AtomArg::Var(Ident { value: span2.slice(..3) }))
/// );
/// assert!(matches!(comb.parse(span3), SResult::Fail(Failure::Common(Common::Alt { .. }))));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "either a constant or a variable", Output = ast::AtomArg<F, S>, Error = ParseError<F, S>)]
pub fn atom_arg<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + WhileUtf8,
{
    branch::alt((comb::map(ident(), ast::AtomArg::Atom), comb::map(var(), ast::AtomArg::Var))).parse(input)
}



/// Parses a $Datalog^\neg$ identifier.
///
/// This is _not_ a variable. I.e., it cannot start with an uppercase letter.
///
/// # Returns
/// A combinator that can parse the input to an [`Ident`](ast::Ident).
///
/// # Fails
/// The returned combinator fails if the input is not an identifier.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::Ident;
/// use datalog::parser::atoms::{ident, ParseError};
///
/// let span1 = Span::new("<example>", "foo");
/// let span2 = Span::new("<example>", "Bar");
/// let span3 = Span::new("<example>", "()");
///
/// let mut comb = ident();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(3..), Ident { value: span1.slice(..3) }));
/// assert!(matches!(
///     comb.parse(span2),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Ident { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span3),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Ident { .. })))
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "an identifier consisting of only lowercase alphanumeric letters, underscores and dashes", Output = ast::Ident<F, S>, Error = ParseError<F, S>)]
pub fn ident<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + WhileUtf8,
{
    let mut first: bool = true;
    match while1(|c: &str| -> bool {
        if c.len() != 1 {
            return false;
        }
        let c: char = c.chars().next().unwrap();
        if first {
            first = false;
            (c >= 'a' && c <= 'z') || c == '_'
        } else {
            (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_'
        }
    })
    .parse(input)
    {
        SResult::Ok(rem, value) => SResult::Ok(rem, ast::Ident { value }),
        SResult::Fail(fail) => SResult::Fail(Failure::Common(Common::Custom(ParseError::Ident { span: fail.span() }))),
        SResult::Error(_) => unreachable!(),
    }
}

/// Parses a $Datalog^\neg$ variable.
///
/// It is essentially a variable with uppercase letter.
///
/// # Returns
/// A combinator that can parse the input to an [`Ident`](ast::Ident).
///
/// # Fails
/// The returned combinator fails if the input is not a variable.
///
/// # Example
/// ```rust
/// use ast_toolkit::snack::error::{Common, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::Ident;
/// use datalog::parser::atoms::{var, ParseError};
///
/// let span1 = Span::new("<example>", "foo");
/// let span2 = Span::new("<example>", "Bar");
/// let span3 = Span::new("<example>", "()");
///
/// let mut comb = var();
/// assert!(matches!(
///     comb.parse(span1),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Var { .. })))
/// ));
/// assert_eq!(comb.parse(span2).unwrap(), (span2.slice(3..), Ident { value: span2.slice(..3) }));
/// assert!(matches!(
///     comb.parse(span3),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Var { .. })))
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "a variable starting with an uppercase letter, then consisting of only lowercase alphanumeric letters, underscores and dashes", Output = ast::Ident<F, S>, Error = ParseError<F, S>)]
pub fn var<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + WhileUtf8,
{
    let mut first: bool = true;
    match while1(|c: &str| -> bool {
        if c.len() != 1 {
            return false;
        }
        let c: char = c.chars().next().unwrap();
        if first {
            first = false;
            c >= 'A' && c <= 'Z'
        } else {
            (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_'
        }
    })
    .parse(input)
    {
        SResult::Ok(rem, value) => SResult::Ok(rem, ast::Ident { value }),
        SResult::Fail(fail) => SResult::Fail(Failure::Common(Common::Custom(ParseError::Var { span: fail.span() }))),
        SResult::Error(_) => unreachable!(),
    }
}
