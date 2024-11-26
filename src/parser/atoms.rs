//  ATOMS.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 10:29:41
//  Last edited:
//    08 May 2024, 11:25:38
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements parsers to parse [`Atom`]s.
//

use std::error::Error;
use std::fmt::{Display, Formatter, Result as FResult};
use std::marker::PhantomData;

use ast_toolkit_snack::error::{Common, Failure};
use ast_toolkit_snack::utf8::complete::while1;
use ast_toolkit_snack::{branch, combinator as comb, error, multi, sequence as seq, utf8, Combinator, Expects, ExpectsFormatter, Result as SResult};
use ast_toolkit_span::Spanning;

use super::tokens;
use crate::ast;


/***** TYPE ALIASES *****/
/// Convenience alias for a [`Span`](ast_toolkit_span::Span) over static strings.
type Span<'f, 's> = ast_toolkit_span::Span<&'f str, &'s str>;





/***** ERRORS *****/
/// Errors returned when parsing atoms and related.
#[derive(Debug)]
pub enum ParseError<'f, 's> {
    /// Failed to parse a comma.
    Comma { span: Span<'f, 's> },
    /// Failed to parse an identifier.
    Ident { span: Span<'f, 's> },
    /// Failed to parse a variable.
    Var { span: Span<'f, 's> },
}
impl<'f, 's> Display for ParseError<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ParseError::*;
        match self {
            Comma { .. } => write!(f, "Expected \",\""),
            Ident { .. } => write!(f, "{}", IdentExpects),
            Var { .. } => write!(f, "{}", VarExpects),
        }
    }
}
impl<'f, 's> Error for ParseError<'f, 's> {}
impl<'f, 's> Spanning<&'f str, &'s str> for ParseError<'f, 's> {
    #[inline]
    fn span(&self) -> Span<'f, 's> {
        use ParseError::*;
        match self {
            Comma { span } => *span,
            Ident { span } => *span,
            Var { span } => *span,
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
/// use ast_toolkit_punctuated::punct;
/// use ast_toolkit_snack::error::{Common, Error, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
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
///     SResult::Error(Error::Common(Common::DelimClose { .. }))
/// ));
/// ```
#[inline]
pub const fn atom<'f, 's>() -> Atom<'f, 's> { Atom { _f: PhantomData, _s: PhantomData } }



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
/// use ast_toolkit_punctuated::punct;
/// use ast_toolkit_snack::error::{Common, Error, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
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
///     SResult::Fail(Failure::Common(Common::DelimOpen { .. }))
/// ));
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Error(Error::Common(Common::DelimClose { .. }))
/// ));
/// assert!(matches!(
///     comb.parse(span6),
///     SResult::Error(Error::Common(Common::DelimClose { .. }))
/// ));
/// ```
#[inline]
pub const fn atom_args<'f, 's>() -> AtomArgs<'f, 's> { AtomArgs { _f: PhantomData, _s: PhantomData } }

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
/// use ast_toolkit_snack::error::{Common, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
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
pub const fn atom_arg<'f, 's>() -> AtomArg<'f, 's> { AtomArg { _f: PhantomData, _s: PhantomData } }



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
/// use ast_toolkit_snack::error::{Common, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
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
pub const fn ident<'f, 's>() -> Ident<'f, 's> { Ident { _f: PhantomData, _s: PhantomData } }

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
/// use ast_toolkit_snack::error::{Common, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
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
pub const fn var<'f, 's>() -> Var<'f, 's> { Var { _f: PhantomData, _s: PhantomData } }





/***** EXPECTS FORMATTERS *****/
/// ExpectsFormatter for the [`Atom`] combinator.
#[derive(Debug)]
pub struct AtomExpects;
impl Display for AtomExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for AtomExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "an atom") }
}



/// ExpectsFormatter for the [`AtomArgs`] combinator.
#[derive(Debug)]
pub struct AtomArgsExpects;
impl Display for AtomArgsExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for AtomArgsExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "zero or more arguments") }
}

/// ExpectsFormatter for the [`AtomArg`] combinator.
#[derive(Debug)]
pub struct AtomArgExpects;
impl Display for AtomArgExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for AtomArgExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "either a constant or a variable") }
}



/// ExpectsFormatter for the [`Ident`] combinator.
#[derive(Debug)]
pub struct IdentExpects;
impl Display for IdentExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for IdentExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult {
        write!(f, "an identifier consisting of only lowercase alphanumeric letters, underscores and dashes")
    }
}

/// ExpectsFormatter for the [`Var`] combinator.
#[derive(Debug)]
pub struct VarExpects;
impl Display for VarExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for VarExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult {
        write!(f, "a variable starting with an uppercase letter, then consisting of only lowercase alphanumeric letters, underscores and dashes")
    }
}





/***** LIBRARY COMBINATORS *****/
/// Combinator returned by [`atom()`].
pub struct Atom<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for Atom<'f, 's> {
    type Formatter = AtomExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { AtomExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for Atom<'f, 's> {
    type Output = ast::Atom<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: ast_toolkit_span::Span<&'f str, &'s str>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
        match seq::pair(ident(), comb::opt(atom_args())).parse(input) {
            SResult::Ok(rem, (ident, args)) => SResult::Ok(rem, ast::Atom { ident, args }),
            SResult::Fail(fail) => SResult::Fail(fail),
            SResult::Error(err) => SResult::Error(err),
        }
    }
}



/// Combinator returned by [`atom_args()`].
pub struct AtomArgs<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for AtomArgs<'f, 's> {
    type Formatter = AtomArgsExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { AtomArgsExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for AtomArgs<'f, 's> {
    type Output = ast::AtomArgs<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: ast_toolkit_span::Span<&'f str, &'s str>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
        match tokens::parens(multi::punctuated0(
            seq::delimited(error::transmute(utf8::whitespace0()), atom_arg(), error::transmute(utf8::whitespace0())),
            error::transmute(tokens::comma()),
        ))
        .parse(input)
        {
            SResult::Ok(rem, (parens, args)) => SResult::Ok(rem, ast::AtomArgs { paren_tokens: parens, args }),
            SResult::Fail(fail) => SResult::Fail(fail),
            SResult::Error(err) => SResult::Error(err),
        }
    }
}

/// Combinator returned by [`atom_arg()`].
pub struct AtomArg<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for AtomArg<'f, 's> {
    type Formatter = AtomArgExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { AtomArgExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for AtomArg<'f, 's> {
    type Output = ast::AtomArg<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: ast_toolkit_span::Span<&'f str, &'s str>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
        branch::alt((comb::map(ident(), ast::AtomArg::Atom), comb::map(var(), ast::AtomArg::Var))).parse(input)
    }
}



/// Combinator returned by [`ident()`].
pub struct Ident<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for Ident<'f, 's> {
    type Formatter = IdentExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { IdentExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for Ident<'f, 's> {
    type Output = ast::Ident<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: Span<'f, 's>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
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
}

/// Combinator returned by [`var()`].
pub struct Var<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for Var<'f, 's> {
    type Formatter = IdentExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { IdentExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for Var<'f, 's> {
    type Output = ast::Ident<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: Span<'f, 's>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
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
}
