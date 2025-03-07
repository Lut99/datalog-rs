//  ATOMS.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 10:29:41
//  Last edited:
//    03 Feb 2025, 19:22:56
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
use ast_toolkit::snack::{Result as SResult, branch, comb, combinator as comb, error, multi, sequence as seq};
use ast_toolkit::span::{Span, Spanning};

use super::{tokens, whitespaces};
use crate::ast;


/***** ERRORS *****/
/// Errors returned when parsing atoms and related.
pub enum ParseError<F, S> {
    /// Failed to parse the argument to an atom.
    FactArgs { span: Span<F, S> },
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
            Self::FactArgs { span } => {
                let mut fmt = f.debug_struct("ParseError::FactArgs");
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
            FactArgs { .. } => write!(f, "{}", FactArgsExpectsFormatter),
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
            FactArgs { span } => span.clone(),
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
            FactArgs { span } => span,
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
/// A combinator that can parse the input to an [`FactArgs`](ast::FactArgs).
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
/// use datalog::ast::{Atom, Fact, FactArgs, Comma, Parens, Ident};
/// use datalog::parser::atoms::{atom, ParseError};
///
/// let span1 = Span::new("<example>", "qux()");
/// let span2 = Span::new("<example>", "qux(foo)");
/// let span3 = Span::new("<example>", "qux(Bar, baz)");
/// let span4 = Span::new("<example>", "foo");
/// let span5 = Span::new("<example>", "(foo bar)");
/// let span6 = Span::new("<example>", "foo(#)");
/// let span7 = Span::new("<example>", "Bar");
///
/// let mut comb = atom();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(5..), Atom::Fact(Fact {
///         ident: Ident { value: span1.slice(..3) },
///         args: Some(FactArgs {
///             paren_tokens: Parens { open: span1.slice(3..4), close: span1.slice(4..5) },
///             args: punct![],
///         }),
///     }))
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(8..), Atom::Fact(Fact {
///         ident: Ident { value: span2.slice(..3) },
///         args: Some(FactArgs {
///             paren_tokens: Parens { open: span2.slice(3..4), close: span2.slice(7..8) },
///             args: punct![v => Atom::Fact(Fact {
///                 ident: Ident { value: span2.slice(4..7) },
///                 args: None,
///             })],
///         }),
///     }))
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(13..), Atom::Fact(Fact {
///         ident: Ident { value: span3.slice(..3) },
///         args: Some(FactArgs {
///             paren_tokens: Parens { open: span3.slice(3..4), close: span3.slice(12..13) },
///             args: punct![
///                 v => Atom::Var(Ident { value: span3.slice(4..7) }),
///                 p => Comma { span: span3.slice(7..8) },
///                 v => Atom::Fact(Fact {
///                     ident: Ident { value: span3.slice(9..12) },
///                     args: None,
///                 })
///             ],
///         }),
///     }))
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (span4.slice(3..), Atom::Fact(Fact {
///         ident: Ident { value: span4.slice(..3) },
///         args: None,
///     }))
/// );
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Fail(Failure::Common(Common::Alt { .. }))
/// ));
/// assert!(matches!(
///     comb.parse(span6),
///     SResult::Error(Error::Common(Common::Custom(ParseError::FactArgs { .. })))
/// ));
/// assert_eq!(
///     comb.parse(span7).unwrap(),
///     (span7.slice(3..), Atom::Var(Ident { value: span7.slice(..3) })),
/// );
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "an atom", Output = ast::Atom<F, S>, Error = ParseError<F, S>)]
pub fn atom<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    branch::alt((comb::map(fact(), ast::Atom::Fact), comb::map(var(), ast::Atom::Var))).parse(input)
}



/// Parses a fact (i.e., a non-variable [`Atom`]).
///
/// # Returns
/// A combinator that can parse the input to a [`Fact`](ast::Fact).
///
/// # Fails
/// The returned combinator fails if the input is not an identifier followed by optional [`fact_args()`].
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, Fact, FactArgs, Comma, Parens, Ident};
/// use datalog::parser::atoms::{fact, ParseError};
///
/// let span1 = Span::new("<example>", "qux()");
/// let span2 = Span::new("<example>", "qux(foo)");
/// let span3 = Span::new("<example>", "qux(Bar, baz)");
/// let span4 = Span::new("<example>", "foo");
/// let span5 = Span::new("<example>", "(foo bar)");
/// let span6 = Span::new("<example>", "foo(#)");
/// let span7 = Span::new("<example>", "Bar");
///
/// let mut comb = fact();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(5..), Fact {
///         ident: Ident { value: span1.slice(..3) },
///         args: Some(FactArgs {
///             paren_tokens: Parens { open: span1.slice(3..4), close: span1.slice(4..5) },
///             args: punct![],
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(8..), Fact {
///         ident: Ident { value: span2.slice(..3) },
///         args: Some(FactArgs {
///             paren_tokens: Parens { open: span2.slice(3..4), close: span2.slice(7..8) },
///             args: punct![v => Atom::Fact(Fact {
///                 ident: Ident { value: span2.slice(4..7) },
///                 args: None,
///             })],
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(13..), Fact {
///         ident: Ident { value: span3.slice(..3) },
///         args: Some(FactArgs {
///             paren_tokens: Parens { open: span3.slice(3..4), close: span3.slice(12..13) },
///             args: punct![
///                 v => Atom::Var(Ident { value: span3.slice(4..7) }),
///                 p => Comma { span: span3.slice(7..8) },
///                 v => Atom::Fact(Fact {
///                     ident: Ident { value: span3.slice(9..12) },
///                     args: None,
///                 })
///             ],
///         }),
///     })
/// );
/// assert_eq!(
///     comb.parse(span4).unwrap(),
///     (span4.slice(3..), Fact {
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
///     SResult::Error(Error::Common(Common::Custom(ParseError::FactArgs { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span7),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Ident { .. })))
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "a fact", Output = ast::Fact<F, S>, Error = ParseError<F, S>)]
pub fn fact<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    // Parse the identifier first; then the optional arguments
    match seq::separated_pair(ident(), error::transmute(whitespaces::whitespace()), comb::opt(fact_args())).parse(input) {
        SResult::Ok(rem, (ident, args)) => SResult::Ok(rem, ast::Fact { ident, args }),
        SResult::Fail(fail) => SResult::Fail(fail),
        SResult::Error(err) => SResult::Error(err),
    }
}

/// Parses a list of fact arguments.
///
/// # Returns
/// A combinator that can parse the input to an [`FactArgs`](ast::FactArgs).
///
/// # Fails
/// The returned combinator fails if the input is not a list of fact arguments wrapped in parenthesis.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{Atom, Fact, FactArgs, Comma, Parens, Ident};
/// use datalog::parser::atoms::{fact_args, ParseError};
///
/// let span1 = Span::new("<example>", "()");
/// let span2 = Span::new("<example>", "(foo)");
/// let span3 = Span::new("<example>", "(Bar, baz)");
/// let span4 = Span::new("<example>", "foo");
/// let span5 = Span::new("<example>", "(foo bar)");
/// let span6 = Span::new("<example>", "(#)");
///
/// let mut comb = fact_args();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(2..), FactArgs {
///         paren_tokens: Parens { open: span1.slice(0..1), close: span1.slice(1..2) },
///         args: punct![],
///     })
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(5..), FactArgs {
///         paren_tokens: Parens { open: span2.slice(0..1), close: span2.slice(4..5) },
///         args: punct![v => Atom::Fact(Fact {
///             ident: Ident { value: span2.slice(1..4) },
///             args: None,
///         })],
///     })
/// );
/// assert_eq!(
///     comb.parse(span3).unwrap(),
///     (span3.slice(10..), FactArgs {
///         paren_tokens: Parens { open: span3.slice(..1), close: span3.slice(9..10) },
///         args: punct![
///             v => Atom::Var(Ident { value: span3.slice(1..4) }),
///             p => Comma { span: span3.slice(4..5) },
///             v => Atom::Fact(Fact {
///                 ident: Ident { value: span3.slice(6..9) },
///                 args: None,
///             })
///         ],
///     })
/// );
/// assert!(matches!(
///     comb.parse(span4),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::FactArgs { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span5),
///     SResult::Error(Error::Common(Common::Custom(ParseError::FactArgs { .. })))
/// ));
/// assert!(matches!(
///     comb.parse(span6),
///     SResult::Error(Error::Common(Common::Custom(ParseError::FactArgs { .. })))
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "zero or more arguments", Output = ast::FactArgs<F, S>, Error = ParseError<F, S>)]
pub fn fact_args<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    match tokens::parens(multi::punctuated0(
        seq::delimited(error::transmute(whitespaces::whitespace()), atom(), error::transmute(whitespaces::whitespace())),
        comb::map_err(tokens::comma(), |err| ParseError::Comma { span: err.into_span() }),
    ))
    .parse(input)
    {
        SResult::Ok(rem, (args, parens)) => SResult::Ok(rem, ast::FactArgs { paren_tokens: parens, args }),
        SResult::Fail(fail) => SResult::Fail(Failure::Common(Common::Custom(ParseError::FactArgs { span: fail.into_span() }))),
        SResult::Error(err) => SResult::Error(Error::Common(Common::Custom(ParseError::FactArgs { span: err.into_span() }))),
    }
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
/// use datalog::parser::atoms::{ParseError, ident};
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
/// use datalog::parser::atoms::{ParseError, var};
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
