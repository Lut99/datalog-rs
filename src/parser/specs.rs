//  SPECS.rs
//    by Lut99
//
//  Created:
//    08 May 2024, 11:12:42
//  Last edited:
//    17 May 2024, 18:07:38
//  Auto updated?
//    Yes
//
//  Description:
//!   Parses the toplevel $Datalog^\neg$ program.
//

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};
use std::marker::PhantomData;
use std::rc::Rc;

use ast_toolkit_snack::error::{Common, Failure};
use ast_toolkit_snack::{combinator as comb, error, multi, sequence as seq, utf8, Combinator, Expects, ExpectsFormatter, Result as SResult};
use ast_toolkit_span::Spanning;

use super::rules;
use crate::ast;


/***** TYPE ALIASES *****/
/// Convenience alias for a [`Span`](ast_toolkit_span::Span) over static strings.
type Span<'f, 's> = ast_toolkit_span::Span<&'f str, &'s str>;





/***** ERRORS *****/
/// Errors returned when parsing literals and related.
#[derive(Debug)]
pub enum ParseError<F, S> {
    /// Failed to parse a rule.
    Rule { span: ast_toolkit_span::Span<F, S> },
}
impl<F, S> ParseError<F, S> {
    /// Casts the [`Span`]s in this Failure into their owned counterparts.
    ///
    /// This performs some wizardry to clone the `from`- and `source`-strings only once, and then share them among the [`Span`]s using reference-counted pointers.
    ///
    /// See [`Failure::to_owned_arc()`] to get [`Arc`]-shared strings instead of [`Rc`]-shared ones.
    ///
    /// # Returns
    /// An equivalent Failure that owns the underlying source text among itself.
    #[inline]
    pub fn into_owned<FO: From<F>, SO: From<S>>(self) -> ParseError<Rc<FO>, Rc<SO>> {
        match self {
            Self::Rule { span } => ParseError::Rule { span: span.into_owned() },
        }
    }
}
impl<F, S> Display for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Rule { .. } => write!(f, "Expected a rule"),
        }
    }
}
impl<F: Debug, S: Debug> Error for ParseError<F, S> {}
impl<F: Clone, S: Clone> Spanning<F, S> for ParseError<F, S> {
    #[inline]
    fn span(&self) -> ast_toolkit_span::Span<F, S> {
        use ParseError::*;
        match self {
            Rule { span } => span.clone(),
        }
    }
}





/***** LIBRARY *****/
/// Parses $Datalog^\neg$ program.
///
/// # Returns
/// A combinator that parses list of rules.
///
/// # Fails
/// This combinator fails if the input was not solidly consisting of $Datalog^\neg$ rules.
///
/// # Example
/// ```rust
/// use ast_toolkit_punctuated::punct;
/// use ast_toolkit_snack::error::{Common, Error, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
/// use datalog::ast::{
///     Arrow, Atom, AtomArg, AtomArgs, Dot, Comma, Ident, Literal, NegAtom, Not, Parens, Rule,
///     RuleAntecedents, Spec,
/// };
/// use datalog::parser::specs::{spec, ParseError};
///
/// let span1 = Span::new("<example>", "");
/// let span2 = Span::new("<example>", "foo :- bar.");
/// let span3 = Span::new("<example>", "foo :- bar. foo, bar.");
/// let span4 = Span::new("<example>", "foo :- bar. foo, bar. baz");
///
/// let mut comb = spec();
/// assert_eq!(comb.parse(span1).unwrap(), (span1, Spec {
///     rules: vec![],
/// }));
/// assert_eq!(comb.parse(span2).unwrap(), (span2.slice(11..), Spec {
///     rules: vec![Rule {
///         consequences: punct![
///             v => Atom {
///                 ident: Ident { value: span2.slice(..3) },
///                 args: None,
///             }
///         ],
///         tail: Some(RuleAntecedents {
///             arrow_token: Arrow { span: span2.slice(4..6) },
///             antecedents: punct![v => Literal::Atom(Atom { ident: Ident { value: span2.slice(7..10) }, args: None })],
///         }),
///         dot: Dot { span: span2.slice(10..11) },
///     }],
/// }));
/// assert_eq!(comb.parse(span3).unwrap(), (span3.slice(21..), Spec {
///     rules: vec![
///         Rule {
///             consequences: punct![
///                 v => Atom {
///                     ident: Ident { value: span2.slice(..3) },
///                     args: None,
///                 }
///             ],
///             tail: Some(RuleAntecedents {
///                 arrow_token: Arrow { span: span2.slice(4..6) },
///                 antecedents: punct![v => Literal::Atom(Atom { ident: Ident { value: span2.slice(7..10) }, args: None })],
///             }),
///             dot: Dot { span: span2.slice(10..11) },
///         },
///         Rule {
///             consequences: punct![
///                 v => Atom {
///                     ident: Ident { value: span3.slice(12..15) },
///                     args: None,
///                 },
///                 p => Comma { span: span3.slice(15..16) },
///                 v => Atom {
///                     ident: Ident { value: span3.slice(17..20) },
///                     args: None,
///                 }
///             ],
///             tail: None,
///             dot: Dot { span: span3.slice(20..21) },
///         },
///     ]
/// }));
/// println!("{:?}", comb.parse(span4));
/// assert!(if let SResult::Fail(Failure::Common(Common::Custom(ParseError::Rule { span }))) = comb.parse(span4) { span == span4.slice(22..) } else { false });
/// ```
#[inline]
pub const fn spec<'f, 's>() -> Spec<'f, 's> { Spec { _f: PhantomData, _s: PhantomData } }





/***** LIBRARY EXPECTS *****/
/// ExpectsFormatter for the [`Spec`]-combinator.
#[derive(Debug)]
pub struct SpecExpects;
impl Display for SpecExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for SpecExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "zero or more rules") }
}





/***** LIBRARY COMBINATORS *****/
/// Combinator returned by [`spec()`].
pub struct Spec<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for Spec<'f, 's> {
    type Formatter = SpecExpects;
    #[inline]
    fn expects(&self) -> Self::Formatter { SpecExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for Spec<'f, 's> {
    type Output = ast::Spec<'f, 's>;
    type Error = ParseError<&'f str, &'s str>;

    #[inline]
    fn parse(&mut self, input: Span<'f, 's>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
        match comb::all(multi::many0(seq::delimited(
            error::transmute(utf8::whitespace0()),
            comb::map_err(rules::rule(), |err| ParseError::Rule { span: err.span() }),
            error::transmute(utf8::whitespace0()),
        )))
        .parse(input)
        {
            SResult::Ok(rem, rules) => SResult::Ok(rem, ast::Spec { rules }),
            SResult::Fail(Failure::Common(Common::All { span })) => SResult::Fail(Failure::Common(Common::Custom(ParseError::Rule { span }))),
            SResult::Fail(fail) => SResult::Fail(fail),
            SResult::Error(err) => SResult::Error(err),
        }
    }
}
