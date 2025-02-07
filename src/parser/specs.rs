//  SPECS.rs
//    by Lut99
//
//  Created:
//    08 May 2024, 11:12:42
//  Last edited:
//    07 Feb 2025, 17:43:27
//  Auto updated?
//    Yes
//
//  Description:
//!   Parses the toplevel $Datalog^\neg$ program.
//

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};
use std::rc::Rc;

use ast_toolkit::snack::error::{Common, Failure};
use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{Result as SResult, comb, combinator as comb, error, multi, sequence as seq};
use ast_toolkit::span::{Span, Spannable, Spanning};

use super::{rules, whitespaces};
use crate::ast;


/***** ERRORS *****/
/// Errors returned when parsing literals and related.
pub enum ParseError<F, S> {
    /// Failed to parse a rule.
    Rule { span: Span<F, S> },
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
impl<F, S> Debug for ParseError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Rule { span } => {
                let mut fmt = f.debug_struct("ParseError::Rule");
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
            Rule { .. } => write!(f, "Expected a rule"),
        }
    }
}
impl<F, S> Error for ParseError<F, S> {}
impl<F: Clone, S: Clone> Spanning<F, S> for ParseError<F, S> {
    #[inline]
    fn span(&self) -> Span<F, S> {
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
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Fact, Dot, Comma, Ident, Literal, NegAtom, Not, Parens, Rule,
///     RuleBody, Spec,
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
///         consequents: punct![
///             v => Atom::Fact(Fact {
///                 ident: Ident { value: span2.slice(..3) },
///                 args: None,
///             })
///         ],
///         tail: Some(RuleBody {
///             arrow_token: Arrow { span: span2.slice(4..6) },
///             antecedents: punct![v => Literal::Atom(Atom::Fact(Fact { ident: Ident { value: span2.slice(7..10) }, args: None }))],
///         }),
///         dot: Dot { span: span2.slice(10..11) },
///     }],
/// }));
/// assert_eq!(comb.parse(span3).unwrap(), (span3.slice(21..), Spec {
///     rules: vec![
///         Rule {
///             consequents: punct![
///                 v => Atom::Fact(Fact {
///                     ident: Ident { value: span2.slice(..3) },
///                     args: None,
///                 })
///             ],
///             tail: Some(RuleBody {
///                 arrow_token: Arrow { span: span2.slice(4..6) },
///                 antecedents: punct![v => Literal::Atom(Atom::Fact(Fact { ident: Ident { value: span2.slice(7..10) }, args: None }))],
///             }),
///             dot: Dot { span: span2.slice(10..11) },
///         },
///         Rule {
///             consequents: punct![
///                 v => Atom::Fact(Fact {
///                     ident: Ident { value: span3.slice(12..15) },
///                     args: None,
///                 }),
///                 p => Comma { span: span3.slice(15..16) },
///                 v => Atom::Fact(Fact {
///                     ident: Ident { value: span3.slice(17..20) },
///                     args: None,
///                 })
///             ],
///             tail: None,
///             dot: Dot { span: span3.slice(20..21) },
///         },
///     ]
/// }));
/// assert!(if let SResult::Fail(Failure::Common(Common::Custom(ParseError::Rule { span }))) = comb.parse(span4) { span == span4.slice(22..) } else { false });
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "zero or more rules", Output = ast::Spec<F, S>, Error = ParseError<F, S>)]
pub fn spec<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + Spannable + WhileUtf8,
{
    match comb::all(multi::many0(seq::delimited(
        error::transmute(whitespaces::whitespace()),
        comb::map_err(rules::rule(), |err| ParseError::Rule { span: err.span() }),
        error::transmute(whitespaces::whitespace()),
    )))
    .parse(input)
    {
        SResult::Ok(rem, rules) => SResult::Ok(rem, ast::Spec { rules }),
        SResult::Fail(Failure::Common(Common::All { span })) => SResult::Fail(Failure::Common(Common::Custom(ParseError::Rule { span }))),
        SResult::Fail(fail) => SResult::Fail(fail),
        SResult::Error(err) => SResult::Error(err),
    }
}
