//  RULES.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 16:38:16
//  Last edited:
//    03 Feb 2025, 19:20:48
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements combinators for parsing $Datalog^\neg$ rules.
//

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FResult};

use ast_toolkit::snack::combinator::map_err;
use ast_toolkit::snack::span::{MatchBytes, OneOfBytes, OneOfUtf8, WhileUtf8};
use ast_toolkit::snack::{Result as SResult, comb, combinator as comb, error, multi, sequence as seq, utf8};
use ast_toolkit::span::{Span, Spanning};

use super::{atoms, literals, tokens, whitespaces};
use crate::ast;


/***** ERRORS *****/
/// Errors returned when parsing literals and related.
pub enum ParseError<F, S> {
    /// Failed to parse an atom.
    Atom { span: Span<F, S> },
    /// Failed to parse a literal.
    Literal { span: Span<F, S> },
    /// Failed to parse an arrow.
    Arrow { span: Span<F, S> },
    /// Failed to parse a comma.
    Comma { span: Span<F, S> },
    /// Failed to parse a dot.
    Dot { span: Span<F, S> },
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
            Literal { span } => {
                let mut fmt = f.debug_struct("ParseError::Literal");
                fmt.field("span", span);
                fmt.finish()
            },
            Arrow { span } => {
                let mut fmt = f.debug_struct("ParseError::Arrow");
                fmt.field("span", span);
                fmt.finish()
            },
            Comma { span } => {
                let mut fmt = f.debug_struct("ParseError::Comma");
                fmt.field("span", span);
                fmt.finish()
            },
            Dot { span } => {
                let mut fmt = f.debug_struct("ParseError::Dot");
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
            Literal { .. } => write!(f, "Expected a literal"),
            Arrow { .. } => write!(f, "Expected an arrow"),
            Comma { .. } => write!(f, "Expected a comma"),
            Dot { .. } => write!(f, "Expected a dot"),
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
            Literal { span } => span.clone(),
            Arrow { span } => span.clone(),
            Comma { span } => span.clone(),
            Dot { span } => span.clone(),
        }
    }

    #[inline]
    fn into_span(self) -> Span<F, S>
    where
        Self: Sized,
    {
        match self {
            Self::Atom { span } => span,
            Self::Literal { span } => span,
            Self::Arrow { span } => span,
            Self::Comma { span } => span,
            Self::Dot { span } => span,
        }
    }
}





/***** LIBRARY *****/
/// Parses $Datalog^\neg$ rules.
///
/// # Returns
/// A combinator that parses a punctuated list of consequences, then `:-`, and then a punctuated list of antecedents, finalized by a dot.
///
/// # Fails
/// This combinator fails if the input was not an arrow followed by comma-separated atoms.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Fact, FactArgs, Dot, Comma, Ident, Literal, NegAtom, Not, Parens, Rule,
///     RuleAntecedents,
/// };
/// use datalog::parser::rules::{rule, ParseError};
///
/// let span1 = Span::new("<example>", "foo :- bar.");
/// let span2 = Span::new("<example>", "foo, bar.");
/// let span3 = Span::new("<example>", "bar(foo) :- baz(Qux).");
/// let span4 = Span::new("<example>", ".");
/// let span5 = Span::new("<example>", ":-");
///
/// let mut comb = rule();
/// assert_eq!(comb.parse(span1).unwrap(), (span1.slice(11..), Rule {
///     consequents: punct![
///         v => Atom::Fact(Fact {
///             ident: Ident { value: span1.slice(..3) },
///             args: None,
///         })
///     ],
///     tail: Some(RuleAntecedents {
///         arrow_token: Arrow { span: span1.slice(4..6) },
///         antecedents: punct![v => Literal::Atom(Atom::Fact(Fact { ident: Ident { value: span1.slice(7..10) }, args: None }))],
///     }),
///     dot: Dot { span: span1.slice(10..11) },
/// }));
/// assert_eq!(comb.parse(span2).unwrap(), (span2.slice(9..), Rule {
///     consequents: punct![
///         v => Atom::Fact(Fact {
///             ident: Ident { value: span2.slice(..3) },
///             args: None,
///         }),
///         p => Comma { span: span2.slice(3..4) },
///         v => Atom::Fact(Fact {
///             ident: Ident { value: span2.slice(5..8) },
///             args: None,
///         })
///     ],
///     tail: None,
///     dot: Dot { span: span2.slice(8..9) },
/// }));
/// assert_eq!(comb.parse(span3).unwrap(), (span3.slice(21..), Rule {
///     consequents: punct![
///         v => Atom::Fact(Fact {
///             ident: Ident { value: span3.slice(..3) },
///             args: Some(FactArgs {
///                 paren_tokens: Parens { open: span3.slice(3..4), close: span3.slice(7..8) },
///                 args: punct![v => Atom::Fact(Fact {
///                     ident: Ident { value: span3.slice(4..7) },
///                     args: None,
///                 })],
///             }),
///         })
///     ],
///     tail: Some(RuleAntecedents {
///         arrow_token: Arrow { span: span3.slice(9..11) },
///         antecedents: punct![v => Literal::Atom(Atom::Fact(Fact {
///             ident: Ident { value: span3.slice(12..15) },
///             args: Some(FactArgs {
///                 paren_tokens: Parens { open: span3.slice(15..16), close: span3.slice(19..20) },
///                 args: punct![v => Atom::Var(Ident { value: span3.slice(16..19) })],
///             }),
///         }))],
///     }),
///     dot: Dot { span: span3.slice(20..21) },
/// }));
/// assert!(matches!(comb.parse(span4), SResult::Fail(Failure::Common(Common::PunctuatedList1 { .. }))));
/// assert!(matches!(comb.parse(span5), SResult::Fail(Failure::Common(Common::PunctuatedList1 { .. }))));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "a rule", Output = ast::Rule<F, S>, Error = ParseError<F, S>)]
pub fn rule<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    match seq::tuple((
        multi::punctuated1(
            seq::delimited(
                error::transmute(whitespaces::whitespace()),
                map_err(atoms::atom(), |err| ParseError::Atom { span: err.span() }),
                error::transmute(comb::not(utf8::complete::while1(|c| {
                    if c.len() != 1 {
                        return false;
                    }
                    let c: char = c.chars().next().unwrap();
                    (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_'
                }))),
            ),
            comb::map_err(tokens::comma(), |err| ParseError::Comma { span: err.into_span() }),
        ),
        error::transmute(whitespaces::whitespace()),
        comb::opt(rule_antecedents()),
        error::transmute(whitespaces::whitespace()),
        comb::map_err(tokens::dot(), |err| ParseError::Dot { span: err.into_span() }),
    ))
    .parse(input)
    {
        SResult::Ok(rem, (consequents, _, tail, _, dot)) => SResult::Ok(rem, ast::Rule { consequents, tail, dot }),
        SResult::Fail(fail) => SResult::Fail(fail),
        SResult::Error(err) => SResult::Error(err),
    }
}

/// Parses the antecedent-part of a rule.
///
/// # Returns
/// A combinator that parses `:-`, then a punctuated list of atoms.
///
/// # Fails
/// This combinator fails if the input was not an arrow followed by comma-separated atoms.
///
/// # Example
/// ```rust
/// use ast_toolkit::punctuated::punct;
/// use ast_toolkit::snack::error::{Common, Error, Failure};
/// use ast_toolkit::snack::{Combinator as _, Result as SResult};
/// use ast_toolkit::span::Span;
/// use datalog::ast::{
///     Arrow, Atom, Fact, FactArgs, Comma, Ident, Literal, NegAtom, Not, Parens, RuleAntecedents,
/// };
/// use datalog::parser::rules::{rule_antecedents, ParseError};
///
/// let span1 = Span::new("<example>", ":- foo");
/// let span2 = Span::new("<example>", ":- not foo(), bar(baz)");
/// let span3 = Span::new("<example>", "foo");
/// let span4 = Span::new("<example>", ":-");
///
/// let mut comb = rule_antecedents();
/// assert_eq!(
///     comb.parse(span1).unwrap(),
///     (span1.slice(6..), RuleAntecedents {
///         arrow_token: Arrow { span: span1.slice(..2) },
///         antecedents: punct![v => Literal::Atom(Atom::Fact(Fact { ident: Ident { value: span1.slice(3..6) }, args: None }))],
///     }),
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(22..), RuleAntecedents {
///         arrow_token: Arrow { span: span2.slice(..2) },
///         antecedents: punct![
///             v => Literal::NegAtom(NegAtom {
///                 not_token: Not { span: span2.slice(3..6) },
///                 atom: Atom::Fact(Fact {
///                     ident: Ident { value: span2.slice(7..10) },
///                     args: Some(FactArgs {
///                         paren_tokens: Parens { open: span2.slice(10..11), close: span2.slice(11..12) },
///                         args: punct![],
///                     }),
///                 }),
///             }),
///             p => Comma { span: span2.slice(12..13) },
///             v => Literal::Atom(Atom::Fact(Fact {
///                 ident: Ident { value: span2.slice(14..17) },
///                 args: Some(FactArgs {
///                     paren_tokens: Parens { open: span2.slice(17..18), close: span2.slice(21..22) },
///                     args: punct![v => Atom::Fact(Fact {
///                         ident: Ident { value: span2.slice(18..21) },
///                         args: None,
///                     })],
///                 }),
///             }))
///         ],
///     }),
/// );
/// assert!(matches!(
///     comb.parse(span3),
///     SResult::Fail(Failure::Common(Common::Custom(ParseError::Arrow { .. }))),
/// ));
/// assert!(matches!(
///     comb.parse(span4),
///     SResult::Error(Error::Common(Common::PunctuatedList1 { .. })),
/// ));
/// ```
#[inline]
#[comb(snack = ::ast_toolkit::snack, expected = "an arrow symbol followed by antecedents", Output = ast::RuleAntecedents<F, S>, Error = ParseError<F, S>)]
pub fn rule_antecedents<F, S>(input: Span<F, S>) -> _
where
    F: Clone,
    S: Clone + MatchBytes + OneOfBytes + OneOfUtf8 + WhileUtf8,
{
    match seq::pair(
        comb::map_err(tokens::arrow(), |err| ParseError::Arrow { span: err.into_span() }),
        error::cut(multi::punctuated1(
            comb::map_err(
                seq::delimited(
                    error::transmute(whitespaces::whitespace()),
                    literals::literal(),
                    error::transmute(comb::not(utf8::complete::while1(|c| {
                        if c.len() != 1 {
                            return false;
                        }
                        let c: char = c.chars().next().unwrap();
                        (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_'
                    }))),
                ),
                |err| ParseError::Literal { span: err.span() },
            ),
            comb::map_err(tokens::comma(), |err| ParseError::Comma { span: err.into_span() }),
        )),
    )
    .parse(input)
    {
        SResult::Ok(rem, (arrow_token, antecedents)) => SResult::Ok(rem, ast::RuleAntecedents { arrow_token, antecedents }),
        SResult::Fail(fail) => SResult::Fail(fail),
        SResult::Error(err) => SResult::Error(err),
    }
}
