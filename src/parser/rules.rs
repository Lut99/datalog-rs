//  RULES.rs
//    by Lut99
//
//  Created:
//    07 May 2024, 16:38:16
//  Last edited:
//    08 May 2024, 11:26:08
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements combinators for parsing $Datalog^\neg$ rules.
//

use std::error::Error;
use std::fmt::{Display, Formatter, Result as FResult};
use std::marker::PhantomData;

use ast_toolkit_snack::combinator::map_err;
use ast_toolkit_snack::{combinator as comb, error, multi, sequence as seq, utf8, Combinator, Expects, ExpectsFormatter, Result as SResult};
use ast_toolkit_span::Spanning;

use super::{atoms, literals, tokens};
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
    /// Failed to parse a literal.
    Literal { span: Span<'f, 's> },
}
impl<'f, 's> Display for ParseError<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Atom { .. } => write!(f, "Expected an atom"),
            Literal { .. } => write!(f, "Expected a literal"),
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
            Literal { span } => *span,
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
/// use ast_toolkit_punctuated::punct;
/// use ast_toolkit_snack::error::{Common, Error, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
/// use datalog::ast::{
///     Arrow, Atom, AtomArg, AtomArgs, Dot, Comma, Ident, Literal, NegAtom, Not, Parens, Rule,
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
///     consequences: punct![
///         v => Atom {
///             ident: Ident { value: span1.slice(..3) },
///             args: None,
///         }
///     ],
///     tail: Some(RuleAntecedents {
///         arrow_token: Arrow { span: span1.slice(4..6) },
///         antecedents: punct![v => Literal::Atom(Atom { ident: Ident { value: span1.slice(7..10) }, args: None })],
///     }),
///     dot: Dot { span: span1.slice(10..11) },
/// }));
/// assert_eq!(comb.parse(span2).unwrap(), (span2.slice(9..), Rule {
///     consequences: punct![
///         v => Atom {
///             ident: Ident { value: span2.slice(..3) },
///             args: None,
///         },
///         p => Comma { span: span2.slice(3..4) },
///         v => Atom {
///             ident: Ident { value: span2.slice(5..8) },
///             args: None,
///         }
///     ],
///     tail: None,
///     dot: Dot { span: span2.slice(8..9) },
/// }));
/// assert_eq!(comb.parse(span3).unwrap(), (span3.slice(21..), Rule {
///     consequences: punct![
///         v => Atom {
///             ident: Ident { value: span3.slice(..3) },
///             args: Some(AtomArgs {
///                 paren_tokens: Parens { open: span3.slice(3..4), close: span3.slice(7..8) },
///                 args: punct![v => AtomArg::Atom(Ident { value: span3.slice(4..7) })],
///             }),
///         }
///     ],
///     tail: Some(RuleAntecedents {
///         arrow_token: Arrow { span: span3.slice(9..11) },
///         antecedents: punct![v => Literal::Atom(Atom {
///             ident: Ident { value: span3.slice(12..15) },
///             args: Some(AtomArgs {
///                 paren_tokens: Parens { open: span3.slice(15..16), close: span3.slice(19..20) },
///                 args: punct![v => AtomArg::Var(Ident { value: span3.slice(16..19) })],
///             }),
///         })],
///     }),
///     dot: Dot { span: span3.slice(20..21) },
/// }));
/// assert!(matches!(comb.parse(span4), SResult::Fail(Failure::Common(Common::PunctuatedList1 { .. }))));
/// assert!(matches!(comb.parse(span5), SResult::Fail(Failure::Common(Common::PunctuatedList1 { .. }))));
/// ```
#[inline]
pub const fn rule<'f, 's>() -> Rule<'f, 's> { Rule { _f: PhantomData, _s: PhantomData } }

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
/// use ast_toolkit_punctuated::punct;
/// use ast_toolkit_snack::error::{Common, Error, Failure};
/// use ast_toolkit_snack::{Combinator as _, Result as SResult};
/// use ast_toolkit_span::Span;
/// use datalog::ast::{
///     Arrow, Atom, AtomArg, AtomArgs, Comma, Ident, Literal, NegAtom, Not, Parens, RuleAntecedents,
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
///         antecedents: punct![v => Literal::Atom(Atom { ident: Ident { value: span1.slice(3..6) }, args: None })],
///     }),
/// );
/// assert_eq!(
///     comb.parse(span2).unwrap(),
///     (span2.slice(22..), RuleAntecedents {
///         arrow_token: Arrow { span: span2.slice(..2) },
///         antecedents: punct![
///             v => Literal::NegAtom(NegAtom {
///                 not_token: Not { span: span2.slice(3..6) },
///                 atom: Atom {
///                     ident: Ident { value: span2.slice(7..10) },
///                     args: Some(AtomArgs {
///                         paren_tokens: Parens { open: span2.slice(10..11), close: span2.slice(11..12) },
///                         args: punct![],
///                     }),
///                 },
///             }),
///             p => Comma { span: span2.slice(12..13) },
///             v => Literal::Atom(Atom {
///                 ident: Ident { value: span2.slice(14..17) },
///                 args: Some(AtomArgs {
///                     paren_tokens: Parens { open: span2.slice(17..18), close: span2.slice(21..22) },
///                     args: punct![v => AtomArg::Atom(Ident { value: span2.slice(18..21) })],
///                 }),
///             })
///         ],
///     }),
/// );
/// assert!(matches!(
///     comb.parse(span3),
///     SResult::Fail(Failure::Common(Common::TagUtf8 { tag: ":-", .. })),
/// ));
/// assert!(matches!(
///     comb.parse(span4),
///     SResult::Error(Error::Common(Common::PunctuatedList1 { .. })),
/// ));
/// ```
#[inline]
pub const fn rule_antecedents<'f, 's>() -> RuleAntecedents<'f, 's> { RuleAntecedents { _f: PhantomData, _s: PhantomData } }





/***** LIBRARY EXPECTS *****/
/// ExpectsForamtter for the [`Rule`] combinator.
#[derive(Debug)]
pub struct RuleExpects;
impl Display for RuleExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for RuleExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "a rule") }
}

/// ExpectsForamtter for the [`RuleAntecedents`] combinator.
#[derive(Debug)]
pub struct RuleAntecedentsExpects;
impl Display for RuleAntecedentsExpects {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "Expected ")?;
        self.expects_fmt(f, 0)
    }
}
impl ExpectsFormatter for RuleAntecedentsExpects {
    #[inline]
    fn expects_fmt(&self, f: &mut Formatter, _indent: usize) -> FResult { write!(f, "an arrow symbol followed by antecedents") }
}





/***** LIBRARY COMBINATORS *****/
/// Combinator returned by [`rule()`].
pub struct Rule<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for Rule<'f, 's> {
    type Formatter = RuleExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { RuleExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for Rule<'f, 's> {
    type Output = ast::Rule<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: Span<'f, 's>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
        match seq::tuple((
            multi::punctuated1(
                seq::delimited(
                    error::transmute(utf8::whitespace0()),
                    map_err(atoms::atom(), |err| ParseError::Atom { span: err.span() }),
                    error::transmute(comb::not(utf8::complete::while1(|c| {
                        if c.len() != 1 {
                            return false;
                        }
                        let c: char = c.chars().next().unwrap();
                        (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_'
                    }))),
                ),
                error::transmute(tokens::comma()),
            ),
            error::transmute(utf8::whitespace0()),
            comb::opt(rule_antecedents()),
            error::transmute(utf8::whitespace0()),
            error::transmute(tokens::dot()),
        ))
        .parse(input)
        {
            SResult::Ok(rem, (consequences, _, tail, _, dot)) => SResult::Ok(rem, ast::Rule { consequences, tail, dot }),
            SResult::Fail(fail) => SResult::Fail(fail),
            SResult::Error(err) => SResult::Error(err),
        }
    }
}

/// Combinator returned by [`rule_antecedents()`].
pub struct RuleAntecedents<'f, 's> {
    _f: PhantomData<&'f ()>,
    _s: PhantomData<&'s ()>,
}
impl<'f, 's> Expects<'static> for RuleAntecedents<'f, 's> {
    type Formatter = RuleAntecedentsExpects;

    #[inline]
    fn expects(&self) -> Self::Formatter { RuleAntecedentsExpects }
}
impl<'f, 's> Combinator<'static, &'f str, &'s str> for RuleAntecedents<'f, 's> {
    type Output = ast::RuleAntecedents<'f, 's>;
    type Error = ParseError<'f, 's>;

    #[inline]
    fn parse(&mut self, input: Span<'f, 's>) -> SResult<'static, Self::Output, &'f str, &'s str, Self::Error> {
        match seq::pair(
            error::transmute(tokens::arrow()),
            error::cut(multi::punctuated1(
                comb::map_err(
                    seq::delimited(
                        error::transmute(utf8::whitespace0()),
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
                error::transmute(tokens::comma()),
            )),
        )
        .parse(input)
        {
            SResult::Ok(rem, (arrow_token, antecedents)) => SResult::Ok(rem, ast::RuleAntecedents { arrow_token, antecedents }),
            SResult::Fail(fail) => SResult::Fail(fail),
            SResult::Error(err) => SResult::Error(err),
        }
    }
}
