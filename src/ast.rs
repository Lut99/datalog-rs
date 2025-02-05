//  AST.rs
//    by Lut99
//
//  Created:
//    13 Mar 2024, 16:43:37
//  Last edited:
//    05 Feb 2025, 17:47:26
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines the datalog-with-negation AST.
//

use std::fmt::{Display, Formatter, Result as FResult};

pub use ast_toolkit::punctuated::Punctuated;
#[cfg(feature = "macros")]
pub use ast_toolkit::punctuated::punct;
#[cfg(feature = "railroad")]
use ast_toolkit::railroad::{ToDelimNode, ToNode, ToNonTerm, railroad as rr};
use ast_toolkit::span::SpannableDisplay;
pub use ast_toolkit::span::{Span, Spanning as _};
use ast_toolkit::tokens::{utf8_delimiter, utf8_token};
use better_derive::{Clone, Copy, Debug, Eq, Hash, PartialEq};
// Re-export the derive macro
#[cfg(feature = "macros")]
pub use datalog_macros::datalog;
use enum_debug::EnumDebug;


/***** INTERFACES *****/
/// Generalizes over different kinds of atoms.
pub trait Atomlike<F, S> {
    /// Returns whether this atom has any arguments.
    ///
    /// If true, implies [`Atomlike::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    fn is_constant(&self) -> bool;

    /// Returns whether this atom has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    fn is_grounded(&self) -> bool;

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i;

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i;
}





/***** LIBRARY FUNCTIONS *****/
/// Generates a static railroad diagram of the $Datalog^\neg$ AST.
///
/// This simply wraps [`Spec`] and calls [`ToNode::railroad()`] on it.
///
/// # Returns
/// - A [`railroad::Diagram`] that represents the generated diagram.
#[cfg(feature = "railroad")]
#[inline]
pub fn diagram() -> rr::Diagram<rr::VerticalGrid<Box<dyn rr::Node>>> {
    ast_toolkit::railroad::diagram!(
        Spec::<Atom<(), ()>, (), ()> as "Spec",
    )
}

/// Generates a static railroad diagram of the $Datalog^\neg$ AST to a location of your choice.
///
/// This simply wraps [`Spec`] and calls [`ToNode::railroad()`] on it.
///
/// # Arguments
/// - `path`: The path to generate the file.
///
/// # Errors
/// This function may error if it failed to write the file.
#[cfg(feature = "railroad")]
pub fn diagram_to_path(path: impl AsRef<std::path::Path>) -> Result<(), std::io::Error> {
    // Generate the diagram
    let mut diagram: rr::Diagram<_> = diagram();
    diagram.add_element(rr::svg::Element::new("style").set("type", "text/css").text(rr::DEFAULT_CSS));

    // Write it to a file
    let path: &std::path::Path = path.as_ref();
    std::fs::write(path, diagram.to_string())
}





/***** LIBRARY *****/
/// The root node that specifies a policy.
///
/// # Syntax
/// ```plain
/// foo :- bar, baz(quz).
/// foo.
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNonTerm))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub struct Spec<A, F, S> {
    /// The list of rules in this program.
    pub rules: Vec<Rule<A, F, S>>,
}
impl<A: Display, F, S: SpannableDisplay> Display for Spec<A, F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        for rule in &self.rules {
            rule.fmt(f)?;
            writeln!(f)?;
        }
        Ok(())
    }
}



/// Specifies a single rule.
///
/// # Syntax
/// ```plain
/// foo :- bar, baz(quz).
/// foo.
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Rule<A, F, S> {
    /// A list of consequents (i.e., instances produced by this rule).
    pub consequents: Punctuated<A, Comma<F, S>>,
    /// An optional second part that describes the antecedents.
    pub tail: Option<RuleAntecedents<A, F, S>>,
    /// The closing dot after each rule.
    pub dot: Dot<F, S>,
}
impl<A, F, S> Rule<A, F, S> {
    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more atoms.
    #[inline]
    pub fn atoms<'s>(&'s self) -> impl 's + Iterator<Item = &'s A> {
        self.consequents.values().chain(self.tail.iter().flat_map(RuleAntecedents::atoms))
    }

    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to atoms.
    #[inline]
    pub fn atoms_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut A> {
        self.consequents.values_mut().chain(self.tail.iter_mut().flat_map(RuleAntecedents::atoms_mut))
    }
}
impl<A: Display, F, S: SpannableDisplay> Display for Rule<A, F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        for (i, atom) in self.consequents.values().enumerate() {
            if i > 0 {
                write!(f, ",")?;
                if f.alternate() {
                    write!(f, " ")?;
                }
            }
            atom.fmt(f)?;
        }
        if let Some(tail) = &self.tail {
            tail.fmt(f)?;
        }
        Ok(())
    }
}
#[cfg(feature = "railroad")]
impl<A: ToNode, F, S> ToNode for Rule<A, F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(rr::Repeat::new(A::railroad(), Comma::<F, S>::railroad())),
            Box::new(rr::Optional::new(RuleAntecedents::<A, F, S>::railroad())),
            Box::new(Dot::<F, S>::railroad()),
        ])
    }
}

/// Defines the second half of the rule, if any.
///
/// # Syntax
/// ```plain
/// :- foo, bar(baz)
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RuleAntecedents<A, F, S> {
    /// The arrow token.
    pub arrow_token: Arrow<F, S>,
    /// The list of antecedents.
    pub antecedents: Punctuated<Literal<A, F, S>, Comma<F, S>>,
}
impl<A, F, S> RuleAntecedents<A, F, S> {
    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more antecedents.
    #[inline]
    pub fn atoms<'s>(&'s self) -> impl 's + Iterator<Item = &'s A> { self.antecedents.values().map(Literal::atom) }

    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to antecedents.
    #[inline]
    pub fn atoms_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut A> { self.antecedents.values_mut().map(Literal::atom_mut) }
}
impl<A: Display, F, S: SpannableDisplay> Display for RuleAntecedents<A, F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, " :- ")?;
        for (i, lit) in self.antecedents.values().enumerate() {
            if i > 0 {
                write!(f, ",")?;
                if f.alternate() {
                    write!(f, " ")?;
                }
            }
            lit.fmt(f)?;
        }
        Ok(())
    }
}
#[cfg(feature = "railroad")]
impl<A: ToNode, F, S> ToNode for RuleAntecedents<A, F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Arrow::<F, S>::railroad()),
            Box::new(rr::Repeat::new(Literal::<A, F, S>::railroad(), Comma::<F, S>::railroad())),
        ])
    }
}



/// Represents a single antecedent, as it were.
///
/// # Syntax
/// ```plain
/// foo
/// foo(bar)
/// not foo
/// ```
#[derive(Clone, Debug, EnumDebug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum Literal<A, F, S> {
    /// Non-negated atom.
    ///
    /// # Syntax
    /// ```plain
    /// foo
    /// foo(bar)
    /// ```
    Atom(A),
    /// Negated atom.
    ///
    /// # Syntax
    /// ```plain
    /// not foo
    /// ```
    NegAtom(NegAtom<A, F, S>),
}
impl<A, F, S> Literal<A, F, S> {
    /// Returns the polarity of the literal.
    ///
    /// # Returns
    /// True if this is a positive literal ([`Literal::Atom`]), or false if it's a negative literal ([`Literal::NegAtom`]).
    pub fn is_positive(&self) -> bool { matches!(self, Self::Atom(_)) }

    /// Returns the atom that appears in all variants of the literal.
    ///
    /// # Returns
    /// A reference to the [`Atom`] contained within.
    pub fn atom(&self) -> &A {
        match self {
            Self::Atom(a) => a,
            Self::NegAtom(na) => &na.atom,
        }
    }

    /// Returns the atom that appears in all variants of the literal.
    ///
    /// # Returns
    /// A mutable reference to the [`Atom`] contained within.
    pub fn atom_mut(&mut self) -> &mut A {
        match self {
            Self::Atom(a) => a,
            Self::NegAtom(na) => &mut na.atom,
        }
    }

    /// Returns if there are any variables in the nested atom.
    ///
    /// # Returns
    /// False if there is at least one [`Atom::Var`] recursively, or true otherwise.
    #[inline]
    pub fn is_grounded(&self) -> bool { self.atom().is_grounded() }
}
impl<A: Display, F, S: SpannableDisplay> Display for Literal<A, F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Atom(a) => a.fmt(f),
            Self::NegAtom(na) => na.fmt(f),
        }
    }
}

/// Wraps around an [`Atom`] to express its non-existance.
///
/// # Syntax
/// ```plain
/// not foo
/// not foo(bar)
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub struct NegAtom<A, F, S> {
    /// The not-token.
    pub not_token: Not<F, S>,
    /// The atom that was negated.
    pub atom:      A,
}
impl<A: Display, F, S: SpannableDisplay> Display for NegAtom<A, F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "not ")?;
        self.atom.fmt(f)
    }
}



/// Defines a constructor application of facts _or_ a variable.
///
/// # Syntax
/// ```plain
/// foo
/// foo(bar, Baz)
/// Bar
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum Atom<F, S> {
    /// It's a Fact.
    ///
    /// # Syntax
    /// ```plain
    /// foo
    /// foo(bar, Baz)
    /// ```
    Fact(Fact<F, S>),
    /// It's a variable.
    ///
    /// # Syntax
    /// ```plain
    /// Bar
    /// ```
    Var(Ident<F, S>),
}
impl<F, S> Atom<F, S> {
    /// Returns an iterator over the internal arguments.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Atom`] (references).
    #[inline]
    fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Self> {
        match self {
            Self::Fact(f) => Some(f.args.iter().flat_map(|t| t.args.values())).into_iter().flatten(),
            Self::Var(_) => None.into_iter().flatten(),
        }
    }

    /// Returns an iterator over the internal arguments.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Atom`] (mutable references).
    #[inline]
    fn args_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Self> {
        match self {
            Self::Fact(f) => Some(f.args.iter_mut().flat_map(|t| t.args.values_mut())).into_iter().flatten(),
            Self::Var(_) => None.into_iter().flatten(),
        }
    }
}
impl<F, S> Atomlike<F, S> for Atom<F, S> {
    #[inline]
    fn is_constant(&self) -> bool {
        match self {
            Self::Fact(f) => f.is_constant(),
            Self::Var(_) => false,
        }
    }

    #[inline]
    fn is_grounded(&self) -> bool {
        match self {
            Self::Fact(f) => f.is_grounded(),
            Self::Var(_) => false,
        }
    }

    #[inline]
    fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        match self {
            Self::Fact(f) => Box::new(f.vars()) as Box<dyn 's + Iterator<Item = &'s Ident<F, S>>>,
            Self::Var(v) => Box::new(Some(v).into_iter()),
        }
    }

    #[inline]
    fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        match self {
            Self::Fact(f) => Box::new(f.vars_mut()) as Box<dyn 's + Iterator<Item = &'s mut Ident<F, S>>>,
            Self::Var(v) => Box::new(Some(v).into_iter()),
        }
    }
}
impl<F, S: SpannableDisplay> Display for Atom<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Fact(fa) => fa.fmt(f),
            Self::Var(v) => v.fmt(f),
        }
    }
}

/// Defines a fact, which is an identifier followed by zero or more arguments.
///
/// Kinda like a function application. Can be recursive.
///
/// # Syntax
/// ```plain
/// foo
/// foo(bar, Baz)
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub struct Fact<F, S> {
    /// The identifier itself.
    pub ident: Ident<F, S>,
    /// Any arguments.
    pub args:  Option<FactArgs<F, S>>,
}
impl<F, S> Fact<F, S> {
    /// Returns an iterator over the arguments in this fact, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more [`Atom`]s representing each argument.
    #[inline]
    pub fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Atom<F, S>> { self.args.iter().flat_map(|t| t.args.values()).into_iter() }
    /// Returns an iterator over the arguments in this fact, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to [`Atom`]s representing each
    /// argument.
    #[inline]
    pub fn args_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Atom<F, S>> {
        self.args.iter_mut().flat_map(|t| t.args.values_mut()).into_iter()
    }
}
impl<F, S> Atomlike<F, S> for Fact<F, S> {
    #[inline]
    fn is_constant(&self) -> bool { self.args.as_ref().map(|a| a.args.is_empty()).unwrap_or(true) }

    #[inline]
    fn is_grounded(&self) -> bool {
        match &self.args {
            Some(args) => args.args.values().all(Atomlike::is_grounded),
            None => false,
        }
    }

    #[inline]
    fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.args.iter().flat_map(|args| args.args.values().flat_map(Atomlike::vars))
    }

    #[inline]
    fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.args.iter_mut().flat_map(|args| args.args.values_mut().flat_map(Atomlike::vars_mut))
    }
}
impl<F, S: SpannableDisplay> Display for Fact<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FResult {
        self.ident.fmt(f)?;
        if let Some(args) = &self.args {
            args.fmt(f)?;
        }
        Ok(())
    }
}

/// Defines the (optional) arguments-part of the constructor application.
///
/// # Generics
/// - `A`: Some [atom-like](Atomlike) object that represents an atom.
///
/// # Syntax
/// ```plain
/// (foo, bar(baz), Baz)
/// ```
pub struct FactArgs<F, S> {
    /// The parenthesis wrapping the arguments.
    pub paren_tokens: Parens<F, S>,
    /// The arguments contained within.
    pub args: Punctuated<Atom<F, S>, Comma<F, S>>,
}
// NOTE: We implement `Clone`, `Debug`, `Eq`, `Hash` and `PartialEq` manually to prevent an endless
// cycle in deriving that `Punctuated<Atom, Comma>` implements one of those traits (since the
// question of whether it does depends on `Atom`, which transitively depends on `FactArgs`).
impl<F, S> Clone for FactArgs<F, S>
where
    Span<F, S>: Clone,
{
    #[inline]
    fn clone(&self) -> Self { Self { paren_tokens: self.paren_tokens.clone(), args: self.args.clone() } }
}
impl<F, S> std::fmt::Debug for FactArgs<F, S>
where
    Span<F, S>: std::fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let Self { paren_tokens, args } = self;
        let mut fmt = f.debug_struct("FactArgs");
        fmt.field("paren_tokens", paren_tokens);
        fmt.field("args", args);
        fmt.finish()
    }
}
impl<F, S> std::cmp::Eq for FactArgs<F, S> where Span<F, S>: std::cmp::Eq {}
impl<F, S> std::hash::Hash for FactArgs<F, S>
where
    Span<F, S>: std::hash::Hash,
{
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.args.hash(state); }
}
impl<F, S> std::cmp::PartialEq for FactArgs<F, S>
where
    Span<F, S>: std::cmp::PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.args.values().zip(other.args.values()).all(|(lhs, rhs)| lhs == rhs) }

    #[inline]
    fn ne(&self, other: &Self) -> bool { self.args.values().zip(other.args.values()).any(|(lhs, rhs)| lhs != rhs) }
}
impl<F, S: SpannableDisplay> Display for FactArgs<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "(")?;
        for (i, arg) in self.args.values().enumerate() {
            if i > 0 {
                write!(f, ",")?;
                if f.alternate() {
                    write!(f, " ")?;
                }
            }
            arg.fmt(f)?;
        }
        write!(f, ")")
    }
}
#[cfg(feature = "railroad")]
impl<F, S> ToNode for FactArgs<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Parens::<F, S>::railroad_open()),
            Box::new(rr::Repeat::new(Fact::<F, S>::railroad(), Comma::<F, S>::railroad())),
            Box::new(Parens::<F, S>::railroad_close()),
        ])
    }
}



/// Represents identifiers.
///
/// # Syntax
/// ```plain
/// foo
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad), regex = "^[a-z_][a-z_-]*$"))]
pub struct Ident<F, S> {
    /// The value of the identifier itself.
    pub value: Span<F, S>,
}
impl<F, S: SpannableDisplay> Display for Ident<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { write!(f, "{}", self.value) }
}



// Implement all tokens
utf8_token!(Arrow, ":-");
utf8_token!(Comma, ",");
utf8_token!(Dot, ".");
utf8_token!(Not, "not");
utf8_delimiter!(Parens, "(", ")");

// Implement their railroads
#[doc(hidden)]
#[cfg(feature = "railroad")]
mod railroad_impl {
    use ast_toolkit::tokens::{utf8_delimiter_railroad, utf8_token_railroad};

    use super::*;

    utf8_token_railroad!(Arrow, ":-");
    utf8_token_railroad!(Comma, ",");
    utf8_token_railroad!(Dot, ".");
    utf8_token_railroad!(Not, "not");
    utf8_delimiter_railroad!(Parens, "(", ")");
}
