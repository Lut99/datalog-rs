//  AST.rs
//    by Lut99
//
//  Created:
//    13 Mar 2024, 16:43:37
//  Last edited:
//    06 Feb 2025, 15:51:31
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
        Spec::<(), ()> as "Spec",
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
pub struct Spec<F, S> {
    /// The list of rules in this program.
    pub rules: Vec<Rule<F, S>>,
}
impl<F, S: SpannableDisplay> Display for Spec<F, S> {
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
pub struct Rule<F, S> {
    /// A list of consequents (i.e., instances produced by this rule).
    pub consequents: Punctuated<Atom<F, S>, Comma<F, S>>,
    /// An optional second part that describes the antecedents.
    pub tail: Option<RuleAntecedents<F, S>>,
    /// The closing dot after each rule.
    pub dot: Dot<F, S>,
}
impl<F, S> Rule<F, S> {
    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more atoms.
    #[inline]
    pub fn atoms<'s>(&'s self) -> impl 's + Iterator<Item = &'s Atom<F, S>> {
        self.consequents.values().chain(self.tail.iter().flat_map(RuleAntecedents::atoms))
    }

    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to atoms.
    #[inline]
    pub fn atoms_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Atom<F, S>> {
        self.consequents.values_mut().chain(self.tail.iter_mut().flat_map(RuleAntecedents::atoms_mut))
    }
}
impl<F, S: SpannableDisplay> Display for Rule<F, S> {
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
impl<F, S> ToNode for Rule<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(rr::Repeat::new(Atom::<F, S>::railroad(), Comma::<F, S>::railroad())),
            Box::new(rr::Optional::new(RuleAntecedents::<F, S>::railroad())),
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
pub struct RuleAntecedents<F, S> {
    /// The arrow token.
    pub arrow_token: Arrow<F, S>,
    /// The list of antecedents.
    pub antecedents: Punctuated<Literal<F, S>, Comma<F, S>>,
}
impl<F, S> RuleAntecedents<F, S> {
    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more antecedents.
    #[inline]
    pub fn atoms<'s>(&'s self) -> impl 's + Iterator<Item = &'s Atom<F, S>> { self.antecedents.values().map(Literal::atom) }

    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to antecedents.
    #[inline]
    pub fn atoms_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Atom<F, S>> { self.antecedents.values_mut().map(Literal::atom_mut) }
}
impl<F, S: SpannableDisplay> Display for RuleAntecedents<F, S> {
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
impl<F, S> ToNode for RuleAntecedents<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Arrow::<F, S>::railroad()),
            Box::new(rr::Repeat::new(Literal::<F, S>::railroad(), Comma::<F, S>::railroad())),
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
pub enum Literal<F, S> {
    /// Non-negated atom.
    ///
    /// # Syntax
    /// ```plain
    /// foo
    /// foo(bar)
    /// ```
    Atom(Atom<F, S>),
    /// Negated atom.
    ///
    /// # Syntax
    /// ```plain
    /// not foo
    /// ```
    NegAtom(NegAtom<F, S>),
}
impl<F, S> Literal<F, S> {
    /// Returns the polarity of the literal.
    ///
    /// # Returns
    /// True if this is a positive literal ([`Literal::Atom`]), or false if it's a negative literal ([`Literal::NegAtom`]).
    pub fn is_positive(&self) -> bool { matches!(self, Self::Atom(_)) }

    /// Returns the atom that appears in all variants of the literal.
    ///
    /// # Returns
    /// A reference to the [`Atom`] contained within.
    pub fn atom(&self) -> &Atom<F, S> {
        match self {
            Self::Atom(a) => a,
            Self::NegAtom(na) => &na.atom,
        }
    }

    /// Returns the atom that appears in all variants of the literal.
    ///
    /// # Returns
    /// A mutable reference to the [`Atom`] contained within.
    pub fn atom_mut(&mut self) -> &mut Atom<F, S> {
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
impl<F, S: SpannableDisplay> Display for Literal<F, S> {
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
pub struct NegAtom<F, S> {
    /// The not-token.
    pub not_token: Not<F, S>,
    /// The atom that was negated.
    pub atom:      Atom<F, S>,
}
impl<F, S: SpannableDisplay> Display for NegAtom<F, S> {
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
    /// Returns whether this atom has any arguments.
    ///
    /// If true, implies [`Atom::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    fn is_constant(&self) -> bool {
        match self {
            Self::Fact(f) => f.is_constant(),
            Self::Var(_) => false,
        }
    }

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



    /// Returns whether this atom has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    fn is_grounded(&self) -> bool {
        match self {
            Self::Fact(f) => f.is_grounded(),
            Self::Var(_) => false,
        }
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
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

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
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
    /// Returns whether this atom has any arguments.
    ///
    /// If true, implies [`Fact::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    fn is_constant(&self) -> bool { self.args.as_ref().map(|a| a.args.is_empty()).unwrap_or(true) }

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



    /// Returns whether this atom has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    fn is_grounded(&self) -> bool {
        match &self.args {
            Some(args) => args.args.values().all(Atom::is_grounded),
            None => false,
        }
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    #[inline]
    fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.args.iter().flat_map(|args| args.args.values().flat_map(Atom::vars))
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.args.iter_mut().flat_map(|args| args.args.values_mut().flat_map(Atom::vars_mut))
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
/// # Syntax
/// ```plain
/// (foo, bar(baz), Baz)
/// ```
// NOTE: We implement `Clone`, `Debug`, `Eq`, `Hash` and `PartialEq` manually to prevent an endless
// cycle in deriving that `Punctuated<Atom, Comma>` implements one of those traits (since the
// question of whether it does depends on `Atom`, which transitively depends on `FactArgs`).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[better_derive(bound = (Span<F, S>))]
pub struct FactArgs<F, S> {
    /// The parenthesis wrapping the arguments.
    pub paren_tokens: Parens<F, S>,
    /// The arguments contained within.
    pub args: Punctuated<Atom<F, S>, Comma<F, S>>,
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
