//  MOD.rs
//    by Lut99
//
//  Created:
//    13 Mar 2024, 16:43:37
//  Last edited:
//    13 Feb 2025, 16:54:35
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines the datalog-with-negation AST.
//

// Define the visiting modules
#[cfg(feature = "visit")]
pub mod visit;
#[cfg(feature = "visit-mut")]
pub mod visit_mut;

// Imports
use std::fmt::{Display, Formatter, Result as FResult};

pub use ast_toolkit::punctuated::Punctuated;
#[cfg(feature = "macros")]
pub use ast_toolkit::punctuated::punct;
#[cfg(feature = "railroad")]
use ast_toolkit::railroad::{ToDelimNode, ToNode, ToNonTerm, railroad as rr};
use ast_toolkit::span::SpannableBytes;
pub use ast_toolkit::span::{Span, Spanning as _};
use ast_toolkit::tokens::{utf8_delim, utf8_token};
use better_derive::{Debug, Eq, Hash, Ord, PartialEq, PartialOrd};
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
        Spec::<()> as "Spec",
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
pub struct Spec<S> {
    /// The list of rules in this program.
    pub rules: Vec<Rule<S>>,
}
impl<'s, S: SpannableBytes<'s>> Display for Spec<S> {
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
pub struct Rule<S> {
    /// A list of consequents (i.e., instances produced by this rule).
    pub consequents: Punctuated<Atom<S>, Comma<S>>,
    /// An optional second part that describes the antecedents.
    pub tail: Option<RuleBody<S>>,
    /// The closing dot after each rule.
    pub dot: Dot<S>,
}
impl<S> Rule<S> {
    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more atoms.
    #[inline]
    pub fn atoms<'s>(&'s self) -> impl 's + Iterator<Item = &'s Atom<S>> {
        self.consequents.values().chain(self.tail.iter().flat_map(RuleBody::atoms))
    }

    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to atoms.
    #[inline]
    pub fn atoms_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Atom<S>> {
        self.consequents.values_mut().chain(self.tail.iter_mut().flat_map(RuleBody::atoms_mut))
    }

    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more antecedents.
    #[inline]
    pub fn antecedents<'s>(&'s self) -> impl 's + Iterator<Item = &'s Literal<S>> { self.tail.iter().flat_map(|t| t.antecedents.values()) }

    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to antecedents.
    #[inline]
    pub fn antecedents_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Literal<S>> {
        self.tail.iter_mut().flat_map(|t| t.antecedents.values_mut())
    }
}
impl<'s, S: SpannableBytes<'s>> Display for Rule<S> {
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
impl<S> ToNode for Rule<S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(rr::Repeat::new(Atom::<S>::railroad(), Comma::<S>::railroad())),
            Box::new(rr::Optional::new(RuleBody::<S>::railroad())),
            Box::new(Dot::<S>::railroad()),
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
pub struct RuleBody<S> {
    /// The arrow token.
    pub arrow_token: Arrow<S>,
    /// The list of antecedents.
    pub antecedents: Punctuated<Literal<S>, Comma<S>>,
}
impl<S> RuleBody<S> {
    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more antecedents.
    #[inline]
    pub fn atoms<'s>(&'s self) -> impl 's + Iterator<Item = &'s Atom<S>> { self.antecedents.values().map(Literal::atom) }

    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to antecedents.
    #[inline]
    pub fn atoms_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Atom<S>> { self.antecedents.values_mut().map(Literal::atom_mut) }
}
impl<'s, S: SpannableBytes<'s>> Display for RuleBody<S> {
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
impl<S> ToNode for RuleBody<S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![Box::new(Arrow::<S>::railroad()), Box::new(rr::Repeat::new(Literal::<S>::railroad(), Comma::<S>::railroad()))])
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
pub enum Literal<S> {
    /// Non-negated atom.
    ///
    /// # Syntax
    /// ```plain
    /// foo
    /// foo(bar)
    /// ```
    Atom(Atom<S>),
    /// Negated atom.
    ///
    /// # Syntax
    /// ```plain
    /// not foo
    /// ```
    NegAtom(NegAtom<S>),
}
impl<S> Literal<S> {
    /// Returns the polarity of the literal.
    ///
    /// # Returns
    /// True if this is a positive literal ([`Literal::Atom`]), or false if it's a negative literal ([`Literal::NegAtom`]).
    pub fn is_positive(&self) -> bool { matches!(self, Self::Atom(_)) }

    /// Returns the atom that appears in all variants of the literal.
    ///
    /// # Returns
    /// A reference to the [`Atom`] contained within.
    pub fn atom(&self) -> &Atom<S> {
        match self {
            Self::Atom(a) => a,
            Self::NegAtom(na) => &na.atom,
        }
    }

    /// Returns the atom that appears in all variants of the literal.
    ///
    /// # Returns
    /// A mutable reference to the [`Atom`] contained within.
    pub fn atom_mut(&mut self) -> &mut Atom<S> {
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
impl<'s, S: SpannableBytes<'s>> Display for Literal<S> {
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
pub struct NegAtom<S> {
    /// The not-token.
    pub not_token: Not<S>,
    /// The atom that was negated.
    pub atom:      Atom<S>,
}
impl<'s, S: SpannableBytes<'s>> Display for NegAtom<S> {
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
pub enum Atom<S> {
    /// It's a Fact.
    ///
    /// # Syntax
    /// ```plain
    /// foo
    /// foo(bar, Baz)
    /// ```
    Fact(Fact<S>),
    /// It's a variable.
    ///
    /// # Syntax
    /// ```plain
    /// Bar
    /// ```
    Var(Ident<S>),
}
impl<S> Atom<S> {
    /// Returns whether this atom has any arguments.
    ///
    /// If true, implies [`Atom::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_constant(&self) -> bool {
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
    pub fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Self> {
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
    pub fn args_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Self> {
        match self {
            Self::Fact(f) => Some(f.args.iter_mut().flat_map(|t| t.args.values_mut())).into_iter().flatten(),
            Self::Var(_) => None.into_iter().flatten(),
        }
    }

    /// Returns whether this atom is a variable
    ///
    /// Note that this is different from [`Atom::is_grounded()`]. That one checks if THIS atom
    /// _or_, if not_ any ARGUMENTS are variables recursively; this function checks only if THIS
    /// atom is a variable.
    ///
    /// # Returns
    /// True if this is an [`Atom::Var`], or else false.
    #[inline]
    pub const fn is_var(&self) -> bool { matches!(self, Self::Var(_)) }

    /// Returns whether this atom has any variables.
    ///
    /// Note that this is different from [`Atom::is_var()`]. That one checks if THIS atom is a
    /// variable; this function checks if THIS atom _or_, if not, any ARGUMENTS are variables
    /// recursively.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_grounded(&self) -> bool {
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
    pub fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<S>>
    where
        'i: 's,
        Ident<S>: 'i,
    {
        match self {
            Self::Fact(f) => Box::new(f.vars()) as Box<dyn 's + Iterator<Item = &'s Ident<S>>>,
            Self::Var(v) => Box::new(Some(v).into_iter()),
        }
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    pub fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<S>>
    where
        'i: 's,
        Ident<S>: 'i,
    {
        match self {
            Self::Fact(f) => Box::new(f.vars_mut()) as Box<dyn 's + Iterator<Item = &'s mut Ident<S>>>,
            Self::Var(v) => Box::new(Some(v).into_iter()),
        }
    }
}
impl<'s, S: SpannableBytes<'s>> Display for Atom<S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Fact(fa) => fa.fmt(f),
            Self::Var(v) => v.fmt(f),
        }
    }
}
#[cfg(feature = "railroad")]
impl<S> ToNode for Atom<S> {
    type Node = rr::Choice<rr::LabeledBox<Box<dyn rr::Node>, rr::Comment>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Choice::new(vec![
            rr::LabeledBox::new(Box::new(Fact::<S>::railroad()) as Box<dyn rr::Node>, rr::Comment::new("Atom::Fact".into())),
            rr::LabeledBox::new(
                Box::new(rr::Sequence::new(vec![
                    Box::new(rr::Comment::new("regex".into())) as Box<dyn rr::Node>,
                    Box::new(rr::Terminal::new("^[A-Z][a-zA-Z_-]*$".into())),
                ])) as Box<dyn rr::Node>,
                rr::Comment::new("Atom::Var".into()),
            ),
        ])
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
pub struct Fact<S> {
    /// The identifier itself.
    pub ident: Ident<S>,
    /// Any arguments.
    pub args:  Option<FactArgs<S>>,
}
impl<S> Fact<S> {
    /// Returns whether this atom has any arguments.
    ///
    /// If true, implies [`Fact::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_constant(&self) -> bool { self.args.as_ref().map(|a| a.args.is_empty()).unwrap_or(true) }

    /// Returns an iterator over the arguments in this fact, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more [`Atom`]s representing each argument.
    #[inline]
    pub fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Atom<S>> { self.args.iter().flat_map(|t| t.args.values()).into_iter() }

    /// Returns an iterator over the arguments in this fact, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to [`Atom`]s representing each
    /// argument.
    #[inline]
    pub fn args_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Atom<S>> {
        self.args.iter_mut().flat_map(|t| t.args.values_mut()).into_iter()
    }

    /// Returns whether this atom has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_grounded(&self) -> bool {
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
    pub fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<S>>
    where
        'i: 's,
        Ident<S>: 'i,
    {
        self.args.iter().flat_map(|args| args.args.values().flat_map(Atom::vars))
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    pub fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<S>>
    where
        'i: 's,
        Ident<S>: 'i,
    {
        self.args.iter_mut().flat_map(|args| args.args.values_mut().flat_map(Atom::vars_mut))
    }
}
impl<'s, S: SpannableBytes<'s>> Display for Fact<S> {
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
#[better_derive(impl_gen = <'s, S>, bound = (S: SpannableBytes<'s>))]
pub struct FactArgs<S> {
    /// The parenthesis wrapping the arguments.
    pub paren_tokens: Parens<S>,
    /// The arguments contained within.
    pub args: Punctuated<Atom<S>, Comma<S>>,
}
impl<'s, S: SpannableBytes<'s>> Display for FactArgs<S> {
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
impl<S> ToNode for FactArgs<S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Parens::<S>::railroad_open()),
            Box::new(rr::Repeat::new(rr::NonTerminal::new("Fact".into()), Comma::<S>::railroad())),
            Box::new(Parens::<S>::railroad_close()),
        ])
    }
}



/// Represents identifiers.
///
/// # Syntax
/// ```plain
/// foo
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad), regex = "^[a-z_][a-z_-]*$"))]
pub struct Ident<S> {
    /// The value of the identifier itself.
    pub value: String,
    /// Where we found it.
    pub span:  Option<Span<S>>,
}
impl<S> Ident<S> {
    /// Creates a new identifier that's not attached to any source.
    ///
    /// # Arguments
    /// - `value`: The value of the identifier.
    ///
    /// # Returns
    /// A new Ident with  [`Ident::span`] set to [`None`].
    #[inline]
    pub const fn new(value: String) -> Self { Self { value, span: None } }
}
impl<'s, S: SpannableBytes<'s>> Display for Ident<S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { write!(f, "{}", self.value) }
}



// Implement all tokens
utf8_token!(Arrow, ":-");
utf8_token!(Comma, ",");
utf8_token!(Dot, ".");
utf8_token!(Not, "not");
utf8_delim!(Parens, "(", ")");

// Implement their railroads
#[doc(hidden)]
#[cfg(feature = "railroad")]
mod railroad_impl {
    use ast_toolkit::tokens::{utf8_delim_railroad, utf8_token_railroad};

    use super::*;

    utf8_token_railroad!(Arrow, ":-");
    utf8_token_railroad!(Comma, ",");
    utf8_token_railroad!(Dot, ".");
    utf8_token_railroad!(Not, "not");
    utf8_delim_railroad!(Parens, "(", ")");
}
