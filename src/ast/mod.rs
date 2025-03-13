//  MOD.rs
//    by Lut99
//
//  Created:
//    13 Mar 2024, 16:43:37
//  Last edited:
//    13 Mar 2025, 22:10:54
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
use ast_toolkit::span::SpannableDisplay;
pub use ast_toolkit::span::{Span, Spanning as _};
use ast_toolkit::tokens::{utf8_delim, utf8_token};
use better_derive::{Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd};
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
    pub tail: Option<RuleBody<F, S>>,
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
        self.consequents.values().chain(self.tail.iter().flat_map(RuleBody::atoms))
    }

    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to atoms.
    #[inline]
    pub fn atoms_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Atom<F, S>> {
        self.consequents.values_mut().chain(self.tail.iter_mut().flat_map(RuleBody::atoms_mut))
    }

    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more antecedents.
    #[inline]
    pub fn antecedents<'s>(&'s self) -> impl 's + Iterator<Item = &'s Literal<F, S>> { self.tail.iter().flat_map(|t| t.antecedents.values()) }

    /// Returns an iterator over the atoms in the rule's antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to antecedents.
    #[inline]
    pub fn antecedents_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Literal<F, S>> {
        self.tail.iter_mut().flat_map(|t| t.antecedents.values_mut())
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
            Box::new(rr::Optional::new(RuleBody::<F, S>::railroad())),
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
pub struct RuleBody<F, S> {
    /// The arrow token.
    pub arrow_token: Arrow<F, S>,
    /// The list of antecedents.
    pub antecedents: Punctuated<Literal<F, S>, Comma<F, S>>,
}
impl<F, S> RuleBody<F, S> {
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
impl<F, S: SpannableDisplay> Display for RuleBody<F, S> {
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
impl<F, S> ToNode for RuleBody<F, S> {
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
/// 42
/// 21 + 21
/// Bar
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Atom<F, S> {
    /// It's a Fact.
    ///
    /// # Syntax
    /// ```plain
    /// foo
    /// foo(bar, Baz)
    /// ```
    Fact(Fact<F, S>),
    /// It's an expression.
    ///
    /// # Syntax
    /// ```plain
    /// 42
    /// 21 + 21
    /// ```
    Expr(Expr<F, S>),
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
    /// For expressions, returns true if it's a direct integer literal.
    ///
    /// If true, implies [`Atom::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_constant(&self) -> bool {
        match self {
            Self::Fact(f) => f.is_constant(),
            Self::Expr(e) => e.is_literal(),
            Self::Var(_) => false,
        }
    }

    /// Returns an iterator over the internal arguments.
    ///
    /// Note that expressions have no arguments.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Atom`] (references).
    #[inline]
    pub fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Self> {
        match self {
            Self::Fact(f) => Some(f.args()).into_iter().flatten(),
            Self::Expr(_) => None.into_iter().flatten(),
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
            Self::Fact(f) => Some(f.args_mut()).into_iter().flatten(),
            Self::Expr(_) => None.into_iter().flatten(),
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
            Self::Expr(e) => e.is_grounded(),
            Self::Var(_) => false,
        }
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    #[inline]
    pub fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        match self {
            Self::Fact(f) => Box::new(f.vars()) as Box<dyn 's + Iterator<Item = &'s Ident<F, S>>>,
            Self::Expr(e) => Box::new(e.vars()),
            Self::Var(v) => Box::new(Some(v).into_iter()),
        }
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    pub fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        match self {
            Self::Fact(f) => Box::new(f.vars_mut()) as Box<dyn 's + Iterator<Item = &'s mut Ident<F, S>>>,
            Self::Expr(e) => Box::new(e.vars_mut()),
            Self::Var(v) => Box::new(Some(v).into_iter()),
        }
    }
}
impl<F, S: SpannableDisplay> Display for Atom<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Fact(fa) => fa.fmt(f),
            Self::Expr(e) => e.fmt(f),
            Self::Var(v) => v.fmt(f),
        }
    }
}
#[cfg(feature = "railroad")]
impl<F, S> ToNode for Atom<F, S> {
    type Node = rr::Choice<rr::LabeledBox<Box<dyn rr::Node>, rr::Comment>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Choice::new(vec![
            rr::LabeledBox::new(Box::new(Fact::<F, S>::railroad()) as Box<dyn rr::Node>, rr::Comment::new("Atom::Fact".into())),
            rr::LabeledBox::new(Box::new(Expr::<F, S>::railroad()), rr::Comment::new("Atom::Expr".into())),
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
    pub fn is_constant(&self) -> bool { self.args.as_ref().map(|a| a.args.is_empty()).unwrap_or(true) }

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
    pub fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
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
    pub fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
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
            Box::new(rr::Repeat::new(rr::NonTerminal::new("Fact".into()), Comma::<F, S>::railroad())),
            Box::new(Parens::<F, S>::railroad_close()),
        ])
    }
}



/// Defines an expression over integers.
///
/// # Syntax
/// ```plain
/// 42
/// 21 + 21
/// X + Y
/// 33 + (88 / 3 + 2) - 6
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum Expr<F, S> {
    /// A literal integer.
    ///
    /// # Syntax
    /// ```plain
    /// 42
    /// ```
    LitInt(ExprLitInt<F, S>),
    /// A variable which evaluates to "every" integer in existance.
    ///
    /// This is more all integers in the knowledge base.
    ///
    /// # Syntax
    /// ```plain
    /// A
    /// ```
    Var(Ident<F, S>),
    /// A unary operator.
    ///
    /// # Syntax
    /// ```plain
    /// -5
    /// ```
    UnOp(ExprUnOp<F, S>),
    /// A binary operator.
    ///
    /// # Syntax
    /// ```plain
    /// 21 + 21
    /// 77 * (33 + 5)
    /// 1 + (2 - (((3 * 4) / 5) % 6))
    /// ```
    BinOp(ExprBinOp<F, S>),
    /// Parenthesis.
    Parens(ExprParens<F, S>),
}
impl<F, S> Expr<F, S> {
    /// Returns whether this expression is a literal.
    ///
    /// If true, implies [`Expr::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub const fn is_literal(&self) -> bool {
        match self {
            Self::LitInt(_) => true,
            Self::Var(_) | Self::UnOp(_) | Self::BinOp(_) | Self::Parens(_) => false,
        }
    }

    /// Returns whether this expression is a variable
    ///
    /// Note that this is different from [`Expr::is_grounded()`]. That one checks if THIS atom
    /// _or_, if not_ any ARGUMENTS are variables recursively; this function checks only if THIS
    /// expression is a variable.
    ///
    /// # Returns
    /// True if this is an [`Atom::Var`], or else false.
    #[inline]
    pub const fn is_var(&self) -> bool { matches!(self, Self::Var(_)) }

    /// Returns whether this expression has any variables.
    ///
    /// Note that this is different from [`Expr::is_var()`]. That one checks if THIS expression is
    /// a variable; this function checks if THIS expression _or_, if not, any ARGUMENTS are
    /// variables recursively.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_grounded(&self) -> bool {
        match self {
            // Base cases
            Self::LitInt(_) => true,
            Self::Var(_) => false,
            // Recursive cases
            Self::UnOp(uo) => uo.is_grounded(),
            Self::BinOp(bo) => bo.is_grounded(),
            Self::Parens(p) => p.is_grounded(),
        }
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    #[inline]
    pub fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        match self {
            // Base cases
            Self::LitInt(_) => Box::new(None.into_iter()) as Box<dyn 's + Iterator<Item = &'s Ident<F, S>>>,
            Self::Var(v) => Box::new(Some(v).into_iter()),
            // Recursive cases
            Self::UnOp(uo) => Box::new(uo.vars()),
            Self::BinOp(bo) => Box::new(bo.vars()),
            Self::Parens(p) => Box::new(p.vars()),
        }
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    pub fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        match self {
            // Base cases
            Self::LitInt(_) => Box::new(None.into_iter()) as Box<dyn 's + Iterator<Item = &'s mut Ident<F, S>>>,
            Self::Var(v) => Box::new(Some(v).into_iter()),
            // Recursive cases
            Self::UnOp(uo) => Box::new(uo.vars_mut()),
            Self::BinOp(bo) => Box::new(bo.vars_mut()),
            Self::Parens(p) => Box::new(p.vars_mut()),
        }
    }
}
impl<F, S: SpannableDisplay> Display for Expr<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::LitInt(li) => {
                write!(f, "(")?;
                li.fmt(f)?;
                write!(f, ")")
            },
            Self::Var(v) => v.fmt(f),
            Self::UnOp(uo) => {
                write!(f, "(")?;
                uo.fmt(f)?;
                write!(f, ")")
            },
            Self::BinOp(bo) => {
                write!(f, "(")?;
                bo.fmt(f)?;
                write!(f, ")")
            },
            Self::Parens(p) => p.fmt(f),
        }
    }
}

/// Defines a literal integer in an expression.
///
/// # Syntax
/// ```plain
/// 42
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad), regex = "^[0-9]*$"))]
pub struct ExprLitInt<F, S> {
    /// The value that we parsed.
    pub value: i64,
    /// The span linking this literal to the source text.
    pub span:  Span<F, S>,
}
impl<F, S: SpannableDisplay> Display for ExprLitInt<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { self.value.fmt(f) }
}

/// Defines a unary operator.
///
/// # Syntax
/// ```plain
/// -5
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[better_derive(bound = (Span<F, S>))]
pub struct ExprUnOp<F, S> {
    /// The operator in question.
    pub op:   UnOp<F, S>,
    /// The expression that contains the affected value.
    pub expr: Box<Expr<F, S>>,
}
impl<F, S> ExprUnOp<F, S> {
    /// Returns whether this unary expression has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_grounded(&self) -> bool { self.expr.is_grounded() }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    #[inline]
    pub fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.expr.vars()
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    pub fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.expr.vars_mut()
    }
}
impl<F, S: SpannableDisplay> Display for ExprUnOp<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        self.op.fmt(f)?;
        self.expr.fmt(f)
    }
}
#[cfg(feature = "railroad")]
impl<F, S> ToNode for ExprUnOp<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![Box::new(UnOp::<F, S>::railroad()) as Box<dyn rr::Node>, Box::new(Expr::<F, S>::railroad())])
    }
}

/// Defines a binary operator.
///
/// # Syntax
/// ```plain
/// 21 + 21
/// 77 * (33 + 5)
/// 1 + (2 - (((3 * 4) / 5) % 6))
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[better_derive(bound = (Span<F, S>))]
pub struct ExprBinOp<F, S> {
    /// The operator in question.
    pub op:  BinOp<F, S>,
    /// The lefthand-side expression of the operation.
    pub lhs: Box<Expr<F, S>>,
    /// The righthand-side expression of the operation.
    pub rhs: Box<Expr<F, S>>,
}
impl<F, S> ExprBinOp<F, S> {
    /// Returns whether this binary expression has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_grounded(&self) -> bool { self.lhs.is_grounded() && self.rhs.is_grounded() }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    #[inline]
    pub fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.lhs.vars().chain(self.rhs.vars())
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    pub fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.lhs.vars_mut().chain(self.rhs.vars_mut())
    }
}
impl<F, S: SpannableDisplay> Display for ExprBinOp<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        self.lhs.fmt(f)?;
        if f.alternate() {
            write!(f, " ")?;
        }
        self.op.fmt(f)?;
        if f.alternate() {
            write!(f, " ")?;
        }
        self.rhs.fmt(f)
    }
}
#[cfg(feature = "railroad")]
impl<F, S> ToNode for ExprBinOp<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Expr::<F, S>::railroad()) as Box<dyn rr::Node>,
            Box::new(BinOp::<F, S>::railroad()),
            Box::new(Expr::<F, S>::railroad()),
        ])
    }
}

/// Defines an expression wrapped in parenthesis.
///
/// # Syntax
/// ```plain
/// (42)
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[better_derive(bound = (Span<F, S>))]
pub struct ExprParens<F, S> {
    /// The parenthesis.
    pub paren_tokens: Parens<F, S>,
    /// The wrapped expression.
    pub expr: Box<Expr<F, S>>,
}
impl<F, S> ExprParens<F, S> {
    /// Returns whether the wrapped expression has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    pub fn is_grounded(&self) -> bool { self.expr.is_grounded() }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    #[inline]
    pub fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.expr.vars()
    }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    pub fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.expr.vars_mut()
    }
}
impl<F, S: SpannableDisplay> Display for ExprParens<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "(")?;
        self.expr.fmt(f)?;
        write!(f, ")")
    }
}
#[cfg(feature = "railroad")]
impl<F, S> ToNode for ExprParens<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Parens::<F, S>::railroad_open()) as Box<dyn rr::Node>,
            Box::new(Expr::<F, S>::railroad()),
            Box::new(Parens::<F, S>::railroad_close()),
        ])
    }
}

/// Lists all unary operators.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum UnOp<F, S> {
    /// Arithmetic negation.
    ///
    /// # Syntax
    /// ```plain
    /// -
    /// ```
    Neg(Minus<F, S>),
}
impl<F, S> UnOp<F, S> {
    /// Returns the binding power of this operator.
    ///
    /// The binding power is used by a [pratt parser](crate::parser::exprs::expr()) to decide
    /// operator precedence- and associativity. Therefore, unary operators have one power
    /// associated with the direction they work in (for us, always to the **right**).
    ///
    /// The rule is:
    /// - The operator with the higher power on the side facing the other operator, has higher
    ///   precedence (i.e., we parse until we find a weaker operator).
    ///
    /// Arithmetic negation (the only unary operator) binds stronger than any other.
    ///
    /// # Returns
    /// The _right_ binding power of the operator.
    #[inline]
    pub fn binding_power(&self) -> u32 {
        match self {
            Self::Neg(_) => 5,
        }
    }
}
impl<F, S: SpannableDisplay> Display for UnOp<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Neg(_) => write!(f, "-"),
        }
    }
}

/// Lists all binary operators.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum BinOp<F, S> {
    /// Addition.
    ///
    /// # Syntax
    /// ```plain
    /// +
    /// ```
    Add(Add<F, S>),
    /// Subtraction.
    ///
    /// # Syntax
    /// ```plain
    /// -
    /// ```
    Sub(Minus<F, S>),
    /// Multiplication.
    ///
    /// # Syntax
    /// ```plain
    /// *
    /// ```
    Mul(Star<F, S>),
    /// (Floating-point) Division.
    ///
    /// # Syntax
    /// ```plain
    /// /
    /// ```
    Div(Slash<F, S>),
    /// (Integer) Division (i.e., remainder).
    ///
    /// # Syntax
    /// ```plain
    /// %
    /// ```
    Rem(Percent<F, S>),
}
impl<F, S> BinOp<F, S> {
    /// Returns the binding power of this operator.
    ///
    /// The binding power is used by a [pratt parser](crate::parser::exprs::expr()) to decide
    /// operator precedence- and associativity. Therefore, binary operators have two powers
    /// associated with them: a left and a right.
    ///
    /// The rule is:
    /// - Operators are _left_ associative if their left binding is lower (i.e., they yield to an
    ///   identical operator that binds higher to the right);
    /// - Operators are _right_ associative if their right binding is lower; and
    /// - The operator with the higher power on the side facing the other operator, has higher
    ///   precedence (i.e., we parse until we find a weaker operator).
    ///
    /// Furthermore, associativity and precedence works as you'd expect (multiplication, dividsion
    /// and remainder have higher precedence than addition and subtraction; all are left-
    /// associative).
    ///
    /// # Returns
    /// A tuple with the _left_ binding power and the _right_ binding power, respectively.
    #[inline]
    pub fn binding_power(&self) -> (u32, u32) {
        match self {
            Self::Add(_) => (1, 2),
            Self::Sub(_) => (1, 2),
            Self::Mul(_) => (3, 4),
            Self::Div(_) => (3, 4),
            Self::Rem(_) => (3, 4),
        }
    }
}
impl<F, S: SpannableDisplay> Display for BinOp<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Add(_) => write!(f, "+"),
            Self::Sub(_) => write!(f, "-"),
            Self::Mul(_) => write!(f, "*"),
            Self::Div(_) => write!(f, "/"),
            Self::Rem(_) => write!(f, "%"),
        }
    }
}



/// Represents identifiers.
///
/// # Syntax
/// ```plain
/// foo
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
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
utf8_token!(Add, "+");
utf8_token!(Arrow, ":-");
utf8_token!(Comma, ",");
utf8_token!(Dot, ".");
utf8_token!(Minus, "-");
utf8_token!(Not, "not");
utf8_token!(Percent, "%");
utf8_token!(Slash, "/");
utf8_token!(Star, "*");
utf8_delim!(Parens, "(", ")");

// Implement their parsers
#[doc(hidden)]
mod parser_impl {
    use ast_toolkit::tokens::{utf8_delim_snack, utf8_token_snack};

    use super::*;

    utf8_token_snack!(Add);
    utf8_token_snack!(Arrow);
    utf8_token_snack!(Comma);
    utf8_token_snack!(Dot);
    utf8_token_snack!(Minus);
    utf8_token_snack!(Not);
    utf8_token_snack!(Percent);
    utf8_token_snack!(Slash);
    utf8_token_snack!(Star);
    utf8_delim_snack!(Parens);
}

// Implement their railroads
#[doc(hidden)]
#[cfg(feature = "railroad")]
mod railroad_impl {
    use ast_toolkit::tokens::{utf8_delim_railroad, utf8_token_railroad};

    use super::*;

    utf8_token_railroad!(Add, "+");
    utf8_token_railroad!(Arrow, ":-");
    utf8_token_railroad!(Comma, ",");
    utf8_token_railroad!(Dot, ".");
    utf8_token_railroad!(Minus, "-");
    utf8_token_railroad!(Not, "not");
    utf8_token_railroad!(Percent, "%");
    utf8_token_railroad!(Slash, "/");
    utf8_token_railroad!(Star, "*");
    utf8_delim_railroad!(Parens, "(", ")");
}
