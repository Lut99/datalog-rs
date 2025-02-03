//  AST.rs
//    by Lut99
//
//  Created:
//    13 Mar 2024, 16:43:37
//  Last edited:
//    03 Feb 2025, 18:59:51
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines the datalog-with-negation AST.
//

use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{Hash, Hasher};

pub use ast_toolkit::punctuated::Punctuated;
#[cfg(feature = "macros")]
pub use ast_toolkit::punctuated::punct;
#[cfg(feature = "railroad")]
use ast_toolkit::railroad::{ToDelimNode, ToNode, ToNonTerm, railroad as rr};
use ast_toolkit::span::SpannableDisplay;
pub use ast_toolkit::span::{Span, Spanning as _};
use ast_toolkit::tokens::{utf8_delimiter, utf8_token};
// Re-export the derive macro
#[cfg(feature = "macros")]
pub use datalog_macros::datalog;
use enum_debug::EnumDebug;
use paste::paste;


/***** HELPER MACROS *****/
/// Automatically implements [`Eq`], [`Hash`] and [`PartialEq`] for the given fields in the given
/// struct.
macro_rules! impl_map {
    ($for:ident, $($fields:ident),+) => {
        impl<F, S> Eq for $for<F, S> where S: ast_toolkit::span::SpannableEq {}

        impl<F, S> Hash for $for<F, S> where S: ast_toolkit::span::SpannableHash {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                $(
                    self.$fields.hash(state);
                )+
            }
        }

        impl<F, S> PartialEq for $for<F, S> where S: ast_toolkit::span::SpannableEq {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                $(
                    self.$fields == other.$fields
                )&&+
            }
        }
    };
}
pub(crate) use impl_map;

/// Automatically implements [`Eq`], [`Hash`] and [`PartialEq`] for the given fields of the given
/// variants in the given enum.
macro_rules! impl_enum_map {
    ($for:ident, $($variants:ident($($fields:ident),+)),+) => {
        impl<F, S> Eq for $for<F, S> where S: ast_toolkit::span::SpannableEq {}

        impl<F, S> Hash for $for<F, S> where S: ast_toolkit::span::SpannableHash {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                match self {
                    $(
                        Self::$variants ( $($fields),+ ) => {
                            stringify!($variants).hash(state);
                            $($fields.hash(state);)+
                        }
                    ),+
                }
            }
        }

        paste! {
            impl<F, S> PartialEq for $for<F, S> where S: ast_toolkit::span::SpannableEq {
                #[inline]
                fn eq(&self, other: &Self) -> bool {
                    match (self, other) {
                        $(
                            (Self::$variants ( $([< $fields _lhs >]),+ ), Self::$variants ( $([< $fields _rhs >]),+ )) => {
                                $([< $fields _lhs >] == [< $fields _rhs >])&&+
                            }
                        ),+

                        // Any other variant is inequal by default
                        (_, _) => false,
                    }
                }
            }
        }
    };
}
pub(crate) use impl_enum_map;





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
#[derive(Clone, Debug)]
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
impl_map!(Spec, rules);



/// Specifies a single rule.
///
/// # Syntax
/// ```plain
/// foo :- bar, baz(quz).
/// foo.
/// ```
#[derive(Clone, Debug)]
pub struct Rule<F, S> {
    /// A list of consequents (i.e., instances produced by this rule).
    pub consequents: Punctuated<Atom<F, S>, Comma<F, S>>,
    /// An optional second part that describes the antecedents.
    pub tail: Option<RuleAntecedents<F, S>>,
    /// The closing dot after each rule.
    pub dot: Dot<F, S>,
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
impl_map!(Rule, consequents, tail);

/// Defines the second half of the rule, if any.
///
/// # Syntax
/// ```plain
/// :- foo, bar(baz)
/// ```
#[derive(Clone, Debug)]
pub struct RuleAntecedents<F, S> {
    /// The arrow token.
    pub arrow_token: Arrow<F, S>,
    /// The list of antecedents.
    pub antecedents: Punctuated<Literal<F, S>, Comma<F, S>>,
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
impl_map!(RuleAntecedents, antecedents);



/// Represents a single antecedent, as it were.
///
/// # Syntax
/// ```plain
/// foo
/// foo(bar)
/// not foo
/// ```
#[derive(Clone, Debug, EnumDebug)]
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
    /// True if there is at least one [`Atom::Var`] recursively, or false otherwise.
    #[inline]
    pub fn has_vars(&self) -> bool { self.atom().has_vars() }
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
impl_enum_map!(Literal, Atom(atom), NegAtom(atom));

/// Wraps around an [`Atom`] to express its non-existance.
///
/// # Syntax
/// ```plain
/// not foo
/// not foo(bar)
/// ```
#[derive(Clone, Debug)]
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
impl_map!(NegAtom, atom);



/// Defines a constructor application of facts _or_ a variable.
///
/// # Syntax
/// ```plain
/// foo
/// foo(bar, Baz)
/// Bar
/// ```
#[derive(Clone, Debug)]
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
    /// Returns if there are any variables in this atom.
    ///
    /// # Returns
    /// True if there is at least one [`Atom::Var`] recursively, or false otherwise.
    #[inline]
    pub fn has_vars(&self) -> bool {
        match self {
            Self::Fact(f) => f.has_vars(),
            Self::Var(_) => true,
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
impl_enum_map!(Atom, Fact(fact), Var(ident));

/// Defines a fact, which is an identifier followed by zero or more arguments.
///
/// Kinda like a function application. Can be recursive.
///
/// # Syntax
/// ```plain
/// foo
/// foo(bar, Baz)
/// ```
#[derive(Clone, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub struct Fact<F, S> {
    /// The identifier itself.
    pub ident: Ident<F, S>,
    /// Any arguments.
    pub args:  Option<FactArgs<F, S>>,
}
impl<F, S> Fact<F, S> {
    /// Returns if there are any variables in the argument to this fact, if any.
    ///
    /// # Returns
    /// True if there is at least one [`Atom::Var`] recursively, or false otherwise.
    #[inline]
    pub fn has_vars(&self) -> bool {
        match &self.args {
            Some(args) => args.has_vars(),
            None => false,
        }
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
impl_map!(Fact, ident, args);

/// Defines the (optional) arguments-part of the constructor application.
///
/// # Syntax
/// ```plain
/// (foo, bar(baz), Baz)
/// ```
#[derive(Clone, Debug)]
pub struct FactArgs<F, S> {
    /// The parenthesis wrapping the arguments.
    pub paren_tokens: Parens<F, S>,
    /// The arguments contained within.
    pub args: Punctuated<Atom<F, S>, Comma<F, S>>,
}
impl<F, S> FactArgs<F, S> {
    /// Returns if there are any variables in the arguments to this fact.
    ///
    /// # Returns
    /// True if there is at least one [`Atom::Var`] recursively, or false otherwise.
    #[inline]
    pub fn has_vars(&self) -> bool { self.args.values().any(Atom::has_vars) }
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
            Box::new(rr::Repeat::new(Atom::<F, S>::railroad(), Comma::<F, S>::railroad())),
            Box::new(Parens::<F, S>::railroad_close()),
        ])
    }
}
impl_map!(FactArgs, args);

/// Represents identifiers.
///
/// # Syntax
/// ```plain
/// foo
/// ```
#[derive(Clone, Copy, Debug)]
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
impl_map!(Ident, value);



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
