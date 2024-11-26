//  AST.rs
//    by Lut99
//
//  Created:
//    13 Mar 2024, 16:43:37
//  Last edited:
//    26 Nov 2024, 11:25:17
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines the datalog-with-negation AST.
//

use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{Hash, Hasher};

pub use ast_toolkit_punctuated::Punctuated;
#[cfg(feature = "railroad")]
use ast_toolkit_railroad::{railroad as rr, ToDelimNode, ToNode, ToNonTerm};
pub use ast_toolkit_span::Span;
// Re-export the derive macro
#[cfg(feature = "macros")]
pub use datalog_macros::datalog;
use enum_debug::EnumDebug;
use paste::paste;


/***** HELPER MACROS *****/
/// Automatically implements `Eq`, `Hash` and `PartialEq` for the given fields in the given struct.
macro_rules! impl_map {
    ($for:ident, $($fields:ident),+) => {
        impl<'f, 's> Eq for $for<'f, 's> {}

        impl<'f, 's> Hash for $for<'f, 's> {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                $(
                    self.$fields.hash(state);
                )+
            }
        }

        impl<'f, 's> PartialEq for $for<'f, 's> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                $(
                    self.$fields == other.$fields
                )&&+
            }
        }
    };
}
/// Automatically implements `Eq`, `Hash` and `PartialEq` for a type that is semantically always the same.
///
/// Examples: tokens (no value to change them).
macro_rules! impl_map_invariant {
    ($name:ident) => {
        impl<'f, 's> Eq for $name<'f, 's> {}
        impl<'f, 's> Hash for $name<'f, 's> {
            #[inline]
            fn hash<H: Hasher>(&self, _state: &mut H) {}
        }
        impl<'f, 's> PartialEq for $name<'f, 's> {
            #[inline]
            fn eq(&self, _other: &Self) -> bool { true }

            #[inline]
            fn ne(&self, _other: &Self) -> bool { false }
        }
    };
}
macro_rules! impl_enum_map {
    ($for:ident, $($variants:ident($($fields:ident),+)),+) => {
        impl<'f, 's> Eq for $for<'f, 's> {}

        impl<'f, 's> Hash for $for<'f, 's> {
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
            impl<'f, 's> PartialEq for $for<'f, 's> {
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





/***** FORMATTERS *****/
/// Given an AST node, calls [`Reserialize::reserialize_fmt()`] on it.
#[cfg(feature = "reserialize")]
pub struct ReserializeFormatter<'n, N: ?Sized> {
    /// The node to reserialize.
    node: &'n N,
}
#[cfg(feature = "reserialize")]
impl<'n, N: Reserialize> Display for ReserializeFormatter<'n, N> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { self.node.reserialize_fmt(f) }
}

/// Given an AST node, calls [`ReserializeDelim::reserialize_open_fmt()`] on it.
#[cfg(feature = "reserialize")]
pub struct ReserializeOpenFormatter<'n, N: ?Sized> {
    /// The node to reserialize.
    node: &'n N,
}
#[cfg(feature = "reserialize")]
impl<'n, N: ReserializeDelim> Display for ReserializeOpenFormatter<'n, N> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { self.node.reserialize_open_fmt(f) }
}

/// Given an AST node, calls [`ReserializeDelim::reserialize_close_fmt()`] on it.
#[cfg(feature = "reserialize")]
pub struct ReserializeCloseFormatter<'n, N: ?Sized> {
    /// The node to reserialize.
    node: &'n N,
}
#[cfg(feature = "reserialize")]
impl<'n, N: ReserializeDelim> Display for ReserializeCloseFormatter<'n, N> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { self.node.reserialize_close_fmt(f) }
}





/***** AUXILLARY *****/
/// Serializes a node in the $Datalog^\neg$-tree such that is serializable to the same tree (modulo whitespace).
#[cfg(feature = "reserialize")]
pub trait Reserialize {
    /// Formats this AST node to some formatter.
    ///
    /// The idea is that it is deterministic, i.e., serialializing and then parsing this output should yield you an equivalent tree (modulo whitespace).
    ///
    /// # Arguments
    /// - `f`: The [`Formatter`] to serialize to.
    ///
    /// # Errors
    /// This function is allowed to error if it failed to write to the given `f`ormatter.
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult;
}

/// Allows a node in the $Datalog^\neg$ to be serializable in a repeatable way.
///
/// Specifically, if serialized through this trait, it should be guaranteed that parsing it yields the same AST modulo whitespace.
#[cfg(feature = "reserialize")]
pub trait Reserializable: Reserialize {
    /// Returns a formatter that re-serializes this node in the AST.
    ///
    /// # Returns
    /// A [`ReserializeFormatter`] that implements [`Display`].
    fn reserialize(&self) -> ReserializeFormatter<Self>;
}
#[cfg(feature = "reserialize")]
impl<T: Reserialize> Reserializable for T {
    #[inline]
    fn reserialize(&self) -> ReserializeFormatter<Self> { ReserializeFormatter { node: self } }
}



/// Serializes a delimiting node in the $Datalog^\neg$-tree such that is serializable to the same tree (modulo whitespace).
#[cfg(feature = "reserialize")]
pub trait ReserializeDelim {
    /// Formats the opening token of this AST node to some formatter.
    ///
    /// The idea is that it is deterministic, i.e., serialializing and then parsing this output should yield you an equivalent tree (modulo whitespace).
    ///
    /// # Arguments
    /// - `f`: The [`Formatter`] to serialize to.
    ///
    /// # Errors
    /// This function is allowed to error if it failed to write to the given `f`ormatter.
    fn reserialize_open_fmt(&self, f: &mut Formatter) -> FResult;

    /// Formats the closing token of this AST node to some formatter.
    ///
    /// The idea is that it is deterministic, i.e., serialializing and then parsing this output should yield you an equivalent tree (modulo whitespace).
    ///
    /// # Arguments
    /// - `f`: The [`Formatter`] to serialize to.
    ///
    /// # Errors
    /// This function is allowed to error if it failed to write to the given `f`ormatter.
    fn reserialize_close_fmt(&self, f: &mut Formatter) -> FResult;
}

/// Allows a delimited node in the $Datalog^\neg$ to be serializable in a repeatable way.
///
/// Specifically, if serialized through this trait, it should be guaranteed that parsing it yields the same AST modulo whitespace.
#[cfg(feature = "reserialize")]
pub trait ReserializableDelim: ReserializeDelim {
    /// Returns a formatter that re-serializes the opening token of this node in the AST.
    ///
    /// # Returns
    /// A [`ReserializeOpenFormatter`] that implements [`Display`].
    fn reserialize_open(&self) -> ReserializeOpenFormatter<Self>;
    /// Returns a formatter that re-serializes the closing token of this node in the AST.
    ///
    /// # Returns
    /// A [`ReserializeCloseFormatter`] that implements [`Display`].
    fn reserialize_close(&self) -> ReserializeCloseFormatter<Self>;
}
#[cfg(feature = "reserialize")]
impl<T: ReserializeDelim> ReserializableDelim for T {
    #[inline]
    fn reserialize_open(&self) -> ReserializeOpenFormatter<Self> { ReserializeOpenFormatter { node: self } }
    #[inline]
    fn reserialize_close(&self) -> ReserializeCloseFormatter<Self> { ReserializeCloseFormatter { node: self } }
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
    ast_toolkit_railroad::diagram!(
        Spec as "Spec",
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
pub struct Spec<'f, 's> {
    /// The list of rules in this program.
    pub rules: Vec<Rule<'f, 's>>,
}
impl<'f, 's> Spec<'f, 's> {}
impl<'f, 's> Display for Spec<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        for rule in &self.rules {
            writeln!(f, "{rule}")?;
        }
        Ok(())
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Spec<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        for rule in &self.rules {
            rule.reserialize_fmt(f)?;
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
pub struct Rule<'f, 's> {
    /// A list of consequences (i.e., instances produced by this rule).
    pub consequences: Punctuated<Atom<'f, 's>, Comma<'f, 's>>,
    /// An optional second part that describes the antecedents.
    pub tail: Option<RuleAntecedents<'f, 's>>,
    /// The closing dot after each rule.
    pub dot: Dot<'f, 's>,
}
impl<'f, 's> Display for Rule<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(
            f,
            "{}{}.",
            self.consequences.values().map(|c| c.to_string()).collect::<Vec<String>>().join(", "),
            if let Some(tail) = &self.tail { tail.to_string() } else { String::new() }
        )
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Rule<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        for (value, punct) in self.consequences.pairs() {
            value.reserialize_fmt(f)?;
            if let Some(punct) = punct {
                punct.reserialize_fmt(f)?;
                write!(f, " ")?;
            }
        }
        if let Some(tail) = &self.tail {
            tail.reserialize_fmt(f)?;
        }
        self.dot.reserialize_fmt(f)
    }
}
#[cfg(feature = "railroad")]
impl<'f, 's> ToNode for Rule<'f, 's> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(rr::Repeat::new(Atom::railroad(), Comma::railroad())),
            Box::new(rr::Optional::new(RuleAntecedents::railroad())),
            Box::new(Dot::railroad()),
        ])
    }
}
impl_map!(Rule, consequences, tail);

/// Defines the second half of the rule, if any.
///
/// # Syntax
/// ```plain
/// :- foo, bar(baz)
/// ```
#[derive(Clone, Debug)]
pub struct RuleAntecedents<'f, 's> {
    /// The arrow token.
    pub arrow_token: Arrow<'f, 's>,
    /// The list of antecedents.
    pub antecedents: Punctuated<Literal<'f, 's>, Comma<'f, 's>>,
}
#[cfg(feature = "railroad")]
impl<'f, 's> ToNode for RuleAntecedents<'f, 's> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![Box::new(Arrow::railroad()), Box::new(rr::Repeat::new(Literal::railroad(), Comma::railroad()))])
    }
}
impl<'f, 's> Display for RuleAntecedents<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, " :- {}", self.antecedents.values().map(|a| a.to_string()).collect::<Vec<String>>().join(", "))
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for RuleAntecedents<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        self.arrow_token.reserialize_fmt(f)?;
        write!(f, " ")?;
        for (value, punct) in self.antecedents.pairs() {
            value.reserialize_fmt(f)?;
            if let Some(punct) = punct {
                punct.reserialize_fmt(f)?;
                write!(f, " ")?;
            }
        }
        Ok(())
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
pub enum Literal<'f, 's> {
    /// Non-negated atom.
    ///
    /// # Syntax
    /// ```plain
    /// foo
    /// foo(bar)
    /// ```
    Atom(Atom<'f, 's>),
    /// Negated atom.
    ///
    /// # Syntax
    /// ```plain
    /// not foo
    /// ```
    NegAtom(NegAtom<'f, 's>),
}
impl<'f, 's> Literal<'f, 's> {
    /// Returns if there are any variables in the antecedents.
    ///
    /// # Returns
    /// True if there is at least one [`AtomArg::Var`], or false otherwise.
    #[inline]
    pub fn has_vars(&self) -> bool { self.atom().has_vars() }

    /// Returns the polarity of the literal.
    ///
    /// # Returns
    /// True if this is a positive literal ([`Literal::Atom`]), or false if it's a negative literal ([`Literal::NegAtom`]).
    pub fn polarity(&self) -> bool { matches!(self, Self::Atom(_)) }

    /// Returns the atom that appears in all variants of the literal.
    ///
    /// # Returns
    /// A reference to the [`Atom`] contained within.
    pub fn atom(&self) -> &Atom<'f, 's> {
        match self {
            Self::Atom(a) => a,
            Self::NegAtom(na) => &na.atom,
        }
    }

    /// Returns the atom that appears in all variants of the literal.
    ///
    /// # Returns
    /// A mutable reference to the [`Atom`] contained within.
    pub fn atom_mut(&mut self) -> &mut Atom<'f, 's> {
        match self {
            Self::Atom(a) => a,
            Self::NegAtom(na) => &mut na.atom,
        }
    }
}
impl<'f, 's> Display for Literal<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Atom(a) => write!(f, "{a}"),
            Self::NegAtom(na) => write!(f, "{na}"),
        }
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Literal<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        match self {
            Self::Atom(a) => a.reserialize_fmt(f),
            Self::NegAtom(na) => na.reserialize_fmt(f),
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
pub struct NegAtom<'f, 's> {
    /// The not-token.
    pub not_token: Not<'f, 's>,
    /// The atom that was negated.
    pub atom:      Atom<'f, 's>,
}
impl<'f, 's> Display for NegAtom<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { write!(f, "not {}", self.atom) }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for NegAtom<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        self.not_token.reserialize_fmt(f)?;
        write!(f, " ")?;
        self.atom.reserialize_fmt(f)
    }
}
impl_map!(NegAtom, atom);



/// Defines a constructor application of facts.
///
/// # Syntax
/// ```plain
/// foo
/// foo(bar, Baz)
/// ```
#[derive(Clone, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
pub struct Atom<'f, 's> {
    /// The identifier itself.
    pub ident: Ident<'f, 's>,
    /// Any arguments.
    pub args:  Option<AtomArgs<'f, 's>>,
}
impl<'f, 's> Atom<'f, 's> {
    /// Returns if there are any variables in the antecedents.
    ///
    /// # Returns
    /// True if there is at least one [`AtomArg::Var`], or false otherwise.
    #[inline]
    pub fn has_vars(&self) -> bool { self.args.iter().flat_map(|a| a.args.values()).find(|a| matches!(a, AtomArg::Var(_))).is_some() }

    /// Creates a new [`Span`] that covers the entire Atom.
    ///
    /// # Returns
    /// A new [`Span`] that is this atom.
    pub fn span(&self) -> Span<&'f str, &'s str> {
        match &self.args {
            Some(args) => self.ident.value.join(&args.paren_tokens.span()).unwrap_or_else(|| self.ident.value.clone()),
            None => self.ident.value.clone(),
        }
    }
}
impl<'f, 's> Display for Atom<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "{}{}", self.ident, if let Some(args) = &self.args { args.to_string() } else { String::new() })
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Atom<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        self.ident.reserialize_fmt(f)?;
        if let Some(args) = &self.args {
            args.reserialize_fmt(f)?;
        }
        Ok(())
    }
}
impl_map!(Atom, ident, args);

/// Defines the (optional) arguments-part of the constructor application.
///
/// # Syntax
/// ```plain
/// (foo, bar(baz))
/// ```
#[derive(Clone, Debug)]
pub struct AtomArgs<'f, 's> {
    /// The parenthesis wrapping the arguments.
    pub paren_tokens: Parens<'f, 's>,
    /// The arguments contained within.
    pub args: Punctuated<AtomArg<'f, 's>, Comma<'f, 's>>,
}
impl<'f, 's> Display for AtomArgs<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "({})", self.args.values().map(|a| a.to_string()).collect::<Vec<String>>().join(","))
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for AtomArgs<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        self.paren_tokens.reserialize_open_fmt(f)?;
        for (value, punct) in self.args.pairs() {
            value.reserialize_fmt(f)?;
            if let Some(punct) = punct {
                punct.reserialize_fmt(f)?;
                write!(f, " ")?;
            };
        }
        self.paren_tokens.reserialize_close_fmt(f)?;
        Ok(())
    }
}
#[cfg(feature = "railroad")]
impl<'f, 's> ToNode for AtomArgs<'f, 's> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Parens::railroad_open()),
            Box::new(rr::Repeat::new(AtomArg::railroad(), Comma::railroad())),
            Box::new(Parens::railroad_close()),
        ])
    }
}
impl_map!(AtomArgs, args);

/// Represents an argument to an Atom, which is either a variable or a nested atom.
///
/// # Syntax
/// ```plain
/// foo
/// Baz
/// ```
#[derive(Clone, Debug, EnumDebug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
pub enum AtomArg<'f, 's> {
    /// It's a nested atom.
    ///
    /// Note that $Datalog^\neg$ does not support full nesting, so only direct identifiers allowed.
    ///
    /// # Syntax
    /// ```plain
    /// foo
    /// ```
    Atom(Ident<'f, 's>),
    /// It's a variable.
    ///
    /// # Syntax
    /// ```plain
    /// Foo
    /// ```
    #[cfg_attr(feature = "railroad", railroad(regex = "^[A-Z_][a-zA-Z_-]*$"))]
    Var(Ident<'f, 's>),
}
impl<'f, 's> AtomArg<'f, 's> {
    /// Returns the identifier that appears in all variants of the AtomArg.
    ///
    /// # Returns
    /// A reference to the [`Ident`] contained within.
    pub fn ident(&self) -> &Ident<'f, 's> {
        match self {
            Self::Atom(a) => a,
            Self::Var(v) => v,
        }
    }

    /// Returns the identifier that appears in all variants of the AtomArg.
    ///
    /// # Returns
    /// A mutable reference to the [`Ident`] contained within.
    pub fn ident_mut(&mut self) -> &mut Ident<'f, 's> {
        match self {
            Self::Atom(a) => a,
            Self::Var(v) => v,
        }
    }
}
impl<'f, 's> Display for AtomArg<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { write!(f, "{}", self.ident()) }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for AtomArg<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{}", self.ident()) }
}
impl_enum_map!(AtomArg, Atom(ident), Var(ident));

/// Represents identifiers.
///
/// # Syntax
/// ```plain
/// foo
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(regex = "^[a-z_][a-z_-]*$"))]
pub struct Ident<'f, 's> {
    /// The value of the identifier itself.
    pub value: Span<&'f str, &'s str>,
}
impl<'f, 's> Display for Ident<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { write!(f, "{}", self.value.value()) }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Ident<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{}", self.value) }
}
impl_map!(Ident, value);



/// Defines an arrow token.
///
/// # Syntax
/// ```plain
/// :-
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(term = ":-"))]
pub struct Arrow<'f, 's> {
    /// The source of this arrow in the source.
    pub span: Span<&'f str, &'s str>,
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Arrow<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, ":-") }
}
impl_map_invariant!(Arrow);

/// Defines a comma token.
///
/// # Syntax
/// ```plain
/// ,
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(term = ","))]
pub struct Comma<'f, 's> {
    /// The source of this comma in the source.
    pub span: Span<&'f str, &'s str>,
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Comma<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, ",") }
}
impl_map_invariant!(Comma);

/// Defines a dot token.
///
/// # Syntax
/// ```plain
/// .
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(term = "."))]
pub struct Dot<'f, 's> {
    /// The source of this dot in the source.
    pub span: Span<&'f str, &'s str>,
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Dot<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, ".") }
}
impl_map_invariant!(Dot);

/// Defines a not token.
///
/// # Syntax
/// ```plain
/// not
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(term = "not"))]
pub struct Not<'f, 's> {
    /// The source of this not in the source.
    pub span: Span<&'f str, &'s str>,
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Not<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "not") }
}
impl_map_invariant!(Not);

/// Defines parenthesis.
///
/// # Syntax
/// ```plain
/// ()
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToDelimNode))]
#[cfg_attr(feature = "railroad", railroad(open = "(", close = ")"))]
pub struct Parens<'f, 's> {
    /// The opening-parenthesis.
    pub open:  Span<&'f str, &'s str>,
    /// The closing-parenthesis.
    pub close: Span<&'f str, &'s str>,
}
impl<'f, 's> Parens<'f, 's> {
    /// Creates a new [`Span`] that covers the entire parentheses' range.
    ///
    /// # Returns
    /// A new [`Span`] that wraps these parenthesis.
    #[inline]
    pub fn span(&self) -> Span<&'f str, &'s str> { self.open.join(&self.close).unwrap_or_else(|| self.open.clone()) }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> ReserializeDelim for Parens<'f, 's> {
    #[inline]
    fn reserialize_open_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "(") }
    #[inline]
    fn reserialize_close_fmt(&self, f: &mut Formatter) -> FResult { write!(f, ")") }
}
impl_map_invariant!(Parens);
