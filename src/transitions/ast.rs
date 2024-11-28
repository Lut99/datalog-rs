//  AST.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 10:50:29
//  Last edited:
//    28 Nov 2024, 11:08:18
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines an AST that is a strict superset of the datalog one.
//

use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{Hash, Hasher};

#[cfg(feature = "railroad")]
use ast_toolkit_railroad::{railroad as rr, ToDelimNode, ToNode, ToNonTerm};
use datalog::ast::{Reserialize, ReserializeDelim, Rule, Span};
use paste::paste;


/***** HELPER MACROS *****/
/// Automatically implements [`Eq`], [`Hash`] and [`PartialEq`] for the given fields in the given
/// struct.
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

/// Automatically implements [`Eq`], [`Hash`] and [`PartialEq`] for a type which, hash-wise, is not
/// dynamic (i.e., it always produces the same hash).
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

/// Automatically implements [`Eq`], [`Hash`] and [`PartialEq`] for the given fields in variants of the given enum.
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





/***** TOPLEVEL *****/
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
    /// The list of phrases (rules|transitions) in this program.
    pub phrases: Vec<Phrase<'f, 's>>,
}
impl<'f, 's> Display for Spec<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        for phrase in &self.phrases {
            writeln!(f, "{phrase}")?;
        }
        Ok(())
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Spec<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        for phrase in &self.phrases {
            phrase.reserialize_fmt(f)?;
            writeln!(f)?;
        }
        Ok(())
    }
}
impl_map!(Spec, phrases);

/// Specifies a single phrase.
///
/// # Syntax
/// ```plain
/// #foo {
///     +{ foo. }
///     ~{ bar :- baz(quz). }
/// }.
/// !{ #foo }.
/// foo :- bar, baz(quz).
/// ```
#[derive(Clone, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
pub enum Phrase<'f, 's> {
    /// It's a postulation of zero or more rules.
    Postulation(Postulation<'f, 's>),
    /// It's a plain rule.
    Rule(Rule<'f, 's>),
    /// It's the definition of a transition.
    Transition(Transition<'f, 's>),
    /// It's the trigger of zero or more transitions.
    Trigger(Trigger<'f, 's>),
}
impl<'f, 's> Display for Phrase<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Postulation(p) => writeln!(f, "{p}"),
            Self::Rule(r) => writeln!(f, "{r}"),
            Self::Transition(t) => writeln!(f, "{t}"),
            Self::Trigger(t) => writeln!(f, "{t}"),
        }
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Phrase<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        match self {
            Self::Postulation(p) => p.reserialize_fmt(f),
            Self::Rule(r) => r.reserialize_fmt(f),
            Self::Transition(t) => t.reserialize_fmt(f),
            Self::Trigger(t) => t.reserialize_fmt(f),
        }
    }
}
impl_enum_map!(Phrase, Postulation(nested), Rule(nested), Transition(nested), Trigger(nested));



/// Specifies a postulation of some kind.
///
/// # Syntax
/// ```plain
/// +{ foo. }
/// ~{ bar :- baz(quz). }
/// ```
#[derive(Clone, Debug)]
pub struct Postulation<'f, 's> {
    /// The operator.
    pub op: PostulationOp<'f, 's>,
    /// The curly brackets wrapping the rules.
    pub curly_tokens: Curly<'f, 's>,
    /// The rule(s) postulated.
    pub rules: Vec<Rule<'f, 's>>,
}
impl<'f, 's> Display for Postulation<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "{}{{", self.op)?;
        if !self.rules.is_empty() {
            writeln!(f)?;
        }
        for rule in &self.rules {
            writeln!(f, "    {rule}")?;
        }
        write!(f, "}}")
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Postulation<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        self.op.reserialize_fmt(f)?;
        self.curly_tokens.reserialize_open_fmt(f)?;
        if !self.rules.is_empty() {
            writeln!(f)?;
        }
        for rule in &self.rules {
            write!(f, "    ")?;
            rule.reserialize_fmt(f)?;
            writeln!(f)?;
        }
        self.curly_tokens.reserialize_close_fmt(f)
    }
}
#[cfg(feature = "railroad")]
impl<'f, 's> ToNode for Postulation<'f, 's> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(PostulationOp::railroad()) as Box<dyn rr::Node>,
            Box::new(Curly::railroad_open()),
            Box::new(rr::Repeat::new(Rule::railroad(), rr::Empty)),
            Box::new(Curly::railroad_close()),
        ])
    }
}
impl_map!(Postulation, rules);

/// Specifies the possible postulation types.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
pub enum PostulationOp<'f, 's> {
    /// Creates facts.
    Create(Add<'f, 's>),
    /// Hides previously created facts.
    Obfuscate(Dash<'f, 's>),
}
impl<'f, 's> Display for PostulationOp<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Create(_) => write!(f, "+"),
            Self::Obfuscate(_) => write!(f, "-"),
        }
    }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for PostulationOp<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        match self {
            Self::Create(c) => c.reserialize_fmt(f),
            Self::Obfuscate(o) => o.reserialize_fmt(f),
        }
    }
}
impl_enum_map!(PostulationOp, Create(op), Obfuscate(op));





/***** TOKENS *****/
/// Defines a plus-token.
///
/// # Syntax
/// ```plain
/// +
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(term = "+"))]
pub struct Add<'f, 's> {
    /// The source of this arrow in the source.
    pub span: Span<&'f str, &'s str>,
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Add<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "+") }
}
impl_map_invariant!(Add);

/// Defines a minus-token.
///
/// # Syntax
/// ```plain
/// -
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(term = "-"))]
pub struct Dash<'f, 's> {
    /// The source of this arrow in the source.
    pub span: Span<&'f str, &'s str>,
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Dash<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "-") }
}
impl_map_invariant!(Dash);

/// Defines an exclaimation mark-token.
///
/// # Syntax
/// ```plain
/// !
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(term = "!"))]
pub struct Exclaim<'f, 's> {
    /// The source of this arrow in the source.
    pub span: Span<&'f str, &'s str>,
}
#[cfg(feature = "reserialize")]
impl<'f, 's> Reserialize for Exclaim<'f, 's> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "!") }
}
impl_map_invariant!(Exclaim);

/// Defines curly brackets.
///
/// # Syntax
/// ```plain
/// {}
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToDelimNode))]
#[cfg_attr(feature = "railroad", railroad(open = "{", close = "}"))]
pub struct Curly<'f, 's> {
    /// The opening-parenthesis.
    pub open:  Span<&'f str, &'s str>,
    /// The closing-parenthesis.
    pub close: Span<&'f str, &'s str>,
}
impl<'f, 's> Curly<'f, 's> {
    /// Creates a new [`Span`] that covers the entire curlies' range.
    ///
    /// # Returns
    /// A new [`Span`] that wraps these curlies.
    #[inline]
    pub fn span(&self) -> Span<&'f str, &'s str> { self.open.join(&self.close).unwrap_or_else(|| self.open.clone()) }
}
#[cfg(feature = "reserialize")]
impl<'f, 's> ReserializeDelim for Curly<'f, 's> {
    #[inline]
    fn reserialize_open_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{{") }
    #[inline]
    fn reserialize_close_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "}}") }
}
impl_map_invariant!(Curly);
