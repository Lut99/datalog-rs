//  AST.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 10:50:29
//  Last edited:
//    28 Nov 2024, 17:32:58
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines an AST that is a strict superset of the datalog one.
//

use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{Hash, Hasher};

#[cfg(feature = "railroad")]
use ast_toolkit::railroad::{railroad as rr, ToDelimNode, ToNode, ToNonTerm};
use ast_toolkit::span::{Span, SpannableDisplay};
use ast_toolkit::tokens::{utf8_delimiter, utf8_token};
use paste::paste;

use crate::ast::{impl_enum_map, impl_map, Reserialize, ReserializeDelim, Rule};


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
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub struct TransitionSpec<F, S> {
    /// The list of phrases (rules|transitions) in this program.
    pub phrases: Vec<Phrase<F, S>>,
}
impl<F, S> Display for TransitionSpec<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        for phrase in &self.phrases {
            writeln!(f, "{phrase}")?;
        }
        Ok(())
    }
}
#[cfg(feature = "reserialize")]
impl<F, S> Reserialize for TransitionSpec<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        for phrase in &self.phrases {
            phrase.reserialize_fmt(f)?;
            writeln!(f)?;
        }
        Ok(())
    }
}
impl_map!(TransitionSpec, phrases);

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
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum Phrase<F, S> {
    /// It's a postulation of zero or more rules.
    Postulation(Postulation<F, S>),
    /// It's a plain rule.
    Rule(Rule<F, S>),
    /// It's the definition of a transition.
    Transition(Transition<F, S>),
    /// It's the trigger of zero or more transitions.
    Trigger(Trigger<F, S>),
}
impl<F, S> Display for Phrase<F, S>
where
    S: SpannableDisplay,
{
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
impl<F, S> Reserialize for Phrase<F, S>
where
    S: SpannableDisplay,
{
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
pub struct Postulation<F, S> {
    /// The operator.
    pub op: PostulationOp<F, S>,
    /// The curly brackets wrapping the rules.
    pub curly_tokens: Curly<F, S>,
    /// The rule(s) postulated.
    pub rules: Vec<Rule<F, S>>,
}
impl<F, S> Display for Postulation<F, S>
where
    S: SpannableDisplay,
{
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
impl<F, S> Reserialize for Postulation<F, S>
where
    S: SpannableDisplay,
{
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
impl<F, S> ToNode for Postulation<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(PostulationOp::<F, S>::railroad()) as Box<dyn rr::Node>,
            Box::new(Curly::<F, S>::railroad_open()),
            Box::new(rr::Repeat::new(Rule::<F, S>::railroad(), rr::Empty)),
            Box::new(Curly::<F, S>::railroad_close()),
        ])
    }
}
impl_map!(Postulation, rules);

/// Specifies the possible postulation types.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum PostulationOp<F, S> {
    /// Creates facts.
    Create(Add<F, S>),
    /// Hides previously created facts.
    Obfuscate(Dash<F, S>),
}
impl<F, S> Display for PostulationOp<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Create(_) => write!(f, "+"),
            Self::Obfuscate(_) => write!(f, "-"),
        }
    }
}
#[cfg(feature = "reserialize")]
impl<F, S> Reserialize for PostulationOp<F, S> {
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        match self {
            Self::Create(c) => c.reserialize_fmt(f),
            Self::Obfuscate(o) => o.reserialize_fmt(f),
        }
    }
}
impl_enum_map!(PostulationOp, Create(op), Obfuscate(op));



/// Specifies the definition of a transition.
///
/// # Syntax
/// ```plain
/// #foo {
///     +{ foo. }
///     ~{ bar :- baz(quz). }
/// }.
/// ```
#[derive(Clone, Debug)]
pub struct Transition<F, S> {
    /// The identifier of the transition.
    pub ident: TransIdent<F, S>,
    /// The curly brackets wrapping the postulations.
    pub curly_tokens: Curly<F, S>,
    /// The posulations nested inside.
    pub postulations: Vec<Postulation<F, S>>,
}
impl<F, S> Display for Transition<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "{} {{", self.ident)?;
        if !self.postulations.is_empty() {
            writeln!(f)?;
        }
        for post in &self.postulations {
            writeln!(f, "    {post}")?;
        }
        write!(f, "}}")
    }
}
#[cfg(feature = "reserialize")]
impl<F, S> Reserialize for Transition<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        self.ident.reserialize_fmt(f)?;
        self.curly_tokens.reserialize_open_fmt(f)?;
        if !self.postulations.is_empty() {
            writeln!(f)?;
        }
        for post in &self.postulations {
            write!(f, "    ")?;
            post.reserialize_fmt(f)?;
            writeln!(f)?;
        }
        self.curly_tokens.reserialize_close_fmt(f)
    }
}
#[cfg(feature = "railroad")]
impl<F, S> ToNode for Transition<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(TransIdent::<F, S>::railroad()) as Box<dyn rr::Node>,
            Box::new(Curly::<F, S>::railroad_open()),
            Box::new(rr::Repeat::new(Postulation::<F, S>::railroad(), rr::Empty)),
            Box::new(Curly::<F, S>::railroad_close()),
        ])
    }
}
impl_map!(Transition, ident, postulations);

/// An [`Ident`]ifier prefixed by a `#`.
///
/// # Syntax
/// ```plain
/// #foo
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad), regex = "^#[a-z_][a-z_-]*$"))]
pub struct TransIdent<F, S> {
    /// The value of the identifier itself, including the pound.
    pub value: Span<F, S>,
}
impl<F, S> Display for TransIdent<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { write!(f, "{}", self.value) }
}
#[cfg(feature = "reserialize")]
impl<F, S> Reserialize for TransIdent<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{}", self.value) }
}
impl_map!(TransIdent, value);



/// Specifies the triggering of a transition.
///
/// # Syntax
/// ```plain
/// !{ #foo }.
/// ```
#[derive(Clone, Debug)]
pub struct Trigger<F, S> {
    /// The exclamation mark.
    pub exclaim_token: Exclaim<F, S>,
    /// The curly brackets wrapping the transition identifiers.
    pub curly_tokens: Curly<F, S>,
    /// The list of transition identifiers triggered.
    pub idents: Vec<TransIdent<F, S>>,
}
impl<F, S> Display for Trigger<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "!{{")?;
        if !self.idents.is_empty() {
            writeln!(f)?;
        }
        for ident in &self.idents {
            writeln!(f, "    {ident}")?;
        }
        write!(f, "}}")
    }
}
#[cfg(feature = "reserialize")]
impl<F, S> Reserialize for Trigger<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn reserialize_fmt(&self, f: &mut Formatter) -> FResult {
        self.exclaim_token.reserialize_fmt(f)?;
        self.curly_tokens.reserialize_open_fmt(f)?;
        if !self.idents.is_empty() {
            writeln!(f)?;
        }
        for ident in &self.idents {
            write!(f, "    ")?;
            ident.reserialize_fmt(f)?;
            writeln!(f)?;
        }
        self.curly_tokens.reserialize_close_fmt(f)
    }
}
#[cfg(feature = "railroad")]
impl<F, S> ToNode for Trigger<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Exclaim::<F, S>::railroad()) as Box<dyn rr::Node>,
            Box::new(Curly::<F, S>::railroad_open()),
            Box::new(rr::Repeat::new(TransIdent::<F, S>::railroad(), rr::Empty)),
            Box::new(Curly::<F, S>::railroad_close()),
        ])
    }
}
impl_map!(Trigger, idents);





/***** TOKENS *****/
utf8_token!(Add, "+");
utf8_token!(Dash, "-");
utf8_token!(Exclaim, "!");
utf8_delimiter!(Curly, "{", "}");

// Implement their railroads
#[doc(hidden)]
#[cfg(feature = "railroad")]
mod railroad_impl {
    use ast_toolkit::tokens::{utf8_delimiter_railroad, utf8_token_railroad};

    use super::*;

    utf8_token_railroad!(Add, "+");
    utf8_token_railroad!(Dash, "-");
    utf8_token_railroad!(Exclaim, "!");
    utf8_delimiter_railroad!(Curly, "{", "}");
}

// Implement reserialize
#[doc(hidden)]
#[cfg(feature = "reserialize")]
mod reserialize_impl {
    use super::*;

    impl<F, S> Reserialize for Add<F, S> {
        #[inline]
        fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "+") }
    }
    impl<F, S> Reserialize for Dash<F, S> {
        #[inline]
        fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "-") }
    }
    impl<F, S> Reserialize for Exclaim<F, S> {
        #[inline]
        fn reserialize_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "!") }
    }
    impl<F, S> ReserializeDelim for Curly<F, S> {
        #[inline]
        fn reserialize_open_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{{") }
        #[inline]
        fn reserialize_close_fmt(&self, f: &mut Formatter) -> FResult { write!(f, "}}") }
    }
}
