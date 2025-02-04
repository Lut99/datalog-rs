//  AST.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 10:50:29
//  Last edited:
//    04 Feb 2025, 17:28:33
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines an AST that is a strict superset of the datalog one.
//

use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{Hash, Hasher};

use ast_toolkit::punctuated::Punctuated;
#[cfg(feature = "railroad")]
use ast_toolkit::railroad::{ToDelimNode, ToNode, ToNonTerm, railroad as rr};
use ast_toolkit::span::SpannableDisplay;
use ast_toolkit::tokens::{utf8_delimiter, utf8_token};
use better_derive::{Clone, Copy, Debug};
use paste::paste;

use crate::ast::{Atom, Comma, Dot, Ident, Rule, RuleAntecedents, impl_enum_map, impl_map};


/***** HELPERS *****/
/// Generates the railroad node for the transition identifiers.
#[inline]
#[cfg(feature = "railroad")]
fn railroad_trans_ident() -> Box<dyn rr::Node> {
    Box::new(rr::Sequence::new(vec![
        Box::new(rr::Comment::new("regex".into())) as Box<dyn rr::Node>,
        Box::new(rr::Terminal::new("^#[a-z_-]*$".into())),
    ]))
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
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub struct TransitionSpec<F, S> {
    /// The list of phrases (rules|transitions) in this program.
    pub phrases: Vec<Phrase<F, S>>,
}
impl<F, S: SpannableDisplay> Display for TransitionSpec<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        for phrase in &self.phrases {
            phrase.fmt(f)?;
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
///     +{ foo }.
///     ~{ bar } :- baz(quz).
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
impl<F, S: SpannableDisplay> Display for Phrase<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Postulation(p) => p.fmt(f),
            Self::Rule(r) => r.fmt(f),
            Self::Transition(t) => t.fmt(f),
            Self::Trigger(t) => t.fmt(f),
        }
    }
}
impl_enum_map!(Phrase, Postulation(nested), Rule(nested), Transition(nested), Trigger(nested));



/// Specifies a postulation of some kind.
///
/// # Syntax
/// ```plain
/// +{ foo }.
/// ~{ bar } :- baz(quz).
/// ```
#[derive(Clone, Debug)]
pub struct Postulation<F, S> {
    /// The operator.
    pub op: PostulationOp<F, S>,
    /// The curly brackets wrapping the postulated facts.
    pub curly_tokens: Curly<F, S>,
    /// The fact(s) postulated.
    pub consequents: Punctuated<Atom<F, S>, Comma<F, S>>,
    /// The tail of the postulation.
    pub tail: Option<RuleAntecedents<F, S>>,
    /// The dot token at the end.
    pub dot: Dot<F, S>,
}
impl<F, S> Postulation<F, S>
where
    Atom<F, S>: Clone,
    Comma<F, S>: Clone,
    Dot<F, S>: Clone,
    RuleAntecedents<F, S>: Clone,
{
    /// Gets the postulation as a regular rule.
    ///
    /// This is powerful for reasoning, where the postconditions are computed on whether the
    /// preconditions hold in the current state.
    ///
    /// # Returns
    /// A [`Rule`] that can be used to find out if the post conditions hold.
    pub fn to_rule(&self) -> Rule<F, S> { Rule { consequents: self.consequents.clone(), tail: self.tail.clone(), dot: self.dot.clone() } }
}
impl<F, S: SpannableDisplay> Display for Postulation<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "{}{{", self.op)?;
        if !self.consequents.is_empty() {
            write!(f, " ")?;
            for (i, atom) in self.consequents.values().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                    if f.alternate() {
                        write!(f, " ")?;
                    }
                }
                atom.fmt(f)?;
            }
            write!(f, " ")?;
        }
        write!(f, "}}")?;
        if let Some(tail) = &self.tail {
            tail.fmt(f)?;
        }
        write!(f, ".")
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
            Box::new(rr::Repeat::new(Ident::<F, S>::railroad(), rr::Empty)),
            Box::new(Curly::<F, S>::railroad_close()),
            Box::new(rr::Optional::new(RuleAntecedents::<F, S>::railroad())),
            Box::new(Dot::<F, S>::railroad()),
        ])
    }
}
impl_map!(Postulation, consequents, tail);

/// Specifies the possible postulation types.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum PostulationOp<F, S> {
    /// Creates facts.
    Create(Add<F, S>),
    /// Hides previously created facts.
    Obfuscate(Squiggly<F, S>),
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
impl_enum_map!(PostulationOp, Create(op), Obfuscate(op));



/// Specifies the definition of a transition.
///
/// # Syntax
/// ```plain
/// #foo {
///     +{ foo }.
///     ~{ bar } :- baz(quz).
/// }.
/// ```
#[derive(Clone, Debug)]
pub struct Transition<F, S> {
    /// The identifier of the transition.
    pub ident: Ident<F, S>,
    /// The curly brackets wrapping the postulations.
    pub curly_tokens: Curly<F, S>,
    /// The posulations nested inside.
    pub postulations: Vec<Postulation<F, S>>,
    /// The dot token at the end.
    pub dot: Dot<F, S>,
}
impl<F, S: SpannableDisplay> Display for Transition<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "{} {{", self.ident)?;
        if f.alternate() && !self.postulations.is_empty() {
            writeln!(f)?;
        }
        for post in self.postulations.iter() {
            write!(f, " ")?;
            if f.alternate() {
                write!(f, "   ")?;
            }
            post.fmt(f)?;
            if f.alternate() {
                writeln!(f)?;
            }
        }
        if !f.alternate() {
            write!(f, " ")?;
        }
        write!(f, "}}")
    }
}
#[cfg(feature = "railroad")]
impl<F, S> ToNode for Transition<F, S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            railroad_trans_ident(),
            Box::new(Curly::<F, S>::railroad_open()),
            Box::new(rr::Repeat::new(Postulation::<F, S>::railroad(), rr::Empty)),
            Box::new(Curly::<F, S>::railroad_close()),
        ])
    }
}
impl_map!(Transition, ident, postulations);



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
    pub idents: Vec<Ident<F, S>>,
    /// The dot token at the end.
    pub dot: Dot<F, S>,
}
impl<F, S: SpannableDisplay> Display for Trigger<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        write!(f, "!{{")?;
        if f.alternate() && !self.idents.is_empty() {
            writeln!(f)?;
        }
        for ident in &self.idents {
            write!(f, " ")?;
            if f.alternate() {
                write!(f, "   ")?;
            }
            ident.fmt(f)?;
        }
        if !f.alternate() {
            write!(f, " ")?;
        }
        write!(f, "}}")
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
            Box::new(rr::Repeat::new(railroad_trans_ident(), rr::Empty)),
            Box::new(Curly::<F, S>::railroad_close()),
        ])
    }
}
impl_map!(Trigger, idents);





/***** TOKENS *****/
utf8_token!(Add, "+");
utf8_token!(Squiggly, "~");
utf8_token!(Exclaim, "!");
utf8_delimiter!(Curly, "{", "}");

// Implement their railroads
#[doc(hidden)]
#[cfg(feature = "railroad")]
mod railroad_impl {
    use ast_toolkit::tokens::{utf8_delimiter_railroad, utf8_token_railroad};

    use super::*;

    utf8_token_railroad!(Add, "+");
    utf8_token_railroad!(Squiggly, "~");
    utf8_token_railroad!(Exclaim, "!");
    utf8_delimiter_railroad!(Curly, "{", "}");
}
