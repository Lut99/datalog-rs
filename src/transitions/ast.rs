//  AST.rs
//    by Lut99
//
//  Created:
//    28 Nov 2024, 10:50:29
//  Last edited:
//    11 Feb 2025, 17:58:09
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines an AST that is a strict superset of the datalog one.
//

use std::fmt::{Display, Formatter, Result as FResult};

use ast_toolkit::punctuated::Punctuated;
#[cfg(feature = "railroad")]
use ast_toolkit::railroad::{ToDelimNode, ToNode, ToNonTerm, railroad as rr};
use ast_toolkit::span::SpannableBytes;
use ast_toolkit::tokens::{utf8_delim, utf8_token};
use better_derive::{Clone, Copy, Debug, Eq, Hash, PartialEq};

use crate::ast::{Atom, Comma, Dot, Ident, Literal, Rule, RuleBody};
use crate::ir;


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
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNonTerm))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub struct TransitionSpec<S> {
    /// The list of phrases (rules|transitions) in this program.
    pub phrases: Vec<Phrase<S>>,
}
impl<'s, S: SpannableBytes<'s>> Display for TransitionSpec<S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        for phrase in &self.phrases {
            phrase.fmt(f)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

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
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum Phrase<S> {
    /// It's a postulation of zero or more rules.
    Postulation(Postulation<S>),
    /// It's a plain rule.
    Rule(Rule<S>),
    /// It's the definition of a transition.
    Transition(Transition<S>),
    /// It's the trigger of zero or more transitions.
    Trigger(Trigger<S>),
}
impl<'s, S: SpannableBytes<'s>> Display for Phrase<S> {
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



/// Specifies a postulation of some kind.
///
/// # Syntax
/// ```plain
/// +{ foo }.
/// ~{ bar } :- baz(quz).
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Postulation<S> {
    /// The operator.
    pub op: PostulationOp<S>,
    /// The curly brackets wrapping the postulated facts.
    pub curly_tokens: Curly<S>,
    /// The fact(s) postulated.
    pub consequents: Punctuated<Atom<S>, Comma<S>>,
    /// The tail of the postulation.
    pub tail: Option<RuleBody<S>>,
    /// The dot token at the end.
    pub dot: Dot<S>,
}
impl<S: Clone> Postulation<S> {
    /// Gets the postulation as a regular rule.
    ///
    /// This is powerful for reasoning, where the postconditions are computed on whether the
    /// preconditions hold in the current state.
    ///
    /// # Returns
    /// A [`Rule`] that can be used to find out if the post conditions hold.
    pub fn to_rule(&self) -> ir::Rule<ir::Atom<S>> {
        ir::Rule {
            consequents:     self.consequents.values().map(Atom::compile).collect(),
            pos_antecedents: self
                .tail
                .iter()
                .flat_map(|t| t.antecedents.values().filter(|l| l.is_positive()).map(Literal::atom))
                .map(Atom::compile)
                .collect(),
            neg_antecedents: self
                .tail
                .iter()
                .flat_map(|t| t.antecedents.values().filter(|l| !l.is_positive()).map(Literal::atom))
                .map(Atom::compile)
                .collect(),
        }
    }
}
impl<'s, S: SpannableBytes<'s>> Display for Postulation<S> {
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
impl<S> ToNode for Postulation<S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(PostulationOp::<S>::railroad()) as Box<dyn rr::Node>,
            Box::new(Curly::<S>::railroad_open()),
            Box::new(rr::Repeat::new(Ident::<S>::railroad(), rr::Empty)),
            Box::new(Curly::<S>::railroad_close()),
            Box::new(rr::Optional::new(RuleBody::<S>::railroad())),
            Box::new(Dot::<S>::railroad()),
        ])
    }
}

/// Specifies the possible postulation types.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "railroad", derive(ToNode))]
#[cfg_attr(feature = "railroad", railroad(prefix(::ast_toolkit::railroad)))]
pub enum PostulationOp<S> {
    /// Creates facts.
    Create(Add<S>),
    /// Hides previously created facts.
    Obfuscate(Squiggly<S>),
}
impl<S> Display for PostulationOp<S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Create(_) => write!(f, "+"),
            Self::Obfuscate(_) => write!(f, "-"),
        }
    }
}



/// Specifies the definition of a transition.
///
/// # Syntax
/// ```plain
/// #foo {
///     +{ foo }.
///     ~{ bar } :- baz(quz).
/// }.
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Transition<S> {
    /// The identifier of the transition.
    pub ident: Ident<S>,
    /// The curly brackets wrapping the postulations.
    pub curly_tokens: Curly<S>,
    /// The posulations nested inside.
    pub postulations: Vec<Postulation<S>>,
    /// The dot token at the end.
    pub dot: Dot<S>,
}
impl<'s, S: SpannableBytes<'s>> Display for Transition<S> {
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
impl<S> ToNode for Transition<S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            railroad_trans_ident(),
            Box::new(Curly::<S>::railroad_open()),
            Box::new(rr::Repeat::new(Postulation::<S>::railroad(), rr::Empty)),
            Box::new(Curly::<S>::railroad_close()),
        ])
    }
}



/// Specifies the triggering of a transition.
///
/// # Syntax
/// ```plain
/// !{ #foo }.
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Trigger<S> {
    /// The exclamation mark.
    pub exclaim_token: Exclaim<S>,
    /// The curly brackets wrapping the transition identifiers.
    pub curly_tokens: Curly<S>,
    /// The list of transition identifiers triggered.
    pub idents: Vec<Ident<S>>,
    /// The dot token at the end.
    pub dot: Dot<S>,
}
impl<'s, S: SpannableBytes<'s>> Display for Trigger<S> {
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
impl<S> ToNode for Trigger<S> {
    type Node = rr::Sequence<Box<dyn rr::Node>>;

    #[inline]
    fn railroad() -> Self::Node {
        rr::Sequence::new(vec![
            Box::new(Exclaim::<S>::railroad()) as Box<dyn rr::Node>,
            Box::new(Curly::<S>::railroad_open()),
            Box::new(rr::Repeat::new(railroad_trans_ident(), rr::Empty)),
            Box::new(Curly::<S>::railroad_close()),
        ])
    }
}





/***** TOKENS *****/
utf8_token!(Add, "+");
utf8_token!(Squiggly, "~");
utf8_token!(Exclaim, "!");
utf8_delim!(Curly, "{", "}");

// Implement their railroads
#[doc(hidden)]
#[cfg(feature = "railroad")]
mod railroad_impl {
    use ast_toolkit::tokens::{utf8_delim_railroad, utf8_token_railroad};

    use super::*;

    utf8_token_railroad!(Add, "+");
    utf8_token_railroad!(Squiggly, "~");
    utf8_token_railroad!(Exclaim, "!");
    utf8_delim_railroad!(Curly, "{", "}");
}
