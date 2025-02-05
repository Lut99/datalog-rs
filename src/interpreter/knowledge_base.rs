//  KNOLWEDGE BASE.rs
//    by Lut99
//
//  Created:
//    03 Feb 2025, 17:11:26
//  Last edited:
//    05 Feb 2025, 17:39:11
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the New^{TM} Shiny^{TM} [`State`]^{TM} which is capable of
//!   building Herbrand universes over complex things like recursive atoms and
//!   integers.
//!   
//!   Actually, scratch that. Now uses Chris' safety property!
//

use std::borrow::Cow;
use std::collections::HashSet;
use std::hash::Hash;

use better_derive::{Clone, Debug};

use crate::ast::{Atom, Ident, Span};
use crate::safe_ast::SafeRule;


/***** LIBRARY *****/
/// Defines the state during derivation.
///
/// Specifically, it is always contextualized within the Herbrand Universe in a spec, i.e., the
/// complete list of grounded atoms we want to quantify over. Then, during derivation, these are
/// shuffled around as we learn information about them. This lands you in a specific
/// _interpretation_ where all of them have a truth value assigned to them (true, false, or
/// unknown).
#[derive(Clone, Debug)]
pub struct KnowledgeBase<'s, F, S>
where
    Atom<F, S>: Clone,
{
    /// The universe of things we iterate over. This is either collected constants from the State,
    /// or generated instantiations from the `vars`.
    universe: Vec<Cow<'s, Atom<F, S>>>,
    /// Which of the atoms in the universe are _true_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unknwns }.
    truths:   HashSet<usize>,
    /// Which of the atoms in the universe are _false_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unknwns }.
    falses:   HashSet<usize>,
    /// Which of the atoms in the universe are _unknown_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unkwns }.
    unkwns:   HashSet<usize>,
}

// Constructors
impl<'s, F, S> Default for KnowledgeBase<'s, F, S>
where
    Atom<F, S>: Clone,
{
    #[inline]
    fn default() -> Self { Self::new() }
}
impl<'s, F, S> KnowledgeBase<'s, F, S>
where
    Atom<F, S>: Clone,
{
    /// Constructor for the State that initializes it from the given spec.
    ///
    /// # Arguments
    /// - `spec`: Some [`Spec<'s, F, S>`] to interpret.
    ///
    /// # Returns
    /// A new State that is initialized to the universe of possible atoms read from the spec.
    ///
    /// Note that ALL atoms are assumed to be _false_ initially.
    pub fn new() -> Self { Self { universe: Vec::new(), truths: HashSet::new(), falses: HashSet::new(), unkwns: HashSet::new() } }
}

// Reasoning
impl<'s, F, S> KnowledgeBase<'s, F, S>
where
    Atom<F, S>: Clone,
    Ident<F, S>: Eq + Hash,
    SafeRule<Atom<F, S>>: Clone,
    Span<F, S>: Clone,
{
    /// Updates the knowledge base with the consequents of the given rule if the rule's antecedents
    /// hold.
    ///
    /// Note that this function does concretizing of it for you. Pretty convenient, eh?
    ///
    /// # Arguments
    /// - `rule`: Some rule to potentially concretize and potentially apply.
    pub fn update(&mut self, rule: &'s SafeRule<Atom<F, S>>) {
        // Concretize the rule first using the atoms that are true.
        for rule in rule.quantify(self.truths.iter().map(|i| self.universe[*i].as_ref())) {}
    }
}
