//  KNOLWEDGE BASE.rs
//    by Lut99
//
//  Created:
//    03 Feb 2025, 17:11:26
//  Last edited:
//    10 Feb 2025, 17:16:11
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

use std::collections::HashSet;
use std::hash::{DefaultHasher, Hash, Hasher};

use better_derive::{Clone, Debug};

use crate::ir::{Atom, GroundAtom, Rule, Span};


/***** LIBRARY *****/
/// Defines the state during derivation.
///
/// Specifically, it is always contextualized within the Herbrand Universe in a spec, i.e., the
/// complete list of grounded atoms we want to quantify over. Then, during derivation, these are
/// shuffled around as we learn information about them. This lands you in a specific
/// _interpretation_ where all of them have a truth value assigned to them (true, false, or
/// unknown).
#[derive(Clone, Debug)]
pub struct KnowledgeBase<F, S> {
    /// The universe of things we iterate over. This is either collected constants from the State,
    /// or generated instantiations from the `vars`.
    universe: Vec<GroundAtom<F, S>>,
    /// Which of the atoms in the universe are _true_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unknwns }.
    truths:   HashSet<usize>,
    /// Which of the atoms in the universe are _unknown_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unkwns }.
    unkwns:   HashSet<usize>,

    /// An auxillary cache to speed up writing updates during derivation.
    updates: HashSet<GroundAtom<F, S>>,
}

// Constructors
impl<F, S> Default for KnowledgeBase<F, S> {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl<F, S> KnowledgeBase<F, S> {
    /// Constructor for the State that initializes it from the given spec.
    ///
    /// # Arguments
    /// - `spec`: Some [`Spec<'s, F, S>`] to interpret.
    ///
    /// # Returns
    /// A new State that is initialized to the universe of possible atoms read from the spec.
    ///
    /// Note that ALL atoms are assumed to be _false_ initially.
    pub fn new() -> Self { Self { universe: Vec::new(), truths: HashSet::new(), unkwns: HashSet::new(), updates: HashSet::new() } }
}

// Hashing
impl<F, S> KnowledgeBase<F, S>
where
    Span<F, S>: Hash,
{
    /// Returns a hash of the knowledge base.
    ///
    /// # Returns
    /// A [`u64`] hash.
    #[inline]
    pub fn hash(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        <Self as Hash>::hash(self, &mut hasher);
        hasher.finish()
    }
}
impl<F, S> Eq for KnowledgeBase<F, S> where Span<F, S>: PartialEq {}
impl<F, S> Hash for KnowledgeBase<F, S>
where
    Span<F, S>: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        for (i, atom) in self.universe.iter().enumerate() {
            atom.hash(state);
            if self.truths.contains(&i) {
                Some(true).hash(state);
            } else if self.unkwns.contains(&i) {
                None::<bool>.hash(state);
            } else {
                Some(false).hash(state);
            }
        }
    }
}
impl<F, S> PartialEq for KnowledgeBase<F, S>
where
    Span<F, S>: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.universe.eq(&other.universe) && self.truths.eq(&other.truths) && self.unkwns.eq(&other.unkwns) }
}

// Reasoning
impl<F, S> KnowledgeBase<F, S>
where
    Span<F, S>: Clone + Eq + Hash,
{
    /// Updates the knowledge base with the consequents of the given rule if the rule's antecedents
    /// hold.
    ///
    /// Note that this function does concretizing of it for you. Pretty convenient, eh?
    ///
    /// # Arguments
    /// - `rule`: Some rule to potentially concretize and potentially apply.
    ///
    /// # Returns
    /// Whether any update of the knowledge base has occurred.
    pub fn update(&mut self, rule: &Rule<Atom<F, S>>) -> bool {
        let Self { universe, truths, unkwns, updates } = self;

        // Concretize the rule first using the atoms that are true.
        'rule: for rule in rule.concretize_for(truths.iter().map(|i| &universe[*i])) {
            // Check if the rule's positive antecedents exist as true atoms
            for atom in &rule.pos_antecedents {
                // See if this atom exists in the knowledge base
                if let Some(idx) = universe.iter().enumerate().find_map(|(i, a)| if atom == a { Some(i) } else { None }) {
                    // It does; is it also true?
                    if !truths.contains(&idx) {
                        continue 'rule;
                    }
                } else {
                    continue 'rule;
                }
            }

            // Then check if all the rule's negative antecedents exist as false atoms
            for atom in &rule.neg_antecedents {
                // See if this atom exists in the knowledge base
                if let Some(idx) = universe.iter().enumerate().find_map(|(i, a)| if atom == a { Some(i) } else { None }) {
                    // It does; is it also false?
                    if truths.contains(&idx) || unkwns.contains(&idx) {
                        continue 'rule;
                    }
                } else {
                    continue 'rule;
                }
            }

            // So far so good: we derive the consequents
            updates.extend(rule.consequents.iter().cloned());
        }

        // Apply the updates
        let updated: bool = !updates.is_empty();
        for atom in updates.drain() {
            if let Some(idx) = universe.iter().enumerate().find_map(|(i, a)| if &atom == a { Some(i) } else { None }) {
                // It already exists; add it to the truths set
                truths.insert(idx);
            } else {
                // It didn't already exist; add it to the universe and then define it
                truths.insert(universe.len());
                if universe.len() + 1 > universe.capacity() {
                    universe.reserve(2 * universe.capacity());
                }
                universe.push(atom);
            }
        }
        updated
    }

    /// Applies the stable transformation to the knowledge base; i.e., assumes that everything not
    /// derived is false.
    pub fn apply_stable_transformation(&mut self) {
        // For us, if I'm right, all we have to do is move all the truths to unknowns.
        // By virtue of anything in the universe which isn't in truth, this will cause everything
        // not derived to become false.
        self.unkwns.clear();
        self.unkwns.extend(self.truths.drain());
    }
}

// Collection
impl<F, S> KnowledgeBase<F, S> {
    /// Clears the knowledge base, resetting it to start but keeping the memory around.
    #[inline]
    pub fn clear(&mut self) {
        self.universe.clear();
        self.truths.clear();
        self.unkwns.clear();
    }



    /// Returns whether there is any fact in this knowledge base.
    ///
    /// # Returns
    /// True if the universe is empty, or false otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Returns the number of facts in this knowledge base's universe.
    ///
    /// # Returns
    /// Yep.
    #[inline]
    pub fn len(&self) -> usize { self.universe.len() }
}
