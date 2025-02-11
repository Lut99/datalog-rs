//  KNOLWEDGE BASE.rs
//    by Lut99
//
//  Created:
//    03 Feb 2025, 17:11:26
//  Last edited:
//    11 Feb 2025, 16:02:20
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

use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{DefaultHasher, Hash, Hasher};

use ast_toolkit::span::{Spannable, SpannableDisplay};
use better_derive::{Clone, Debug};
use indexmap::IndexSet;

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
    universe:    IndexSet<GroundAtom<F, S>>,
    /// Defines derived atoms.
    pos_truths:  HashSet<usize>,
    /// Defines derived _negated_ atoms.
    ///
    /// This is the other half of `pos_truths`, which behaves exactly the same except that you
    /// should imagine a `not` in front of all of them.
    neg_truths:  HashSet<usize>,
    /// A temporary overflow set when swapping `pos_truths` and `neg_truths`.
    swap_buffer: Vec<usize>,
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
    pub fn new() -> Self { Self { universe: IndexSet::new(), pos_truths: HashSet::new(), neg_truths: HashSet::new(), swap_buffer: Vec::new() } }
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
impl<F, S> Eq for KnowledgeBase<F, S> where Span<F, S>: Eq + Hash {}
impl<F, S> Hash for KnowledgeBase<F, S>
where
    Span<F, S>: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        for (i, atom) in self.universe.iter().enumerate() {
            atom.hash(state);
            if self.pos_truths.contains(&i) {
                Some(true).hash(state);
            }
            if self.neg_truths.contains(&i) {
                Some(false).hash(state);
            }
            if !self.pos_truths.contains(&i) && !self.neg_truths.contains(&i) {
                None::<bool>.hash(state);
            }
        }
    }
}
impl<F, S> PartialEq for KnowledgeBase<F, S>
where
    Span<F, S>: Eq + Hash,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.universe.eq(&other.universe) && self.pos_truths.eq(&other.pos_truths) && self.neg_truths.eq(&other.neg_truths)
    }
}

// Reasoning
impl<F, S> KnowledgeBase<F, S>
where
    Span<F, S>: Eq + Hash,
{
    /// Updates the knowledge base with a new fact to learn.
    ///
    /// # Arguments
    /// - `atom`: Some [`GroundAtom`] to learn that it is TRUE.
    ///
    /// # Returns
    /// Whether anything has actually changed.
    pub fn learn(&mut self, atom: GroundAtom<F, S>) -> bool {
        // Insert it if it doesn't exist
        let idx: usize = if let Some(idx) = self.universe.get_index_of(&atom) {
            idx
        } else {
            let idx: usize = self.universe.len();
            self.universe.insert(atom);
            idx
        };

        // Update the truth
        self.pos_truths.insert(idx)
    }

    /// Applies the stable transformation to the knowledge base; i.e., assumes that everything not
    /// derived is false.
    pub fn apply_stable_transformation(&mut self) {
        // // For us, if I'm right, all we have to do is move all the truths to unknowns.
        // // By virtue of anything in the universe which isn't in truth, this will cause everything
        // // not derived to become false.
        // self.falses.clear();
        // self.falses.extend((0..self.universe.len()).filter(|i| !self.truths.contains(&i)));
        // self.truths.clear();

        // We take the complement of everything we've derived and put that in the false-set
        self.swap_buffer.extend((0..self.universe.len()).filter(|i| !self.pos_truths.contains(i)));
        self.pos_truths.clear();
        self.neg_truths.clear();
        self.neg_truths.extend(self.swap_buffer.drain(..));
    }



    /// Checks whether the given fact is TRUE in this knowledge base.
    ///
    /// Note that this is slightly different from [`KnowledgeBase::closed_world_truth()`] because
    /// the latter can only give a single answer, even though it may be derived that a fact is true
    /// _and_ false at the same time in certain steps of the algorithm.
    ///
    /// # Arguments
    /// - `is_pos`: Whether to take the atom as-is (true) or imagine a negation in front of it (false).
    /// - `atom`: Some [`GroundAtom`] to find the truth of.
    ///
    /// # Returns
    /// True if the given fact is true, or false otherwise.
    #[inline]
    pub fn holds(&self, is_pos: bool, atom: &GroundAtom<F, S>) -> bool {
        // See if we know about the atom
        let idx: usize = match self.universe.get_index_of(atom) {
            Some(idx) => idx,
            None => return false,
        };
        if is_pos { self.pos_truths.contains(&idx) } else { self.neg_truths.contains(&idx) }
    }

    /// Returns what this knowledge base knows about the given fact.
    ///
    /// # Arguments
    /// - `atom`: Some [`GroundAtom`] to find the truth of.
    ///
    /// # Returns
    /// This function returns:
    /// - [`Some(true)`] if we know the fact to be true;
    /// - [`Some(false)`] if we neither know it to be true or unknown; or
    /// - [`None`] if we know it to be unknown (e.g., underivable).
    pub fn closed_world_truth(&self, atom: &GroundAtom<F, S>) -> Option<bool> {
        // See if we know about the atom
        let idx: usize = match self.universe.get_index_of(atom) {
            Some(idx) => idx,
            None => return Some(false),
        };

        // Now find the assigned truth value
        if self.pos_truths.contains(&idx) {
            Some(true)
        } else if self.neg_truths.contains(&idx) {
            Some(false)
        } else {
            None
        }
    }

    /// Returns an iterator over all the true ground atoms.
    ///
    /// # Returns
    /// An [`Iterator`] over (references to) [`GroundAtom`]s.
    #[inline]
    pub fn truths<'s>(&'s self) -> impl 's + Clone + ExactSizeIterator + Iterator<Item = &'s GroundAtom<F, S>> {
        self.pos_truths.iter().map(|i| &self.universe[*i])
    }
}
impl<F, S> KnowledgeBase<F, S>
where
    Span<F, S>: Clone + Eq + Hash,
{
    /// Extends the universe of the knowledge base with constants in the given rule.
    ///
    /// This is necessary because we are looking for explicit cases of negation. If we don't know
    /// about atoms that aren't derived, we won't learn that they are false (even when not
    /// quantified).
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] (over [`Atom`]s) to scan for constants.
    pub fn extend_universe_with_rule(&mut self, rule: &Rule<Atom<F, S>>) {
        /// Recursively adds a grounded atom to the universe
        fn extend_universe_with_ground_atom<F, S>(universe: &mut IndexSet<GroundAtom<F, S>>, atom: GroundAtom<F, S>)
        where
            Span<F, S>: Clone + Eq + Hash,
        {
            // We'll recurse first
            for arg in &atom.args {
                extend_universe_with_ground_atom(universe, arg.clone());
            }
            universe.insert(atom);
        }

        // Add all atoms if they are grounded
        for atom in rule.atoms() {
            if let Some(atom) = atom.to_ground_atom() {
                extend_universe_with_ground_atom(&mut self.universe, atom);
            }
        }
    }
}

// Collection
impl<F, S> KnowledgeBase<F, S> {
    /// Clears the knowledge base, resetting it to start but keeping the memory around.
    #[inline]
    pub fn clear(&mut self) {
        self.universe.clear();
        self.pos_truths.clear();
        self.neg_truths.clear();
    }
}

// Formatting
impl<F, S> Display for KnowledgeBase<F, S>
where
    S: Spannable + SpannableDisplay,
    for<'s> S::Slice<'s>: Ord,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        /// Sorts two ground atoms, first by identifier, then arity, and finally argument order
        fn atom_sort<F, S>(lhs: &&GroundAtom<F, S>, rhs: &&GroundAtom<F, S>) -> Ordering
        where
            S: Spannable,
            for<'s> S::Slice<'s>: Ord,
        {
            lhs.ident.value.value().cmp(&rhs.ident.value.value()).then_with(|| lhs.args.len().cmp(&rhs.args.len())).then_with(|| {
                lhs.args
                    .iter()
                    .zip(rhs.args.iter())
                    .find_map(|(lhs, rhs)| {
                        let ord = atom_sort(&lhs, &rhs);
                        if !ord.is_eq() { Some(ord) } else { None }
                    })
                    .unwrap_or(Ordering::Equal)
            })
        }

        // Create three sorted lists of atoms
        let mut pos_truths: Vec<&GroundAtom<F, S>> =
            self.universe.iter().enumerate().filter_map(|(i, a)| if self.pos_truths.contains(&i) { Some(a) } else { None }).collect();
        let mut neg_truths: Vec<&GroundAtom<F, S>> =
            self.universe.iter().enumerate().filter_map(|(i, a)| if self.neg_truths.contains(&i) { Some(a) } else { None }).collect();
        let mut unkwns: Vec<&GroundAtom<F, S>> = self
            .universe
            .iter()
            .enumerate()
            .filter_map(|(i, a)| if !self.pos_truths.contains(&i) && !self.neg_truths.contains(&i) { Some(a) } else { None })
            .collect();
        pos_truths.sort_by(atom_sort::<F, S>);
        neg_truths.sort_by(atom_sort::<F, S>);
        unkwns.sort_by(atom_sort::<F, S>);

        // Write 'em
        writeln!(f, "Knowledge base {{")?;
        write!(f, "    true:")?;
        if !pos_truths.is_empty() || !neg_truths.is_empty() {
            writeln!(f)?;
            for atom in pos_truths {
                writeln!(f, "      + {atom}")?;
            }
            for atom in neg_truths {
                writeln!(f, "      + not {atom}")?;
            }
        } else {
            writeln!(f, " <none>")?;
        }
        write!(f, "    unknown:")?;
        if !unkwns.is_empty() {
            writeln!(f)?;
            for atom in unkwns {
                writeln!(f, "      ? {atom}")?;
            }
        } else {
            writeln!(f, " <none>")?;
        }
        writeln!(f, "}}")
    }
}
