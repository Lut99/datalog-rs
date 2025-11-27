//  KNOLWEDGE BASE.rs
//    by Lut99
//
//  Created:
//    03 Feb 2025, 17:11:26
//  Last edited:
//    13 Feb 2025, 15:44:57
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

use std::collections::BTreeSet;
use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{DefaultHasher, Hash, Hasher};

use ast_toolkit::span::SpannableBytes;
use better_derive::{Clone, Debug};

use crate::ir::GroundAtom;


/***** HELPERS *****/
/// Defines a struct that complements a given set.
///
/// That is, any membership test on this set is inverted. As a result, it effectively implements a
/// "lazy" complement over it.
///
/// Note that, due to the lazy functionality, the set is not iterable.
#[derive(Clone, Debug)]
struct ComplementedSet<T> {
    /// The things we're complementing.
    set: BTreeSet<T>,
    /// Whether this set is empty.
    ///
    /// We could've made this an enum, but now we keep the memory around.
    complements_the_whole_universe: bool,
}

// Constructors
impl<T> Default for ComplementedSet<T> {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl<T> ComplementedSet<T> {
    /// Creates a new ComplementedSet that contains nothing.
    ///
    /// To make the magic happen, call [`ComplementedSet::complement()`].
    ///
    /// # Returns
    /// A new ComplementedSet that complements the whole of the universe (resulting in an empty
    /// set).
    #[inline]
    pub fn new() -> Self { Self { set: BTreeSet::new(), complements_the_whole_universe: true } }
}

// Standard traits
impl<T: Ord> Eq for ComplementedSet<T> {}
impl<T: Hash + Ord> Hash for ComplementedSet<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Because the order is deterministic, we can actually do this!
        for elem in &self.set {
            elem.hash(state)
        }
    }
}
impl<T: Ord> PartialEq for ComplementedSet<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.set.eq(&other.set) && self.complements_the_whole_universe.eq(&other.complements_the_whole_universe) }
}

// Collection
impl<T> ComplementedSet<T> {
    /// Clears the contents of this set, reversing it to a set which contains EVERYTHING.
    #[inline]
    pub fn clear(&mut self) {
        self.set.clear();
        self.complements_the_whole_universe = true;
    }
}
impl<T> ComplementedSet<T>
where
    T: Ord,
{
    /// Replaces the contents of the set with the complements of the given ones.
    ///
    /// Note that membership tests are inverted over this set. I.e., the elements are
    /// describing what is _not_ in the set.
    ///
    /// # Arguments
    /// - `elems`: The elements to NOT set this set's contents to.
    #[inline]
    pub fn complement(&mut self, elems: impl IntoIterator<Item = T>) {
        self.set.clear();
        self.set.extend(elems);
        self.complements_the_whole_universe = false;
    }



    /// Checks whether the given element exists in this set.
    ///
    /// # Arguments
    /// - `elem`: The element to check for membership.
    ///
    /// # Returns
    /// True if the element is a member in this set, or false otherwise.
    #[inline]
    pub fn contains(&self, elem: &T) -> bool { if self.complements_the_whole_universe { false } else { !self.set.contains(elem) } }

    /// Checks whether this set is empty.
    ///
    /// By that we mean really empty, not taking the complement of empty. In other words, checks if
    /// we're taking the complement of everything.
    ///
    /// # Returns
    /// True if no element is a member of this set, or false otherwise.
    #[inline]
    pub const fn is_empty(&self) -> bool { self.complements_the_whole_universe }
}
impl<T> ComplementedSet<T> {
    /// We said this set isn't iterable, but you know what, we are still interested in iterating
    /// the _complement_ of this complemented set (i.e., the original one).
    ///
    /// Note that the ComplementedSet implements [`Hash`] and, as such, this iteration yields a
    /// deterministic order (that of insertion).
    ///
    /// # Returns
    /// An [`Iterator`] over the original / complement-of-complement set.
    ///
    /// # Panics
    /// This set panics if [`ComplementedSet::complement()`] has never been called (or hasn't been
    /// called after [`ComplementedSet::clear()`]).
    ///
    /// This because the cases described above represent a set that complements everything. That's
    /// infinite, and hence, not iterable.
    ///
    /// You can check if a panic would occur by seeing if [`ComplementedSet::is_empty()`] returns
    /// true.
    #[inline]
    #[track_caller]
    pub fn iter_complement<'s>(&'s self) -> impl 's + Iterator<Item = &'s T> {
        if self.complements_the_whole_universe {
            panic!("Cannot iterate the complement of a ComplementedSet that complements the whole universe");
        }
        self.set.iter()
    }
}





/***** LIBRARY *****/
/// Defines what has been derived how.
///
/// This KnowledgeBase is created for the alternating fixpoint semantics, where we assume a
/// _stable transformation_ that will assume the negated complement of anything derived up to that
/// point.
///
/// To realize this, it defines two sets:
/// - A set of _truths_, which are atoms we derived as true; and
/// - A set of _negated assumptions_, which are atoms we assume as false.
///
/// The latter cases uses a special implementation trick to avoid instantiating the Herbrand
/// universe: we wrap it in a `Complement`-enum, which does this negated complement trick lazily
/// (i.e., only at query time instead of quantification time).
#[derive(Clone, Debug)]
pub struct KnowledgeBase<S> {
    /// Defines derived atoms.
    truths:      BTreeSet<GroundAtom<S>>,
    /// Defines assumed _negated_ atoms.
    ///
    /// This is the other half of `pos_truths`, which behaves exactly the same except that you
    /// should imagine a `not` in front of all of them.
    assumptions: ComplementedSet<GroundAtom<S>>,
}

// Constructors
impl<S> Default for KnowledgeBase<S> {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl<S> KnowledgeBase<S> {
    /// Constructor for the State that initializes it from the given spec.
    ///
    /// # Arguments
    /// - `spec`: Some [`Spec<'s, S>`] to interpret.
    ///
    /// # Returns
    /// A new State that is initialized to the universe of possible atoms read from the spec.
    ///
    /// Note that ALL atoms are assumed to be _false_ initially.
    pub fn new() -> Self { Self { truths: BTreeSet::new(), assumptions: ComplementedSet::new() } }
}

// Hashing
impl<'s, S: SpannableBytes<'s>> KnowledgeBase<S> {
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
impl<'s, S: SpannableBytes<'s>> Eq for KnowledgeBase<S> {}
impl<'s, S: SpannableBytes<'s>> Hash for KnowledgeBase<S> {
    #[inline]
    #[track_caller]
    fn hash<H: Hasher>(&self, state: &mut H) {
        for atom in &self.truths {
            // Hash `true` to disambiguate an equivalent complemented set
            2.hash(state);
            atom.hash(state);
        }
        if !self.assumptions.is_empty() {
            for atom in self.assumptions.iter_complement() {
                // Hash `true` to disambiguate an equivalent truth set
                1.hash(state);
                atom.hash(state);
            }
        } else {
            0.hash(state);
        }
    }
}
impl<'s, S: SpannableBytes<'s>> PartialEq for KnowledgeBase<S> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.truths.eq(&other.truths) && self.assumptions.eq(&other.assumptions) }
}

// Reasoning
impl<'s, S: SpannableBytes<'s>> KnowledgeBase<S> {
    /// Updates the knowledge base with a new fact to learn.
    ///
    /// # Arguments
    /// - `atom`: Some [`GroundAtom`] to learn that it is TRUE.
    ///
    /// # Returns
    /// Whether anything has actually changed.
    pub fn learn(&mut self, atom: GroundAtom<S>) -> bool { self.truths.insert(atom) }

    /// Applies the stable transformation to the knowledge base; i.e., assumes that everything not
    /// derived is false.
    pub fn apply_stable_transformation(&mut self) {
        // With the new complemented set this is actually super-duper easy!
        let mut truths: BTreeSet<GroundAtom<S>> = BTreeSet::new();
        std::mem::swap(&mut truths, &mut self.truths);
        self.assumptions.complement(truths.into_iter());
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
    pub fn holds(&self, is_pos: bool, atom: &GroundAtom<S>) -> bool {
        if is_pos { self.truths.contains(atom) } else { self.assumptions.contains(atom) }
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
    pub fn closed_world_truth(&self, atom: &GroundAtom<S>) -> Option<bool> {
        // Now find the assigned truth value
        if self.truths.contains(atom) {
            Some(true)
        } else if self.assumptions.contains(atom) {
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
    pub fn truths<'kb>(&'kb self) -> impl 'kb + Clone + ExactSizeIterator + Iterator<Item = &'kb GroundAtom<S>> { self.truths.iter() }
}

// Collection
impl<S> KnowledgeBase<S> {
    /// Clears the knowledge base, resetting it to start but keeping the memory around.
    #[inline]
    pub fn reset(&mut self) {
        self.truths.clear();
        self.assumptions.clear();
    }
}

// Formatting
impl<'s, S> Display for KnowledgeBase<S>
where
    S: SpannableBytes<'s>,
{
    #[inline]
    #[track_caller]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        // Write 'em
        writeln!(f, "Knowledge base {{")?;
        write!(f, "    true:")?;
        if !self.truths.is_empty() {
            writeln!(f)?;
            for atom in &self.truths {
                writeln!(f, "      + {atom}")?;
            }
        } else {
            writeln!(f, " <none>")?;
        }
        write!(f, "    unknown:")?;
        let mut first: bool = true;
        if !self.assumptions.is_empty() {
            for atom in self.assumptions.iter_complement().filter(|a| !self.truths.contains(*a)) {
                if first {
                    writeln!(f)?;
                    first = false;
                }
                writeln!(f, "      ? {atom}")?;
            }
            if first {
                writeln!(f, " <none>")?;
            }
        } else {
            writeln!(f, " <none>")?;
        }
        writeln!(f, "}}")
    }
}
