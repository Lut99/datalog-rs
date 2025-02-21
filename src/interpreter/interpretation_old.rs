//  INTERPRETATION.rs
//    by Lut99
//
//  Created:
//    21 Mar 2024, 10:22:40
//  Last edited:
//    04 Feb 2025, 18:05:19
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines how an interpretation $I$ looks like as given in [1].
//

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::{BuildHasher, DefaultHasher, Hash as _, Hasher, RandomState};

use indexmap::IndexSet;

use super::quantify::RuleQuantifier;
use crate::ast::{Atom, Ident, Literal, NegAtom, Rule, Spec};
use crate::log::warn;


/***** TESTS *****/
#[cfg(all(test, feature = "macros"))]
mod tests {
    use datalog_macros::datalog;

    use super::*;
    use crate::tests::make_atom;


    #[test]
    fn test_interpretation_from_universe_empty() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Empty spec first
        let empty: Spec<_, _> = datalog! {
            #![crate]
        };
        let int: Interpretation = Interpretation::from_universe(&empty);
        assert!(int.is_empty());
    }

    #[test]
    fn test_interpretation_from_universe_constant_single() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Spec with only constants (one, first)
        let one: Spec<_, _> = datalog! {
            #![crate]
            foo.
        };
        let int: Interpretation = Interpretation::from_universe(&one);
        assert_eq!(int.len(), 1);
        assert_eq!(int.closed_world_truth(&make_atom("foo", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("bar", [])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("baz", [])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("bingo", ["boingo"])), Some(false));
    }

    #[test]
    fn test_interpretation_from_universe_constant_multi() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Multiple constants
        let consts: Spec<_, _> = datalog! {
            #![crate]
            foo. bar. baz.
        };
        let int: Interpretation = Interpretation::from_universe(&consts);
        assert_eq!(int.len(), 3);
        assert_eq!(int.closed_world_truth(&make_atom("foo", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("bar", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("baz", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("bingo", ["boingo"])), Some(false));
    }

    #[test]
    fn test_interpretation_from_universe_constant_duplicate() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Duplicate constants
        let dups: Spec<_, _> = datalog! {
            #![crate]
            foo. foo. bar.
        };
        let int: Interpretation = Interpretation::from_universe(&dups);
        assert_eq!(int.len(), 2);
        assert_eq!(int.closed_world_truth(&make_atom("foo", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("bar", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("baz", [])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("bingo", ["boingo"])), Some(false));
    }

    #[test]
    fn test_interpretation_from_universe_arity_1() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Spec with arity-1 atoms (functions)
        let funcs: Spec<_, _> = datalog! {
            #![crate]
            foo(bar). bar(baz). baz(quz).
        };
        let int: Interpretation = Interpretation::from_universe(&funcs);
        assert_eq!(int.len(), 3);
        assert_eq!(int.closed_world_truth(&make_atom("foo", [])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("bar", [])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("baz", ["quz"])), None);
        assert_eq!(int.closed_world_truth(&make_atom("quz", ["qux", "quux"])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("corge", ["grault", "garply", "waldo"])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("foo", ["bar"])), None);
        assert_eq!(int.closed_world_truth(&make_atom("bar", ["baz"])), None);
        assert_eq!(int.closed_world_truth(&make_atom("bingo", ["boingo"])), Some(false));
    }

    #[test]
    fn test_interpretation_from_universe_arity_mixed() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Mixed arity
        let arity: Spec<_, _> = datalog! {
            #![crate]
            foo. bar(). baz(quz). quz(qux, quux). corge(grault, garply, waldo).
        };
        let int: Interpretation = Interpretation::from_universe(&arity);
        assert_eq!(int.len(), 5);
        assert_eq!(int.closed_world_truth(&make_atom("foo", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("bar", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("baz", ["quz"])), None);
        assert_eq!(int.closed_world_truth(&make_atom("quz", ["qux", "quux"])), None);
        assert_eq!(int.closed_world_truth(&make_atom("corge", ["grault", "garply", "waldo"])), None);
        assert_eq!(int.closed_world_truth(&make_atom("foo", ["bar"])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("bar", ["baz"])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("bingo", ["boingo"])), Some(false));
    }

    #[test]
    fn test_interpretation_from_universe_full() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Full rules
        let rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar(baz). quz(X) :- bar(X), qux(quux).
        };
        let int: Interpretation = Interpretation::from_universe(&rules);
        println!("{int}");
        assert_eq!(int.len(), 3);
        assert_eq!(int.closed_world_truth(&make_atom("foo", [])), None);
        assert_eq!(int.closed_world_truth(&make_atom("bar", ["foo"])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("bar", ["baz"])), None);
        assert_eq!(int.closed_world_truth(&make_atom("quz", ["foo"])), None);
        assert_eq!(int.closed_world_truth(&make_atom("quz", ["baz"])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("qux", ["quux"])), Some(false));
        assert_eq!(int.closed_world_truth(&make_atom("bingo", ["boingo"])), Some(false));
    }
}





/***** CONSTANTS *****/
/// Defines the maximum amount of _variables_ that a consequent can have.
pub const STACK_VEC_LEN: usize = 16;





/***** LIBRARY *****/
/// Defines a set of values in the logical sense.
///
/// # Usage
/// The Interpretation is meant to be used in the well-founded semantics, where it represents a total set of atoms that can be derived from a spec.
///
/// These atoms can have one of two states:
/// - They are _known_, and have a particular truth value; or
/// - They are _unknown_, meaning we have inconclusive evidence to even assume either way.
///
/// An important assumption is that this Interpretation assigns a global truth value to _all_ its _known_ atoms.
/// This is possible because $Datalog^\neg$ cannot derive negative facts, meaning that during immediate consequence reasoning, all newly derived
/// facts are true, and after the stable transformation, the complement of facts is false.
///
/// This assumption allows to us to compute the stable transformation super effectively, as it simply swaps the known and unknown sets to find the
/// complement, and negates the global truth to compute the per-fact negation.
///
/// The purpose of the immediate consequence operator is then to shuffle facts from unknown to known.
#[derive(Debug, Clone)]
pub struct Interpretation<'f, 's, R = RandomState> {
    /// The atoms stored in this set that we know (or assume!) to be _true_.
    tknown:  HashSet<u64>,
    /// The atoms stored in this set that we know (or assume!) to be _false_.
    fknown:  HashSet<u64>,
    /// The elements in this set for which the truth value is ambigious or contradictory.
    unknown: HashSet<u64>,
    /// All definitions in the Interpretation.
    defs:    HashMap<u64, Atom<&'f str, &'s str>>,
    /// The random state used to compute hashes.
    state:   R,
}
impl<'f, 's, R: Default> Interpretation<'f, 's, R> {
    /// Constructor for the LogicalSet that initializes it as empty.
    ///
    /// # Returns
    /// An empty Interpretation.
    #[inline]
    pub fn new() -> Self {
        Self { tknown: HashSet::new(), fknown: HashSet::new(), unknown: HashSet::new(), defs: HashMap::new(), state: R::default() }
    }

    /// Constructor for the Interpretation that initializes it with the given capacity.
    ///
    /// # Arguments
    /// - `capacity`: The (minimum) number of elements for which this set has space before needing to re-allocate.
    ///
    /// # Returns
    /// An empty Interpretation with enough space for at least `capacity` elements.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            tknown:  HashSet::with_capacity(capacity),
            fknown:  HashSet::with_capacity(capacity),
            unknown: HashSet::with_capacity(capacity),
            defs:    HashMap::with_capacity(capacity),
            state:   R::default(),
        }
    }
}
impl<'f, 's, R: BuildHasher + Default> Interpretation<'f, 's, R> {
    /// Constructor for the Interpretation that initializes it with a universe of possible atoms from a given [`Spec`].
    ///
    /// # Arguments
    /// - `spec`: The [`Spec`] to find all possible atoms in. This is simply the _concretized_ version of all consequents, as these are the only ones that may be assigned truths.
    ///
    /// # Returns
    /// An Interpretation with a lot of unknown atoms in it.
    #[inline]
    pub fn from_universe(spec: &Spec<&'f str, &'s str>) -> Self {
        // Built an empty self first
        let mut res: Self = Self::new();
        res.extend_universe(&spec.rules);
        res
    }
}
impl<'f, 's, R: BuildHasher> Interpretation<'f, 's, R> {
    /// Constructor for the Interpretation that initializes it with the given hash state.
    ///
    /// # Arguments
    /// - `state`: The random state used for hashing to initialize the Interpretation with.
    ///
    /// # Returns
    /// An empty Interpretation with the given state for hashes.
    #[inline]
    pub fn with_state(state: R) -> Self {
        Self { tknown: HashSet::new(), fknown: HashSet::new(), unknown: HashSet::new(), defs: HashMap::new(), state }
    }

    /// Performs the stable transformation on the Interpretation.
    ///
    /// This is implemented as making all unknown atoms known and vice versa, and negating the truth of _all_ _newly_ known atoms (i.e., they will all be false if they were true and vice versa).
    #[inline]
    pub fn apply_stable_transformation(&mut self) {
        // Because we're doing the assumptions in-interpretation, and because $Datalog^\neg$ cannot derive negatives, we should first discard all negatives to remove the assumptions
        // Also, if both the assumption and a true counterpart are true, then definitely get rid of the assumption altogether
        self.unknown.extend(self.fknown.drain().filter(|h| !self.tknown.contains(&h)));

        // Then we move the unknowns to false...
        std::mem::swap(&mut self.fknown, &mut self.unknown);
        // ...and the trues to unknown to complete the negated complemented
        std::mem::swap(&mut self.unknown, &mut self.tknown);
    }

    /// Removes all knowledge in the interpretation. Sad :'(.
    ///
    /// Note that this _also_ resets the truth of atoms to `true`.
    ///
    /// This does not change the capacity of the interpretation.
    #[inline]
    pub fn clear(&mut self) {
        self.tknown.clear();
        self.fknown.clear();
        self.unknown.clear();
        self.defs.clear();
    }

    /// Returns whether the universe exists.
    ///
    /// # Returns
    /// True if we know that at least one fact is either known or unknown.
    #[inline]
    pub fn is_empty(&self) -> bool { self.defs.is_empty() }

    /// Returns the number of facts in the universe.
    ///
    /// I.e., this is the number of facts we know _and_ don't know.
    ///
    /// # Returns
    /// The number of atoms in this Interpretation.
    #[inline]
    pub fn len(&self) -> usize { self.defs.len() }

    /// Computes some hash of this interpretation.
    ///
    /// This is computed using some general [`Hasher`] that does not rely on the internal random state of the Interpretation.
    /// This allows this hash to be compared between specific instances. Thus, can be used to check if two instances are the same.
    ///
    /// # Returns
    /// A [`u64`] representing a hash of this interpretation.
    #[inline]
    pub fn hash(&self) -> u64 {
        let mut state: DefaultHasher = DefaultHasher::new();

        // Get a predictable order on the known keys (in case the hasher is not cummatative), then hash them
        let mut keys: Vec<u64> = self.tknown.iter().cloned().collect();
        keys.sort();
        for key in &keys {
            // Write it's true
            state.write_u8(2);
            state.write_u64(*key);
        }

        // Do the same for false knowns
        keys.clear();
        keys.extend(self.fknown.iter().cloned());
        keys.sort();
        for key in &keys {
            // Write it's false
            state.write_u8(1);
            state.write_u64(*key);
        }

        // And finally the unknowns
        keys.clear();
        keys.extend(self.unknown.iter().cloned());
        keys.sort();
        for key in &keys {
            // Write it's unknown
            state.write_u8(0);
            state.write_u64(*key);
        }

        // Done
        state.finish()
    }

    /// Returns all [`Atom`]s without arguments in existance.
    ///
    /// This means both known _and_ unknown constants are returned.
    ///
    /// # Returns
    /// An [`IndexSet`] that can be used to generate, say, [`VarQuantifier`]s.
    #[inline]
    pub fn find_existing_consts(&self) -> IndexSet<Ident<&'f str, &'s str>> {
        let mut consts: IndexSet<Ident<&'f str, &'s str>> = IndexSet::new();
        for atom in self.defs.values() {
            if atom.args.as_ref().map(|a| a.args.len()).unwrap_or(0) == 0 {
                consts.insert(atom.ident);
            }
        }
        consts
    }
}
impl<'f, 's, R: BuildHasher> Interpretation<'f, 's, R> {
    /// Computes the hash of the given atom.
    ///
    /// This is used internally but exposed for completeness.
    ///
    /// # Arguments
    /// - `atom`: The [`Atom`] to compute the hash of.
    ///
    /// # Returns
    /// Some [`u64`] encoding the `atom`'s hash.
    #[inline]
    pub fn hash_atom(&self, atom: &Atom<&'f str, &'s str>) -> u64 {
        let mut state: R::Hasher = self.state.build_hasher();

        // Hash the identifier, then all arguments
        atom.ident.value.value().hash(&mut state);
        for arg in atom.args.iter().flat_map(|a| a.args.values()) {
            // Warn if it's a var
            if matches!(arg, Atom::Var(_)) {
                warn!("Hashing an `Atom::Var` (this is probably unintended)");
            }

            // Hash the AtomArg
            arg.hash(&mut state);
        }

        // Done
        state.finish()
    }

    // /// Computes the hash of the given atom that has an external assignment.
    // ///
    // /// This is exposed to be useful for [`Self::truth_of_lit_by_hash()`](Interpretation::truth_of_lit_by_hash()).
    // ///
    // /// # Arguments
    // /// - `atom`: The [`Atom`] to compute the hash of.
    // /// - `assign`: Some map that maps variables to their concrete values to hash.
    // ///
    // /// # Returns
    // /// Some [`u64`] encoding the atom's hash.
    // ///
    // /// # Panics
    // /// This function can panic if there is a variable in the `atom` that is not in the `assignment`.
    // #[inline]
    // #[track_caller]
    // pub fn hash_atom_with_assign(&self, atom: &Atom<&'f str, &'s str>, assign: &HashMap<Ident<&'f str, &'s str>, Ident<&'f str, &'s str>>) -> u64 {
    //     let mut state: R::Hasher = self.state.build_hasher();

    //     // Hash the identifier, then all arguments
    //     atom.ident.value.value().hash(&mut state);
    //     for arg in atom.args.iter().flat_map(|a| a.args.values()) {
    //         // If it's a variable, apply the assignment instead
    //         if let AtomArg::Var(v) = arg {
    //             AtomArg::Atom(*assign.get(v).unwrap_or_else(|| panic!("Found variable '{v}' in atom that was not in assignment"))).hash(&mut state);
    //             continue;
    //         }

    //         // Hash the AtomArg as-is
    //         arg.hash(&mut state);
    //     }

    //     // Done
    //     state.finish()
    // }

    /// Learns the truth value of a new atom.
    ///
    /// This promotes an _existing_ atom from the unknown list to the known list.
    ///
    /// # Arguments
    /// - `atom`: The [`Atom`] to add to the knowledge base.
    /// - `truth`: The truth value of the atom in question.
    ///
    /// # Returns
    /// Whether we already knew about this `atom` and, if so, what.
    ///
    /// # Panics
    /// This function can panic if the atom is not in the list of unknown truths.
    #[inline]
    #[track_caller]
    pub fn learn(&mut self, atom: &Atom<&'f str, &'s str>, truth: bool) -> Option<bool> {
        let hash: u64 = self.hash_atom(&atom);

        // Attempt to find the atom in the list of truths
        match self.unknown.remove(&hash) {
            true => {
                // For this one, can never already exist
                if truth {
                    self.tknown.insert(hash);
                    None
                } else {
                    self.fknown.insert(hash);
                    None
                }
            },
            false => {
                // NOTE: We don't _move_ the atom from false -> true and vice versa; we merely observe that it is _also_ true.
                if truth {
                    if self.tknown.contains(&hash) {
                        Some(true)
                    } else if self.fknown.contains(&hash) {
                        self.tknown.insert(hash);
                        Some(false)
                    } else {
                        panic!("Cannot learn anything about non-existing atom '{atom}'");
                    }
                } else {
                    if self.fknown.contains(&hash) {
                        Some(false)
                    } else if self.tknown.contains(&hash) {
                        self.fknown.insert(hash);
                        Some(true)
                    } else {
                        panic!("Cannot learn anything about non-existing atom '{atom}'");
                    }
                }
            },
        }
    }

    // /// Learns the truth value of a new atom with a custom assignment of its arguments.
    // ///
    // /// This promotes an _existing_ atom from the unknown list to the known list.
    // ///
    // /// # Arguments
    // /// - `atom`: Some atom, potentially with variables as arguments, to learn.
    // /// - `assign`: An assignment of values for the perhaps-existing variables in `atom`.
    // /// - `truth`: The truth value of the atom in question.
    // ///
    // /// # Returns
    // /// Whether we already knew about this `atom`.
    // ///
    // /// # Panics
    // /// This function can panic if the atom is not in the list of unknown truths, or if there was a variable in `atom` that was not in the `assign`ment.
    // #[inline]
    // #[track_caller]
    // pub fn learn_with_assign(
    //     &mut self,
    //     atom: &Atom<&'f str, &'s str>,
    //     assign: &HashMap<Ident<&'f str, &'s str>, Ident<&'f str, &'s str>>,
    //     truth: bool,
    // ) -> Option<bool> {
    //     let hash: u64 = self.hash_atom_with_assign(atom, assign);

    //     // Attempt to find the atom in the list of truths
    //     match self.unknown.remove(&hash) {
    //         true => {
    //             // For this one, can never already exist
    //             if truth {
    //                 self.tknown.insert(hash);
    //                 None
    //             } else {
    //                 self.fknown.insert(hash);
    //                 None
    //             }
    //         },
    //         false => {
    //             // NOTE: We don't _move_ the atom from false -> true and vice versa; we merely observe that it is _also_ true/false.
    //             if truth {
    //                 if self.tknown.contains(&hash) {
    //                     Some(true)
    //                 } else if self.fknown.contains(&hash) {
    //                     self.tknown.insert(hash);
    //                     Some(false)
    //                 } else {
    //                     panic!("Cannot learn anything about non-existing atom '{atom}'");
    //                 }
    //             } else {
    //                 if self.fknown.contains(&hash) {
    //                     Some(false)
    //                 } else if self.tknown.contains(&hash) {
    //                     self.fknown.insert(hash);
    //                     Some(true)
    //                 } else {
    //                     panic!("Cannot learn anything about non-existing atom '{atom}'");
    //                 }
    //             }
    //         },
    //     }
    // }

    /// Makes a new atom possible.
    ///
    /// Is is the method that truly "adds" an atom to the interpretation. This is necessary to define all atoms we might learn something about truth from.
    ///
    /// Note that the atom will begin life being unknown.
    ///
    /// # Arguments
    /// - `atom`: The [`Atom`] to add internally.
    ///
    /// # Returns
    /// True if we already considered this atom in the universe, or false otherwise.
    #[inline]
    pub fn insert(&mut self, atom: Atom<&'f str, &'s str>) -> bool {
        let hash: u64 = self.hash_atom(&atom);

        // Just to be sure, remove it from the true & false lists
        self.tknown.remove(&hash);
        self.fknown.remove(&hash);

        // Insert it into the unknown atoms, as that's how it starts, and then the defs
        self.unknown.insert(hash);
        self.defs.insert(hash, atom).is_some()
    }

    /// Populates the Interpretation with the Herbrand universe dictated by the given [`Spec`].
    ///
    /// Concretely, this will extend the `unknown` database with all _instantiated_ consequents of the rules in the spec.
    /// Here, instantiation means all possible substitutions of variables for all found consequent constants (i.e., atoms with arity 0).
    /// This sufficies for $Datalog^\neg$ because it cannot nest arguments.
    ///
    /// # Arguments
    /// - `rules`: The [`Rule`]s to populate this interpretation with.
    pub fn extend_universe<'r, I>(&mut self, rules: I)
    where
        'f: 'r,
        's: 'r,
        I: IntoIterator<Item = &'r Rule<&'f str, &'s str>>,
        I::IntoIter: Clone,
    {
        let rules = rules.into_iter();

        // First, find the Herbrand 0-base of the spec (i.e., constants only)
        let mut consts: IndexSet<Ident<&'f str, &'s str>> = IndexSet::new();
        for rule in rules.clone() {
            // Go over the consequences only (since these are the only ones that can be true)
            for cons in rule.consequents.values() {
                // Add the consequent if it has no arguments
                if cons.args.as_ref().map(|a| a.args.len()).unwrap_or(0) == 0 {
                    consts.insert(cons.ident);
                }
            }
        }

        // Then, go over the rules to instantiate any variables in the rules with the assignment
        // NOTE: Is an IndexMap to have predictable assignment order, nice for testing
        for rule in rules.flat_map(|r| RuleQuantifier::new(r, &consts)) {
            // Go over the consequences only... and _negative_ antecedents
            // The former represents the possible atoms that _can_ be true, the latter represents the things we may want to search for are false.
            for atom in rule.consequents.into_values().chain(rule.tail.into_iter().flat_map(|t| {
                t.antecedents.into_values().filter_map(|a| match a {
                    Literal::Atom(_) => None,
                    Literal::NegAtom(NegAtom { atom, .. }) => Some(atom),
                })
            })) {
                let hash: u64 = self.hash_atom(&atom);
                self.unknown.insert(hash);
                self.defs.insert(hash, atom);
            }
        }

        // OK, return self
        self.tknown.reserve(self.unknown.len());
        self.fknown.reserve(self.unknown.len());
    }

    /// Returns whether a particular atom is in the know.
    ///
    /// This function is more powerful than comparing the result of open world queries, because you can specifically ask for the status of the positive and negative atom variants.
    /// [`Self::open_world_truth()`](Interpretation::open_world_truth()) will always tell you true exists if it does, regardless of whether false exists.
    ///
    /// # Arguments
    /// - `atom`: Some [`Atom`] to attempt to find the truth of.
    /// - `truth`: The specific truth-variant of the atom to investigate.
    ///
    /// # Returns
    /// True if we know that this atom has this truth value, or false otherwise. This may mean we know it has the other truth value (which is _not_ mutually exclusive with the first case! I.e., we may know of it _both_ existing!).
    #[inline]
    pub fn knows_about_atom(&self, atom: &Atom<&'f str, &'s str>, truth: bool) -> bool {
        let hash: u64 = self.hash_atom(&atom);

        // Do the procedure above
        if truth { self.tknown.contains(&hash) } else { self.fknown.contains(&hash) }
    }

    // /// Returns whether a particular atom is in the know.
    // ///
    // /// This function is more powerful than comparing the result of open world queries, because you can specifically ask for the status of the positive and negative atom variants.
    // /// [`Self::open_world_truth()`](Interpretation::open_world_truth()) will always tell you true exists if it does, regardless of whether false exists.
    // ///
    // /// # Arguments
    // /// - `atom`: Some [`Atom`] to attempt to find the truth of.
    // /// - `assign`: Some particular assignment for any variables occuring in the `atom`.
    // /// - `truth`: The specific truth-variant of the atom to investigate.
    // ///
    // /// # Returns
    // /// True if we know that this atom has this truth value, or false otherwise. This may mean we know it has the other truth value (which is _not_ mutually exclusive with the first case! I.e., we may know of it _both_ existing!).
    // #[inline]
    // pub fn knows_about_atom_with_assign(
    //     &self,
    //     atom: &Atom<&'f str, &'s str>,
    //     assign: &HashMap<Ident<&'f str, &'s str>, Ident<&'f str, &'s str>>,
    //     truth: bool,
    // ) -> bool {
    //     let hash: u64 = self.hash_atom_with_assign(&atom, assign);

    //     // Do the procedure above
    //     if truth { self.tknown.contains(&hash) } else { self.fknown.contains(&hash) }
    // }

    /// Returns the truth value of the given atom under the closed-world assumption.
    ///
    /// # Arguments
    /// - `atom`: Some [`Atom`] to attempt to find the truth of.
    ///
    /// # Returns
    /// This applies the following procedure:
    /// - If the atom is known, returns the truth value of it;
    /// - If the atom is unknown, returns [`None`]; or
    /// - Returns [`Some(false)`] if the atom doesn't exist in the universe.
    #[inline]
    pub fn closed_world_truth(&self, atom: &Atom<&'f str, &'s str>) -> Option<bool> {
        let hash: u64 = self.hash_atom(&atom);

        // Do the procedure above
        if self.tknown.contains(&hash) {
            Some(true)
        } else if self.fknown.contains(&hash) {
            Some(false)
        } else if self.unknown.contains(&hash) {
            None
        } else {
            Some(false)
        }
    }

    /// Returns the truth value of the given atom under the open-world assumption.
    ///
    /// # Arguments
    /// - `atom`: Some [`Atom`] to attempt to find the truth of.
    ///
    /// # Returns
    /// This applies the following procedure:
    /// - If the atom is known, returns the truth value of it;
    /// - If the atom is unknown, returns [`None`]; or
    /// - Returns [`None`] if the atom doesn't exist in the universe.
    #[inline]
    pub fn open_world_truth(&self, atom: &Atom<&'f str, &'s str>) -> Option<bool> {
        let hash: u64 = self.hash_atom(&atom);

        // Do the procedure above
        if self.tknown.contains(&hash) {
            Some(true)
        } else if self.fknown.contains(&hash) {
            Some(false)
        } else if self.unknown.contains(&hash) {
            None
        } else {
            None
        }
    }

    // /// Returns the truth value of the given atom under the open-world assumption.
    // ///
    // /// # Arguments
    // /// - `atom`: Some [`Atom`] to attempt to find the truth of.
    // /// - `assign`: A list of assignments for the variables in the atom, if any.
    // ///
    // /// # Returns
    // /// This applies the following procedure:
    // /// - If the atom is known, returns the truth value of it;
    // /// - If the atom is unknown, returns [`None`]; or
    // /// - Returns [`None`] if the atom doesn't exist in the universe.
    // ///
    // /// # Panics
    // /// This function panics if there was a variable in `atom` that was not in the `assign`ment.
    // #[inline]
    // #[track_caller]
    // pub fn open_world_truth_with_assign(
    //     &self,
    //     atom: &Atom<&'f str, &'s str>,
    //     assign: &HashMap<Ident<&'f str, &'s str>, Ident<&'f str, &'s str>>,
    // ) -> Option<bool> {
    //     let hash: u64 = self.hash_atom_with_assign(&atom, assign);

    //     // Do the procedure above
    //     if self.tknown.contains(&hash) {
    //         Some(true)
    //     } else if self.fknown.contains(&hash) {
    //         Some(false)
    //     } else if self.unknown.contains(&hash) {
    //         None
    //     } else {
    //         None
    //     }
    // }
}

// Format
impl<'f, 's, R: BuildHasher> Display for Interpretation<'f, 's, R> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        // Get a sorted list of both kinds of atoms
        let mut tknown: Vec<&Atom<_, _>> = self.tknown.iter().map(|h| self.defs.get(h).unwrap()).collect();
        let mut fknown: Vec<&Atom<_, _>> = self.fknown.iter().map(|h| self.defs.get(h).unwrap()).collect();
        let mut unknown: Vec<&Atom<_, _>> = self.unknown.iter().map(|h| self.defs.get(h).unwrap()).collect();
        tknown.sort_by(|i1, i2| {
            i1.ident
                .value
                .value()
                .cmp(i2.ident.value.value())
                .then(i1.args.as_ref().map(|a| a.args.len()).unwrap_or(0).cmp(&i2.args.as_ref().map(|a| a.args.len()).unwrap_or(0)))
        });
        fknown.sort_by(|i1, i2| {
            i1.ident
                .value
                .value()
                .cmp(i2.ident.value.value())
                .then(i1.args.as_ref().map(|a| a.args.len()).unwrap_or(0).cmp(&i2.args.as_ref().map(|a| a.args.len()).unwrap_or(0)))
        });
        unknown.sort_by(|i1, i2| {
            i1.ident
                .value
                .value()
                .cmp(i2.ident.value.value())
                .then(i1.args.as_ref().map(|a| a.args.len()).unwrap_or(0).cmp(&i2.args.as_ref().map(|a| a.args.len()).unwrap_or(0)))
        });

        // Print 'em
        writeln!(f, "Interpretation {{")?;
        write!(f, "{}", tknown.into_iter().map(|a| format!("    {a}=true\n")).collect::<String>())?;
        write!(f, "{}", fknown.into_iter().map(|a| format!("    {a}=false\n")).collect::<String>())?;
        write!(f, "{}", unknown.into_iter().map(|a| format!("    {a}=unknown\n")).collect::<String>())?;
        writeln!(f, "}}")
    }
}

// Iteration
impl<'f, 's, R> Interpretation<'f, 's, R> {
    /// Returns an iterator over all the known truths in the Interpretation.
    ///
    /// # Returns
    /// An [`Iterator`] which will yield [`Atom`], [`Option<bool>`](Option) pairs, where a [`None`]
    /// in the value position encodes a logical contradiction.
    #[inline]
    pub fn iter<'a>(&'a self) -> impl 'a + Iterator<Item = (&'a Atom<&'f str, &'s str>, Option<bool>)> {
        self.defs.iter().map(|(h, d)| {
            if self.tknown.contains(h) {
                (d, Some(true))
            } else if self.fknown.contains(h) {
                (d, Some(false))
            } else if self.unknown.contains(h) {
                (d, None)
            } else {
                panic!("Encountered a definition {d:?} ({h}) that is not in the known trues, known falses or known unknowns");
            }
        })
    }

    /// Returns an iterator over all the known truths in the Interpretation, consuming ourselfs to
    /// return the atoms by ownership.
    ///
    /// # Returns
    /// An [`Iterator`] which will yield [`Atom`], [`Option<bool>`](Option) pairs, where a [`None`]
    /// in the value position encodes a logical contradiction.
    #[inline]
    pub fn into_iter(self) -> impl Iterator<Item = (Atom<&'f str, &'s str>, Option<bool>)> {
        self.defs.into_iter().map(move |(h, d)| {
            if self.tknown.contains(&h) {
                (d, Some(true))
            } else if self.fknown.contains(&h) {
                (d, Some(false))
            } else if self.unknown.contains(&h) {
                (d, None)
            } else {
                panic!("Encountered a definition {d:?} ({h}) that is not in the known trues, known falses or known unknowns");
            }
        })
    }
}
