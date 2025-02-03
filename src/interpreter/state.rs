//  STATE.rs
//    by Lut99
//
//  Created:
//    03 Feb 2025, 17:11:26
//  Last edited:
//    03 Feb 2025, 18:35:18
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the New^{TM} Shiny^{TM} [`State`]^{TM} which is capable of
//!   building Herbrand universes over complex things like recursive atoms and
//!   integers.
//

use std::collections::HashSet;
use std::marker::PhantomData;

use stackvec::StackVec;

use crate::ast::{Atom, Literal, Spec};


/***** LIBRARY *****/
/// Defines the state during derivation.
///
/// Specifically, it is always contextualized within the Herbrand Universe in a spec, i.e., the
/// complete list of grounded atoms we want to quantify over. Then, during derivation, these are
/// shuffled around as we learn information about them. This lands you in a specific
/// _interpretation_ where all of them have a truth value assigned to them (true, false, or
/// unknown).
#[derive(Debug, Clone)]
pub struct State<'s, F, S> {
    /// All non-grounded atoms in the spec, i.e., atoms with variables in them.
    ///
    /// This is what we use to generate new inhabitants of the set below when new grounded atoms
    /// are discovered. This can happen at creation (i.e., read from the spec) or during
    /// derivation, when we potentially construct new atoms.
    vars: Vec<&'s Atom<F, S>>,

    /// Which of the atoms in the universe are _true_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unknwns }.
    truths: HashSet<*const Atom<F, S>>,
    /// Which of the atoms in the universe are _false_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unknwns }.
    falses: HashSet<*const Atom<F, S>>,
    /// Which of the atoms in the universe are _unknown_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unkwns }.
    unkwns: HashSet<*const Atom<F, S>>,

    /// Phony lifetime link to ensure the pointers remain valid.
    _lt: PhantomData<&'s ()>,
}
impl<'s, F, S> State<'s, F, S> {
    /// Constructor for the State that initializes it from the given spec.
    ///
    /// # Arguments
    /// - `spec`: Some [`Spec<'s, F, S>`] to interpret.
    ///
    /// # Returns
    /// A new State that is initialized to the universe of possible atoms read from the spec.
    ///
    /// Note that ALL atoms are assumed to be _false_ initially.
    pub fn new(spec: &'s Spec<F, S>) -> Self {
        // Let's start by quantifying and collecting grounded- and non-grounded atoms.
        let mut falses: Vec<*const Atom<F, S>> = Vec::new();
        let mut vars: Vec<&'s Atom<F, S>> = Vec::new();
        for rule in &spec.rules {
            for atom in rule.consequents.values().chain(rule.tail.iter().flat_map(|t| {
                t.antecedents.values().map(|l| match l {
                    Literal::Atom(a) => a,
                    Literal::NegAtom(na) => &na.atom,
                })
            })) {}
        }

        todo!()
    }
}
