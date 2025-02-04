//  STATE.rs
//    by Lut99
//
//  Created:
//    03 Feb 2025, 17:11:26
//  Last edited:
//    04 Feb 2025, 18:34:54
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the New^{TM} Shiny^{TM} [`State`]^{TM} which is capable of
//!   building Herbrand universes over complex things like recursive atoms and
//!   integers.
//

use std::borrow::Cow;
use std::collections::HashSet;
use std::hash::Hash;
use std::marker::PhantomData;

use better_derive::{Clone, Debug};

use crate::ast::{Atom, Ident, Literal, Spec};


/***** HELPER FUNCTIONS *****/
/// Does recursive sorting of the atom as either a grounded one or one containing a variable.
///
/// Note that the recursion means that any arguments to the given atom will be sorted too.
///
/// # Arguments
/// - `atom`: The [`Atom`] to sort.
/// - `grounded`: The list of grounded atoms (= atoms without variables) to potentially add to.
/// - `vars`: The list of non-grounded atoms (= atoms with variables) to potentially add to.
fn sort_atom<'a, F, S>(atom: &'a Atom<F, S>, grounded: &mut Vec<Cow<'a, Atom<F, S>>>, vars: &mut Vec<&'a Atom<F, S>>)
where
    Atom<F, S>: Clone,
{
    // Sort the atom itself
    if atom.has_vars() {
        if vars.len() + 1 > vars.capacity() {
            vars.reserve(2 * vars.capacity());
        }
        vars.push(atom);
    } else {
        if grounded.len() + 1 > grounded.capacity() {
            grounded.reserve(2 * vars.capacity());
        }
        grounded.push(Cow::Borrowed(atom));
    }

    // Then sort its arguments
    for atom in atom.args() {
        sort_atom(atom, grounded, vars);
    }
}





/***** LIBRARY *****/
/// Defines the state during derivation.
///
/// Specifically, it is always contextualized within the Herbrand Universe in a spec, i.e., the
/// complete list of grounded atoms we want to quantify over. Then, during derivation, these are
/// shuffled around as we learn information about them. This lands you in a specific
/// _interpretation_ where all of them have a truth value assigned to them (true, false, or
/// unknown).
#[derive(Clone, Debug)]
pub struct State<'s, F, S>
where
    Atom<F, S>: Clone,
{
    /// The universe of things we iterate over. This is either collected constants from the State,
    /// or generated instantiations from the `vars`.
    universe: Vec<Cow<'s, Atom<F, S>>>,
    /// All non-grounded atoms in the spec, i.e., atoms with variables in them.
    ///
    /// This is what we use to generate new inhabitants of the set below when new grounded atoms
    /// are discovered. This can happen at creation (i.e., read from the spec) or during
    /// derivation, when we potentially construct new atoms.
    vars:     Vec<&'s Atom<F, S>>,

    /// Which of the atoms in the universe are _true_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unknwns }.
    truths: HashSet<usize>,
    /// Which of the atoms in the universe are _false_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unknwns }.
    falses: HashSet<usize>,
    /// Which of the atoms in the universe are _unknown_.
    ///
    /// They are identified by index in the `universe` set, and guaranteed to be in ONLY one of the
    /// sets { truths, falses, unkwns }.
    unkwns: HashSet<usize>,

    /// Phony lifetime link to ensure the pointers remain valid.
    _lt: PhantomData<&'s ()>,
}

// Constructors
impl<'s, F, S> State<'s, F, S>
where
    Atom<F, S>: Clone,
    Ident<F, S>: Clone + Eq + Hash,
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
    pub fn new(spec: &'s Spec<F, S>) -> Self {
        // Let's start by quantifying and collecting grounded- and non-grounded atoms.
        let mut universe: Vec<Cow<'s, Atom<F, S>>> = Vec::new();
        let mut vars: Vec<&'s Atom<F, S>> = Vec::new();
        for rule in &spec.rules {
            for atom in rule.consequents.values().chain(rule.tail.iter().flat_map(|t| {
                t.antecedents.values().map(|l| match l {
                    Literal::Atom(a) => a,
                    Literal::NegAtom(na) => &na.atom,
                })
            })) {
                sort_atom(atom, &mut universe, &mut vars);
            }
        }

        // Now we add the instantiated variables
        let mut grounded: Vec<Cow<'s, Atom<F, S>>> = Vec::with_capacity(vars.len() * universe.len());
        for var in &vars {
            // Quantify over the atom
            let iter = var.quantify(universe.iter().map(Cow::as_ref));
            grounded.reserve(iter.len());
            for atom in iter {
                grounded.push(Cow::Owned(atom));
            }
        }
        universe.extend(grounded);

        // Now we can construct self
    }
}
