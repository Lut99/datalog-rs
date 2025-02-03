//  STATE.rs
//    by Lut99
//
//  Created:
//    03 Feb 2025, 17:11:26
//  Last edited:
//    03 Feb 2025, 18:20:39
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the New^{TM} Shiny^{TM} [`State`]^{TM} which is capable of
//!   building Herbrand universes over complex things like recursive atoms and
//!   integers.
//

use std::collections::HashSet;

use stackvec::StackVec;

use crate::ast::Atom;


/***** LIBRARY *****/
/// Defines the state during derivation.
///
/// Specifically, it is always contextualized within the Herbrand Universe in a spec, i.e., the
/// complete list of grounded atoms we want to quantify over. Then, during derivation, these are
/// shuffled around as we learn information about them. This lands you in a specific
/// _interpretation_ where all of them have a truth value assigned to them (true, false, or
/// unknown).
#[derive(Debug, Clone)]
pub struct State<F, S> {
    /// All atoms in the universe.
    ///
    /// Will be allocated to a specific size beforehand. This capacity represents the maximum size
    /// we're willing to commit to.
    universe: Vec<Atom<F, S>>,

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
}
impl<F, S> State<F, S> {
    /// Constructor for the State that initializes it without any universe.
    /// 
    /// # Arguments
    /// - `max_universe_size`: The maximum size the universe can have. I.e., the maximum number of
    ///   concrete atoms to quantify over.
    /// 
    /// # Returns
    /// A new State that doesn't know anything, not even how the universe of potential looks like.
    /// Rather sad!
    #[inline]
    pub fn new()
}
