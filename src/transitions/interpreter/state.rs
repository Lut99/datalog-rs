//  STATE.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 16:32:11
//  Last edited:
//    11 Feb 2025, 18:14:47
//  Auto updated?
//    Yes
//
//  Description:
//!   The transition system equivalent of an
//!   [`Interpretation`](crate::interpreter::interpretation::Interpretation).
//

use std::collections::HashMap;

use indexmap::IndexSet;

use super::super::ast::Transition;
use crate::ir::{Atom, GroundAtom, Ident, Rule};


/***** LIBRARY *****/
/// The transition system equivalent of an
/// [`Interpretation`](crate::interpreter::interpretation::Interpretation).
#[derive(Clone, better_derive::Debug)]
pub struct State<S> {
    /// Currently defined transitions.
    pub trans: HashMap<Ident<S>, Transition<S>>,
    /// Currently defined rules.
    pub rules: IndexSet<Rule<Atom<S>>>,
    /// Any facts that are currently postulated (somehow).
    pub posts: IndexSet<GroundAtom<S>>,
}
impl<S> Default for State<S> {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl<S> State<S> {
    /// Constructor for the State that initializes it to an empty one.
    ///
    /// # Returns
    /// A new State ready to [`run()`](super::super::ast::TransitionSpec::run_mut()).
    #[inline]
    pub fn new() -> Self { Self { trans: HashMap::new(), rules: IndexSet::new(), posts: IndexSet::new() } }
}
