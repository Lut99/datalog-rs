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
#[derive(Clone, Debug)]
pub struct State<F, S> {
    /// Currently defined transitions.
    pub trans: HashMap<Ident<F, S>, Transition<F, S>>,
    /// Currently defined rules.
    pub rules: IndexSet<Rule<Atom<F, S>>>,
    /// Any facts that are currently postulated (somehow).
    pub posts: IndexSet<GroundAtom<F, S>>,
}
impl<F, S> Default for State<F, S> {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl<F, S> State<F, S> {
    /// Constructor for the State that initializes it to an empty one.
    ///
    /// # Returns
    /// A new State ready to [`run()`](super::super::ast::TransitionSpec::run_mut()).
    #[inline]
    pub fn new() -> Self { Self { trans: HashMap::new(), rules: IndexSet::new(), posts: IndexSet::new() } }
}
