//  STATE.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 16:32:11
//  Last edited:
//    03 Dec 2024, 16:59:25
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
use crate::ast::{Atom, Ident, Rule};


/***** LIBRARY *****/
/// The transition system equivalent of an
/// [`Interpretation`](crate::interpreter::interpretation::Interpretation).
#[derive(Clone, Debug)]
pub struct State<'f, 's> {
    /// Currently defined transitions.
    pub trans: HashMap<Ident<&'f str, &'s str>, Transition<&'f str, &'s str>>,
    /// Currently defined rules.
    pub rules: IndexSet<Rule<&'f str, &'s str>>,
    /// Any facts that are currently postulated (somehow).
    pub posts: IndexSet<Atom<&'f str, &'s str>>,
}
impl<'f, 's> Default for State<'f, 's> {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl<'f, 's> State<'f, 's> {
    /// Constructor for the State that initializes it to an empty one.
    ///
    /// # Returns
    /// A new State ready to [`run()`](super::super::ast::TransitionSpec::run_mut()).
    #[inline]
    pub fn new() -> Self { Self { trans: HashMap::new(), rules: IndexSet::new(), posts: IndexSet::new() } }
}
