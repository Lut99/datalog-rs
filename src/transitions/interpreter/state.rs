//  STATE.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 16:32:11
//  Last edited:
//    03 Dec 2024, 15:40:48
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
use crate::ast::{Ident, Rule, Spec};


/***** LIBRARY *****/
/// The transition system equivalent of an
/// [`Interpretation`](crate::interpreter::interpretation::Interpretation).
#[derive(Clone, Debug)]
pub struct State<'f, 's> {
    /// Currently defined transitions.
    pub trans: HashMap<Ident<&'f str, &'s str>, Transition<&'f str, &'s str>>,
    /// Currently defined rules.
    pub rules: Rules<'f, 's>,
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
    pub fn new() -> Self { Self { trans: HashMap::new(), rules: Rules::new() } }
}



/// Implements a store for rules that remembers which are given in the spec and which are results
/// of transitions.
///
/// This mostly exists as one to be able to correct borrow the transitions as read while writing to
/// the rules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rules<'f, 's> {
    /// A list of rules that are from the spec.
    pub(crate) spec_rules:  IndexSet<Rule<&'f str, &'s str>>,
    /// A list of rules that are from transitions.
    pub(crate) trans_rules: IndexSet<Rule<&'f str, &'s str>>,
}
impl<'f, 's> Default for Rules<'f, 's> {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl<'f, 's> Rules<'f, 's> {
    /// Constructor for the Rules.
    ///
    /// # Returns
    /// A new Rules without any rules in it yet.
    #[inline]
    pub fn new() -> Self { Self { spec_rules: IndexSet::new(), trans_rules: IndexSet::new() } }



    /// Stores a new rule from the specification.
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] to store.
    ///
    /// # Returns
    /// True if the rule was already present in the state, or false otherwise.
    #[inline]
    pub fn add_spec_rule(&mut self, rule: Rule<&'f str, &'s str>) -> bool {
        let exists: bool = self.trans_rules.contains(&rule);
        self.spec_rules.insert(rule) || exists
    }

    /// Creates a rule as the effect of a transition.
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] to create.
    ///
    /// # Returns
    /// True if the rule was already present in the state, or false otherwise.
    #[inline]
    pub fn create_rule(&mut self, rule: Rule<&'f str, &'s str>) -> bool {
        let exists: bool = self.spec_rules.contains(&rule);
        self.trans_rules.insert(rule) || exists
    }

    /// Obfuscates a rule as the effect of a transition.
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] to obfuscate.
    ///
    /// # Returns
    /// True if the rule was obfuscated. May be false if it didn't exist or it was still in the
    /// spec rules.
    #[inline]
    pub fn obfuscate_rule(&mut self, rule: &Rule<&'f str, &'s str>) -> bool {
        let exists: bool = self.spec_rules.contains(rule);
        self.trans_rules.swap_remove(rule) && !exists
    }



    /// Collapses the State into a typical Datalog specification for inference.
    ///
    /// # Returns
    /// A [`Spec`] that encodes the currently applicable set of rules.
    #[inline]
    pub fn to_spec(&self) -> Spec<&'f str, &'s str> {
        Spec { rules: self.spec_rules.iter().cloned().chain(self.trans_rules.iter().cloned()).collect() }
    }



    /// The total number of active rules.
    #[inline]
    pub fn len(&self) -> usize { self.spec_rules.len() + self.trans_rules.len() }

    /// Whether there are any active rules.
    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }
}
