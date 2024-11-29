//  STATE.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 16:32:11
//  Last edited:
//    29 Nov 2024, 17:13:19
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
    pub(crate) trans: HashMap<Ident<&'f str, &'s str>, Transition<&'f str, &'s str>>,
    /// A list of rules that are from the spec.
    pub(crate) spec_rules: IndexSet<Rule<&'f str, &'s str>>,
    /// A list of rules that are from transitions.
    pub(crate) trans_rules: IndexSet<Rule<&'f str, &'s str>>,
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
    pub fn new() -> Self { Self { trans: HashMap::new(), spec_rules: IndexSet::new(), trans_rules: IndexSet::new() } }



    /// Stores a new transition from the specification.
    ///
    /// # Arguments
    /// - `trans`: The [`Transition`] to store.
    ///
    /// # Returns
    /// True if a transition with the same identifier was already present in the state, or false otherwise.
    #[inline]
    pub fn add_transition(&mut self, trans: Transition<&'f str, &'s str>) -> bool { self.trans.insert(trans.ident.clone(), trans).is_some() }

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



    /// Retrieves the transition matching the given identifier.
    ///
    /// # Arguments
    /// - `ident`: The [`Ident`]ifier of the transition to retrieve.
    ///
    /// # Returns
    /// The found [`Transition`] if any, or else [`None`].
    #[inline]
    pub fn get_transition(&self, ident: &Ident<&'f str, &'s str>) -> Option<&Transition<&'f str, &'s str>> { self.trans.get(ident) }



    /// Collapses the State into a typical Datalog specification for inference.
    ///
    /// # Returns
    /// A [`Spec`] that encodes the currently applicable set of rules.
    #[inline]
    pub fn to_spec(&self) -> Spec<&'f str, &'s str> {
        Spec { rules: self.spec_rules.iter().cloned().chain(self.trans_rules.iter().cloned()).collect() }
    }
}
