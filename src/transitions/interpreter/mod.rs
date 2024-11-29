//  MOD.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 16:26:50
//  Last edited:
//    29 Nov 2024, 17:12:56
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines an interpreter for the transition-part of the Datalog with
//!   transitions extension.
//

// Modules
pub mod state;

// Imports
use std::collections::HashSet;

use state::State;

use super::ast::{Phrase, Postulation, TransitionSpec};
use crate::ast::{Ident, Rule, Spec};
use crate::interpreter::interpretation::Interpretation;
use crate::transitions::ast::{PostulationOp, Transition};


/***** ERRORS *****/
/// Defines errors occurring when computing transitions.
#[derive(Debug)]
pub enum Error<'f, 's> {
    /// The inference procedure failed.
    Inference { err: crate::interpreter::Error<'f, 's> },
    /// A given transition is undefined.
    UndefinedTransition { ident: Ident<&'f str, &'s str> },
}
impl<'f, 's> From<crate::interpreter::Error<'f, 's>> for Error<'f, 's> {
    #[inline]
    fn from(value: crate::interpreter::Error<'f, 's>) -> Self { Self::Inference { err: value } }
}





/***** AUXILLARY *****/
/// Keeps track of effects as they occur during transitions.
#[derive(Clone, Debug)]
pub struct Effect<'f, 's> {
    /// The phrase that triggered this effect.
    pub phrase: Phrase<&'f str, &'s str>,
    /// Tracks which rules have been _created_ this step.
    pub created: Vec<Rule<&'f str, &'s str>>,
    /// Tracks which rules have been _obfuscated_ this step.
    pub obfuscated: Vec<Rule<&'f str, &'s str>>,
    /// The denotation after the step.
    pub interpretation: Interpretation<'f, 's>,
}
impl<'f, 's> Effect<'f, 's> {
    /// Constructor for the Effect that initializes it to an empty one.
    ///
    /// # Arguments
    /// - `phrase`: The phrase that triggered this effect.
    ///
    /// # Returns
    /// A new Effect that has yet to be populated.
    #[inline]
    pub fn new(phrase: Phrase<&'f str, &'s str>) -> Self {
        Self { phrase, created: Vec::new(), obfuscated: Vec::new(), interpretation: Interpretation::new() }
    }
}





/***** LIBRARY *****/
impl<'f, 's> TransitionSpec<&'f str, &'s str> {
    /// Computes the denotation of the specification after every transition.
    ///
    /// # Arguments
    /// - `state`: The [`State`] that we derive in. This state may already be non-zero, if multiple specs in sequence are derived.
    ///
    /// # Returns
    /// A series of [`Effect`]s that tell the user what happened.
    ///
    /// # Errors
    /// This function can error if the total number of arguments in a rule exceeds [`STACK_VEC_LEN`](crate::interpreter::interpretation::STACK_VEC_LEN).
    #[inline]
    pub fn run_mut(&self, state: &mut State<'f, 's>) -> Result<Vec<Effect<'f, 's>>, Error> {
        // Go through everything in the spec!
        let mut effects: Vec<Effect<'f, 's>> = Vec::new();
        for phrase in &self.phrases {
            match phrase {
                // We collect rules & definitions as we find them.
                Phrase::Rule(rule) => {
                    state.add_spec_rule(rule.clone());
                },
                Phrase::Transition(trans) => {
                    state.add_transition(trans.clone());
                },

                // Postulations and triggers will trigger inferences
                Phrase::Postulation(post) => {
                    // Update the state with the proper rules
                    let mut effect: Effect<'f, 's> = Effect::new(Phrase::Postulation(post.clone()));
                    match post.op {
                        PostulationOp::Create(_) => {
                            for rule in &post.rules {
                                if state.create_rule(rule.clone()) {
                                    effect.created.push(rule.clone());
                                }
                            }
                        },
                        PostulationOp::Obfuscate(_) => {
                            for rule in &post.rules {
                                if state.obfuscate_rule(rule) {
                                    effect.obfuscated.push(rule.clone());
                                }
                            }
                        },
                    }

                    // Collapse the state into a specification
                    let spec: Spec<&'f str, &'s str> = state.to_spec();

                    // Run an interpretation and add that to the state too
                    spec.alternating_fixpoint_mut(&mut effect.interpretation)?;

                    // OK!
                    effects.push(effect);
                },
                Phrase::Trigger(trigger) => {
                    let mut effect: Effect<'f, 's> = Effect::new(Phrase::Trigger(trigger.clone()));
                    for ident in &trigger.idents {
                        // Find the transition in the state
                        let trans: &Transition<&'f str, &'s str> = match state.get_transition(ident) {
                            Some(trans) => trans,
                            None => return Err(Error::UndefinedTransition { ident: ident.clone() }),
                        };

                        // Handle its postulations
                        for post in &trans.postulations {
                            match post.op {
                                PostulationOp::Create(_) => {
                                    for rule in &post.rules {
                                        if state.create_rule(rule.clone()) {
                                            effect.created.push(rule.clone());
                                        }
                                    }
                                },
                                PostulationOp::Obfuscate(_) => {
                                    for rule in &post.rules {
                                        if state.obfuscate_rule(rule) {
                                            effect.obfuscated.push(rule.clone());
                                        }
                                    }
                                },
                            }
                        }
                    }
                },
            };
        }

        todo!()
    }
}
