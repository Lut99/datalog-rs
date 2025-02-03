//  MOD.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 16:26:50
//  Last edited:
//    03 Feb 2025, 18:20:47
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines an interpreter for the transition-part of the Datalog with
//!   transitions extension.
//

// Modules
pub mod state;

use std::error;
// Imports
use std::fmt::{Display, Formatter, Result as FResult};

use ast_toolkit::punctuated::punct;
use indexmap::IndexSet;
use log::{debug, trace};
use state::State;

use super::ast::{Phrase, Postulation, TransitionSpec, Trigger};
use crate::ast::{Atom, Dot, Ident, Rule, Spec};
use crate::interpreter::state::Interpretation;
use crate::transitions::ast::{PostulationOp, Transition};


/***** ERRORS *****/
/// Defines errors occurring when computing transitions.
#[derive(Debug)]
pub enum Error<'f, 's> {
    /// A given transition is undefined.
    UndefinedTransition { ident: Ident<&'f str, &'s str> },
}
impl<'f, 's> Display for Error<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::UndefinedTransition { ident } => write!(f, "Undefined transition {:?}", ident.value.value()),
        }
    }
}
impl<'f, 's> error::Error for Error<'f, 's> {}





/***** HELPER FUNCTIONS ****/
/// Computes a [`Spec`] from the given [`State`].
fn state_to_spec<'a, 'f: 'a, 's: 'a>(
    rules: impl IntoIterator<Item = &'a Rule<&'f str, &'s str>>,
    posts: impl IntoIterator<Item = &'a Atom<&'f str, &'s str>>,
) -> Spec<&'f str, &'s str> {
    Spec {
        rules: rules
            .into_iter()
            .cloned()
            .chain(posts.into_iter().map(|atom| Rule { consequents: punct![v => atom.clone()], tail: None, dot: Dot::default() }))
            .collect(),
    }
}





/***** AUXILLARY *****/
/// Keeps track of effects as they occur during transitions.
#[derive(Clone, Debug)]
pub struct Effect<'f, 's> {
    /// The phrase that triggered this effect.
    pub trigger: EffectTrigger<'f, 's>,
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
    pub fn new(trigger: impl Into<EffectTrigger<'f, 's>>) -> Self { Self { trigger: trigger.into(), interpretation: Interpretation::new() } }
}

/// The reason that triggered an [`Effect`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum EffectTrigger<'f, 's> {
    /// A raw postulation.
    Postulation(Postulation<&'f str, &'s str>),
    /// A trigger.
    Trigger(Trigger<&'f str, &'s str>),
    /// The end of the spec.
    End,
}
impl<'f, 's> Display for EffectTrigger<'f, 's> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Postulation(p) => p.fmt(f),
            Self::Trigger(p) => p.fmt(f),
            Self::End => write!(f, "<end of spec>"),
        }
    }
}
impl<'f, 's> From<Postulation<&'f str, &'s str>> for EffectTrigger<'f, 's> {
    #[inline]
    fn from(value: Postulation<&'f str, &'s str>) -> Self { Self::Postulation(value) }
}
impl<'f, 's> From<Trigger<&'f str, &'s str>> for EffectTrigger<'f, 's> {
    #[inline]
    fn from(value: Trigger<&'f str, &'s str>) -> Self { Self::Trigger(value) }
}
impl<'f, 's> From<()> for EffectTrigger<'f, 's> {
    #[inline]
    fn from(_value: ()) -> Self { Self::End }
}





/***** LIBRARY *****/
impl<'f, 's> TransitionSpec<&'f str, &'s str> {
    /// Computes the denotation of the specification after every transition.
    ///
    /// # Returns
    /// A tuple of a produced [`State`], that keeps track of the currently enabled rules and
    /// transitions; and a series of [`Effect`]s that tell the user what happened.
    ///
    /// # Errors
    /// This function can error if the total number of arguments in a rule exceeds
    /// [`STACK_VEC_LEN`](crate::interpreter::interpretation::STACK_VEC_LEN).
    #[inline]
    pub fn run(&self) -> Result<(State<'f, 's>, Vec<Effect<'f, 's>>), Error<'f, 's>> {
        let mut state = State::new();

        // Leave the rest to the mutable interface
        let effects: Vec<Effect<'f, 's>> = self.run_mut(&mut state)?;
        Ok((state, effects))
    }

    /// Computes the denotation of the specification after every transition.
    ///
    /// Unlike [`Spec::alternating_fixpoint_mut()`], the given `state` _can_ contain previous state
    /// from previous runs. I.e., it is not cleared at the start like an `int` is.
    ///
    /// # Arguments
    /// - `state`: The [`State`] that we derive in. This state may already be non-zero, if multiple
    /// specs in sequence are derived.
    ///
    /// # Returns
    /// A series of [`Effect`]s that tell the user what happened.
    ///
    /// # Errors
    /// This function can error if the total number of arguments in a rule exceeds
    /// [`STACK_VEC_LEN`](crate::interpreter::interpretation::STACK_VEC_LEN).
    #[inline]
    pub fn run_mut(&self, state: &mut State<'f, 's>) -> Result<Vec<Effect<'f, 's>>, Error<'f, 's>> {
        let State { trans: transitions, rules, posts } = state;
        debug!(
            "Running transitions\n\nTransitionSpec:\n{}\n{}{}\n",
            "-".repeat(80),
            self.phrases.iter().map(|p| format!("   {}\n", p.to_string().replace('\n', "\n   "))).collect::<String>(),
            "-".repeat(80),
        );

        // Go through everything in the spec!
        let mut effects: Vec<Effect<'f, 's>> = Vec::new();
        for phrase in &self.phrases {
            match phrase {
                // We collect rules & definitions as we find them.
                Phrase::Rule(rule) => {
                    trace!("--> Rule '{rule}'");
                    rules.insert(rule.clone());
                },
                Phrase::Transition(trans) => {
                    trace!("--> Transition '{trans}'");
                    if transitions.insert(trans.ident, trans.clone()).is_some() {
                        // TODO: Already exists. Warning of some kind.
                    }
                },

                // Postulations and triggers will trigger inferences
                Phrase::Postulation(post) => {
                    trace!("--> Postulation '{post}'");
                    let mut effect: Effect<'f, 's> = Effect::new(post.clone());

                    // First, with the current KB, do an inference run to find out which postconditions are derived
                    let mut spec: Spec<&str, &str> = state_to_spec(rules.iter(), posts.iter());
                    spec.rules.push(post.to_rule());
                    // NOTE: This function clears the interpretation for us
                    debug!("Running post-condition inference step");
                    let int: Interpretation = spec.alternating_fixpoint();
                    let consts: IndexSet<Ident<&str, &str>> = int.find_existing_consts();

                    // Update the state according to the current knowledge base
                    match post.op {
                        PostulationOp::Create(_) => {
                            for atom in post.consequents.values().flat_map(|atom| atom.quantify(consts.iter())) {
                                if int.closed_world_truth(&atom) == Some(true) {
                                    debug!("Postulated '{atom}'");
                                    posts.insert(atom);
                                }
                            }
                        },
                        PostulationOp::Obfuscate(_) => {
                            for atom in post.consequents.values().flat_map(|atom| atom.quantify(consts.iter())) {
                                if int.closed_world_truth(&atom) == Some(true) {
                                    debug!("Obfuscated '{atom}'");
                                    posts.shift_remove(&atom);
                                }
                            }
                        },
                    }

                    // Now we run an interpretation FOR REAL
                    debug!("Running REAL inference step");
                    state_to_spec(rules.iter(), posts.iter()).alternating_fixpoint_mut(&mut effect.interpretation);

                    // OK!
                    effects.push(effect);
                },
                Phrase::Trigger(trigger) => {
                    trace!("--> Trigger '{trigger}'");
                    let mut effect: Effect<'f, 's> = Effect::new(trigger.clone());

                    // Process all the rules postulation by all referred transitions
                    let mut creations: Vec<Atom<&'f str, &'s str>> = Vec::new();
                    let mut obfuscations: Vec<Atom<&'f str, &'s str>> = Vec::new();
                    for ident in &trigger.idents {
                        // Find the transition in the state
                        let trans: &Transition<&'f str, &'s str> = match transitions.get(ident) {
                            Some(trans) => trans,
                            None => return Err(Error::UndefinedTransition { ident: ident.clone() }),
                        };

                        // Handle its postulations
                        for post in &trans.postulations {
                            // First, with the current KB, do an inference run to find out which postconditions are derived
                            let mut spec: Spec<&str, &str> = state_to_spec(rules.iter(), posts.iter());
                            spec.rules.push(post.to_rule());
                            // NOTE: This function clears the interpretation for us
                            debug!("Running post-condition inference step");
                            let int: Interpretation = spec.alternating_fixpoint();
                            let consts: IndexSet<Ident<&str, &str>> = int.find_existing_consts();

                            // Update the state according to the current knowledge base
                            match post.op {
                                PostulationOp::Create(_) => {
                                    for atom in post.consequents.values().flat_map(|atom| atom.quantify(consts.iter())) {
                                        trace!("Considering atom '{atom}' for creation");
                                        if int.closed_world_truth(&atom) == Some(true) {
                                            debug!("--> Postulated '{atom}'");
                                            creations.push(atom.clone());
                                        }
                                    }
                                },
                                PostulationOp::Obfuscate(_) => {
                                    for atom in post.consequents.values().flat_map(|atom| atom.quantify(consts.iter())) {
                                        trace!("Considering atom '{atom}' for obfuscation");
                                        if int.closed_world_truth(&atom) == Some(true) {
                                            debug!("--> Obfuscated '{atom}'");
                                            obfuscations.push(atom.clone());
                                        }
                                    }
                                },
                            }
                        }
                    }

                    // Apply the updates
                    for atom in obfuscations {
                        posts.shift_remove(&atom);
                    }
                    for atom in creations {
                        posts.insert(atom);
                    }

                    // Now we run an interpretation FOR REAL
                    debug!("Running REAL inference step");
                    state_to_spec(rules.iter(), posts.iter()).alternating_fixpoint_mut(&mut effect.interpretation);

                    // OK!
                    effects.push(effect);
                },
            };
        }

        // Run a final postulation
        let mut effect: Effect<'f, 's> = Effect::new(EffectTrigger::End);
        state_to_spec(rules.iter(), posts.iter()).alternating_fixpoint_mut(&mut effect.interpretation);
        effects.push(effect);

        // OK, report all effects back
        Ok(effects)
    }
}





/***** TESTS *****/
#[cfg(all(test, feature = "macros"))]
mod tests {
    use std::collections::HashMap;

    use ast_toolkit::punctuated::Punctuated;
    use ast_toolkit::span::Span;
    use datalog_macros::datalog_trans;

    use super::*;
    use crate::ast::{Arrow, Atom, Comma, Dot, Literal, RuleAntecedents};
    use crate::tests::{make_atom, make_curly, make_ident};
    use crate::transitions::ast::{Add, Exclaim, Squiggly};


    /// Makes a [`Postulation`] conveniently.
    fn make_postulation(
        create: bool,
        consequents: impl IntoIterator<Item = Atom<&'static str, &'static str>>,
        antecedents: impl IntoIterator<Item = Literal<&'static str, &'static str>>,
    ) -> Postulation<&'static str, &'static str> {
        // Convert the consequents and antecedents first
        let consequents: Punctuated<Atom<&'static str, &'static str>, Comma<&'static str, &'static str>> = consequents.into_iter().collect();
        let antecedents: Punctuated<Literal<&'static str, &'static str>, Comma<&'static str, &'static str>> = antecedents.into_iter().collect();

        // Now build the rule
        Postulation {
            op: if create {
                PostulationOp::Create(Add { span: Span::new("make_postulation::op::create", "+") })
            } else {
                PostulationOp::Obfuscate(Squiggly { span: Span::new("make_postulation::op::obfuscate", "~") })
            },
            curly_tokens: make_curly(),
            consequents,
            tail: if !antecedents.is_empty() {
                Some(RuleAntecedents { arrow_token: Arrow { span: Span::new("make_postulation::arrow", ":-") }, antecedents })
            } else {
                None
            },
            dot: Dot { span: Span::new("make_postulation::dot", ".") },
        }
    }

    /// Makes a [`Trigger`] conveniently.
    fn make_trigger(idents: impl IntoIterator<Item = &'static str>) -> Trigger<&'static str, &'static str> {
        Trigger {
            exclaim_token: Exclaim { span: Span::new("make_trigger::exclaim", "!") },
            curly_tokens: make_curly(),
            idents: idents.into_iter().map(|i| Ident { value: Span::new("make_trigger::ident", i) }).collect(),
            dot: Dot { span: Span::new("make_trigger::dot", ".") },
        }
    }


    #[test]
    fn test_transition_run_paper_5_1() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Example 5.1 (to assert the original behaviour is preserved)
        let five_one: TransitionSpec<_, _> = datalog_trans! {
            #![crate]
            a :- c, not b.
            b :- not a.
            c.

            p :- q, not r.
            p :- r, not s.
            p :- t.
            q :- p.
            r :- q.
            r :- not c.
        };
        let mut effects: Vec<Effect> = match five_one.run() {
            Ok((_, effects)) => effects,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(effects.len(), 1);

        let effect: Effect = effects.pop().unwrap();
        assert_eq!(effect.interpretation.len(), 7);
        assert_eq!(effect.interpretation.closed_world_truth(&make_atom("a", None)), None);
        assert_eq!(effect.interpretation.closed_world_truth(&make_atom("b", None)), None);
        assert_eq!(effect.interpretation.closed_world_truth(&make_atom("c", None)), Some(true));
        assert_eq!(effect.interpretation.closed_world_truth(&make_atom("p", None)), Some(false));
        assert_eq!(effect.interpretation.closed_world_truth(&make_atom("q", None)), Some(false));
        assert_eq!(effect.interpretation.closed_world_truth(&make_atom("r", None)), Some(false));
        assert_eq!(effect.interpretation.closed_world_truth(&make_atom("s", None)), Some(false));
        assert_eq!(effect.interpretation.closed_world_truth(&make_atom("t", None)), Some(false));
    }

    #[test]
    fn test_transition_run_define_empty() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Just give the definition of a transition
        let def: TransitionSpec<_, _> = datalog_trans! {
            #![crate]
            #foo {}.
        };
        let (state, mut effects): (State, Vec<Effect>) = match def.run() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(
            state.trans,
            HashMap::from([(make_ident("#foo"), Transition {
                ident: make_ident("#foo"),
                curly_tokens: make_curly(),
                postulations: vec![],
                dot: Dot { span: Span::new("<example>", ".") },
            })])
        );
        assert!(state.rules.is_empty());
        assert_eq!(effects.len(), 1);

        let effect: Effect = effects.pop().unwrap();
        assert_eq!(effect.trigger, EffectTrigger::End);
        assert_eq!(effect.interpretation.len(), 0);
    }

    #[test]
    fn test_transition_run_define_single() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Just give the definition of a transition
        let def: TransitionSpec<_, _> = datalog_trans! {
            #![crate]
            #bar {
                +{ foo }.
            }.
        };
        let (state, mut effects): (State, Vec<Effect>) = match def.run() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(
            state.trans,
            HashMap::from([(make_ident("#bar"), Transition {
                ident: make_ident("#bar"),
                curly_tokens: make_curly(),
                postulations: vec![make_postulation(true, [make_atom("foo", None)], None)],
                dot: Dot { span: Span::new("<example>", ".") },
            })])
        );
        assert!(state.rules.is_empty());
        assert_eq!(effects.len(), 1);

        let effect: Effect = effects.pop().unwrap();
        assert_eq!(effect.trigger, EffectTrigger::End);
        assert_eq!(effect.interpretation.len(), 0);
    }

    #[test]
    fn test_transition_run_define_multi() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Just give the definition of a transition
        let def: TransitionSpec<_, _> = datalog_trans! {
            #![crate]
            #baz {
                +{ foo }.
                ~{ bar } :- baz(quz).
            }.
        };
        let (state, mut effects): (State, Vec<Effect>) = match def.run() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(
            state.trans,
            HashMap::from([(make_ident("#baz"), Transition {
                ident: make_ident("#baz"),
                curly_tokens: make_curly(),
                postulations: vec![
                    make_postulation(true, [make_atom("foo", None)], None),
                    make_postulation(false, [make_atom("bar", None)], [Literal::Atom(make_atom("baz", ["quz"]))])
                ],
                dot: Dot { span: Span::new("<example>", ".") },
            })])
        );
        assert!(state.rules.is_empty());
        assert_eq!(effects.len(), 1);

        let effect: Effect = effects.pop().unwrap();
        assert_eq!(effect.trigger, EffectTrigger::End);
        assert_eq!(effect.interpretation.len(), 0);
    }

    #[test]
    fn test_transition_postulate_create() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Run two postulations
        let def: TransitionSpec<_, _> = datalog_trans! {
            #![crate]
            foo :- bar.
            +{ bar }.
        };
        let (_, mut effects): (State, Vec<Effect>) = match def.run() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(effects.len(), 2);

        let effect2: Effect = effects.pop().unwrap();
        assert_eq!(effect2.trigger, EffectTrigger::End);
        assert_eq!(effect2.interpretation.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(effect2.interpretation.closed_world_truth(&make_atom("bar", None)), Some(true));

        let effect1: Effect = effects.pop().unwrap();
        assert_eq!(effect1.trigger, EffectTrigger::Postulation(make_postulation(true, [make_atom("bar", None)], None)));
        assert_eq!(effect1.interpretation.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(effect1.interpretation.closed_world_truth(&make_atom("bar", None)), Some(true));
    }

    #[test]
    fn test_transition_postulate_obfuscate() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Run a postulation, then revert it
        let def: TransitionSpec<_, _> = datalog_trans! {
            #![crate]
            +{ foo }.
            ~{ foo }.
        };
        let (_, mut effects): (State, Vec<Effect>) = match def.run() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(effects.len(), 3);

        let effect3: Effect = effects.pop().unwrap();
        assert_eq!(effect3.trigger, EffectTrigger::End);
        assert_eq!(effect3.interpretation.closed_world_truth(&make_atom("foo", None)), Some(false));

        let effect2: Effect = effects.pop().unwrap();
        assert_eq!(effect2.trigger, EffectTrigger::Postulation(make_postulation(false, [make_atom("foo", None)], None)));
        assert_eq!(effect2.interpretation.closed_world_truth(&make_atom("foo", None)), Some(false));

        let effect1: Effect = effects.pop().unwrap();
        assert_eq!(effect1.trigger, EffectTrigger::Postulation(make_postulation(true, [make_atom("foo", None)], None)));
        assert_eq!(effect1.interpretation.closed_world_truth(&make_atom("foo", None)), Some(true));
    }

    // #[test]
    // fn test_transition_race() {
    //     #[cfg(feature = "log")]
    //     crate::tests::setup_logger();

    //     // Setup a nice example with a race
    //     let race: TransitionSpec<&str, &str> = datalog_trans!(
    //         #![crate]

    //         amy. racer(amy).
    //         bob. racer(bob).

    //         apple_town. place(apple_town).
    //         banana_city. place(banana_city).
    //         pear_ville. place(pear_ville).
    //         path(apple_town, banana_city).
    //         path(banana_city, pear_ville).

    //         // We do this as a postulation, so the transition below can undo it
    //         +{ at(amy, apple_town), at(bob, apple_town) }.

    //         #move_amy {
    //             +{ at(amy, X) } :- at(amy, Y), path(Y, X).
    //             ~{ at(amy, X) }.
    //         }.

    //         !{ #move_amy }.
    //     );
    //     let (_, mut effects): (State, Vec<Effect>) = match race.run() {
    //         Ok(res) => res,
    //         Err(err) => panic!("{err}"),
    //     };
    //     assert_eq!(effects.len(), 3);
    //     println!("EFFECT1: {}", effects[0].interpretation);
    //     println!("EFFECT2: {}", effects[1].interpretation);
    //     println!("EFFECT3: {}", effects[2].interpretation);

    //     // Replay the effects
    //     let effect3: Effect = effects.pop().unwrap();
    //     assert_eq!(effect3.trigger, EffectTrigger::End);
    //     assert_eq!(effect3.interpretation.closed_world_truth(&make_atom("at", ["amy", "apple_town"])), Some(false));
    //     assert_eq!(effect3.interpretation.closed_world_truth(&make_atom("at", ["amy", "banana_city"])), Some(true));
    //     assert_eq!(effect3.interpretation.closed_world_truth(&make_atom("at", ["amy", "pear_ville"])), Some(false));

    //     let effect2: Effect = effects.pop().unwrap();
    //     assert_eq!(effect2.trigger, EffectTrigger::Trigger(make_trigger(["#move_amy"])));
    //     assert_eq!(effect2.interpretation.closed_world_truth(&make_atom("at", ["amy", "apple_town"])), Some(false));
    //     assert_eq!(effect2.interpretation.closed_world_truth(&make_atom("at", ["amy", "banana_city"])), Some(true));
    //     assert_eq!(effect2.interpretation.closed_world_truth(&make_atom("at", ["amy", "pear_ville"])), Some(false));

    //     let effect1: Effect = effects.pop().unwrap();
    //     assert_eq!(
    //         effect1.trigger,
    //         EffectTrigger::Postulation(make_postulation(
    //             true,
    //             [make_atom("at", ["amy", "apple_town"]), make_atom("at", ["bob", "apple_town"])],
    //             None
    //         ))
    //     );
    //     assert_eq!(effect1.interpretation.closed_world_truth(&make_atom("at", ["amy", "apple_town"])), Some(true));
    //     assert_eq!(effect1.interpretation.closed_world_truth(&make_atom("at", ["amy", "banana_city"])), Some(false));
    //     assert_eq!(effect1.interpretation.closed_world_truth(&make_atom("at", ["amy", "pear_ville"])), Some(false));
    // }
}
