//  MOD.rs
//    by Lut99
//
//  Created:
//    29 Nov 2024, 16:26:50
//  Last edited:
//    13 Feb 2025, 15:47:15
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
use std::error;
use std::fmt::{Display, Formatter, Result as FResult};

use ast_toolkit::span::SpannableDisplay;
use better_derive::{Clone, Debug, Eq, Hash, PartialEq};
use log::{debug, trace};
use state::State;

use super::ast::{Phrase, Postulation, TransitionSpec, Trigger};
use crate::interpreter::KnowledgeBase;
use crate::ir::{Atom, GroundAtom, Ident, Rule, Span, Spec};
use crate::transitions::ast::{PostulationOp, Transition};


/***** ERRORS *****/
/// Defines errors occurring when computing transitions.
#[derive(Debug)]
pub enum Error<F, S> {
    /// Failed to compile an input rule.
    RuleCompile { err: crate::ir::compile::Error<F, S> },
    /// A given transition is undefined.
    UndefinedTransition { ident: Ident<F, S> },
}
impl<F, S: SpannableDisplay> Display for Error<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::RuleCompile { .. } => write!(f, "Failed to compile rule"),
            Self::UndefinedTransition { ident } => write!(f, "Undefined transition \"{ident}\""),
        }
    }
}
impl<F, S: SpannableDisplay> error::Error for Error<F, S>
where
    Span<F, S>: 'static,
{
    #[inline]
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::RuleCompile { err } => Some(err),
            Self::UndefinedTransition { .. } => None,
        }
    }
}
impl<F, S> From<crate::ir::compile::Error<F, S>> for Error<F, S> {
    #[inline]
    fn from(value: crate::ir::compile::Error<F, S>) -> Self { Self::RuleCompile { err: value } }
}





/***** HELPER FUNCTIONS ****/
/// Computes a [`Spec`] from the given [`State`].
fn state_to_spec<'a, F, S>(
    rules: impl IntoIterator<Item = &'a Rule<Atom<F, S>>>,
    posts: impl IntoIterator<Item = &'a GroundAtom<F, S>>,
) -> Spec<Atom<F, S>>
where
    Span<F, S>: 'a + Clone,
{
    Spec {
        rules: rules
            .into_iter()
            .cloned()
            .chain(posts.into_iter().map(|atom| Rule {
                consequents:     vec![atom.to_atom()],
                pos_antecedents: Vec::new(),
                neg_antecedents: Vec::new(),
            }))
            .collect(),
    }
}





/***** AUXILLARY *****/
/// Keeps track of effects as they occur during transitions.
#[derive(Clone, Debug)]
pub struct Effect<F, S> {
    /// The phrase that triggered this effect.
    pub trigger: EffectTrigger<F, S>,
    /// The denotation after the step.
    pub kb:      KnowledgeBase<F, S>,
}
impl<F, S> Effect<F, S> {
    /// Constructor for the Effect that initializes it to an empty one.
    ///
    /// # Arguments
    /// - `phrase`: The phrase that triggered this effect.
    ///
    /// # Returns
    /// A new Effect that has yet to be populated.
    #[inline]
    pub fn new(trigger: impl Into<EffectTrigger<F, S>>) -> Self { Self { trigger: trigger.into(), kb: KnowledgeBase::new() } }
}

/// The reason that triggered an [`Effect`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum EffectTrigger<F, S> {
    /// A raw postulation.
    Postulation(Postulation<F, S>),
    /// A trigger.
    Trigger(Trigger<F, S>),
    /// The end of the spec.
    End,
}
impl<F, S> Display for EffectTrigger<F, S>
where
    S: SpannableDisplay,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        match self {
            Self::Postulation(p) => p.fmt(f),
            Self::Trigger(p) => p.fmt(f),
            Self::End => write!(f, "<end of spec>"),
        }
    }
}
impl<F, S> From<Postulation<F, S>> for EffectTrigger<F, S> {
    #[inline]
    fn from(value: Postulation<F, S>) -> Self { Self::Postulation(value) }
}
impl<F, S> From<Trigger<F, S>> for EffectTrigger<F, S> {
    #[inline]
    fn from(value: Trigger<F, S>) -> Self { Self::Trigger(value) }
}
impl<F, S> From<()> for EffectTrigger<F, S> {
    #[inline]
    fn from(_value: ()) -> Self { Self::End }
}





/***** LIBRARY *****/
impl<F, S> TransitionSpec<F, S>
where
    S: SpannableDisplay,
    Span<F, S>: Clone + Eq + std::hash::Hash + Ord,
{
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
    pub fn run(&self) -> Result<(State<F, S>, Vec<Effect<F, S>>), Error<F, S>> {
        let mut state = State::new();

        // Leave the rest to the mutable interface
        let effects: Vec<Effect<F, S>> = self.run_mut(&mut state)?;
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
    pub fn run_mut(&self, state: &mut State<F, S>) -> Result<Vec<Effect<F, S>>, Error<F, S>> {
        let State { trans: transitions, rules, posts } = state;
        debug!(
            "Running transitions\n\nTransitionSpec:\n{}\n{}{}\n",
            "-".repeat(80),
            self.phrases.iter().map(|p| format!("   {}\n", p.to_string().replace('\n', "\n   "))).collect::<String>(),
            "-".repeat(80),
        );

        // Go through everything in the spec!
        let mut effects: Vec<Effect<F, S>> = Vec::new();
        for phrase in &self.phrases {
            match phrase {
                // We collect rules & definitions as we find them.
                Phrase::Rule(rule) => {
                    trace!("--> Rule '{rule}'");
                    rules.insert(rule.compile()?);
                },
                Phrase::Transition(trans) => {
                    trace!("--> Transition '{trans}'");
                    if transitions.insert(trans.ident.clone(), trans.clone()).is_some() {
                        // TODO: Already exists. Warning of some kind.
                    }
                },

                // Postulations and triggers will trigger inferences
                Phrase::Postulation(post) => {
                    trace!("--> Postulation '{post}'");
                    let mut effect: Effect<F, S> = Effect::new(post.clone());

                    // First, with the current KB, do an inference run to find out which postconditions are derived
                    let mut spec: Spec<Atom<F, S>> = state_to_spec(rules.iter(), posts.iter());
                    spec.rules.push(post.to_rule());
                    // NOTE: This function clears the interpretation for us
                    debug!("Running post-condition inference step");
                    let kb: KnowledgeBase<F, S> = spec.alternating_fixpoint();

                    // Update the state according to the current knowledge base
                    match post.op {
                        PostulationOp::Create(_) => {
                            for atom in post.consequents.values() {
                                let atom = atom.compile();
                                for atom in atom.concretize_for(kb.truths()) {
                                    if kb.closed_world_truth(&atom) == Some(true) {
                                        debug!("Postulated '{atom}'");
                                        posts.insert(atom);
                                    }
                                }
                            }
                        },
                        PostulationOp::Obfuscate(_) => {
                            for atom in post.consequents.values() {
                                let atom = atom.compile();
                                for atom in atom.concretize_for(kb.truths()) {
                                    if kb.closed_world_truth(&atom) == Some(true) {
                                        debug!("Obfuscated '{atom}'");
                                        posts.shift_remove(&atom);
                                    }
                                }
                            }
                        },
                    }

                    // Now we run an interpretation FOR REAL
                    debug!("Running REAL inference step");
                    effect.kb.reset();
                    state_to_spec(rules.iter(), posts.iter()).alternating_fixpoint_mut(&mut effect.kb);

                    // OK!
                    effects.push(effect);
                },
                Phrase::Trigger(trigger) => {
                    trace!("--> Trigger '{trigger}'");
                    let mut effect: Effect<F, S> = Effect::new(trigger.clone());

                    // Process all the rules postulation by all referred transitions
                    let mut creations: Vec<GroundAtom<F, S>> = Vec::new();
                    let mut obfuscations: Vec<GroundAtom<F, S>> = Vec::new();
                    for ident in &trigger.idents {
                        // Find the transition in the state
                        let trans: &Transition<F, S> = match transitions.get(ident) {
                            Some(trans) => trans,
                            None => return Err(Error::UndefinedTransition { ident: ident.clone() }),
                        };

                        // Handle its postulations
                        for post in &trans.postulations {
                            // First, with the current KB, do an inference run to find out which postconditions are derived
                            let mut spec: Spec<Atom<F, S>> = state_to_spec(rules.iter(), posts.iter());
                            spec.rules.push(post.to_rule());
                            // NOTE: This function clears the interpretation for us
                            debug!("Running post-condition inference step");
                            let kb: KnowledgeBase<F, S> = spec.alternating_fixpoint();

                            // Update the state according to the current knowledge base
                            match post.op {
                                PostulationOp::Create(_) => {
                                    for atom in post.consequents.values() {
                                        let atom = atom.compile();
                                        for atom in atom.concretize_for(kb.truths()) {
                                            trace!("Considering atom '{atom}' for creation");
                                            if kb.closed_world_truth(&atom) == Some(true) {
                                                debug!("--> Postulated '{atom}'");
                                                creations.push(atom.clone());
                                            }
                                        }
                                    }
                                },
                                PostulationOp::Obfuscate(_) => {
                                    for atom in post.consequents.values() {
                                        let atom = atom.compile();
                                        for atom in atom.concretize_for(kb.truths()) {
                                            trace!("Considering atom '{atom}' for obfuscation");
                                            if kb.closed_world_truth(&atom) == Some(true) {
                                                debug!("--> Obfuscated '{atom}'");
                                                obfuscations.push(atom.clone());
                                            }
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
                    effect.kb.reset();
                    state_to_spec(rules.iter(), posts.iter()).alternating_fixpoint_mut(&mut effect.kb);

                    // OK!
                    effects.push(effect);
                },
            };
        }

        // Run a final postulation
        let mut effect: Effect<F, S> = Effect::new(EffectTrigger::End);
        effect.kb.reset();
        state_to_spec(rules.iter(), posts.iter()).alternating_fixpoint_mut(&mut effect.kb);
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
    use crate::ast::{Arrow, Atom, Comma, Dot, Literal, RuleBody};
    use crate::tests::{make_atom, make_curly, make_ident, make_ir_ground_atom};
    use crate::transitions::ast::{Add, Squiggly};


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
                Some(RuleBody { arrow_token: Arrow { span: Span::new("make_postulation::arrow", ":-") }, antecedents })
            } else {
                None
            },
            dot: Dot { span: Span::new("make_postulation::dot", ".") },
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
        let mut effects: Vec<Effect<&'static str, &'static str>> = match five_one.run() {
            Ok((_, effects)) => effects,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(effects.len(), 1);

        let effect: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect.kb.closed_world_truth(&make_ir_ground_atom("a", None)), None);
        assert_eq!(effect.kb.closed_world_truth(&make_ir_ground_atom("b", None)), None);
        assert_eq!(effect.kb.closed_world_truth(&make_ir_ground_atom("c", None)), Some(true));
        assert_eq!(effect.kb.closed_world_truth(&make_ir_ground_atom("p", None)), Some(false));
        assert_eq!(effect.kb.closed_world_truth(&make_ir_ground_atom("q", None)), Some(false));
        assert_eq!(effect.kb.closed_world_truth(&make_ir_ground_atom("r", None)), Some(false));
        assert_eq!(effect.kb.closed_world_truth(&make_ir_ground_atom("s", None)), Some(false));
        assert_eq!(effect.kb.closed_world_truth(&make_ir_ground_atom("t", None)), Some(false));
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
        let (state, mut effects): (State<&'static str, &'static str>, Vec<Effect<&'static str, &'static str>>) = match def.run() {
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

        let effect: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect.trigger, EffectTrigger::End);
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
        let (state, mut effects): (State<&'static str, &'static str>, Vec<Effect<&'static str, &'static str>>) = match def.run() {
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

        let effect: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect.trigger, EffectTrigger::End);
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
        let (state, mut effects): (State<&'static str, &'static str>, Vec<Effect<&'static str, &'static str>>) = match def.run() {
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

        let effect: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect.trigger, EffectTrigger::End);
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
        let (_, mut effects): (State<&'static str, &'static str>, Vec<Effect<&'static str, &'static str>>) = match def.run() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(effects.len(), 2);

        let effect2: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect2.trigger, EffectTrigger::End);
        assert_eq!(effect2.kb.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(true));
        assert_eq!(effect2.kb.closed_world_truth(&make_ir_ground_atom("bar", None)), Some(true));

        let effect1: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect1.trigger, EffectTrigger::Postulation(make_postulation(true, [make_atom("bar", None)], None)));
        assert_eq!(effect1.kb.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(true));
        assert_eq!(effect1.kb.closed_world_truth(&make_ir_ground_atom("bar", None)), Some(true));
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
        let (_, mut effects): (State<&'static str, &'static str>, Vec<Effect<&'static str, &'static str>>) = match def.run() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(effects.len(), 3);

        let effect3: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect3.trigger, EffectTrigger::End);
        assert_eq!(effect3.kb.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(false));

        let effect2: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect2.trigger, EffectTrigger::Postulation(make_postulation(false, [make_atom("foo", None)], None)));
        assert_eq!(effect2.kb.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(false));

        let effect1: Effect<&'static str, &'static str> = effects.pop().unwrap();
        assert_eq!(effect1.trigger, EffectTrigger::Postulation(make_postulation(true, [make_atom("foo", None)], None)));
        assert_eq!(effect1.kb.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(true));
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
