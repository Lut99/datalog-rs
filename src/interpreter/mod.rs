//  MOD.rs
//    by Lut99
//
//  Created:
//    26 Mar 2024, 19:36:31
//  Last edited:
//    11 Feb 2025, 17:47:49
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements an interpreter that can evaluate $Datalog^\neg$ programs
//!   ([`Spec`]s).
//!
//!   The interpreter implements the _alternating fixed-point semantics_,
//!   an operational variation on the _well-founded semantics_.
//!
//!   The implementation is based on [1].
//!
//!   # References
//!   [1] A. Van Gelder. 1989. _The alternating fixpoint of logic programs with
//!       negation._ In Proceedings of the eighth ACM SIGACT-SIGMOD-SIGART
//!       symposium on Principles of database systems (PODS '89). Association
//!       for Computing Machinery, New York, NY, USA, 1–10.
//!       <https://doi.org/10.1145/73721.73722>

// Nested modules
mod knowledge_base;
pub mod quantify;

// Imports
use std::collections::HashSet;
use std::hash::Hash;

use ast_toolkit::span::SpannableDisplay;
pub use knowledge_base::KnowledgeBase;

use crate::ir::{Atom, GroundAtom, Rule, Span, Spec};
use crate::log::{debug, trace};


/***** LIBRARY FUNCTIONS *****/
/// Performs forward derivation of a [`Spec`].
///
/// In the paper, this is called the _immediate consequence operator_. It is simply defined as
/// the "forward derivation" of all rules, where we note the rule's consequences as derived if we
/// observe all of its antecedents to be in the given interpretation.
///
/// Note that the paper makes a point to consider all negative antecedents to be "new" atoms,
/// i.e., we must observe negative atoms explicitly instead of the absence of positives.
///
/// # Arguments
/// - `rules`: A set of rules that are in the spec.
/// - `kb`: Some [`KnowledgeBase`] to derive in. Specifically, will move atoms from unknown to
///   known if they can be derived.
pub fn immediate_consequence<'s, I, F, S>(rules: I, kb: &mut KnowledgeBase<F, S>)
where
    I: IntoIterator<Item = &'s Rule<Atom<F, S>>>,
    I::IntoIter: Clone,
    S: SpannableDisplay,
    Span<F, S>: 's + Clone + Eq + Hash,
{
    let rules = rules.into_iter();

    // This transformation is saturating, so continue until the database did not change anymore.
    // NOTE: Monotonic because we can never remove truths, inferring the same fact does not count
    //       as a change and we are iterating over a Herbrand instantiation so our search space is
    //       finite (for $Datalog^\neg$, at least).
    let mut updates: HashSet<GroundAtom<F, S>> = HashSet::new();
    let mut changed: bool = true;
    #[cfg(feature = "log")]
    let mut i: usize = 0;
    while changed {
        changed = false;
        #[cfg(feature = "log")]
        {
            i += 1;
        }
        trace!("Derivation run {i} starting");

        // Go thru da rules to collect updates
        for rule in rules.clone() {
            for rule in rule.concretize_for(kb.truths()) {
                trace!("--> Considering concretized rule '{rule}'");
                if rule.is_satisfied(kb) {
                    trace!("-----> Rule '{rule}' is SATISFIED");
                    updates.extend(rule.consequents)
                }
            }
        }

        // Apply the updates
        for atom in updates.drain() {
            trace!("-----> Deriving '{atom}'");
            changed |= kb.learn(atom);
        }
    }

    // Done!
    trace!("Done saturating immediate consequent transformation (took {i} passes)");
}

/// Performs a proper derivation using the full well-founded semantics.
///
/// In the paper, this is given as:
/// - Apply the immediate consequence operator;
/// - Apply the [stable transformation](KnowledgeBase::apply_stable_transformation()); and
/// - Repeat the last two steps until you reach some state you've seen before (it sufficies to just
///   check the last three states).
///
/// Then the interpretation you're left with is a well-founded model for the spec.
///
/// # Arguments
/// - `rules`: An iterator producing the rules to derive with.
///
/// # Returns
/// A new [`KnowledgeBase`] that contains the things we derived about the facts in the [`Spec`].
pub fn alternating_fixpoint<'s, I, F, S>(rules: I) -> KnowledgeBase<F, S>
where
    I: IntoIterator<Item = &'s Rule<Atom<F, S>>>,
    I::IntoIter: Clone,
    S: SpannableDisplay,
    for<'a> S::Slice<'a>: Ord,
    Span<F, S>: 's + Clone + Eq + Hash,
{
    let mut int: KnowledgeBase<F, S> = KnowledgeBase::new();
    alternating_fixpoint_mut(rules, &mut int);
    int
}

/// Performs a proper derivation using the full well-founded semantics.
///
/// In the paper, this is given as:
/// - Apply the [immediate consequence operator](Self::immediate_consequence());
/// - Apply the [stable transformation](KnowledgeBase::apply_stable_transformation()); and
/// - Repeat the last two steps until you reach some state you've seen before (it sufficies to just
///   check the last three states).
///
/// Then the interpretation you're left with is a well-founded model for the spec.
///
/// # Arguments
/// - `rules`: An iterator producing the rules to derive with.
/// - `kb`: Some existing [`KnowledgeBase`] to populate. Note that it will _not_ be cleared
///   for you; call [`KnowledgeBase::clear()`] first if you're only interested in re-using the
///   memory, not the facts.
pub fn alternating_fixpoint_mut<'s, I, F, S>(rules: I, kb: &mut KnowledgeBase<F, S>)
where
    I: IntoIterator<Item = &'s Rule<Atom<F, S>>>,
    I::IntoIter: Clone,
    S: SpannableDisplay,
    for<'a> S::Slice<'a>: Ord,
    Span<F, S>: 's + Clone + Eq + Hash,
{
    let rules = rules.into_iter();
    debug!(
        "Running alternating-fixpoint transformation\n\nSpec:\n{}\n{}{}\n",
        (0..80).map(|_| '-').collect::<String>(),
        rules.clone().map(|r| format!("   {r}\n")).collect::<String>(),
        (0..80).map(|_| '-').collect::<String>()
    );

    // First, go through the rule once to add its constants to the knowledge base's universe
    for rule in rules.clone() {
        kb.extend_universe_with_rule(rule);
    }

    // We alternate
    let mut prev_hashes: [u64; 3] = [0; 3];
    let mut i: usize = 0;
    loop {
        i += 1;
        debug!("Starting alternating-fixpoint run {i}");

        // Do the trick; first the immediate consequence, then the stable transformation
        immediate_consequence(rules.clone(), kb);
        debug!("Post-consequence knowledge base\n\n{kb}\n");

        // See if we reached a stable point
        let hash: u64 = <KnowledgeBase<F, S>>::hash(kb);
        if i % 2 == 1 && prev_hashes[0] == prev_hashes[2] && prev_hashes[1] == hash {
            // Stable! Merge the stable transformation and the result and we're done
            debug!("Completed alternating-fixpoint transformation (took {i} runs)");
            return;
        }

        // We didn't stabelize; run the stable transformation
        kb.apply_stable_transformation();
        debug!("Post-transformation interpretation\n\n{kb}\n");

        // Move the slots one back
        prev_hashes[0] = prev_hashes[1];
        prev_hashes[1] = prev_hashes[2];
        prev_hashes[2] = hash;
    }
}





/***** LIBRARY *****/
// Interpreter extensions for the [`Spec`].
impl<F, S> Spec<Atom<F, S>>
where
    S: SpannableDisplay,
    Span<F, S>: Clone + Eq + Hash,
{
    /// Performs forward derivation of the Spec.
    ///
    /// In the paper, this is called the _immediate consequence operator_. It is simply defined as
    /// the "forward derivation" of all rules, where we note the rule's consequences as derived if we
    /// observe all of its antecedents to be in the given interpretation.
    ///
    /// Note that the paper makes a point to consider all negative antecedents to be "new" atoms,
    /// i.e., we must observe negative atoms explicitly instead of the absence of positives.
    ///
    /// # Arguments
    /// - `kb`: Some [`KnowledgeBase`] to derive in. Specifically, will move atoms from unknown to
    ///   known if they can be derived.
    #[inline]
    pub fn immediate_consequence(&self, kb: &mut KnowledgeBase<F, S>) { immediate_consequence(&self.rules, kb) }
}
impl<F, S> Spec<Atom<F, S>>
where
    S: SpannableDisplay,
    for<'a> S::Slice<'a>: Ord,
    Span<F, S>: Clone + Eq + Hash,
{
    /// Performs a proper derivation using the full well-founded semantics.
    ///
    /// In the paper, this is given as:
    /// - Apply the immediate consequence operator;
    /// - Apply the [stable transformation](KnowledgeBase::apply_stable_transformation()); and
    /// - Repeat the last two steps until you reach some state you've seen before (it sufficies to
    ///   just check the last three states).
    ///
    /// Then the knowledge base you're left with is a well-founded model for the spec.
    ///
    /// # Returns
    /// A new [`KnowledgeBase`] that contains the things we derived about the facts in the [`Spec`].
    #[inline]
    pub fn alternating_fixpoint(&self) -> KnowledgeBase<F, S> { alternating_fixpoint(&self.rules) }

    /// Performs a proper derivation using the full well-founded semantics.
    ///
    /// In the paper, this is given as:
    /// - Apply the [immediate consequence operator](Self::immediate_consequence());
    /// - Apply the [stable transformation](Interpretation::apply_stable_transformation()); and
    /// - Repeat the last two steps until you reach some state you've seen before (it sufficies to
    ///   just check the last three states).
    ///
    /// Then the interpretation you're left with is a well-founded model for the spec.
    ///
    /// # Arguments
    /// - `kb`: Some existing [`KnowledgeBase`] to populate. Note that it will _not_ be cleared
    ///   for you; call [`KnowledgeBase::clear()`] first if you're only interested in re-using the
    ///   memory, not the facts.
    #[inline]
    pub fn alternating_fixpoint_mut(&self, kb: &mut KnowledgeBase<F, S>) { alternating_fixpoint_mut(&self.rules, kb) }
}



// Interepreter extensions for [`Rule`]s.
impl<F, S> Rule<GroundAtom<F, S>>
where
    S: SpannableDisplay,
    Span<F, S>: Eq + Hash,
{
    /// Checks whether this rule holds in the given knowledge base.
    ///
    /// # Arguments
    /// - `kb`: A knowledge base to check in.
    ///
    /// # Returns
    /// Whether the consequents of this rule can be derived or not.
    #[inline]
    pub fn is_satisfied(&self, kb: &KnowledgeBase<F, S>) -> bool {
        // Check if the rule's positive antecedents exist as true atoms
        for atom in &self.pos_antecedents {
            // See if this atom exists in the knowledge base
            if !kb.holds(true, atom) {
                trace!("-----> Antecedent '{atom}' is UNSATISFIED");
                return false;
            }
            trace!("-----> Antecedent '{atom}' is SATISFIED");
        }

        // Then check if the rule's negative antecedents exist as false atoms
        for atom in &self.neg_antecedents {
            // See if this atom exists in the knowledge base
            if !kb.holds(false, atom) {
                trace!("-----> Antecedent 'not {atom}' is UNSATISFIED");
                return false;
            }
            trace!("-----> Antecedent 'not {atom}' is SATISFIED");
        }

        // Made it this far; derive!
        true
    }
}





/***** TESTS *****/
#[cfg(all(test, feature = "macros"))]
mod tests {
    use datalog_macros::datalog;

    use super::*;
    use crate::tests::make_ir_ground_atom;


    #[test]
    fn test_alternating_fixpoint_constants() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Try some constants
        let consts: Spec<_> = datalog! {
            #![crate]
            foo. bar. baz.
        }
        .compile()
        .unwrap();
        let res: KnowledgeBase<_, _> = consts.alternating_fixpoint();
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bar", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("baz", None)), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_functions() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Try some functions
        let funcs: Spec<_> = datalog! {
            #![crate]
            foo(bar). bar(baz). baz(quz).
        }
        .compile()
        .unwrap();
        let res: KnowledgeBase<_, _> = funcs.alternating_fixpoint();
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("foo", Some("bar"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bar", Some("baz"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("baz", Some("quz"))), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_rules() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Try some rules
        let rules: Spec<_> = datalog! {
            #![crate]
            foo. bar(foo) :- foo.
        }
        .compile()
        .unwrap();
        let res: KnowledgeBase<_, _> = rules.alternating_fixpoint();
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bar", Some("foo"))), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_rules_neg() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Try some rules with negation!
        let neg_rules: Spec<_> = datalog! {
            #![crate]
            foo. bar(foo) :- foo. bar(bar) :- not bar.
        }
        .compile()
        .unwrap();
        let res: KnowledgeBase<_, _> = neg_rules.alternating_fixpoint();
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bar", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bar", Some("foo"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bar", Some("bar"))), Some(true));
    }

    // #[test]
    // fn test_alternating_fixpoint_rules_vars() {
    //     #[cfg(feature = "log")]
    //     crate::tests::setup_logger();

    //     // Now some cool rules with variables
    //     let var_rules: Spec<_> = datalog! {
    //         #![crate]
    //         foo. bar. baz(foo). quz(X) :- baz(X). qux(X) :- not baz(X).
    //     }
    //     .compile()
    //     .unwrap();
    //     let res: KnowledgeBase<_, _> = var_rules.alternating_fixpoint();
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("foo", None)), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bar", None)), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("baz", Some("foo"))), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("baz", Some("bar"))), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("quz", Some("foo"))), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("quz", Some("bar"))), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("qux", Some("foo"))), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("qux", Some("bar"))), Some(true));
    // }

    // #[test]
    // fn test_alternating_fixpoint_rules_many_arity() {
    //     #[cfg(feature = "log")]
    //     crate::tests::setup_logger();

    //     // Arity > 1
    //     let big_rules: Spec<_> = datalog! {
    //         #![crate]
    //         foo. bar. baz(foo). quz(X, foo) :- baz(X), foo. qux(X, Y) :- not quz(X, Y).
    //     }
    //     .compile()
    //     .unwrap();
    //     let res: KnowledgeBase<_, _> = big_rules.alternating_fixpoint();
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("foo", [])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bar", [])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("baz", ["foo"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("baz", ["bar"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("quz", ["foo", "foo"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("quz", ["foo", "bar"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("quz", ["bar", "foo"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("quz", ["bar", "bar"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("qux", ["foo", "foo"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("qux", ["foo", "bar"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("qux", ["bar", "foo"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("qux", ["bar", "bar"])), Some(true));
    // }

    #[test]
    fn test_alternating_fixpoint_rules_unknown() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Impossible rules
        let con_rules: Spec<_> = datalog! {
            #![crate]
            foo :- not foo.
        }
        .compile()
        .unwrap();
        let res: KnowledgeBase<_, _> = con_rules.alternating_fixpoint();
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("foo", [])), None);
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("bingo", ["boingo"])), Some(false));
    }

    #[test]
    fn test_alternating_fixpoint_paper_5_1() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Example 5.1
        let five_one: Spec<_> = datalog! {
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
        }
        .compile()
        .unwrap();
        let res: KnowledgeBase<_, _> = five_one.alternating_fixpoint();
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("a", [])), None);
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("b", [])), None);
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("c", [])), Some(true));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("p", [])), Some(false));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("q", [])), Some(false));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("r", [])), Some(false));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("s", [])), Some(false));
        assert_eq!(res.closed_world_truth(&make_ir_ground_atom("t", [])), Some(false));
    }

    // #[test]
    // fn test_alternating_fixpoint_paper_5_2a() {
    //     #[cfg(feature = "log")]
    //     crate::tests::setup_logger();

    //     // Example 5.2 (a)
    //     // NOTE: Example uses `mov` instead of `move`, cuz `move` is a Rust keyword :)
    //     let five_two_a: Spec<_> = datalog! {
    //         #![crate]
    //         wins(X) :- mov(X, Y), not wins(Y).

    //         a. b. c. d. e. f. g. h. i.

    //         mov(a, b). mov(a, e).
    //         mov(b, c). mov(b, d). mov(e, f). mov(e, g).
    //         mov(g, h). mov(g, i).
    //     }
    //     .compile()
    //     .unwrap();
    //     let res: KnowledgeBase<_, _> = five_two_a.alternating_fixpoint();
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["a"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["b"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["c"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["d"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["e"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["f"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["g"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["h"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["i"])), Some(false));
    // }

    // #[test]
    // fn test_alternating_fixpoint_paper_5_2b() {
    //     #[cfg(feature = "log")]
    //     crate::tests::setup_logger();

    //     // Example 5.2 (b)
    //     // NOTE: Example uses `mov` instead of `move`, cuz `move` is a Rust keyword :)
    //     let five_two_b: Spec<_> = datalog! {
    //         #![crate]
    //         wins(X) :- mov(X, Y), not wins(Y).

    //         a. b. c. d.

    //         mov(a, b).
    //         mov(b, a).
    //         mov(b, c).
    //         mov(c, d).
    //     }
    //     .compile()
    //     .unwrap();
    //     let res: KnowledgeBase<_, _> = five_two_b.alternating_fixpoint();
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["a"])), None);
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["b"])), None);
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["c"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["d"])), Some(false));
    // }

    // #[test]
    // fn test_alternating_fixpoint_paper_5_2c() {
    //     #[cfg(feature = "log")]
    //     crate::tests::setup_logger();

    //     // Example 5.2 (c)
    //     // NOTE: Example uses `mov` instead of `move`, cuz `move` is a Rust keyword :)
    //     let five_two_c: Spec<_> = datalog! {
    //         #![crate]
    //         wins(X) :- mov(X, Y), not wins(Y).

    //         a. b. c.

    //         mov(a, b).
    //         mov(b, a).
    //         mov(b, c).
    //     }
    //     .compile()
    //     .unwrap();
    //     let res: KnowledgeBase<_, _> = five_two_c.alternating_fixpoint();
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["a"])), Some(false));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["b"])), Some(true));
    //     assert_eq!(res.closed_world_truth(&make_ir_ground_atom("wins", ["c"])), Some(false));
    // }
}
