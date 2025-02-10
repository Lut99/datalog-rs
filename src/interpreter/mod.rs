//  MOD.rs
//    by Lut99
//
//  Created:
//    26 Mar 2024, 19:36:31
//  Last edited:
//    10 Feb 2025, 17:10:50
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
// mod interpretation_old;
pub mod knowledge_base;
pub mod quantify;

// Imports
use std::hash::Hash;

use knowledge_base::KnowledgeBase;

use crate::ir::{Atom, Rule, Span};
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
/// - `kb`: Some [`KnowledgeBase`] to derive in. Specifically, will move atoms from unknown to known if they can be derived.
pub fn immediate_consequence<'s, I, F, S>(rules: I, kb: &mut KnowledgeBase<F, S>)
where
    I: IntoIterator<Item = &'s Rule<Atom<F, S>>>,
    I::IntoIter: Clone,
    Span<F, S>: 's + Clone + Eq + Hash,
{
    let rules = rules.into_iter();

    // This transformation is saturating, so continue until the database did not change anymore.
    // NOTE: Monotonic because we can never remove truths, inferring the same fact does not count
    //       as a change and we are iterating over a Herbrand instantiation so our search space is
    //       finite (for $Datalog^\neg$, at least).
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

        // Go thru da rules
        for rule in rules.clone() {
            changed |= kb.update(rule);
        }
    }

    // Done!
    trace!("Done saturating immediate consequent transformation (took {i} passes)");
}

/// Performs a proper derivation using the full well-founded semantics.
///
/// In the paper, this is given as:
/// - Apply the immediate consequence operator;
/// - Apply the [stable transformation](Interpretation::apply_stable_transformation()); and
/// - Repeat the last two steps until you reach some state you've seen before (it sufficies to just check the last three states).
///
/// Then the interpretation you're left with is a well-founded model for the spec.
///
/// # Returns
/// A new [`Interpretation`] that contains the things we derived about the facts in the [`Spec`].
pub fn alternating_fixpoint<'s, I, F, S>(rules: I) -> KnowledgeBase<F, S>
where
    I: IntoIterator<Item = &'s Rule<Atom<F, S>>>,
    I::IntoIter: Clone,
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
/// - Apply the [stable transformation](Interpretation::apply_stable_transformation()); and
/// - Repeat the last two steps until you reach some state you've seen before (it sufficies to just check the last three states).
///
/// Then the interpretation you're left with is a well-founded model for the spec.
///
/// # Arguments
/// - `int`: Some existing [`Interpretation`] to [`clear()`](Interpretation::clear()) and then populate again. Might be more efficient than allocating a new one if you already have one lying around.
pub fn alternating_fixpoint_mut<'s, I, F, S>(rules: I, int: &mut KnowledgeBase<F, S>)
where
    I: IntoIterator<Item = &'s Rule<Atom<F, S>>>,
    I::IntoIter: Clone,
    Span<F, S>: 's + Clone + Eq + Hash,
{
    let rules = rules.into_iter();
    debug!(
        "Running alternating-fixpoint transformation\n\nSpec:\n{}\n{}{}\n",
        (0..80).map(|_| '-').collect::<String>(),
        rules.clone().map(|r| format!("   {r}\n")).collect::<String>(),
        (0..80).map(|_| '-').collect::<String>()
    );
    int.clear();

    // Contains the hash of the last three interpretations, to recognize when we found a stable model.
    let mut prev_hashes: [u64; 3] = [0; 3];

    // We alternate
    let mut i: usize = 0;
    loop {
        i += 1;
        debug!("Starting alternating-fixpoint run {i}");

        // Do the trick; first the immediate consequence, then the stable transformation
        immediate_consequence(rules.clone(), int);
        debug!("Post-operator interpretation\n\n{int}\n");

        // See if we reached a stable point
        let hash: u64 = int.hash();
        if i % 2 == 1 && prev_hashes[0] == prev_hashes[2] && prev_hashes[1] == hash {
            // Stable! Merge the stable transformation and the result and we're done
            debug!("Completed alternating-fixpoint transformation (took {i} runs)");
            return;
        }

        // We didn't stabelize; run the stable transformation
        int.apply_stable_transformation();
        debug!("Post-transformation interpretation\n\n{int}\n");

        // Move the slots one back
        prev_hashes[0] = prev_hashes[1];
        prev_hashes[1] = prev_hashes[2];
        prev_hashes[2] = hash;
    }
}





/***** LIBRARY *****/
// Interpreter extensions for the [`Spec`].
impl<'f, 's> Spec<&'f str, &'s str> {
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
    /// - `int`: Some [`Interpretation`] to derive in. Specifically, will move atoms from unknown to known if they can be derived.
    #[inline]
    pub fn immediate_consequence(&self, int: &mut Interpretation<'f, 's>) { immediate_consequence(&self.rules, int) }

    /// Performs a proper derivation using the full well-founded semantics.
    ///
    /// In the paper, this is given as:
    /// - Apply the immediate consequence operator;
    /// - Apply the [stable transformation](Interpretation::apply_stable_transformation()); and
    /// - Repeat the last two steps until you reach some state you've seen before (it sufficies to just check the last three states).
    ///
    /// Then the interpretation you're left with is a well-founded model for the spec.
    ///
    /// # Returns
    /// A new [`Interpretation`] that contains the things we derived about the facts in the [`Spec`].
    #[inline]
    pub fn alternating_fixpoint(&self) -> Interpretation<'f, 's> { alternating_fixpoint(&self.rules) }

    /// Performs a proper derivation using the full well-founded semantics.
    ///
    /// In the paper, this is given as:
    /// - Apply the [immediate consequence operator](Self::immediate_consequence());
    /// - Apply the [stable transformation](Interpretation::apply_stable_transformation()); and
    /// - Repeat the last two steps until you reach some state you've seen before (it sufficies to just check the last three states).
    ///
    /// Then the interpretation you're left with is a well-founded model for the spec.
    ///
    /// # Arguments
    /// - `int`: Some existing [`Interpretation`] to [`clear()`](Interpretation::clear()) and then populate again. Might be more efficient than allocating a new one if you already have one lying around.
    #[inline]
    pub fn alternating_fixpoint_mut(&self, int: &mut Interpretation<'f, 's>) { alternating_fixpoint_mut(&self.rules, int) }
}





/***** TESTS *****/
#[cfg(all(test, feature = "macros"))]
mod tests {
    use datalog_macros::datalog;

    use super::*;
    use crate::tests::make_atom;


    #[test]
    fn test_alternating_fixpoint_constants() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Try some constants
        let consts: Spec<_, _> = datalog! {
            #![crate]
            foo. bar. baz.
        };
        let res: Interpretation = consts.alternating_fixpoint();
        assert_eq!(res.len(), 3);
        assert_eq!(res.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", None)), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_functions() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Try some functions
        let funcs: Spec<_, _> = datalog! {
            #![crate]
            foo(bar). bar(baz). baz(quz).
        };
        let res: Interpretation = funcs.alternating_fixpoint();
        assert_eq!(res.len(), 3);
        assert_eq!(res.closed_world_truth(&make_atom("foo", Some("bar"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", Some("baz"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", Some("quz"))), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_rules() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Try some rules
        let rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar(foo) :- foo.
        };
        let res: Interpretation = rules.alternating_fixpoint();
        assert_eq!(res.len(), 2);
        assert_eq!(res.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", Some("foo"))), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_rules_neg() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Try some rules with negation!
        let neg_rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar(foo) :- foo. bar(bar) :- not bar.
        };
        let res: Interpretation = neg_rules.alternating_fixpoint();
        assert_eq!(res.len(), 4);
        assert_eq!(res.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("bar", Some("foo"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", Some("bar"))), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_rules_vars() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Now some cool rules with variables
        let var_rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar. baz(foo). quz(X) :- baz(X). qux(X) :- not baz(X).
        };
        let res: Interpretation = var_rules.alternating_fixpoint();
        assert_eq!(res.len(), 8);
        assert_eq!(res.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", Some("foo"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", Some("bar"))), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("quz", Some("foo"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("quz", Some("bar"))), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("qux", Some("foo"))), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("qux", Some("bar"))), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_rules_many_arity() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Arity > 1
        let big_rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar. baz(foo). quz(X, foo) :- baz(X), foo. qux(X, Y) :- not quz(X, Y).
        };
        let res: Interpretation = big_rules.alternating_fixpoint();
        assert_eq!(res.len(), 11);
        assert_eq!(res.closed_world_truth(&make_atom("foo", [])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", [])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", ["foo"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", ["bar"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("quz", ["foo", "foo"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("quz", ["foo", "bar"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("quz", ["bar", "foo"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("quz", ["bar", "bar"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("qux", ["foo", "foo"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("qux", ["foo", "bar"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("qux", ["bar", "foo"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("qux", ["bar", "bar"])), Some(true));
    }

    #[test]
    fn test_alternating_fixpoint_rules_unknown() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Impossible rules
        let con_rules: Spec<_, _> = datalog! {
            #![crate]
            foo :- not foo.
        };
        let res: Interpretation = con_rules.alternating_fixpoint();
        assert_eq!(res.len(), 1);
        assert_eq!(res.closed_world_truth(&make_atom("foo", [])), None);
        assert_eq!(res.closed_world_truth(&make_atom("bingo", ["boingo"])), Some(false));
    }

    #[test]
    fn test_alternating_fixpoint_paper_5_1() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Example 5.1
        let five_one: Spec<_, _> = datalog! {
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
        let res: Interpretation = five_one.alternating_fixpoint();
        assert_eq!(res.len(), 7);
        assert_eq!(res.closed_world_truth(&make_atom("a", None)), None);
        assert_eq!(res.closed_world_truth(&make_atom("b", None)), None);
        assert_eq!(res.closed_world_truth(&make_atom("c", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("p", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("q", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("r", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("s", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("t", None)), Some(false));
    }

    #[test]
    fn test_alternating_fixpoint_paper_5_2a() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Example 5.2 (a)
        // NOTE: Example uses `mov` instead of `move`, cuz `move` is a Rust keyword :)
        let five_two_a: Spec<_, _> = datalog! {
            #![crate]
            wins(X) :- mov(X, Y), not wins(Y).

            a. b. c. d. e. f. g. h. i.

            mov(a, b). mov(a, e).
            mov(b, c). mov(b, d). mov(e, f). mov(e, g).
            mov(g, h). mov(g, i).
        };
        let res: Interpretation = five_two_a.alternating_fixpoint();
        assert_eq!(res.len(), 26);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["a"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["b"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["c"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["d"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["e"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["f"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["g"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["h"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["i"])), Some(false));
    }

    #[test]
    fn test_alternating_fixpoint_paper_5_2b() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Example 5.2 (b)
        // NOTE: Example uses `mov` instead of `move`, cuz `move` is a Rust keyword :)
        let five_two_b: Spec<_, _> = datalog! {
            #![crate]
            wins(X) :- mov(X, Y), not wins(Y).

            a. b. c. d.

            mov(a, b).
            mov(b, a).
            mov(b, c).
            mov(c, d).
        };
        let res: Interpretation = five_two_b.alternating_fixpoint();
        assert_eq!(res.len(), 12);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["a"])), None);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["b"])), None);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["c"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["d"])), Some(false));
    }

    #[test]
    fn test_alternating_fixpoint_paper_5_2c() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Example 5.2 (c)
        // NOTE: Example uses `mov` instead of `move`, cuz `move` is a Rust keyword :)
        let five_two_c: Spec<_, _> = datalog! {
            #![crate]
            wins(X) :- mov(X, Y), not wins(Y).

            a. b. c.

            mov(a, b).
            mov(b, a).
            mov(b, c).
        };
        let res: Interpretation = five_two_c.alternating_fixpoint();
        assert_eq!(res.len(), 9);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["a"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["b"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["c"])), Some(false));
    }
}
