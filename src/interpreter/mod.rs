//  MOD.rs
//    by Lut99
//
//  Created:
//    26 Mar 2024, 19:36:31
//  Last edited:
//    28 Nov 2024, 16:51:31
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
pub mod interpretation;

use std::collections::HashMap;
// Imports
use std::error;
use std::fmt::{Display, Formatter, Result as FResult};

use indexmap::set::IndexSet;

use self::interpretation::{Interpretation, VarQuantifier};
use crate::ast::{AtomArg, Ident, Rule, Spec};
use crate::log::{debug, trace};


/***** TESTS *****/
#[cfg(all(test, feature = "macros"))]
mod tests {
    use ast_toolkit::punctuated::Punctuated;
    use ast_toolkit::span::Span;
    use datalog_macros::datalog;

    use super::*;
    use crate::ast::{Atom, AtomArgs, Comma, Parens};


    /// Sets up a logger if wanted.
    #[cfg(feature = "log")]
    fn setup_logger() {
        use humanlog::{DebugMode, HumanLogger};

        // Check if the envs tell us to
        if let Ok(logger) = std::env::var("LOGGER") {
            if logger == "1" || logger == "true" {
                // Create the logger
                if let Err(err) = HumanLogger::terminal(DebugMode::Full).init() {
                    eprintln!("WARNING: Failed to setup logger: {err} (no logging for this session)");
                }
            }
        }
    }

    /// Makes an [`Atom`] conveniently.
    fn make_atom(name: &'static str, args: impl IntoIterator<Item = &'static str>) -> Atom<&'static str, &'static str> {
        // Make the punctuation
        let mut punct: Punctuated<AtomArg<_, _>, Comma<_, _>> = Punctuated::new();
        for (i, arg) in args.into_iter().enumerate() {
            if i == 0 {
                punct.push_first(AtomArg::Atom(Ident { value: Span::new("make_atom::arg", arg) }));
            } else {
                punct.push(Comma { span: Span::new("make_atom::arg::comma", ",") }, AtomArg::Atom(Ident { value: Span::new("make_atom::arg", arg) }));
            }
        }

        // Make the atom
        Atom {
            ident: Ident { value: Span::new("make_atom::name", name) },
            args:  if !punct.is_empty() {
                Some(AtomArgs {
                    paren_tokens: Parens { open: Span::new("make_atom::parens::open", "("), close: Span::new("make_atom::parens::close", ")") },
                    args: punct,
                })
            } else {
                None
            },
        }
    }


    #[test]
    fn test_spec_alternating_fixpoint() {
        #[cfg(feature = "log")]
        setup_logger();

        // Try some constants
        let consts: Spec<_, _> = datalog! {
            #![crate]
            foo. bar. baz.
        };
        let res: Interpretation = match consts.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 3);
        assert_eq!(res.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", None)), Some(true));

        // Try some functions
        let funcs: Spec<_, _> = datalog! {
            #![crate]
            foo(bar). bar(baz). baz(quz).
        };
        let res: Interpretation = match funcs.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 3);
        assert_eq!(res.closed_world_truth(&make_atom("foo", Some("bar"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", Some("baz"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", Some("quz"))), Some(true));

        // Try some rules
        let rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar(foo) :- foo.
        };
        let res: Interpretation = match rules.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 2);
        assert_eq!(res.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", Some("foo"))), Some(true));

        // Try some rules with negation!
        let neg_rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar(foo) :- foo. bar(bar) :- not bar.
        };
        let res: Interpretation = match neg_rules.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 4);
        assert_eq!(res.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("bar", Some("foo"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", Some("bar"))), Some(true));

        // Now some cool rules with variables
        let var_rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar. baz(foo). quz(X) :- baz(X). qux(X) :- not baz(X).
        };
        let res: Interpretation = match var_rules.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 8);
        assert_eq!(res.closed_world_truth(&make_atom("foo", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("bar", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", Some("foo"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("baz", Some("bar"))), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("quz", Some("foo"))), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("quz", Some("bar"))), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("qux", Some("foo"))), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("qux", Some("bar"))), Some(true));

        // Arity > 1
        let big_rules: Spec<_, _> = datalog! {
            #![crate]
            foo. bar. baz(foo). quz(X, foo) :- baz(X), foo. qux(X, Y) :- not quz(X, Y).
        };
        let res: Interpretation = match big_rules.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
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

        // Impossible rules
        let con_rules: Spec<_, _> = datalog! {
            #![crate]
            foo :- not foo.
        };
        let res: Interpretation = match con_rules.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 1);
        assert_eq!(res.closed_world_truth(&make_atom("foo", [])), None);
        assert_eq!(res.closed_world_truth(&make_atom("bingo", ["boingo"])), Some(false));
    }

    #[test]
    fn test_spec_alternating_fixpoint_paper() {
        #[cfg(feature = "log")]
        setup_logger();


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
        let res: Interpretation = match five_one.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 7);
        assert_eq!(res.closed_world_truth(&make_atom("a", None)), None);
        assert_eq!(res.closed_world_truth(&make_atom("b", None)), None);
        assert_eq!(res.closed_world_truth(&make_atom("c", None)), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("p", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("q", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("r", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("s", None)), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("t", None)), Some(false));


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
        let res: Interpretation = match five_two_a.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
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
        let res: Interpretation = match five_two_b.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 12);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["a"])), None);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["b"])), None);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["c"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["d"])), Some(false));


        // Example 5.2 (b)
        // NOTE: Example uses `mov` instead of `move`, cuz `move` is a Rust keyword :)
        let five_two_c: Spec<_, _> = datalog! {
            #![crate]
            wins(X) :- mov(X, Y), not wins(Y).

            a. b. c.

            mov(a, b).
            mov(b, a).
            mov(b, c).
        };
        let res: Interpretation = match five_two_c.alternating_fixpoint() {
            Ok(res) => res,
            Err(err) => panic!("{err}"),
        };
        assert_eq!(res.len(), 9);
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["a"])), Some(false));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["b"])), Some(true));
        assert_eq!(res.closed_world_truth(&make_atom("wins", ["c"])), Some(false));
    }
}





/***** ERRORS *****/
/// Defines logic errors over the quantification in rules.
#[derive(Debug)]
pub enum Error<'f, 's> {
    QuantifyOverflow { rule: Rule<&'f str, &'s str>, max: usize },
}
impl<'f, 's> Display for Error<'f, 's> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use Error::*;
        match self {
            QuantifyOverflow { rule, max } => {
                write!(f, "Rule '{rule}' has more than {max} arguments in its atoms; cannot quantify over its variables")
            },
        }
    }
}
impl<'f, 's> error::Error for Error<'f, 's> {}





/***** HELPER FUNCTIONS *****/
/// Generates a string that represents an instantiated rule.
///
/// # Arguments
/// - `rule`: The actual [`Rule`] to instantiate.
/// - `assign`: Some assignment for the rule's variables.
///
/// # Returns
/// A [`String`] representing the format.
#[cfg(feature = "log")]
fn format_rule_assign(rule: &Rule<&str, &str>, assign: &HashMap<Ident<&str, &str>, Ident<&str, &str>>) -> String {
    let mut buf: String = String::new();

    // Consequences
    for cons in rule.consequences.values() {
        buf.push_str(&format!(
            "{}({})",
            cons.ident,
            cons.args
                .iter()
                .flat_map(|a| a.args.values())
                .map(|a| match a {
                    AtomArg::Atom(a) => a.to_string(),
                    AtomArg::Var(v) => assign.get(v).unwrap().to_string(),
                })
                .collect::<Vec<String>>()
                .join(",")
        ));
    }

    // Write the arrow
    buf.push_str(" :- ");

    // Antecedents
    for ante in rule.tail.iter().flat_map(|t| t.antecedents.values()) {
        buf.push_str(&format!(
            "{}{}({})",
            if ante.polarity() { "" } else { "not " },
            ante.atom().ident,
            ante.atom()
                .args
                .iter()
                .flat_map(|a| a.args.values())
                .map(|a| match a {
                    AtomArg::Atom(a) => a.to_string(),
                    AtomArg::Var(v) => assign.get(v).unwrap().to_string(),
                })
                .collect::<Vec<String>>()
                .join(",")
        ));
    }

    // Done
    buf.push('.');
    buf
}

/// Generates a string that represents an instantiated literal.
///
/// # Arguments
/// - `lit`: The actual [`Literal`] to instantiate.
/// - `assign`: Some assignment for the literal's variables.
///
/// # Returns
/// A [`String`] representing the format.
#[cfg(feature = "log")]
fn format_lit_assign(lit: &crate::ast::Literal<&str, &str>, assign: &HashMap<Ident<&str, &str>, Ident<&str, &str>>) -> String {
    format!(
        "{}{}({})",
        if lit.polarity() { "" } else { "not " },
        lit.atom().ident,
        lit.atom()
            .args
            .iter()
            .flat_map(|a| a.args.values())
            .map(|a| match a {
                AtomArg::Atom(a) => a.to_string(),
                AtomArg::Var(v) => assign.get(v).unwrap().to_string(),
            })
            .collect::<Vec<String>>()
            .join(",")
    )
}

/// Generates a string that represents an instantiated atom.
///
/// # Arguments
/// - `atom`: The actual [`Atom`] to instantiate.
/// - `assign`: Some assignment for the atom's variables.
///
/// # Returns
/// A [`String`] representing the format.
#[cfg(feature = "log")]
fn format_atom_assign(atom: &crate::ast::Atom<&str, &str>, assign: &HashMap<Ident<&str, &str>, Ident<&str, &str>>) -> String {
    format!(
        "{}({})",
        atom.ident,
        atom.args
            .iter()
            .flat_map(|a| a.args.values())
            .map(|a| match a {
                AtomArg::Atom(a) => a.to_string(),
                AtomArg::Var(v) => assign.get(v).unwrap().to_string(),
            })
            .collect::<Vec<String>>()
            .join(",")
    )
}





/***** LIBRARY FUNCTIONS *****/
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
///
/// # Returns
/// Whether any new facts were derived or not.
///
/// # Errors
/// This function can error if the total number of arguments in a rule exceeds `LEN`,
pub fn immediate_consequence<'f: 'r, 's: 'r, 'r, 'i, I>(rules: I, int: &'i mut Interpretation<'f, 's>) -> Result<bool, Error<'f, 's>>
where
    I: IntoIterator<Item = &'r Rule<&'f str, &'s str>>,
    I::IntoIter: Clone,
{
    let rules = rules.into_iter();
    debug!("Running immediate consequent transformation");

    // Some buffer referring to all the constants in the interpretation.
    let consts: IndexSet<Ident<_, _>> = int.find_existing_consts();
    // Some buffer for holding variable quantifiers
    let mut vars: HashMap<Ident<_, _>, VarQuantifier> = HashMap::new();
    // Some buffer for holding variable assignments
    let mut assign: HashMap<Ident<_, _>, Ident<_, _>> = HashMap::new();

    // This transformation is saturating, so continue until the database did not change anymore.
    // NOTE: Monotonic because we can never remove truths, inferring the same fact does not count as a change and we are iterating over a Herbrand instantiation so our search space is finite (for $Datalog^\neg$, at least).
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
        'rule: for rule in rules.clone() {
            // First, build quantifiers for this rule's variables
            vars.clear();
            for arg in rule
                .consequences
                .values()
                .flat_map(|c| c.args.iter().flat_map(|a| a.args.values()))
                .chain(rule.tail.iter().flat_map(|t| t.antecedents.values().flat_map(|a| a.atom().args.iter().flat_map(|a| a.args.values()))))
            {
                if let AtomArg::Var(v) = arg {
                    let vars_len: usize = vars.len();
                    if !vars.contains_key(v) {
                        vars.insert(*v, VarQuantifier::new(vars_len));
                    }
                }
            }
            let n_vars: usize = vars.len();

            // Now switch on whether there are any or not
            if n_vars > 0 {
                'assign: loop {
                    // Get the next assignment
                    assign.clear();
                    for (v, i) in vars.iter_mut() {
                        match i.next(&consts, n_vars) {
                            Some(a) => {
                                assign.insert(*v, a);
                            },
                            None => break 'assign,
                        }
                    }
                    trace!("--> Rule '{}'", format_rule_assign(rule, &assign));

                    // Do the antecedents for this assignment
                    for ant in rule.tail.iter().flat_map(|t| t.antecedents.values()) {
                        if !int.knows_about_atom_with_assign(ant.atom(), &assign, ant.polarity()) {
                            // Not present; cannot derive
                            trace!("-----> Antecedent '{}' not present in interpretation, rule does not apply", format_lit_assign(ant, &assign));
                            continue 'assign;
                        }
                    }

                    // If here, then derive consequents
                    for con in rule.consequences.values() {
                        trace!("-----> Deriving consequent '{}'", format_atom_assign(con, &assign));
                        if int.learn_with_assign(con, &assign, true) != Some(true) {
                            changed = true;
                        }
                    }
                }
            } else {
                trace!("--> Rule '{rule}'");

                // It's easier; no need to do assignments
                for ant in rule.tail.iter().flat_map(|t| t.antecedents.values()) {
                    if !int.knows_about_atom(ant.atom(), ant.polarity()) {
                        // Not present; cannot derive
                        trace!("-----> Antecedent '{ant}' not present in interpretation, rule does not apply");
                        continue 'rule;
                    }
                }

                // If here, then derive consequents
                for con in rule.consequences.values() {
                    trace!("-----> Deriving consequent '{con}'");
                    if int.learn(con, true) != Some(true) {
                        changed = true;
                    }
                }
            }
        }
    }

    // Done!
    trace!("Done saturating immediate consequent transformation (took {i} passes)");
    Ok(changed)
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
///
/// # Errors
/// This function can error if the total number of arguments in a rule exceeds `LEN`.
pub fn alternating_fixpoint<'f: 'r, 's: 'r, 'r, I>(rules: I) -> Result<Interpretation<'f, 's>, Error<'f, 's>>
where
    I: IntoIterator<Item = &'r Rule<&'f str, &'s str>>,
    I::IntoIter: Clone,
{
    let mut int: Interpretation = Interpretation::new();
    alternating_fixpoint_mut(rules, &mut int)?;
    Ok(int)
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
///
/// # Errors
/// This function can error if the total number of arguments in a rule exceeds `LEN`.
pub fn alternating_fixpoint_mut<'f: 'r, 's: 'r, 'r, 'i, I>(rules: I, int: &'i mut Interpretation<'f, 's>) -> Result<(), Error<'f, 's>>
where
    I: IntoIterator<Item = &'r Rule<&'f str, &'s str>>,
    I::IntoIter: Clone,
{
    let rules = rules.into_iter();
    debug!(
        "Running alternating-fixpoint transformation\n\nSpec:\n{}\n{}{}\n",
        (0..80).map(|_| '-').collect::<String>(),
        rules.clone().map(|r| format!("   {r}\n")).collect::<String>(),
        (0..80).map(|_| '-').collect::<String>()
    );
    int.clear();

    // Create the universe of atoms
    int.extend_universe(rules.clone());

    // Contains the hash of the last three interpretations, to recognize when we found a stable model.
    let mut prev_hashes: [u64; 3] = [0; 3];

    // We alternate
    let mut i: usize = 0;
    loop {
        i += 1;
        debug!("Starting alternating-fixpoint run {i}");

        // Do the trick; first the immediate consequence, then the stable transformation
        immediate_consequence(rules.clone(), int)?;
        debug!("Post-operator interpretation\n\n{int}\n");

        // See if we reached a stable point
        let hash: u64 = int.hash();
        if i % 2 == 1 && prev_hashes[0] == prev_hashes[2] && prev_hashes[1] == hash {
            // Stable! Merge the stable transformation and the result and we're done
            debug!("Completed alternating-fixpoint transformation (took {i} runs)");
            return Ok(());
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
    ///
    /// # Returns
    /// Whether any new facts were derived or not.
    ///
    /// # Errors
    /// This function can error if the total number of arguments in a rule exceeds `LEN`,
    #[inline]
    pub fn immediate_consequence(&self, int: &mut Interpretation<'f, 's>) -> Result<bool, Error> { immediate_consequence(&self.rules, int) }

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
    ///
    /// # Errors
    /// This function can error if the total number of arguments in a rule exceeds `LEN`.
    #[inline]
    pub fn alternating_fixpoint(&self) -> Result<Interpretation<'f, 's>, Error> { alternating_fixpoint(&self.rules) }

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
    ///
    /// # Errors
    /// This function can error if the total number of arguments in a rule exceeds `LEN`.
    #[inline]
    pub fn alternating_fixpoint_mut(&self, int: &mut Interpretation<'f, 's>) -> Result<(), Error> { alternating_fixpoint_mut(&self.rules, int) }
}
