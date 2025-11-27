//  QUANTIFY.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 17:58:01
//  Last edited:
//    13 Feb 2025, 10:57:36
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines the quantification procedure for the $Datalog^\neg$
//!   interpreter, once and for all.
//

use std::collections::HashMap;
use std::hash::Hash;

use ast_toolkit::span::Spannable;
use better_derive::Debug;
use indexmap::IndexSet;

use crate::ir::{Atom, Atomlike, GroundAtom, Ident, Rule, Span};


/***** LIBRARY *****/
/// Iterates over some iterator, repeating its element and repeating the whole sequence.
///
/// Specifically:
/// - _inner_ repetition means every element in constant set is repeated (e.g., `111222333` instead
///   of `123`); and
/// - _outer_ repetition means the whole constant set is repeated (e.g., `123123123` instead of
///   `123`).
///
/// Combining these repetitions leads to us being able to do binary-counting-like quantification
/// over multiple variables. For example, with three `CycleRepeat`s, we can iterate like:
/// ```plain
/// 1 -> 111111111222222222333333333 (inner: 9, outer: 1)
/// 2 -> 111222333111222333111222333 (inner: 3, outer: 3)
/// 3 -> 123123123123123123123123123 (inner: 1, outer: 9)
/// ```
#[derive(Clone, Copy, Debug)]
#[better_derive(bounds = (I: r#trait + Iterator, I::Item: r#trait))]
pub struct CycleRepeat<I>
where
    I: Iterator,
{
    /// The set of constants we will iterate over.
    iter_template: I,
    /// The set of constants that we actually iterate over.
    iter: I,
    /// The element we're currently returning.
    elem: Option<I::Item>,
    /// The total number of inner reptitions.
    inner_max: usize,
    /// The total number of outer reptitions.
    outer_max: usize,
    /// The current index of inner repetitions.
    inner_i: usize,
    /// The current index of outer repetitions.
    outer_i: usize,
}
impl<I: Clone + Iterator> CycleRepeat<I> {
    /// Constructor for the CycleRepeat.
    ///
    /// # Arguments
    /// - `into_iter`: The set of constants to quantify and repeat.
    /// - `inner_max`: The number of _inner_ repetitions.
    /// - `outer_max`: The number of _outer_ repetitions.
    ///
    /// # Returns
    /// A new CycleRepeat that will quantify from the start.
    #[inline]
    pub fn new(into_iter: impl IntoIterator<IntoIter = I>, inner_max: usize, outer_max: usize) -> Self {
        let mut iter = into_iter.into_iter();
        let iter_template = iter.clone();
        let elem: Option<I::Item> = iter.next();
        Self { iter_template, iter, elem, inner_max, outer_max, inner_i: 0, outer_i: 0 }
    }
}
impl<I> Iterator for CycleRepeat<I>
where
    I: Clone + Iterator,
    I::Item: Clone,
{
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // See if we need to (continue) repeating the next element
        if self.elem.is_none() || self.inner_i >= self.inner_max {
            // Move to the next element
            self.inner_i = 0;
            match self.iter.next() {
                Some(elem) => {
                    // There still is an element, so recurse to return it
                    self.elem = Some(elem.clone());
                    return self.next();
                },
                None => {
                    // There isn't; repeat the iterator
                    // NOTE: The `+1` is necessary because outer_max is 1-indexed (e.g., 2 for two
                    // repetitions), but outer_i is not (1 _after_ the second repetition)
                    if self.outer_i + 1 < self.outer_max {
                        self.outer_i += 1;
                        self.iter = self.iter_template.clone();
                        self.elem = None;
                        return self.next();
                    } else {
                        // Truly nothing more for us to iterate
                        return None;
                    }
                },
            }
        }

        // Return the element if it's available and we're repeating it
        self.inner_i += 1;
        self.elem.clone()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n: usize = self.len();
        (n, Some(n))
    }
}
impl<I> ExactSizeIterator for CycleRepeat<I>
where
    I: Clone + Iterator,
    I::Item: Clone,
{
    #[inline]
    fn len(&self) -> usize { self.inner_max * self.outer_max }
}

/// An iterator that produces a powerset of N elements over a set.
#[derive(better_derive::Clone, Debug)]
#[better_derive(bounds = (I: r#trait + Iterator, I::Item: r#trait))]
pub struct PowerSet<I>
where
    I: Iterator,
{
    /// Copies for the iterator with repetitions, one for every element.
    iters: Vec<CycleRepeat<I>>,
    /// The total number of iterations we run for. Not used during iteration, only for size hints.
    total_iters: usize,
}
impl<I> PowerSet<I>
where
    I: Clone + ExactSizeIterator + Iterator,
{
    /// Constructor for the PowerSet.
    ///
    /// # Arguments
    /// - `set`: Something producing a set of things to iterate over.
    /// - `n`: The size of every set (i.e., number of variables).
    ///
    /// # Returns
    /// A new PowerSet, ready to combinatorially explode under your nose.
    pub fn new(set: impl IntoIterator<IntoIter = I>, n: usize) -> Self {
        // Generate iterators for all of those variables
        // We scale from essentially doing `111111...333333`, to `111222...222333`, to `123123...123123`
        //
        // Some examples:
        // ```plain
        // 123, three variables:
        // 111111111222222222333333333      (outer = 1, inner = 9)
        // 111222333111222333111222333      (outer = 3, inner = 3)
        // 123123123123123123123123123      (outer = 9, inner = 1)
        //
        // 12, four variables
        // 1111111122222222                 (outer = 1, inner = 8)
        // 1111222211112222                 (outer = 2, inner = 4)
        // 1122112211221122                 (outer = 4, inner = 2)
        // 1212121212121212                 (outer = 8, inner = 1)
        //
        // 1234, two variables
        // 1111222233334444                 (outer = 1, inner = 4)
        // 1234123412341234                 (outer = 4, inner = 1)
        // ```
        // From this we can observe that the outer grows exponentially over the Herbrand base size, whereas the inner grows inverse exponentially.
        let set = set.into_iter();
        let set_len: usize = set.len();
        let iters: Vec<CycleRepeat<I>> = (0..n)
            .map(|i| {
                let n_inner: usize = set_len.pow((n - 1 - i) as u32);
                let n_outer: usize = set_len.pow(i as u32);
                CycleRepeat::new(set.clone(), n_inner, n_outer)
            })
            .collect();

        // OK, return self
        Self { iters, total_iters: set_len.pow(n as u32) }
    }
}
impl<I> PowerSet<I>
where
    I: Iterator,
{
    /// Returns the number of variables (and thereby the size of the yielded [`Vec`]) this PowerSet
    /// generates combinations for.
    ///
    /// # Returns
    /// A number representing `n` during creation.
    #[inline]
    pub fn n_vars(&self) -> usize { self.iters.len() }
}
impl<I> Iterator for PowerSet<I>
where
    I: Clone + Iterator,
    I::Item: Clone,
{
    type Item = Vec<I::Item>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Special case: if the number of variables is empty, nothing to do
        if self.iters.is_empty() {
            return None;
        }

        // Get a next concretization of all the variables in the rule
        let mut values: Vec<I::Item> = Vec::with_capacity(self.iters.len());
        for iter in &mut self.iters {
            values.push(iter.next()?);
        }
        Some(values)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n: usize = self.len();
        (n, Some(n))
    }
}
impl<I> ExactSizeIterator for PowerSet<I>
where
    I: Clone + Iterator,
    I::Item: Clone,
{
    #[inline]
    fn len(&self) -> usize { self.total_iters }
}



/// Quantifies over an atom's variables to produce a grounded one.
#[derive(better_derive::Clone, Debug)]
#[better_derive(bounds = (I: r#trait + Iterator, I::Item: r#trait, S: Spannable<'a>))]
#[clone(bounds = (I: r#trait + Iterator, I::Item: r#trait, S: Clone))]
pub struct AtomQuantifier<'a, S, I>
where
    I: Iterator,
{
    /// The rule to quantify.
    atom: Option<&'a Atom<S>>,
    /// The names of the variables. Corresponds one-to-one with the values produced by the power-
    /// set.
    vars: IndexSet<Ident<S>>,
    /// Defines an iterator over the powerset of the given constants.
    iter: PowerSet<I>,
}
impl<'a, 's, S, I> AtomQuantifier<'a, S, I>
where
    S: Clone + Spannable<'s>,
    I: Clone + ExactSizeIterator + Iterator,
{
    /// Constructor for the AtomQuantifier.
    ///
    /// # Arguments
    /// - `atom`: The [`Atom`] to quantify over.
    /// - `consts`: The set of constants that make up the Herbrand universe of the spec (i.e., the
    ///   space to quantify over).
    ///
    /// # Returns
    /// A new AtomQuantifier, ready to quantify.
    pub fn new(atom: &'a Atom<S>, consts: impl IntoIterator<IntoIter = I>) -> Self {
        // Count the number of unique variables in the atom
        let vars: IndexSet<Ident<S>> = atom.vars().cloned().collect();

        // OK, create the powerset based on that
        let n_vars: usize = vars.len();
        Self { atom: Some(atom), vars, iter: PowerSet::new(consts, n_vars) }
    }
}
impl<'i, 'a, S, I> Iterator for AtomQuantifier<'a, S, I>
where
    S: Clone,
    I: Clone + Iterator<Item = &'i GroundAtom<S>>,
    Ident<S>: Eq + Hash,
    Atom<S>: 'i,
    Span<S>: Clone,
{
    type Item = GroundAtom<S>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Special case: if there are no variables, simply return the original atom once
        if self.iter.n_vars() == 0 {
            // SAFETY: No variables, so no risk of us not being able to turn it into a grounded rule
            return self.atom.take().map(|r| r.to_ground_atom().unwrap());
        }
        let atom: &Atom<S> = self.atom?;

        // Get a next concretization of all the variables in the rule
        let values: Vec<&'i GroundAtom<S>> = self.iter.next()?;
        let assign: HashMap<Ident<S>, GroundAtom<S>> = self.vars.iter().cloned().zip(values.into_iter().cloned()).collect();

        // Concretize the rule with that assignment (going through the internal map of index to name)
        Some(atom.concretize(&assign).unwrap_or_else(|_| panic!("Unknown variable after already analysing variables; this should never happen!")))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
impl<'i, 'a, S, I> ExactSizeIterator for AtomQuantifier<'a, S, I>
where
    S: Clone,
    I: Clone + Iterator<Item = &'i GroundAtom<S>>,
    Ident<S>: Eq + Hash,
    Atom<S>: 'i,
    Span<S>: Clone,
{
    #[inline]
    fn len(&self) -> usize { self.iter.len() }
}

/// Quantifies over a rule's variables to produce a grounded rule.
#[derive(better_derive::Clone, Debug)]
#[better_derive(bounds = (I: r#trait + Iterator, I::Item: r#trait, S: Spannable<'r>))]
#[clone(bounds = (I: r#trait + Iterator, I::Item: r#trait, S: Clone))]
pub struct RuleQuantifier<'r, S, I>
where
    I: Iterator,
{
    /// The rule to quantify.
    rule: Option<&'r Rule<Atom<S>>>,
    /// The names of the variables. Corresponds one-to-one with the values produced by the power-
    /// set.
    vars: IndexSet<Ident<S>>,
    /// Defines an iterator over the powerset of the given constants.
    iter: PowerSet<I>,
}
impl<'r, S, I> RuleQuantifier<'r, S, I>
where
    I: Clone + ExactSizeIterator + Iterator,
    Ident<S>: Clone + Eq + Hash,
{
    /// Constructor for the RuleQuantifier.
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] to quantify over.
    /// - `consts`: The set of constants that make up the Herbrand universe of the spec (i.e., the
    ///   space to quantify over).
    ///
    /// # Returns
    /// A new RuleQuantifier, ready to quantify.
    pub fn new(rule: &'r Rule<Atom<S>>, consts: impl IntoIterator<IntoIter = I>) -> Self {
        // Count the number of unique variables in the rule
        let vars: IndexSet<Ident<S>> = rule.atoms().flat_map(Atomlike::vars).cloned().collect();

        // OK, create the powerset based on that
        let n_vars: usize = vars.len();
        Self { rule: Some(rule), vars, iter: PowerSet::new(consts, n_vars) }
    }
}
impl<'i, 'r, S, I> Iterator for RuleQuantifier<'r, S, I>
where
    S: Clone,
    I: Clone + Iterator<Item = &'i GroundAtom<S>>,
    Ident<S>: Eq + Hash,
    Rule<Atom<S>>: 'i,
    Span<S>: Clone,
{
    type Item = Rule<GroundAtom<S>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Special case: if there are no variables, simply return the original atom once
        if self.iter.n_vars() == 0 {
            // SAFETY: No variables, so no risk of us not being able to turn it into a grounded rule
            return self.rule.take().map(|r| r.to_grounded_rule().unwrap());
        }
        let rule: &Rule<Atom<S>> = self.rule?;

        // Get a next concretization of all the variables in the rule
        let values: Vec<&'i GroundAtom<S>> = self.iter.next()?;
        let assign: HashMap<Ident<S>, GroundAtom<S>> = self.vars.iter().cloned().zip(values.into_iter().cloned()).collect();

        // Concretize the rule with that assignment (going through the internal map of index to name)
        Some(rule.concretize(&assign).unwrap_or_else(|_| panic!("Unknown variable after already analysing variables; this should never happen!")))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
impl<'i, 'r, S, I> ExactSizeIterator for RuleQuantifier<'r, S, I>
where
    S: Clone,
    I: Clone + Iterator<Item = &'i GroundAtom<S>>,
    Ident<S>: Eq + Hash,
    Rule<Atom<S>>: 'i,
    Span<S>: Clone,
{
    #[inline]
    fn len(&self) -> usize { self.iter.len() }
}





/***** IMPLEMENTATIONS *****/
impl<S> Rule<Atom<S>> {
    /// Convenient way to instantiate a rule for a powerset of the given atoms.
    ///
    /// # Arguments
    /// - `domain`: Some kind of universe of atoms to quantify over.
    ///
    /// # Returns
    /// A [`RuleQuantifier`] that will produce concrete rules without variables in them.
    #[inline]
    pub fn concretize_for<'r, I>(&'r self, domain: impl IntoIterator<IntoIter = I>) -> RuleQuantifier<'r, S, I>
    where
        I: Clone + ExactSizeIterator + Iterator,
        Ident<S>: Clone + Eq + Hash,
    {
        RuleQuantifier::new(self, domain)
    }
}

impl<'s, S: Clone + Spannable<'s>> Atom<S> {
    /// Convenient way to instantiate an atom for a powerset of the given atoms.
    ///
    /// # Arguments
    /// - `domain`: Some kind of universe of atoms to quantify over.
    ///
    /// # Returns
    /// An [`AtomQuantifier`] that will produce concrete atoms without variables in them.
    #[inline]
    pub fn concretize_for<I>(&self, domain: impl IntoIterator<IntoIter = I>) -> AtomQuantifier<'_, S, I>
    where
        I: Clone + ExactSizeIterator + Iterator,
    {
        AtomQuantifier::new(self, domain)
    }
}





/***** TESTS *****/
#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{make_ir_atom, make_ir_ground_atom, make_ir_rule};

    #[test]
    fn test_cycle_repeat_empty_set() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let nums: Vec<i32> = CycleRepeat::new([], 1, 1).collect();
        assert_eq!(nums, vec![]);
    }

    #[test]
    fn test_cycle_repeat_empty_range() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let nums: Vec<i32> = CycleRepeat::new([1, 2, 3], 0, 0).collect();
        assert_eq!(nums, vec![]);
    }

    #[test]
    fn test_cycle_repeat_123_three() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Simply do the test from the thing
        let nums1: Vec<i32> = CycleRepeat::new([1, 2, 3], 9, 1).collect();
        let nums2: Vec<i32> = CycleRepeat::new([1, 2, 3], 3, 3).collect();
        let nums3: Vec<i32> = CycleRepeat::new([1, 2, 3], 1, 9).collect();
        assert_eq!(nums1, vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3]);
        assert_eq!(nums2, vec![1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 1, 2, 2, 2, 3, 3, 3]);
        assert_eq!(nums3, vec![1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3]);
    }

    #[test]
    fn test_cycle_repeat_12_four() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Simply do the test from the thing
        let nums1: Vec<i32> = CycleRepeat::new([1, 2], 8, 1).collect();
        let nums2: Vec<i32> = CycleRepeat::new([1, 2], 4, 2).collect();
        let nums3: Vec<i32> = CycleRepeat::new([1, 2], 2, 4).collect();
        let nums4: Vec<i32> = CycleRepeat::new([1, 2], 1, 8).collect();
        assert_eq!(nums1, vec![1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]);
        assert_eq!(nums2, vec![1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2]);
        assert_eq!(nums3, vec![1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2]);
        assert_eq!(nums4, vec![1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]);
    }

    #[test]
    fn test_cycle_repeat_1234_two() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Simply do the test from the thing
        let nums1: Vec<i32> = CycleRepeat::new([1, 2, 3, 4], 4, 1).collect();
        let nums2: Vec<i32> = CycleRepeat::new([1, 2, 3, 4], 1, 4).collect();
        assert_eq!(nums1, vec![1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4]);
        assert_eq!(nums2, vec![1, 2, 3, 4, 1, 2, 3, 4, 1, 2, 3, 4, 1, 2, 3, 4]);
    }

    #[test]
    fn test_power_set_empty_set() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let nums: Vec<Vec<i32>> = PowerSet::new([], 3).collect();
        assert_eq!(nums, Vec::<Vec<i32>>::new());
    }

    #[test]
    fn test_power_set_empty_range() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let nums: Vec<Vec<i32>> = PowerSet::new([1, 2, 3], 0).collect();
        assert_eq!(nums, Vec::<Vec<i32>>::new());
    }

    #[test]
    fn test_power_set_123_three() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Simply do the test from the thing
        let nums: Vec<Vec<i32>> = PowerSet::new([1, 2, 3], 3).collect();
        assert_eq!(nums, vec![
            vec![1, 1, 1],
            vec![1, 1, 2],
            vec![1, 1, 3],
            vec![1, 2, 1],
            vec![1, 2, 2],
            vec![1, 2, 3],
            vec![1, 3, 1],
            vec![1, 3, 2],
            vec![1, 3, 3],
            vec![2, 1, 1],
            vec![2, 1, 2],
            vec![2, 1, 3],
            vec![2, 2, 1],
            vec![2, 2, 2],
            vec![2, 2, 3],
            vec![2, 3, 1],
            vec![2, 3, 2],
            vec![2, 3, 3],
            vec![3, 1, 1],
            vec![3, 1, 2],
            vec![3, 1, 3],
            vec![3, 2, 1],
            vec![3, 2, 2],
            vec![3, 2, 3],
            vec![3, 3, 1],
            vec![3, 3, 2],
            vec![3, 3, 3],
        ]);
    }

    #[test]
    fn test_power_set_12_four() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Simply do the test from the thing
        let nums: Vec<Vec<i32>> = PowerSet::new([1, 2], 4).collect();
        assert_eq!(nums, vec![
            vec![1, 1, 1, 1],
            vec![1, 1, 1, 2],
            vec![1, 1, 2, 1],
            vec![1, 1, 2, 2],
            vec![1, 2, 1, 1],
            vec![1, 2, 1, 2],
            vec![1, 2, 2, 1],
            vec![1, 2, 2, 2],
            vec![2, 1, 1, 1],
            vec![2, 1, 1, 2],
            vec![2, 1, 2, 1],
            vec![2, 1, 2, 2],
            vec![2, 2, 1, 1],
            vec![2, 2, 1, 2],
            vec![2, 2, 2, 1],
            vec![2, 2, 2, 2],
        ]);
    }

    #[test]
    fn test_power_set_1234_two() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        // Simply do the test from the thing
        let nums: Vec<Vec<i32>> = PowerSet::new([1, 2, 3, 4], 2).collect();
        assert_eq!(nums, vec![
            vec![1, 1],
            vec![1, 2],
            vec![1, 3],
            vec![1, 4],
            vec![2, 1],
            vec![2, 2],
            vec![2, 3],
            vec![2, 4],
            vec![3, 1],
            vec![3, 2],
            vec![3, 3],
            vec![3, 4],
            vec![4, 1],
            vec![4, 2],
            vec![4, 3],
            vec![4, 4]
        ]);
    }

    #[test]
    fn test_rule_quantifier_no_vars_no_args() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<GroundAtom<(&str, &str)>> =
            vec![make_ir_ground_atom("foo", []), make_ir_ground_atom("bar", []), make_ir_ground_atom("baz", [])];
        let inst: Vec<Rule<GroundAtom<(&str, &str)>>> = make_ir_rule([make_ir_atom("atom", [])], [], []).concretize_for(&consts).collect();
        assert_eq!(inst, vec![make_ir_rule([make_ir_ground_atom("atom", [])], [], [])]);
    }

    #[test]
    fn test_rule_quantifier_no_vars_args() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<GroundAtom<(&str, &str)>> =
            vec![make_ir_ground_atom("foo", []), make_ir_ground_atom("bar", []), make_ir_ground_atom("baz", [])];
        let inst1: Vec<Rule<GroundAtom<(&str, &str)>>> = make_ir_rule([make_ir_atom("atom1", ["foo"])], [], []).concretize_for(&consts).collect();
        let inst2: Vec<Rule<GroundAtom<(&str, &str)>>> =
            make_ir_rule([make_ir_atom("atom2", [])], [make_ir_atom("atom1", [])], []).concretize_for(&consts).collect();
        assert_eq!(inst1, vec![make_ir_rule([make_ir_ground_atom("atom1", ["foo"])], [], [])]);
        assert_eq!(inst2, vec![make_ir_rule([make_ir_ground_atom("atom2", [])], [make_ir_ground_atom("atom1", [])], [])]);
    }

    #[test]
    fn test_rule_quantifier_vars_1() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<GroundAtom<(&str, &str)>> =
            vec![make_ir_ground_atom("foo", []), make_ir_ground_atom("bar", []), make_ir_ground_atom("baz", [])];
        let inst1: Vec<Rule<GroundAtom<(&str, &str)>>> = make_ir_rule([make_ir_atom("atom1", ["X"])], [], []).concretize_for(&consts).collect();
        let inst2: Vec<Rule<GroundAtom<(&str, &str)>>> =
            make_ir_rule([make_ir_atom("atom2", [])], [make_ir_atom("atom1", ["Y"])], []).concretize_for(&consts).collect();
        let inst3: Vec<Rule<GroundAtom<(&str, &str)>>> =
            make_ir_rule([make_ir_atom("atom3", ["Z"])], [make_ir_atom("atom1", ["Z"])], []).concretize_for(&consts).collect();
        assert_eq!(inst1, vec![
            make_ir_rule([make_ir_ground_atom("atom1", ["foo"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["bar"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["baz"])], [], [])
        ]);
        assert_eq!(inst2, vec![
            make_ir_rule([make_ir_ground_atom("atom2", [])], [make_ir_ground_atom("atom1", ["foo"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", [])], [make_ir_ground_atom("atom1", ["bar"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", [])], [make_ir_ground_atom("atom1", ["baz"])], [])
        ]);
        assert_eq!(inst3, vec![
            make_ir_rule([make_ir_ground_atom("atom3", ["foo"])], [make_ir_ground_atom("atom1", ["foo"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["bar"])], [make_ir_ground_atom("atom1", ["bar"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["baz"])], [make_ir_ground_atom("atom1", ["baz"])], [])
        ]);
    }

    #[test]
    fn test_rule_quantifier_vars_2() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<GroundAtom<(&str, &str)>> =
            vec![make_ir_ground_atom("foo", []), make_ir_ground_atom("bar", []), make_ir_ground_atom("baz", [])];
        let inst1: Vec<Rule<GroundAtom<(&str, &str)>>> = make_ir_rule([make_ir_atom("atom1", ["X", "Y"])], [], []).concretize_for(&consts).collect();
        let inst2: Vec<Rule<GroundAtom<(&str, &str)>>> =
            make_ir_rule([make_ir_atom("atom2", ["X"])], [make_ir_atom("atom1", ["Y"])], []).concretize_for(&consts).collect();
        let inst3: Vec<Rule<GroundAtom<(&str, &str)>>> =
            make_ir_rule([make_ir_atom("atom3", ["X", "Y"])], [make_ir_atom("atom1", ["Y", "X"])], []).concretize_for(&consts).collect();
        assert_eq!(inst1, vec![
            make_ir_rule([make_ir_ground_atom("atom1", ["foo", "foo"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["foo", "bar"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["foo", "baz"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["bar", "foo"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["bar", "bar"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["bar", "baz"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["baz", "foo"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["baz", "bar"])], [], []),
            make_ir_rule([make_ir_ground_atom("atom1", ["baz", "baz"])], [], [])
        ]);
        assert_eq!(inst2, vec![
            make_ir_rule([make_ir_ground_atom("atom2", ["foo"])], [make_ir_ground_atom("atom1", ["foo"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", ["foo"])], [make_ir_ground_atom("atom1", ["bar"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", ["foo"])], [make_ir_ground_atom("atom1", ["baz"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", ["bar"])], [make_ir_ground_atom("atom1", ["foo"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", ["bar"])], [make_ir_ground_atom("atom1", ["bar"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", ["bar"])], [make_ir_ground_atom("atom1", ["baz"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", ["baz"])], [make_ir_ground_atom("atom1", ["foo"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", ["baz"])], [make_ir_ground_atom("atom1", ["bar"])], []),
            make_ir_rule([make_ir_ground_atom("atom2", ["baz"])], [make_ir_ground_atom("atom1", ["baz"])], [])
        ]);
        assert_eq!(inst3, vec![
            make_ir_rule([make_ir_ground_atom("atom3", ["foo", "foo"])], [make_ir_ground_atom("atom1", ["foo", "foo"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["foo", "bar"])], [make_ir_ground_atom("atom1", ["bar", "foo"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["foo", "baz"])], [make_ir_ground_atom("atom1", ["baz", "foo"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["bar", "foo"])], [make_ir_ground_atom("atom1", ["foo", "bar"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["bar", "bar"])], [make_ir_ground_atom("atom1", ["bar", "bar"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["bar", "baz"])], [make_ir_ground_atom("atom1", ["baz", "bar"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["baz", "foo"])], [make_ir_ground_atom("atom1", ["foo", "baz"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["baz", "bar"])], [make_ir_ground_atom("atom1", ["bar", "baz"])], []),
            make_ir_rule([make_ir_ground_atom("atom3", ["baz", "baz"])], [make_ir_ground_atom("atom1", ["baz", "baz"])], [])
        ]);
    }
}
