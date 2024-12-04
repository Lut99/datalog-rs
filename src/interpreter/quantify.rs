//  QUANTIFY.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 17:58:01
//  Last edited:
//    04 Dec 2024, 17:15:16
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines the quantification procedure for the $Datalog^\neg$
//!   interpreter, once and for all.
//

use std::fmt::{Debug, Formatter, Result as FResult};

use indexmap::IndexSet;

use crate::ast::{Atom, AtomArg, Ident, Rule};


/***** CONSTANTS *****/
/// Defines the maximum amount of **_unique_ variables** that a rule can have.
pub const MAX_RULE_VARS: usize = 16;





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
#[derive(Clone, Debug)]
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
}

/// An iterator that produces a powerset of N elements over a set.
pub struct PowerSet<I>
where
    I: Iterator,
{
    /// Copies for the iterator with repetitions, one for every element.
    iters: Vec<CycleRepeat<I>>,
}
impl<I> Clone for PowerSet<I>
where
    I: Clone + Iterator,
    I::Item: Clone,
{
    #[inline]
    fn clone(&self) -> Self { Self { iters: self.iters.clone() } }
}
impl<I> Debug for PowerSet<I>
where
    I: Debug + Iterator,
    I::Item: Debug,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        let mut fmt = f.debug_struct("PowerSet");
        fmt.field("iters", &self.iters);
        fmt.finish()
    }
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
        Self { iters }
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
    pub fn n(&self) -> usize { self.iters.len() }
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
}



/// Quantifies over an atom given a Herbrand universe to quantify over.
pub struct AtomQuantifier<'a, 'f, 's, I>
where
    I: Iterator,
{
    /// The atom to quantify.
    atom: Option<&'a Atom<&'f str, &'s str>>,
    /// The names of the variables. Corresponds one-to-one with the values produced by the power-
    /// set.
    vars: IndexSet<Ident<&'f str, &'s str>>,
    /// Defines an iterator over the powerset of the given constants.
    iter: PowerSet<I>,
}
impl<'a, 'f, 's, I> Clone for AtomQuantifier<'a, 'f, 's, I>
where
    I: Clone + Iterator,
    I::Item: Clone,
{
    #[inline]
    fn clone(&self) -> Self { Self { atom: self.atom, vars: self.vars.clone(), iter: self.iter.clone() } }
}
impl<'a, 'f, 's, I> Debug for AtomQuantifier<'a, 'f, 's, I>
where
    I: Debug + Iterator,
    I::Item: Debug,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        let mut fmt = f.debug_struct("AtomQuantifier");
        fmt.field("atom", &self.atom);
        fmt.field("vars", &self.vars);
        fmt.field("iter", &self.iter);
        fmt.finish()
    }
}
impl<'a, 'f, 's, I> AtomQuantifier<'a, 'f, 's, I>
where
    I: Clone + ExactSizeIterator + Iterator,
    I::Item: Clone,
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
    pub fn new(atom: &'a Atom<&'f str, &'s str>, consts: impl IntoIterator<IntoIter = I>) -> Self {
        // Count the number of unique variables in the atom
        let mut vars: IndexSet<Ident<&'f str, &'s str>> = IndexSet::with_capacity(4);
        for arg in atom.args.iter().flat_map(|tail| tail.args.values()) {
            // We're looking for variables
            if let AtomArg::Var(var) = arg {
                // Insert it. If it already exists, this function should leave the order untouched.
                vars.insert(var.clone());
            }
        }

        // OK, create the powerset based on that
        let n_vars: usize = vars.len();
        Self { atom: Some(atom), vars, iter: PowerSet::new(consts, n_vars) }
    }
}
impl<'i, 'a, 'f, 's, I> Iterator for AtomQuantifier<'a, 'f, 's, I>
where
    'f: 'i,
    's: 'i,
    I: Clone + Iterator<Item = &'i Ident<&'f str, &'s str>>,
{
    type Item = Atom<&'f str, &'s str>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Special case: if there are no variables, simply return the original atom once
        if self.iter.n() == 0 {
            return self.atom.take().cloned();
        }
        let mut atom: Atom<&'f str, &'s str> = self.atom?.clone();

        // Get a next concretization of all the variables in the rule
        let values: Vec<&'i Ident<&'f str, &'s str>> = self.iter.next()?;

        // Go through the rule to apply it
        for arg in atom.args.iter_mut().flat_map(|tail| tail.args.values_mut()) {
            if let AtomArg::Var(var) = arg {
                // Find which value to take the value of
                let value: &'i Ident<&'f str, &'s str> = values
                    .get(self.vars.get_index_of(var).unwrap_or_else(|| {
                        panic!("Unknown variable {:?} after already analysing variables; this should never happen!", var.value.value())
                    }))
                    .unwrap_or_else(|| panic!("Variables list is longer than values list; this should never happen!"));

                // Set it as the atom's value
                *arg = AtomArg::Atom(value.clone()).clone();
            }
        }

        // Done!
        Some(atom)
    }
}

/// Quantifies over a rule given a Herbrand universe to quantify over.
pub struct RuleQuantifier<'r, 'f, 's, I>
where
    I: Iterator,
{
    /// The rule to quantify.
    rule: Option<&'r Rule<&'f str, &'s str>>,
    /// The names of the variables. Corresponds one-to-one with the values produced by the power-
    /// set.
    vars: IndexSet<Ident<&'f str, &'s str>>,
    /// Defines an iterator over the powerset of the given constants.
    iter: PowerSet<I>,
}
impl<'r, 'f, 's, I> Clone for RuleQuantifier<'r, 'f, 's, I>
where
    I: Clone + Iterator,
    I::Item: Clone,
{
    #[inline]
    fn clone(&self) -> Self { Self { rule: self.rule, vars: self.vars.clone(), iter: self.iter.clone() } }
}
impl<'r, 'f, 's, I> Debug for RuleQuantifier<'r, 'f, 's, I>
where
    I: Debug + Iterator,
    I::Item: Debug,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        let mut fmt = f.debug_struct("RuleQuantifier");
        fmt.field("rule", &self.rule);
        fmt.field("vars", &self.vars);
        fmt.field("iter", &self.iter);
        fmt.finish()
    }
}
impl<'r, 'f, 's, I> RuleQuantifier<'r, 'f, 's, I>
where
    I: Clone + ExactSizeIterator + Iterator,
    I::Item: Clone,
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
    pub fn new(rule: &'r Rule<&'f str, &'s str>, consts: impl IntoIterator<IntoIter = I>) -> Self {
        // Count the number of unique variables in the rule
        let mut vars: IndexSet<Ident<&'f str, &'s str>> = IndexSet::with_capacity(4);
        for arg in rule.consequents.values().flat_map(|atom| atom.args.iter().flat_map(|tail| tail.args.values())).chain(
            rule.tail.iter().flat_map(|tail| tail.antecedents.values().flat_map(|ant| ant.atom().args.iter().flat_map(|tail| tail.args.values()))),
        ) {
            // We're looking for variables
            if let AtomArg::Var(var) = arg {
                // Insert it. If it already exists, this function should leave the order untouched.
                vars.insert(var.clone());
            }
        }

        // OK, create the powerset based on that
        let n_vars: usize = vars.len();
        Self { rule: Some(rule), vars, iter: PowerSet::new(consts, n_vars) }
    }
}
impl<'i, 'r, 'f, 's, I> Iterator for RuleQuantifier<'r, 'f, 's, I>
where
    'f: 'i,
    's: 'i,
    I: Clone + Iterator<Item = &'i Ident<&'f str, &'s str>>,
{
    type Item = Rule<&'f str, &'s str>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Special case: if there are no variables, simply return the original atom once
        if self.iter.n() == 0 {
            return self.rule.take().cloned();
        }
        let mut rule: Rule<&'f str, &'s str> = self.rule?.clone();

        // Get a next concretization of all the variables in the rule
        let values: Vec<&'i Ident<&'f str, &'s str>> = self.iter.next()?;

        // Go through the rule to apply it
        for arg in rule.consequents.values_mut().flat_map(|atom| atom.args.iter_mut().flat_map(|tail| tail.args.values_mut())).chain(
            rule.tail.iter_mut().flat_map(|tail| {
                tail.antecedents.values_mut().flat_map(|ant| ant.atom_mut().args.iter_mut().flat_map(|tail| tail.args.values_mut()))
            }),
        ) {
            if let AtomArg::Var(var) = arg {
                // Find which value to take the value of
                let value: &'i Ident<&'f str, &'s str> = values
                    .get(self.vars.get_index_of(var).unwrap_or_else(|| {
                        panic!("Unknown variable {:?} after already analysing variables; this should never happen!", var.value.value())
                    }))
                    .unwrap_or_else(|| panic!("Variables list is longer than values list; this should never happen!"));

                // Set it as the atom's value
                *arg = AtomArg::Atom(value.clone()).clone();
            }
        }

        // Done!
        Some(rule)
    }
}





/***** IMPLEMENTATIONS *****/
impl<'f, 's> Atom<&'f str, &'s str> {
    /// Convenient way to instantiate an atom for a powerset of the Herbrand universe.
    ///
    /// # Arguments
    /// - `consts`: The Herbrand universe to powerset over.
    ///
    /// # Returns
    /// An [`AtomQuantifier`] that will produce concrete atoms without variables in them.
    #[inline]
    pub fn quantify<'r, I>(&'r self, consts: impl IntoIterator<IntoIter = I>) -> AtomQuantifier<'r, 'f, 's, I>
    where
        I: Clone + ExactSizeIterator + Iterator,
        I::Item: Clone,
    {
        AtomQuantifier::new(self, consts)
    }
}

impl<'f, 's> Rule<&'f str, &'s str> {
    /// Convenient way to instantiate a rule for a powerset of the Herbrand universe.
    ///
    /// # Arguments
    /// - `consts`: The Herbrand universe to powerset over.
    ///
    /// # Returns
    /// A [`RuleQuantifier`] that will produce concrete rules without variables in them.
    #[inline]
    pub fn quantify<'r, I>(&'r self, consts: impl IntoIterator<IntoIter = I>) -> RuleQuantifier<'r, 'f, 's, I>
    where
        I: Clone + ExactSizeIterator + Iterator,
        I::Item: Clone,
    {
        RuleQuantifier::new(self, consts)
    }
}





/***** TESTS *****/
#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{make_atom, make_ident, make_lit, make_rule};

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
    fn test_atom_quantifier_no_vars_no_args() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<Ident<&str, &str>> = vec![make_ident("foo"), make_ident("bar"), make_ident("baz")];
        let inst: Vec<Atom<&str, &str>> = make_atom("atom", None).quantify(&consts).collect();
        assert_eq!(inst, vec![make_atom("atom", None)]);
    }

    #[test]
    fn test_atom_quantifier_no_vars_args() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<Ident<&str, &str>> = vec![make_ident("foo"), make_ident("bar"), make_ident("baz")];
        let inst: Vec<Atom<&str, &str>> = make_atom("atom", Some("other")).quantify(&consts).collect();
        assert_eq!(inst, vec![make_atom("atom", Some("other"))]);
    }

    #[test]
    fn test_atom_quantifier_vars_1() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<Ident<&str, &str>> = vec![make_ident("foo"), make_ident("bar"), make_ident("baz")];
        let inst: Vec<Atom<&str, &str>> = make_atom("atom", ["X"]).quantify(&consts).collect();
        assert_eq!(inst, vec![make_atom("atom", ["foo"]), make_atom("atom", ["bar"]), make_atom("atom", ["baz"])])
    }

    #[test]
    fn test_atom_quantifier_vars_2() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<Ident<&str, &str>> = vec![make_ident("foo"), make_ident("bar"), make_ident("baz")];
        let inst: Vec<Atom<&str, &str>> = make_atom("atom", ["X", "Y"]).quantify(&consts).collect();
        assert_eq!(inst, vec![
            make_atom("atom", ["foo", "foo"]),
            make_atom("atom", ["foo", "bar"]),
            make_atom("atom", ["foo", "baz"]),
            make_atom("atom", ["bar", "foo"]),
            make_atom("atom", ["bar", "bar"]),
            make_atom("atom", ["bar", "baz"]),
            make_atom("atom", ["baz", "foo"]),
            make_atom("atom", ["baz", "bar"]),
            make_atom("atom", ["baz", "baz"])
        ])
    }

    #[test]
    fn test_rule_quantifier_no_vars_no_args() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<Ident<&str, &str>> = vec![make_ident("foo"), make_ident("bar"), make_ident("baz")];
        let inst: Vec<Rule<&str, &str>> = make_rule([make_atom("atom", None)], None).quantify(&consts).collect();
        assert_eq!(inst, vec![make_rule([make_atom("atom", None)], None)]);
    }

    #[test]
    fn test_rule_quantifier_no_vars_args() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<Ident<&str, &str>> = vec![make_ident("foo"), make_ident("bar"), make_ident("baz")];
        let inst1: Vec<Rule<&str, &str>> = make_rule([make_atom("atom1", Some("foo"))], None).quantify(&consts).collect();
        let inst2: Vec<Rule<&str, &str>> = make_rule([make_atom("atom2", None)], Some(make_lit(true, "atom1", None))).quantify(&consts).collect();
        assert_eq!(inst1, vec![make_rule([make_atom("atom1", Some("foo"))], None)]);
        assert_eq!(inst2, vec![make_rule([make_atom("atom2", None)], Some(make_lit(true, "atom1", None)))]);
    }

    #[test]
    fn test_rule_quantifier_vars_1() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<Ident<&str, &str>> = vec![make_ident("foo"), make_ident("bar"), make_ident("baz")];
        let inst1: Vec<Rule<&str, &str>> = make_rule([make_atom("atom1", Some("X"))], None).quantify(&consts).collect();
        let inst2: Vec<Rule<&str, &str>> =
            make_rule([make_atom("atom2", None)], Some(make_lit(true, "atom1", Some("Y")))).quantify(&consts).collect();
        let inst3: Vec<Rule<&str, &str>> =
            make_rule([make_atom("atom3", Some("Z"))], Some(make_lit(true, "atom1", Some("Z")))).quantify(&consts).collect();
        assert_eq!(inst1, vec![
            make_rule([make_atom("atom1", Some("foo"))], None),
            make_rule([make_atom("atom1", Some("bar"))], None),
            make_rule([make_atom("atom1", Some("baz"))], None)
        ]);
        assert_eq!(inst2, vec![
            make_rule([make_atom("atom2", None)], Some(make_lit(true, "atom1", Some("foo")))),
            make_rule([make_atom("atom2", None)], Some(make_lit(true, "atom1", Some("bar")))),
            make_rule([make_atom("atom2", None)], Some(make_lit(true, "atom1", Some("baz"))))
        ]);
        assert_eq!(inst3, vec![
            make_rule([make_atom("atom3", Some("foo"))], Some(make_lit(true, "atom1", Some("foo")))),
            make_rule([make_atom("atom3", Some("bar"))], Some(make_lit(true, "atom1", Some("bar")))),
            make_rule([make_atom("atom3", Some("baz"))], Some(make_lit(true, "atom1", Some("baz"))))
        ]);
    }

    #[test]
    fn test_rule_quantifier_vars_2() {
        #[cfg(feature = "log")]
        crate::tests::setup_logger();

        let consts: Vec<Ident<&str, &str>> = vec![make_ident("foo"), make_ident("bar"), make_ident("baz")];
        let inst1: Vec<Rule<&str, &str>> = make_rule([make_atom("atom1", ["X", "Y"])], None).quantify(&consts).collect();
        let inst2: Vec<Rule<&str, &str>> = make_rule([make_atom("atom2", ["X"])], Some(make_lit(true, "atom1", ["Y"]))).quantify(&consts).collect();
        let inst3: Vec<Rule<&str, &str>> =
            make_rule([make_atom("atom3", ["X", "Y"])], Some(make_lit(true, "atom1", ["Y", "X"]))).quantify(&consts).collect();
        assert_eq!(inst1, vec![
            make_rule([make_atom("atom1", ["foo", "foo"])], None),
            make_rule([make_atom("atom1", ["foo", "bar"])], None),
            make_rule([make_atom("atom1", ["foo", "baz"])], None),
            make_rule([make_atom("atom1", ["bar", "foo"])], None),
            make_rule([make_atom("atom1", ["bar", "bar"])], None),
            make_rule([make_atom("atom1", ["bar", "baz"])], None),
            make_rule([make_atom("atom1", ["baz", "foo"])], None),
            make_rule([make_atom("atom1", ["baz", "bar"])], None),
            make_rule([make_atom("atom1", ["baz", "baz"])], None)
        ]);
        assert_eq!(inst2, vec![
            make_rule([make_atom("atom2", ["foo"])], Some(make_lit(true, "atom1", ["foo"]))),
            make_rule([make_atom("atom2", ["foo"])], Some(make_lit(true, "atom1", ["bar"]))),
            make_rule([make_atom("atom2", ["foo"])], Some(make_lit(true, "atom1", ["baz"]))),
            make_rule([make_atom("atom2", ["bar"])], Some(make_lit(true, "atom1", ["foo"]))),
            make_rule([make_atom("atom2", ["bar"])], Some(make_lit(true, "atom1", ["bar"]))),
            make_rule([make_atom("atom2", ["bar"])], Some(make_lit(true, "atom1", ["baz"]))),
            make_rule([make_atom("atom2", ["baz"])], Some(make_lit(true, "atom1", ["foo"]))),
            make_rule([make_atom("atom2", ["baz"])], Some(make_lit(true, "atom1", ["bar"]))),
            make_rule([make_atom("atom2", ["baz"])], Some(make_lit(true, "atom1", ["baz"])))
        ]);
        assert_eq!(inst3, vec![
            make_rule([make_atom("atom3", ["foo", "foo"])], Some(make_lit(true, "atom1", ["foo", "foo"]))),
            make_rule([make_atom("atom3", ["foo", "bar"])], Some(make_lit(true, "atom1", ["bar", "foo"]))),
            make_rule([make_atom("atom3", ["foo", "baz"])], Some(make_lit(true, "atom1", ["baz", "foo"]))),
            make_rule([make_atom("atom3", ["bar", "foo"])], Some(make_lit(true, "atom1", ["foo", "bar"]))),
            make_rule([make_atom("atom3", ["bar", "bar"])], Some(make_lit(true, "atom1", ["bar", "bar"]))),
            make_rule([make_atom("atom3", ["bar", "baz"])], Some(make_lit(true, "atom1", ["baz", "bar"]))),
            make_rule([make_atom("atom3", ["baz", "foo"])], Some(make_lit(true, "atom1", ["foo", "baz"]))),
            make_rule([make_atom("atom3", ["baz", "bar"])], Some(make_lit(true, "atom1", ["bar", "baz"]))),
            make_rule([make_atom("atom3", ["baz", "baz"])], Some(make_lit(true, "atom1", ["baz", "baz"])))
        ]);
    }
}
