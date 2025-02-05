//  INTERMEDIATE REPRESENTATION AST.rs
//    by Lut99
//
//  Created:
//    05 Feb 2025, 14:24:31
//  Last edited:
//    05 Feb 2025, 17:38:12
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines alternative tops of the Datalog AST for r
//

use std::fmt::{Formatter, Result as FResult};

use better_derive::{Clone, Debug, Eq, Hash, PartialEq};

use crate::ast::{Atomlike, Ident, Span};


/***** LIBRARY *****/
/// Defines a specification consisting only of [safe rules](SafeRule).
///
/// Cannot be parsed directly, but only obtained through compilation.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SafeSpec<A> {
    /// The rules in this safe specification.
    pub rules: Vec<SafeRule<A>>,
}

/// Defines a safe rule, i.e., one with variables that don't quantify over thin air.
///
/// The observation is that quantification is hard in general when using recursive atoms, because
/// the Herbrand base of a specification becomes infinite. To fix this, we restrict variables in
/// the following way:
/// 1. Any variables occurring in consequents _must_ also occur in **positive** antecedents.
/// 2. Any variables occurring in **negative** antecedents _must_ also occur in **positive**
///    antecedents.
///
/// In other words, we can think of positive antecedents binding variables to quantifiers, and then
/// other occurrences referring to those variables.
///
/// A safe rule, then, is a rule for which we've proven the above holds.
///
/// Note: being compiled, this node has no more syntax-only elements (e.g.,
/// [`Arrow`](crate::ast::Arrow) and the likes).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SafeRule<A> {
    /// The consequents of the rule.
    pub consequents:     Vec<A>,
    /// The positive antecedents of the rule.
    pub pos_antecedents: Vec<A>,
    /// The negative antecedents of the rule.
    pub neg_antecedents: Vec<A>,
}
impl<A> SafeRule<A> {
    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more atoms.
    #[inline]
    pub fn atoms<'s>(&'s self) -> impl 's + Iterator<Item = &'s A> {
        self.consequents.iter().chain(self.pos_antecedents.iter()).chain(self.neg_antecedents.iter())
    }

    /// Returns an iterator over the atoms in the rule's consequents and antecedents, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to atoms.
    #[inline]
    pub fn atoms_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut A> {
        self.consequents.iter_mut().chain(self.pos_antecedents.iter_mut()).chain(self.neg_antecedents.iter_mut())
    }
}



/// Defines an atom without any variables in it.
///
/// Note: being compiled, this node has no more syntax-only elements (e.g.,
/// [`Arrow`](crate::ast::Arrow) and the likes).
pub struct GroundedAtom<F, S> {
    /// The identifier of the atom.
    pub ident: Ident<F, S>,
    /// Any arguments to the atom.
    pub args:  Vec<GroundedAtom<F, S>>,
}
// NOTE: We implement `Clone`, `Debug`, `Eq`, `Hash` and `PartialEq` manually to prevent an endless
// cycle in deriving that `Punctuated<Atom, Comma>` implements one of those traits (since the
// question of whether it does depends on `Atom`, which transitively depends on `FactArgs`).
impl<F, S> Clone for GroundedAtom<F, S>
where
    Span<F, S>: Clone,
{
    #[inline]
    fn clone(&self) -> Self { Self { ident: self.ident.clone(), args: self.args.clone() } }
}
impl<F, S> std::fmt::Debug for GroundedAtom<F, S>
where
    Span<F, S>: std::fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let Self { ident, args } = self;
        let mut fmt = f.debug_struct("GroundedAtom");
        fmt.field("ident", ident);
        fmt.field("args", args);
        fmt.finish()
    }
}
impl<F, S> std::cmp::Eq for GroundedAtom<F, S> where Span<F, S>: std::cmp::Eq {}
impl<F, S> std::hash::Hash for GroundedAtom<F, S>
where
    Span<F, S>: std::hash::Hash,
{
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
        self.args.hash(state);
    }
}
impl<F, S> std::cmp::PartialEq for GroundedAtom<F, S>
where
    Span<F, S>: std::cmp::PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.ident == other.ident && self.args == other.args }
}
impl<F, S> Atomlike<F, S> for GroundedAtom<F, S> {
    #[inline]
    fn is_constant(&self) -> bool { self.args.is_empty() }

    #[inline]
    fn is_grounded(&self) -> bool { true }

    #[inline]
    fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        None.into_iter()
    }

    #[inline]
    fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        None.into_iter()
    }
}
