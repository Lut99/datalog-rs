//  INTERMEDIATE REPRESENTATION AST.rs
//    by Lut99
//
//  Created:
//    05 Feb 2025, 14:24:31
//  Last edited:
//    10 Feb 2025, 15:14:07
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a second, much simpler, intermediate representation of a Datalog [`Spec`]ification.
//!
//!   This AST does _not_ carry as detailled source information as the main one. That's because
//!   that one may also be used for language server purposes (refactoring, syntax highlighting,
//!   etc.), whereas this one is aimed for reasoning.
//!
//!   Also note that the translation is not always trivial. In particular, checking for the safety
//!   property may cause some valid ASTs to be rejected as IRs.
//

// Define the visiting modules
pub mod compile;
#[cfg(feature = "visit")]
pub mod visit;
#[cfg(feature = "visit-mut")]
pub mod visit_mut;

// Imports
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Display, Formatter, Result as FResult};

use ast_toolkit::span::SpannableDisplay;
use better_derive::{Clone, Debug, Eq, Hash, PartialEq};

pub use crate::ast::{Ident, Span};


/***** ERRORS *****/
/// Represents that an atom contains a variable.
#[derive(Debug)]
pub struct ContainsVariablesError;
impl Display for ContainsVariablesError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FResult { write!(f, "Cannot turn atom with variables into a grounded atom") }
}
impl Error for ContainsVariablesError {}

/// Represents the case where a variable does not occur in an assignment.
#[derive(Debug)]
pub struct UnassignedVariableError<F, S> {
    /// The name of the variable that was unassigned.
    pub ident: Ident<F, S>,
}
impl<F, S: SpannableDisplay> Display for UnassignedVariableError<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { write!(f, "Variable \"{}\" is not assigned when concretizing it", self.ident) }
}
impl<F, S: SpannableDisplay> Error for UnassignedVariableError<F, S> {}





/***** INTERFACES *****/
/// Generalizes over different kinds of atoms.
pub trait Atomlike<F, S> {
    /// Returns whether this atom has any arguments.
    ///
    /// If true, implies [`Atomlike::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    fn is_constant(&self) -> bool;

    /// Returns an iterator over the arguments in this fact, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more [`Self`](Atomlike)s representing each argument.
    fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Self>;

    /// Returns an iterator over the arguments in this fact, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to [`Self`](Atomlike)s representing each
    /// argument.
    fn args_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Self>;



    /// Returns whether this atom has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    fn is_grounded(&self) -> bool;

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i;

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i;
}





/***** LIBRARY *****/
/// Defines a specification in the IR consisting only of [safe rules](Rule).
///
/// Cannot be parsed directly, but only obtained through compilation.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Spec<A> {
    /// The rules in this specification.
    pub rules: Vec<Rule<A>>,
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
/// Cannot be parsed directly, but only obtained through compilation.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Rule<A> {
    /// The consequents of the rule.
    pub consequents:     Vec<A>,
    /// The positive antecedents of the rule.
    pub pos_antecedents: Vec<A>,
    /// The negative antecedents of the rule.
    pub neg_antecedents: Vec<A>,
}
impl<A> Rule<A> {
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
impl<F, S> Rule<Atom<F, S>>
where
    Ident<F, S>: std::cmp::Eq + std::hash::Hash,
    Span<F, S>: Clone,
{
    /// A fool-proof version of [`Rule::to_ground_atom`] where any variables will be instantiated
    /// using the given assignment.
    ///
    /// # Arguments
    /// - `assign`: A [`HashMap`] that maps [variable names](Ident) to [`GroundAtom`]s.
    ///
    /// # Returns
    /// An equivalent [`GroundAtom`] with all the variables, if any, instantiated with `assign`.
    ///
    /// # Errors
    /// This function will error with an [`UnassignedVariableError`] if one of its variables did
    /// not occur in the given `assign`ment.
    #[inline]
    pub fn concretize(&self, assign: &HashMap<Ident<F, S>, GroundAtom<F, S>>) -> Result<Rule<GroundAtom<F, S>>, UnassignedVariableError<F, S>> {
        Ok(Rule {
            consequents:     self.consequents.iter().map(|a| a.concretize(assign)).collect::<Result<_, UnassignedVariableError<F, S>>>()?,
            pos_antecedents: self.pos_antecedents.iter().map(|a| a.concretize(assign)).collect::<Result<_, UnassignedVariableError<F, S>>>()?,
            neg_antecedents: self.neg_antecedents.iter().map(|a| a.concretize(assign)).collect::<Result<_, UnassignedVariableError<F, S>>>()?,
        })
    }
}
impl<F, S> Rule<Atom<F, S>>
where
    Span<F, S>: Clone,
{
    /// Tries to create an equivalent grounded rule out of this one.
    ///
    /// # Returns
    /// A Rule over [`GroundAtom`]s, or [`None`] if any atoms in this rule contained variables.
    ///
    /// Note, though, that the conversion is optimistic; it will convert as many arguments as
    /// possible until it discovers an argument with a variable _or_ it finishes. As a result, if
    /// you just want to check whether an atom exists, use [`Atom::is_grounded()`] on all atoms
    /// instead.
    #[inline]
    pub fn to_grounded_rule(&self) -> Option<Rule<GroundAtom<F, S>>> {
        Some(Rule {
            consequents:     self.consequents.iter().map(Atom::to_ground_atom).collect::<Option<_>>()?,
            pos_antecedents: self.pos_antecedents.iter().map(Atom::to_ground_atom).collect::<Option<_>>()?,
            neg_antecedents: self.neg_antecedents.iter().map(Atom::to_ground_atom).collect::<Option<_>>()?,
        })
    }
}
impl<F, S> Rule<Atom<F, S>> {
    /// Tries to turn this rule into one with grounded atoms.
    ///
    /// # Returns
    /// A Rule over [`GroundAtom`]s, or [`None`] if any atoms in this rule contained variables.
    ///
    /// Note, though, that the conversion is optimistic; it will convert as many arguments as
    /// possible until it discovers an argument with a variable _or_ it finishes. As a result, if
    /// you just want to check whether an atom exists, use [`Atom::is_grounded()`] on all atoms
    /// instead.
    #[inline]
    pub fn into_grounded_rule(self) -> Option<Rule<GroundAtom<F, S>>> {
        Some(Rule {
            consequents:     self.consequents.into_iter().map(Atom::into_ground_atom).collect::<Option<_>>()?,
            pos_antecedents: self.pos_antecedents.into_iter().map(Atom::into_ground_atom).collect::<Option<_>>()?,
            neg_antecedents: self.neg_antecedents.into_iter().map(Atom::into_ground_atom).collect::<Option<_>>()?,
        })
    }
}
impl<F, S> Rule<GroundAtom<F, S>>
where
    Span<F, S>: Clone,
{
    /// Create an equivalent rule over atoms out of this one.
    ///
    /// # Returns
    /// An equivalent Rule over [`Atom`]s.
    #[inline]
    pub fn to_atom_rule(&self) -> Rule<Atom<F, S>> {
        Rule {
            consequents:     self.consequents.iter().map(GroundAtom::to_atom).collect(),
            pos_antecedents: self.pos_antecedents.iter().map(GroundAtom::to_atom).collect(),
            neg_antecedents: self.neg_antecedents.iter().map(GroundAtom::to_atom).collect(),
        }
    }
}
impl<F, S> Rule<GroundAtom<F, S>> {
    /// Turns this rule into one with grounded atoms.
    ///
    /// # Returns
    /// An equivalent Rule over [`Atom`]s.
    #[inline]
    pub fn into_atom_rule(self) -> Rule<Atom<F, S>> {
        Rule {
            consequents:     self.consequents.into_iter().map(GroundAtom::into_atom).collect(),
            pos_antecedents: self.pos_antecedents.into_iter().map(GroundAtom::into_atom).collect(),
            neg_antecedents: self.neg_antecedents.into_iter().map(GroundAtom::into_atom).collect(),
        }
    }
}



/// Defines an atom with variables in it.
///
/// Note: being compiled, this node has no more syntax-only elements (e.g.,
/// [`Arrow`](crate::ast::Arrow) and the likes).
// NOTE: We implement `Clone`, `Debug`, `Eq`, `Hash` and `PartialEq` manually to prevent an endless
// cycle in deriving that `Punctuated<Atom, Comma>` implements one of those traits (since the
// question of whether it does depends on `Atom`, which transitively depends on `FactArgs`).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[better_derive(bound = (Span<F, S>))]
pub enum Atom<F, S> {
    /// It's a fact (i.e., non-variable).
    Fact(Fact<F, S>),
    /// It's a variable.
    Var(Ident<F, S>),
}
impl<F, S> Atom<F, S>
where
    Ident<F, S>: std::cmp::Eq + std::hash::Hash,
    Span<F, S>: Clone,
{
    /// A fool-proof version of [`Atom::to_ground_atom`] where any variables will be instantiated
    /// using the given assignment.
    ///
    /// # Arguments
    /// - `assign`: A [`HashMap`] that maps [variable names](Ident) to [`GroundAtom`]s.
    ///
    /// # Returns
    /// An equivalent [`GroundAtom`] with all the variables, if any, instantiated with `assign`.
    ///
    /// # Errors
    /// This function will error with an [`UnassignedVariableError`] if one of its variables did
    /// not occur in the given `assign`ment.
    #[inline]
    pub fn concretize(&self, assign: &HashMap<Ident<F, S>, GroundAtom<F, S>>) -> Result<GroundAtom<F, S>, UnassignedVariableError<F, S>> {
        match self {
            Self::Fact(f) => f.concretize(assign),
            Self::Var(v) => Ok(assign.get(v).ok_or(UnassignedVariableError { ident: v.clone() })?.clone()),
        }
    }
}
impl<F, S> Atom<F, S>
where
    Span<F, S>: Clone,
{
    /// Tries to create an equivalent [`GroundAtom`] out of this Atom.
    ///
    /// # Returns
    /// An equivalent [`GroundAtom`] if this atom was variable-free, or else [`None`].
    ///
    /// Note, though, that the conversion is optimistic; it will convert as many arguments as
    /// possible until it discovers an argument with a variable _or_ it finishes. As a result, if
    /// you just want to check whether an atom exists, use [`Atomlike::is_grounded()`] instead.
    #[inline]
    pub fn to_ground_atom(&self) -> Option<GroundAtom<F, S>> {
        match self {
            Self::Fact(f) => f.to_ground_atom(),
            Self::Var(_) => None,
        }
    }
}
impl<F, S> Atom<F, S> {
    /// Tries to turn this Atom into a [`GroundAtom`].
    ///
    /// # Returns
    /// An equivalent [`GroundAtom`] if this atom was variable-free, or else [`None`].
    ///
    /// Note, though, that the conversion is optimistic; it will convert as many arguments as
    /// possible until it discovers an argument with a variable _or_ it finishes. As a result, if
    /// you just want to check whether an atom exists, use [`Atomlike::is_grounded()`] instead.
    #[inline]
    pub fn into_ground_atom(self) -> Option<GroundAtom<F, S>> {
        match self {
            Self::Fact(f) => f.into_ground_atom(),
            Self::Var(_) => None,
        }
    }
}
impl<F, S> Atomlike<F, S> for Atom<F, S> {
    #[inline]
    fn is_constant(&self) -> bool {
        match self {
            Self::Fact(f) => f.is_constant(),
            Self::Var(_) => false,
        }
    }

    #[inline]
    fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Self> {
        match self {
            Self::Fact(f) => Box::new(f.args()) as Box<dyn 's + Iterator<Item = &'s Self>>,
            Self::Var(_) => Box::new(None.into_iter()),
        }
    }

    #[inline]
    fn args_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Self> {
        match self {
            Self::Fact(f) => Box::new(f.args_mut()) as Box<dyn 's + Iterator<Item = &'s mut Self>>,
            Self::Var(_) => Box::new(None.into_iter()),
        }
    }

    #[inline]
    fn is_grounded(&self) -> bool {
        match self {
            Self::Fact(f) => f.is_grounded(),
            Self::Var(_) => false,
        }
    }

    #[inline]
    fn vars<'s, 'i>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        match self {
            Self::Fact(f) => Box::new(f.vars()) as Box<dyn 's + Iterator<Item = &'s Ident<F, S>>>,
            Self::Var(v) => Box::new(Some(v).into_iter()),
        }
    }

    #[inline]
    fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        match self {
            Self::Fact(f) => Box::new(f.vars_mut()) as Box<dyn 's + Iterator<Item = &'s mut Ident<F, S>>>,
            Self::Var(v) => Box::new(Some(v).into_iter()),
        }
    }
}
impl<F, S> From<GroundAtom<F, S>> for Atom<F, S> {
    #[inline]
    fn from(value: GroundAtom<F, S>) -> Self { value.into_atom() }
}

/// Defines a non-variable [`Atom`] that may have variables in it.
///
/// Note: being compiled, this node has no more syntax-only elements (e.g.,
/// [`Arrow`](crate::ast::Arrow) and the likes).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Fact<F, S> {
    /// The identifier of the atom.
    pub ident: Ident<F, S>,
    /// Any arguments to the atom.
    pub args:  Vec<Atom<F, S>>,
}
impl<F, S> Fact<F, S> {
    /// Returns whether this atom has any arguments.
    ///
    /// If true, implies [`Fact::is_grounded`] will also return true.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    fn is_constant(&self) -> bool { self.args.iter().all(Atom::is_constant) }

    /// Returns an iterator over the arguments in this fact, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more [`Atom`]s representing each argument.
    #[inline]
    fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Atom<F, S>> { self.args.iter().flat_map(Atom::args) }

    /// Returns an iterator over the arguments in this fact, if any.
    ///
    /// # Returns
    /// An [`Iterator`] yielding zero or more mutable references to [`Atom`]s representing each
    /// argument.
    #[inline]
    fn args_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Atom<F, S>> { self.args.iter_mut().flat_map(Atom::args_mut) }

    /// Returns whether this atom has any variables.
    ///
    /// # Returns
    /// False if it has, true if it hasn't.
    #[inline]
    fn is_grounded(&self) -> bool { self.args.iter().all(Atom::is_grounded) }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (references).
    #[inline]
    fn vars<'s>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>> { self.args.iter().flat_map(Atom::vars) }

    /// Returns an iterator over the internal variables.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`] (mutable references).
    #[inline]
    fn vars_mut<'s, 'i>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Ident<F, S>>
    where
        'i: 's,
        Ident<F, S>: 'i,
    {
        self.args.iter_mut().flat_map(Atom::vars_mut)
    }
}
impl<F, S> Fact<F, S>
where
    Ident<F, S>: std::cmp::Eq + std::hash::Hash,
    Span<F, S>: Clone,
{
    /// A fool-proof version of [`Fact::to_ground_atom`] where any variables will be instantiated
    /// using the given assignment.
    ///
    /// # Arguments
    /// - `assign`: A [`HashMap`] that maps [variable names](Ident) to [`GroundAtom`]s.
    ///
    /// # Returns
    /// An equivalent [`GroundAtom`] with all the variables, if any, instantiated with `assign`.
    ///
    /// # Errors
    /// This function will error with an [`UnassignedVariableError`] if one of its variables did
    /// not occur in the given `assign`ment.
    #[inline]
    pub fn concretize(&self, assign: &HashMap<Ident<F, S>, GroundAtom<F, S>>) -> Result<GroundAtom<F, S>, UnassignedVariableError<F, S>> {
        Ok(GroundAtom {
            ident: self.ident.clone(),
            args:  self.args.iter().map(|a| a.concretize(assign)).collect::<Result<_, UnassignedVariableError<F, S>>>()?,
        })
    }
}
impl<F, S> Fact<F, S>
where
    Span<F, S>: Clone,
{
    /// Tries to create an equivalent [`GroundAtom`] out of this Fact.
    ///
    /// # Returns
    /// An equivalent [`GroundAtom`] if this atom was variable-free, or else [`None`].
    ///
    /// Note, though, that the conversion is optimistic; it will convert as many arguments as
    /// possible until it discovers an argument with a variable _or_ it finishes. As a result, if
    /// you just want to check whether an atom exists, use [`Fact::is_grounded()`] instead.
    #[inline]
    pub fn to_ground_atom(&self) -> Option<GroundAtom<F, S>> {
        // Try the arguments first
        let mut args: Vec<GroundAtom<F, S>> = Vec::with_capacity(self.args.len());
        for arg in &self.args {
            args.push(arg.to_ground_atom()?);
        }

        // OK, all arguments are variable-free!
        Some(GroundAtom { ident: self.ident.clone(), args })
    }
}
impl<F, S> Fact<F, S> {
    /// Tries to turn this Fact into a [`GroundAtom`].
    ///
    /// # Returns
    /// An equivalent [`GroundAtom`] if this atom was variable-free, or else [`None`].
    ///
    /// Note, though, that the conversion is optimistic; it will convert as many arguments as
    /// possible until it discovers an argument with a variable _or_ it finishes. As a result, if
    /// you just want to check whether an atom exists, use [`Fact::is_grounded()`] instead.
    #[inline]
    pub fn into_ground_atom(self) -> Option<GroundAtom<F, S>> {
        // Try the arguments first
        let mut args: Vec<GroundAtom<F, S>> = Vec::with_capacity(self.args.len());
        for arg in self.args {
            args.push(arg.into_ground_atom()?);
        }

        // OK, all arguments are variable-free!
        Some(GroundAtom { ident: self.ident, args })
    }
}
impl<F, S> From<GroundAtom<F, S>> for Fact<F, S> {
    #[inline]
    fn from(value: GroundAtom<F, S>) -> Self { value.into_fact() }
}



/// Defines an atom without any variables in it.
///
/// Note: being compiled, this node has no more syntax-only elements (e.g.,
/// [`Arrow`](crate::ast::Arrow) and the likes).
// NOTE: We implement `Clone`, `Debug`, `Eq`, `Hash` and `PartialEq` manually to prevent an endless
// cycle in deriving that `Punctuated<Atom, Comma>` implements one of those traits (since the
// question of whether it does depends on `Atom`, which transitively depends on `FactArgs`).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[better_derive(bound = (Span<F, S>))]
pub struct GroundAtom<F, S> {
    /// The identifier of the atom.
    pub ident: Ident<F, S>,
    /// Any arguments to the atom.
    pub args:  Vec<GroundAtom<F, S>>,
}
impl<F, S> GroundAtom<F, S>
where
    Span<F, S>: Clone,
{
    /// Creates an equivalent [`Atom`] out of this GroundAtom.
    ///
    /// # Returns
    /// An equivalent [`Atom::Fact`].
    #[inline]
    pub fn to_atom(&self) -> Atom<F, S> { Atom::Fact(self.to_fact()) }

    /// Creates an equivalent [`Fact`] out of this GroundAtom.
    ///
    /// # Returns
    /// An equivalent [`Fact`].
    #[inline]
    pub fn to_fact(&self) -> Fact<F, S> { Fact { ident: self.ident.clone(), args: self.args.iter().cloned().map(GroundAtom::into_atom).collect() } }
}
impl<F, S> GroundAtom<F, S> {
    /// Turns this GroundAtom into an [`Atom`].
    ///
    /// # Returns
    /// An equivalent [`Atom::Fact`].
    #[inline]
    pub fn into_atom(self) -> Atom<F, S> { Atom::Fact(self.into_fact()) }

    /// Turns this GroundAtom into a [`Fact`].
    ///
    /// # Returns
    /// An equivalent [`Fact`].
    #[inline]
    pub fn into_fact(self) -> Fact<F, S> { Fact { ident: self.ident, args: self.args.into_iter().map(GroundAtom::into_atom).collect() } }
}
impl<F, S> Atomlike<F, S> for GroundAtom<F, S> {
    #[inline]
    fn is_constant(&self) -> bool { self.args.is_empty() }

    #[inline]
    fn args<'s>(&'s self) -> impl 's + Iterator<Item = &'s Self> { self.args.iter() }

    #[inline]
    fn args_mut<'s>(&'s mut self) -> impl 's + Iterator<Item = &'s mut Self> { self.args.iter_mut() }

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
impl<F, S> TryFrom<Atom<F, S>> for GroundAtom<F, S> {
    type Error = ContainsVariablesError;

    #[inline]
    fn try_from(value: Atom<F, S>) -> Result<Self, Self::Error> { value.into_ground_atom().ok_or(ContainsVariablesError) }
}
impl<F, S> TryFrom<Fact<F, S>> for GroundAtom<F, S> {
    type Error = ContainsVariablesError;

    #[inline]
    fn try_from(value: Fact<F, S>) -> Result<Self, Self::Error> { value.into_ground_atom().ok_or(ContainsVariablesError) }
}
