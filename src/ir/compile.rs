//  COMPILE.rs
//    by Lut99
//
//  Created:
//    10 Feb 2025, 15:13:54
//  Last edited:
//    11 Feb 2025, 18:29:55
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements a compiler from the [Datalog AST](crate::ast) to the
//!   [Datalog IR](super).
//

use std::collections::HashSet;
use std::error;
use std::fmt::{Display, Formatter, Result as FResult};
use std::hash::Hash;

use ast_toolkit::span::SpannableDisplay;
use better_derive::Debug;

use crate::ast::{Ident, Span};
use crate::{ast, ir};


/***** ERRORS *****/
/// Defines errors possibly occurring during [compilation](ast::Spec::compile()).
#[derive(Debug)]
pub enum Error<F, S> {
    /// The given rule failed to satisfy the safety property.
    VarsNotEnumerable { vars: Vec<Ident<F, S>> },
}
impl<F, S: SpannableDisplay> Display for Error<F, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FResult {
        match self {
            Self::VarsNotEnumerable { vars } => {
                write!(
                    f,
                    "Variable{} {} {} not enumerable (it does not occur in a positive antecedent)",
                    if vars.len() > 1 { "s" } else { "" },
                    FancyList(vars),
                    if vars.len() > 1 { "are" } else { "is" }
                )
            },
        }
    }
}
impl<F, S: SpannableDisplay> error::Error for Error<F, S> {}





/***** HELPERS *****/
/// A neat formatter for vectors.
struct FancyList<'a, T>(&'a [T]);
impl<'a, T: Display> Display for FancyList<'a, T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        if self.0.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, elem) in self.0.iter().enumerate() {
            if i > 0 && i < self.0.len() - 1 {
                write!(f, ", ")?;
            } else if i > 0 {
                write!(f, " and ")?;
            }
            write!(f, "{elem}")?;
        }
        Ok(())
    }
}





/***** LIBRARY *****/
impl<F, S> ast::Spec<F, S>
where
    Span<F, S>: Clone + Eq + Hash,
{
    /// Checks if all the rules in this spec match the _safety property:_
    /// 1. All variables occurring in a rule, must occur as/in a positive antecedent.
    ///
    /// In other words, positive antecedents "drive" the quantification. Variables occurring on the
    /// left, ánd in negated antecedents, are used to replicate or filter the instantiations
    /// produced by the positive antecedents, respectively.
    ///
    /// # Returns
    /// True if all rules satisfy it, or false otherwise.
    #[inline]
    pub fn is_safe(&self) -> bool { self.rules.iter().all(ast::Rule::is_safe) }

    /// Compiles this relatively-close-to-the-syntax AST to an intermediate representation (IR)
    /// that is suitable for interpretation.
    ///
    /// Most notably, it simplifies the tree a little and makes sure every rule satisfies the
    /// [_safety property_](ast::Spec::is_safe()).
    ///
    /// # Returns
    /// A Datalog IR [`Spec`](ir::Spec) that is the compiled version.
    ///
    /// # Errors
    /// This function may error if any rule did not satisfy the safety property.
    #[inline]
    pub fn compile(&self) -> Result<ir::Spec<ir::Atom<F, S>>, Error<F, S>> {
        Ok(ir::Spec { rules: self.rules.iter().map(ast::Rule::compile).collect::<Result<_, _>>()? })
    }
}



impl<F, S> ast::Rule<F, S>
where
    Span<F, S>: Eq + Hash,
{
    /// Returns an iterator over all unbound variables.
    ///
    /// The definition of an unbound variable is a variable which does not occur in a positive
    /// antecedent.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`]ifiers of variables.
    #[inline]
    pub fn unbound_vars<'s>(&'s self) -> impl 's + Iterator<Item = &'s Ident<F, S>> {
        // Collect all the bound variables first
        let bound: HashSet<&ast::Ident<F, S>> =
            self.tail.iter().flat_map(|t| t.antecedents.values().filter(|l| l.is_positive())).flat_map(|l| l.atom().vars()).collect();

        // Then we're going to filter the others
        self.consequents
            .values()
            .chain(self.tail.iter().flat_map(|t| t.antecedents.values().filter(|l| !l.is_positive())).map(ast::Literal::atom))
            .flat_map(ast::Atom::vars)
            .filter(move |v| !bound.contains(v))
    }

    /// Checks if this rule satisfies the _safety property_.
    ///
    /// The safety property simply states that all variables in a rule must be
    /// [bound](Rule::unbound_vars()).
    ///
    /// # Returns
    /// True if the rule is satisfied, or false otherwise.
    #[inline]
    pub fn is_safe(&self) -> bool { self.unbound_vars().next().is_none() }
}
impl<F, S> ast::Rule<F, S>
where
    Span<F, S>: Clone + Eq + Hash,
{
    /// Compiles this relatively-close-to-the-syntax rule to an intermediate representation (IR)
    /// rule that is suitable for interpretation.
    ///
    /// Most notably, it simplifies the tree a little and makes sure every rule satisfies the
    /// [_safety property_](ast::Rule::is_safe()).
    ///
    /// # Returns
    /// A Datalog IR [`Rule`](ir::Rule) that is the compiled version.
    ///
    /// # Errors
    /// This function may error if any rule did not satisfy the safety property.
    pub fn compile(&self) -> Result<ir::Rule<ir::Atom<F, S>>, Error<F, S>> {
        // Crash if we fail the safety property check
        let unbound_vars: Vec<&Ident<F, S>> = self.unbound_vars().collect();
        if !unbound_vars.is_empty() {
            return Err(Error::VarsNotEnumerable { vars: unbound_vars.into_iter().cloned().collect() });
        }

        // If we do, then compile
        let n_pos_atoms: usize = self.antecedents().filter(|l| l.is_positive()).count();
        let mut rule: ir::Rule<ir::Atom<F, S>> = ir::Rule {
            consequents:     Vec::with_capacity(self.consequents.len()),
            pos_antecedents: Vec::with_capacity(n_pos_atoms),
            neg_antecedents: Vec::with_capacity(self.tail.as_ref().map(|t| t.antecedents.len()).unwrap_or(0) - n_pos_atoms),
        };
        for atom in self.consequents.values() {
            rule.consequents.push(atom.compile());
        }
        for lit in self.antecedents() {
            let atom: ir::Atom<F, S> = lit.atom().compile();
            if lit.is_positive() {
                rule.pos_antecedents.push(atom);
            } else {
                rule.neg_antecedents.push(atom);
            }
        }

        // Done
        Ok(rule)
    }
}



impl<F, S> ast::Atom<F, S>
where
    Span<F, S>: Clone,
{
    /// Compiles this relatively-close-to-the-syntax atom to an intermediate representation (IR)
    /// atom that is suitable for interpretation.
    ///
    /// # Returns
    /// A Datalog IR [`Atom`](ir::Atom) that is the compiled version.
    #[inline]
    pub fn compile(&self) -> ir::Atom<F, S> {
        match self {
            Self::Fact(f) => ir::Atom::Fact(ir::Fact {
                ident: f.ident.clone(),
                args:  f.args.iter().flat_map(|t| t.args.values().map(ast::Atom::compile)).collect(),
            }),
            Self::Var(v) => ir::Atom::Var(v.clone()),
        }
    }
}
