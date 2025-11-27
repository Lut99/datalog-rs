//  COMPILE.rs
//    by Lut99
//
//  Created:
//    10 Feb 2025, 15:13:54
//  Last edited:
//    12 Feb 2025, 15:38:53
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements a compiler from the [Datalog AST](crate::ast) to the
//!   [Datalog IR](super).
//

use std::collections::HashMap;
use std::fmt::{Display, Formatter, Result as FResult};
use std::{error, iter};

use ast_toolkit::span::SpannableBytes;
use better_derive::Debug;

use crate::ast::Ident;
use crate::{ast, ir};


/***** ERRORS *****/
/// Defines errors possibly occurring during [compilation](ast::Spec::compile()).
#[derive(Debug)]
pub enum Error<S> {
    /// The given rule failed to satisfy the safety property.
    VarsNotEnumerable { vars: Vec<Ident<S>> },
}
impl<'s, S: SpannableBytes<'s>> Display for Error<S> {
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
impl<'s, S: SpannableBytes<'s>> error::Error for Error<S> {}





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
impl<'s, S> ast::Spec<S>
where
    S: 's + Clone + SpannableBytes<'s>,
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
    pub fn compile(&self) -> Result<ir::Spec<ir::Atom<S>>, Error<S>> {
        Ok(ir::Spec { rules: self.rules.iter().map(ast::Rule::compile).collect::<Result<_, _>>()? })
    }
}



impl<'s, S> ast::Rule<S>
where
    S: SpannableBytes<'s>,
{
    /// Returns an iterator over all unbound variables.
    ///
    /// The definition of an unbound variable is a variable which does not occur in a positive
    /// antecedent.
    ///
    /// # Returns
    /// Some [`Iterator`] over [`Ident`]ifiers of variables.
    #[inline]
    pub fn unbound_vars<'r>(&'r self) -> impl 'r + Iterator<Item = &'r Ident<S>> {
        // Collect all the bound variables first
        let mut all: HashMap<&ast::Ident<S>, bool> = HashMap::new();
        for (var, binding) in self
            .consequents
            .values()
            .flat_map(|a| a.vars().zip(iter::repeat(false)))
            .chain(self.tail.iter().flat_map(|t| t.antecedents.values().flat_map(|l| l.atom().vars().zip(iter::repeat(l.is_positive())))))
        {
            if let Some(bound) = all.get_mut(&var) {
                *bound |= binding;
            } else {
                all.insert(var, binding);
            }
        }

        // Now we have all unique variables, yield only those unbound
        all.into_iter().filter_map(|(a, b)| if !b { Some(a) } else { None })
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
impl<'s, S> ast::Rule<S>
where
    S: 's + Clone + SpannableBytes<'s>,
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
    pub fn compile(&self) -> Result<ir::Rule<ir::Atom<S>>, Error<S>> {
        // Crash if we fail the safety property check
        let unbound_vars: Vec<&Ident<S>> = self.unbound_vars().collect();
        if !unbound_vars.is_empty() {
            return Err(Error::VarsNotEnumerable { vars: unbound_vars.into_iter().cloned().collect() });
        }

        // If we do, then compile
        let n_pos_atoms: usize = self.antecedents().filter(|l| l.is_positive()).count();
        let mut rule: ir::Rule<ir::Atom<S>> = ir::Rule {
            consequents:     Vec::with_capacity(self.consequents.len()),
            pos_antecedents: Vec::with_capacity(n_pos_atoms),
            neg_antecedents: Vec::with_capacity(self.tail.as_ref().map(|t| t.antecedents.len()).unwrap_or(0) - n_pos_atoms),
        };
        for atom in self.consequents.values() {
            rule.consequents.push(atom.compile());
        }
        for lit in self.antecedents() {
            let atom: ir::Atom<S> = lit.atom().compile();
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



impl<S> ast::Atom<S>
where
    S: Clone,
{
    /// Compiles this relatively-close-to-the-syntax atom to an intermediate representation (IR)
    /// atom that is suitable for interpretation.
    ///
    /// # Returns
    /// A Datalog IR [`Atom`](ir::Atom) that is the compiled version.
    #[inline]
    pub fn compile(&self) -> ir::Atom<S> {
        match self {
            Self::Fact(f) => ir::Atom::Fact(ir::Fact {
                ident: f.ident.clone(),
                args:  f.args.iter().flat_map(|t| t.args.values().map(ast::Atom::compile)).collect(),
            }),
            Self::Var(v) => ir::Atom::Var(v.clone()),
        }
    }
}
