//  VISIT MUT.rs
//    by Lut99
//
//  Created:
//    10 Feb 2025, 15:01:50
//  Last edited:
//    10 Feb 2025, 15:04:34
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a visitor pattern interface for the Datalog IR.
//!
//!   This version promises mutable access to all nodes.
//

use super::{Atom, Fact, GroundAtom, Ident, Rule, Span, Spec};


/***** LIBRARY *****/
/// Defines default (mutable) visit implementations on an IR node.
///
/// This will simply walk the node's edges by calling the given visitor's appropriate functions. By
/// relying on these defaults, anyone looking to traverse the IR only needs to implement functions
/// for nodes they are interested in.
///
/// This version allows mutable access to the visited node. If this is not required, see
/// [`Visitable`](super::visit::Visitable) instead (through the `visit`-feature).
pub trait VisitableMut {
    /// Visit this node mutably.
    ///
    /// The implementation of the node will decide how to proceed by calling the appropriate
    /// functions on the given visitor.
    ///
    /// # Arguments
    /// - `visitor`: The [`VisitorMut`] to call for any edges.
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>));
}

// Implementations for the IR.
impl<A: VisitableMut> VisitableMut for Spec<A> {
    #[inline]
    fn visit_mut<'ir>(&'ir mut self, visitor: &mut (impl ?Sized + VisitorMut<'ir>)) {
        let Self { rules } = self;

        // Visit all the rules in-order
        for rule in rules {
            visitor.visit_rule_mut(rule);
        }
    }
}
impl<A: VisitableMut> VisitableMut for Rule<A> {
    #[inline]
    fn visit_mut<'ir>(&'ir mut self, visitor: &mut (impl ?Sized + VisitorMut<'ir>)) {
        let Self { consequents, pos_antecedents, neg_antecedents } = self;

        // Visit consequents...
        for atom in consequents {
            visitor.visit_any_atom_mut(atom);
        }
        // ...positive antecedents...
        for atom in pos_antecedents {
            visitor.visit_any_atom_mut(atom);
        }
        // ...and, finally, negative ones
        for atom in neg_antecedents {
            visitor.visit_any_atom_mut(atom);
        }
    }
}

impl<S> VisitableMut for Atom<S> {
    #[inline]
    fn visit_mut<'ir>(&'ir mut self, visitor: &mut (impl ?Sized + VisitorMut<'ir>)) {
        match self {
            Self::Fact(f) => visitor.visit_fact_mut(f),
            Self::Var(v) => visitor.visit_ident_mut(v),
        }
    }
}
impl<S> VisitableMut for Fact<S> {
    #[inline]
    fn visit_mut<'ir>(&'ir mut self, visitor: &mut (impl ?Sized + VisitorMut<'ir>)) {
        let Self { ident, args } = self;

        visitor.visit_ident_mut(ident);
        for arg in args {
            visitor.visit_atom_mut(arg);
        }
    }
}

impl<S> VisitableMut for GroundAtom<S> {
    #[inline]
    fn visit_mut<'ir>(&'ir mut self, visitor: &mut (impl ?Sized + VisitorMut<'ir>)) {
        let Self { ident, args } = self;

        visitor.visit_ident_mut(ident);
        for arg in args {
            visitor.visit_ground_atom_mut(arg);
        }
    }
}

impl<S> VisitableMut for Ident<S> {
    #[inline]
    fn visit_mut<'ir>(&'ir mut self, visitor: &mut (impl ?Sized + VisitorMut<'ir>)) {
        if let Some(span) = self.span_mut() {
            visitor.visit_span_mut(span);
        }
    }
}
impl<S> VisitableMut for Span<S> {
    #[inline]
    fn visit_mut<'ir>(&'ir mut self, _visitor: &mut (impl ?Sized + VisitorMut<'ir>)) {
        /* Nothing */
    }
}



/// Defines a set of methods that, together, allow one to walk an entire Datalog IR.
///
/// Usually, you implement this trait only for one or two of its methods, and you rely on all
/// others to walk the nodes you don't find interesting.
///
/// Even better, you can use one of the loose functions (e.g., [`visit_spec()`]) to handle the
/// traversal specific nodes you _are_ interested in after you are done with that node.
///
/// This version allows mutable access to the visited node. If this is not required, see
/// [`Visitor`](super::visit::Visitor) instead (through the `visit`-feature).
pub trait VisitorMut<'ir> {
    /// Visits the toplevel node, a [`Spec`].
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `spec`: The [`Spec`] that is being visited.
    #[inline]
    fn visit_spec_mut<A: VisitableMut>(&mut self, spec: &'ir mut Spec<A>) { spec.visit_mut(self) }

    /// Visits a rule in a spec.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] that is being visited.
    #[inline]
    fn visit_rule_mut<A: VisitableMut>(&mut self, rule: &'ir mut Rule<A>) { rule.visit_mut(self) }

    /// Visits a one of the possible atoms in the spec.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `atom`: The [`A`]tom that is being visited.
    #[inline]
    fn visit_any_atom_mut<A: VisitableMut>(&mut self, atom: &'ir mut A) { atom.visit_mut(self) }



    /// Visits an atom in a spec.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `atom`: The [`Atom`] that is being visited.
    #[inline]
    fn visit_atom_mut<S>(&mut self, atom: &'ir mut Atom<S>) { atom.visit_mut(self) }

    /// Visits a fact in a spec.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `fact`: The [`Fact`] that is being visited.
    #[inline]
    fn visit_fact_mut<S>(&mut self, fact: &'ir mut Fact<S>) { fact.visit_mut(self) }



    /// Visits a ground atom in a spec.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `ground_atom`: The [`GroundAtom`] that is being visited.
    #[inline]
    fn visit_ground_atom_mut<S>(&mut self, ground_atom: &'ir mut GroundAtom<S>) { ground_atom.visit_mut(self) }



    /// Visits an identifier in a spec.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `ident`: The [`Ident`] that is being visited.
    #[inline]
    fn visit_ident_mut<S>(&mut self, ident: &'ir mut Ident<S>) { ident.visit_mut(self) }

    /// Visits a span.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `span`: The [`Span`] that is being visited.
    #[inline]
    fn visit_span_mut<S>(&mut self, span: &'ir mut Span<S>) { span.visit_mut(self) }
}
