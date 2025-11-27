//  VISIT.rs
//    by Lut99
//
//  Created:
//    10 Feb 2025, 10:13:09
//  Last edited:
//    10 Feb 2025, 15:01:30
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a visitor pattern interface for the Datalog IR.
//

use super::{Atom, Fact, GroundAtom, Ident, Rule, Span, Spec};


/***** LIBRARY *****/
/// Defines default visit implementations on an IR node.
///
/// This will simply walk the node's edges by calling the given visitor's appropriate functions. By
/// relying on these defaults, anyone looking to traverse the IR only needs to implement functions
/// for nodes they are interested in.
///
/// This version allows read-only access to the visited node. If mutable access is required, see
/// [`VisitableMut`](super::visit_mut::VisitableMut) instead (through the `visit-mut`-feature).
pub trait Visitable {
    /// Visit this node.
    ///
    /// The implementation of the node will decide how to proceed by calling the appropriate
    /// functions on the given visitor.
    ///
    /// # Arguments
    /// - `visitor`: The [`Visitor`] to call for any edges.
    fn visit<'ir>(&'ir self, visitor: &mut (impl ?Sized + Visitor<'ir>));
}

// Implementations for the IR.
impl<A: Visitable> Visitable for Spec<A> {
    #[inline]
    fn visit<'ir>(&'ir self, visitor: &mut (impl ?Sized + Visitor<'ir>)) {
        let Self { rules } = self;

        // Visit all the rules in-order
        for rule in rules {
            visitor.visit_rule(rule);
        }
    }
}
impl<A: Visitable> Visitable for Rule<A> {
    #[inline]
    fn visit<'ir>(&'ir self, visitor: &mut (impl ?Sized + Visitor<'ir>)) {
        let Self { consequents, pos_antecedents, neg_antecedents } = self;

        // Visit consequents...
        for atom in consequents {
            visitor.visit_any_atom(atom);
        }
        // ...positive antecedents...
        for atom in pos_antecedents {
            visitor.visit_any_atom(atom);
        }
        // ...and, finally, negative ones
        for atom in neg_antecedents {
            visitor.visit_any_atom(atom);
        }
    }
}

impl<S> Visitable for Atom<S> {
    #[inline]
    fn visit<'ir>(&'ir self, visitor: &mut (impl ?Sized + Visitor<'ir>)) {
        match self {
            Self::Fact(f) => visitor.visit_fact(f),
            Self::Var(v) => visitor.visit_ident(v),
        }
    }
}
impl<S> Visitable for Fact<S> {
    #[inline]
    fn visit<'ir>(&'ir self, visitor: &mut (impl ?Sized + Visitor<'ir>)) {
        let Self { ident, args } = self;

        visitor.visit_ident(ident);
        for arg in args {
            visitor.visit_atom(arg);
        }
    }
}

impl<S> Visitable for GroundAtom<S> {
    #[inline]
    fn visit<'ir>(&'ir self, visitor: &mut (impl ?Sized + Visitor<'ir>)) {
        let Self { ident, args } = self;

        visitor.visit_ident(ident);
        for arg in args {
            visitor.visit_ground_atom(arg);
        }
    }
}

impl<S> Visitable for Ident<S> {
    #[inline]
    fn visit<'ir>(&'ir self, visitor: &mut (impl ?Sized + Visitor<'ir>)) {
        if let Some(span) = self.span() {
            visitor.visit_span(span);
        }
    }
}
impl<S> Visitable for Span<S> {
    #[inline]
    fn visit<'ir>(&'ir self, _visitor: &mut (impl ?Sized + Visitor<'ir>)) {
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
/// This version allows read-only access to the visited node. If mutable access is required, see
/// [`VisitorMut`](super::visit_mut::VisitorMut) instead (through the `visit-mut`-feature).
pub trait Visitor<'ir> {
    /// Visits the toplevel node, a [`Spec`].
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `spec`: The [`Spec`] that is being visited.
    #[inline]
    fn visit_spec<A: Visitable>(&mut self, spec: &'ir Spec<A>) { spec.visit(self) }

    /// Visits a rule in a spec.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] that is being visited.
    #[inline]
    fn visit_rule<A: Visitable>(&mut self, rule: &'ir Rule<A>) { rule.visit(self) }

    /// Visits a one of the possible atoms in the spec.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `atom`: The [`A`]tom that is being visited.
    #[inline]
    fn visit_any_atom<A: Visitable>(&mut self, atom: &'ir A) { atom.visit(self) }



    /// Visits an atom in a spec.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `atom`: The [`Atom`] that is being visited.
    #[inline]
    fn visit_atom<S>(&mut self, atom: &'ir Atom<S>) { atom.visit(self) }

    /// Visits a fact in a spec.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `fact`: The [`Fact`] that is being visited.
    #[inline]
    fn visit_fact<S>(&mut self, fact: &'ir Fact<S>) { fact.visit(self) }



    /// Visits a ground atom in a spec.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `ground_atom`: The [`GroundAtom`] that is being visited.
    #[inline]
    fn visit_ground_atom<S>(&mut self, ground_atom: &'ir GroundAtom<S>) { ground_atom.visit(self) }



    /// Visits an identifier in a spec.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `ident`: The [`Ident`] that is being visited.
    #[inline]
    fn visit_ident<S>(&mut self, ident: &'ir Ident<S>) { ident.visit(self) }

    /// Visits a span.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `span`: The [`Span`] that is being visited.
    #[inline]
    fn visit_span<S>(&mut self, span: &'ir Span<S>) { span.visit(self) }
}
