//  VISIT MUT.rs
//    by Lut99
//
//  Created:
//    07 Feb 2025, 16:33:29
//  Last edited:
//    10 Feb 2025, 14:48:00
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a visitor pattern interface for the Datalog AST.
//!   
//!   This version promises mutable access to all nodes.
//

use super::{Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, NegAtom, Not, Parens, ParensClose, ParensOpen, Rule, RuleBody, Span, Spec};


/***** HELPER MACROS *****/
/// Implements a visitor function for the given token.
macro_rules! token_visitor_mut_impl {
    ($name:ident) => {
        impl<S> VisitableMut for $name<S> {
            #[inline]
            fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
                let Self { span } = self;
                if let Some(span) = span {
                    visitor.visit_span_mut(span);
                }
            }
        }
    };
}
pub(crate) use token_visitor_mut_impl;





/***** LIBRARY *****/
/// Defines default (mutable) visit implementations on an AST node.
///
/// This will simply walk the node's edges by calling the given visitor's appropriate functions. By
/// relying on these defaults, anyone looking to traverse the AST only needs to implement functions
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

// Implementations for the AST.
impl<S> VisitableMut for Spec<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { rules } = self;

        // Visit all the rules in-order
        for rule in rules {
            visitor.visit_rule_mut(rule);
        }
    }
}

impl<S> VisitableMut for Rule<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { consequents, tail, dot } = self;

        // Visit everything in the consequents first
        for (atom, comma) in consequents {
            visitor.visit_atom_mut(atom);
            if let Some(comma) = comma {
                visitor.visit_comma_mut(comma);
            }
        }

        // Then, visit the tail
        if let Some(tail) = tail {
            visitor.visit_rule_body_mut(tail);
        }

        // Finally, hit the dot
        visitor.visit_dot_mut(dot)
    }
}
impl<S> VisitableMut for RuleBody<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { arrow_token, antecedents } = self;

        // Visit the token first, as a formality
        visitor.visit_arrow_mut(arrow_token);

        // Then visit all the antecedents
        for (lit, comma) in antecedents {
            visitor.visit_literal_mut(lit);
            if let Some(comma) = comma {
                visitor.visit_comma_mut(comma);
            }
        }
    }
}

impl<S> VisitableMut for Literal<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        match self {
            Self::Atom(a) => visitor.visit_atom_mut(a),
            Self::NegAtom(na) => visitor.visit_neg_atom_mut(na),
        }
    }
}
impl<S> VisitableMut for NegAtom<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { not_token, atom } = self;

        // Do the not-token first, to be kind.
        visitor.visit_not_mut(not_token);

        // Then the atom
        visitor.visit_atom_mut(atom)
    }
}

impl<S> VisitableMut for Atom<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        match self {
            Atom::Fact(f) => visitor.visit_fact_mut(f),
            Atom::Var(v) => visitor.visit_ident_mut(v),
        }
    }
}
impl<S> VisitableMut for Fact<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { ident, args } = self;

        // We can visit the identifier first if we like.
        visitor.visit_ident_mut(ident);

        // Then visit the fact's arguments, if any.
        if let Some(args) = args {
            visitor.visit_fact_args_mut(args);
        }
    }
}
impl<S> VisitableMut for FactArgs<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { paren_tokens, args } = self;

        // Be sure to visit the parenthesis - both of them!
        visitor.visit_parens_mut(paren_tokens);

        // Then visit the fact's arguments (and commas)
        for (arg, comma) in args {
            visitor.visit_atom_mut(arg);
            if let Some(comma) = comma {
                visitor.visit_comma_mut(comma);
            }
        }
    }
}

impl<S> VisitableMut for Ident<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { value: _, span } = self;

        // Visit the span
        if let Some(span) = span {
            visitor.visit_span_mut(span);
        }
    }
}

token_visitor_mut_impl!(Arrow);
token_visitor_mut_impl!(Comma);
token_visitor_mut_impl!(Dot);
token_visitor_mut_impl!(Not);

impl<S> VisitableMut for Parens<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { open, close } = self;
        visitor.visit_parens_open_mut(open);
        visitor.visit_parens_close_mut(close);
    }
}
token_visitor_mut_impl!(ParensOpen);
token_visitor_mut_impl!(ParensClose);

impl<S> VisitableMut for Span<S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, _visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        /* Nothing */
    }
}



/// Defines a set of methods that, together, allow one to walk an entire Datalog AST.
///
/// Usually, you implement this trait only for one or two of its methods, and you rely on all
/// others to walk the nodes you don't find interesting.
///
/// Even better, you can use one of the loose functions (e.g., [`visit_spec()`]) to handle the
/// traversal specific nodes you _are_ interested in after you are done with that node.
///
/// This version allows mutable access to the visited node. If this is not required, see
/// [`Visitor`](super::visit::Visitor) instead (through the `visit`-feature).
pub trait VisitorMut<'ast> {
    /// Visits the toplevel node, a [`Spec`].
    ///
    /// By default, this function redirects to [`visit_spec()`].
    ///
    /// # Arguments
    /// - `spec`: The (mutable reference to the) [`Spec`] that is being visited.
    #[inline]
    fn visit_spec_mut<S>(&mut self, spec: &'ast mut Spec<S>) { spec.visit_mut(self) }



    /// Visits a rule in the specification.
    ///
    /// By default, this function redirects to [`visit_rule()`].
    ///
    /// # Arguments
    /// - `rule`: The (mutable reference to the) [`Rule`] that is being visited.
    #[inline]
    fn visit_rule_mut<S>(&mut self, rule: &'ast mut Rule<S>) { rule.visit_mut(self) }

    /// Visits a rule's body in a rule.
    ///
    /// By default, this function redirects to [`visit_rule_body()`].
    ///
    /// # Arguments
    /// - `rule_body`: The (mutable reference to the) [`RuleBody`] that is being visited.
    #[inline]
    fn visit_rule_body_mut<S>(&mut self, rule_body: &'ast mut RuleBody<S>) { rule_body.visit_mut(self) }



    /// Visits a literal in a rule's body.
    ///
    /// By default, this function redirects to [`visit_literal()`].
    ///
    /// # Arguments
    /// - `literal`: The (mutable reference to the) [`Literal`] that is being visited.
    #[inline]
    fn visit_literal_mut<S>(&mut self, literal: &'ast mut Literal<S>) { literal.visit_mut(self) }

    /// Visits a negative atom in the more generic literal.
    ///
    /// By default, this function redirects to [`visit_neg_atom()`].
    ///
    /// # Arguments
    /// - `neg_atom`: The (mutable reference to the) [`NegAtom`] that is being visited.
    #[inline]
    fn visit_neg_atom_mut<S>(&mut self, neg_atom: &'ast mut NegAtom<S>) { neg_atom.visit_mut(self) }



    /// Visits an atom that occurs either as a literal or as a fact's argument.
    ///
    /// By default, this function redirects to [`visit_atom()`].
    ///
    /// # Arguments
    /// - `atom`: The (mutable reference to the) [`Atom`] that is being visited.
    #[inline]
    fn visit_atom_mut<S>(&mut self, atom: &'ast mut Atom<S>) { atom.visit_mut(self) }

    /// Visits a fact that is a non-variable atom.
    ///
    /// By default, this function redirects to [`visit_fact()`].
    ///
    /// # Arguments
    /// - `fact`: The (mutable reference to the) [`Fact`] that is being visited.
    #[inline]
    fn visit_fact_mut<S>(&mut self, fact: &'ast mut Fact<S>) { fact.visit_mut(self) }

    /// Visits the argument-part of a fact.
    ///
    /// By default, this function redirects to [`visit_fact_args()`].
    ///
    /// # Arguments
    /// - `fact_args`: The (mutable reference to the) [`FactArgs`] that is being visited.
    #[inline]
    fn visit_fact_args_mut<S>(&mut self, fact_args: &'ast mut FactArgs<S>) { fact_args.visit_mut(self) }



    /// Visits a good ol' identifier and/or variable name.
    ///
    /// By default, this function redirects to [`visit_ident()`].
    ///
    /// # Arguments
    /// - `ident`: The (mutable reference to the) [`Ident`] that is being visited.
    #[inline]
    fn visit_ident_mut<S>(&mut self, ident: &'ast mut Ident<S>) { ident.visit_mut(self) }



    /// Visits an arrow.
    ///
    /// By default, this function redirects to [`visit_arrow()`].
    ///
    /// # Arguments
    /// - `arrow`: The (mutable reference to the) [`Arrow`] that is being visited.
    #[inline]
    fn visit_arrow_mut<S>(&mut self, arrow: &'ast mut Arrow<S>) { arrow.visit_mut(self) }

    /// Visits a comma.
    ///
    /// By default, this function redirects to [`visit_comma()`].
    ///
    /// # Arguments
    /// - `comma`: The (mutable reference to the) [`Comma`] that is being visited.
    #[inline]
    fn visit_comma_mut<S>(&mut self, comma: &'ast mut Comma<S>) { comma.visit_mut(self) }

    /// Visits a dot.
    ///
    /// By default, this function redirects to [`visit_dot()`].
    ///
    /// # Arguments
    /// - `dot`: The (mutable reference to the) [`Dot`] that is being visited.
    #[inline]
    fn visit_dot_mut<S>(&mut self, dot: &'ast mut Dot<S>) { dot.visit_mut(self) }

    /// Visits a not.
    ///
    /// By default, this function redirects to [`visit_not()`].
    ///
    /// # Arguments
    /// - `not`: The (mutable reference to the) [`Not`] that is being visited.
    #[inline]
    fn visit_not_mut<S>(&mut self, not: &'ast mut Not<S>) { not.visit_mut(self) }

    /// Visits a parens.
    ///
    /// By default, this function redirects to [`visit_parens()`].
    ///
    /// # Arguments
    /// - `parens`: The (mutable reference to the) [`Parens`] that is being visited.
    #[inline]
    fn visit_parens_mut<S>(&mut self, parens: &'ast mut Parens<S>) { parens.visit_mut(self) }

    /// Visits a parens open token.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `parens_open`: The [`ParensOpen`] that is being visited.
    #[inline]
    fn visit_parens_open_mut<S>(&mut self, parens_open: &'ast mut ParensOpen<S>) { parens_open.visit_mut(self) }

    /// Visits a parens close token.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `parens_close`: The [`ParensClose`] that is being visited.
    #[inline]
    fn visit_parens_close_mut<S>(&mut self, parens_close: &'ast mut ParensClose<S>) { parens_close.visit_mut(self) }



    /// Visits the base of the whole AST, a span.
    ///
    /// By default, this function redirects to [`visit_span()`], which does nothing.
    ///
    /// # Arguments
    /// - `span`: The (mutable reference to the) [`Span`] that is being visited.
    #[inline]
    fn visit_span_mut<S>(&mut self, span: &'ast mut Span<S>) { span.visit_mut(self) }
}
