//  VISIT.rs
//    by Lut99
//
//  Created:
//    07 Feb 2025, 16:33:29
//  Last edited:
//    10 Feb 2025, 14:53:34
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a visitor pattern interface for the Datalog AST.
//

use super::{Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, NegAtom, Not, Parens, Rule, RuleBody, Span, Spec};


/***** HELPER MACROS *****/
/// Implements a visitor function for the given token.
macro_rules! token_visitor_impl {
    ($name:ident) => {
        impl<F, S> Visitable for $name<F, S> {
            #[inline]
            fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
                let Self { span } = self;
                visitor.visit_span(span);
            }
        }
    };
}
pub(crate) use token_visitor_impl;

/// Implements a visitor function for the given token.
macro_rules! delim_visitor_impl {
    ($name:ident) => {
        impl<F, S> Visitable for $name<F, S> {
            #[inline]
            fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
                let Self { open, close } = self;
                visitor.visit_span(open);
                visitor.visit_span(close);
            }
        }
    };
}
pub(crate) use delim_visitor_impl;





/***** LIBRARY *****/
/// Defines default visit implementations on an AST node.
///
/// This will simply walk the node's edges by calling the given visitor's appropriate functions. By
/// relying on these defaults, anyone looking to traverse the AST only needs to implement functions
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
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>));
}

// Implementations for the AST.
impl<F, S> Visitable for Spec<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { rules } = self;

        // Visit all the rules in-order
        for rule in rules {
            visitor.visit_rule(rule);
        }
    }
}

impl<F, S> Visitable for Rule<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { consequents, tail, dot } = self;

        // Visit everything in the consequents first
        for (atom, comma) in consequents.pairs() {
            visitor.visit_atom(atom);
            if let Some(comma) = comma {
                visitor.visit_comma(comma);
            }
        }

        // Then, visit the tail
        if let Some(tail) = tail {
            visitor.visit_rule_body(tail);
        }

        // Finally, hit the dot
        visitor.visit_dot(dot)
    }
}
impl<F, S> Visitable for RuleBody<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { arrow_token, antecedents } = self;

        // Visit the token first, as a formality
        visitor.visit_arrow(arrow_token);

        // Then visit all the antecedents
        for (lit, comma) in antecedents.pairs() {
            visitor.visit_literal(lit);
            if let Some(comma) = comma {
                visitor.visit_comma(comma);
            }
        }
    }
}

impl<F, S> Visitable for Literal<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        match self {
            Self::Atom(a) => visitor.visit_atom(a),
            Self::NegAtom(na) => visitor.visit_neg_atom(na),
        }
    }
}
impl<F, S> Visitable for NegAtom<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { not_token, atom } = self;

        // Do the not-token first, to be kind.
        visitor.visit_not(not_token);

        // Then the atom
        visitor.visit_atom(atom)
    }
}

impl<F, S> Visitable for Atom<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        match self {
            Atom::Fact(f) => visitor.visit_fact(f),
            Atom::Var(v) => visitor.visit_ident(v),
        }
    }
}
impl<F, S> Visitable for Fact<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { ident, args } = self;

        // We can visit the identifier first if we like.
        visitor.visit_ident(ident);

        // Then visit the fact's arguments, if any.
        if let Some(args) = args {
            visitor.visit_fact_args(args);
        }
    }
}
impl<F, S> Visitable for FactArgs<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { paren_tokens, args } = self;

        // Be sure to visit the parenthesis - both of them!
        visitor.visit_parens(paren_tokens);

        // Then visit the fact's arguments (and commas)
        for (arg, comma) in args.pairs() {
            visitor.visit_atom(arg);
            if let Some(comma) = comma {
                visitor.visit_comma(comma);
            }
        }
    }
}

impl<F, S> Visitable for Ident<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { value } = self;

        // Visit the span
        visitor.visit_span(value)
    }
}

token_visitor_impl!(Arrow);
token_visitor_impl!(Comma);
token_visitor_impl!(Dot);
token_visitor_impl!(Not);
delim_visitor_impl!(Parens);

impl<F, S> Visitable for Span<F, S> {
    #[inline]
    fn visit<'ast>(&self, _visitor: &mut (impl ?Sized + Visitor<'ast>)) {
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
/// This version allows read-only access to the visited node. If mutable access is required, see
/// [`VisitorMut`](super::visit_mut::VisitorMut) instead (through the `visit-mut`-feature).
pub trait Visitor<'ast> {
    /// Visits the toplevel node, a [`Spec`].
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `spec`: The [`Spec`] that is being visited.
    #[inline]
    fn visit_spec<F, S>(&mut self, spec: &'ast Spec<F, S>) { spec.visit(self) }



    /// Visits a rule in the specification.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] that is being visited.
    #[inline]
    fn visit_rule<F, S>(&mut self, rule: &'ast Rule<F, S>) { rule.visit(self) }

    /// Visits a rule's body in a rule.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `rule_body`: The [`RuleBody`] that is being visited.
    #[inline]
    fn visit_rule_body<F, S>(&mut self, rule_body: &'ast RuleBody<F, S>) { rule_body.visit(self) }



    /// Visits a literal in a rule's body.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `literal`: The [`Literal`] that is being visited.
    #[inline]
    fn visit_literal<F, S>(&mut self, literal: &'ast Literal<F, S>) { literal.visit(self) }

    /// Visits a negative atom in the more generic literal.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `neg_atom`: The [`NegAtom`] that is being visited.
    #[inline]
    fn visit_neg_atom<F, S>(&mut self, neg_atom: &'ast NegAtom<F, S>) { neg_atom.visit(self) }



    /// Visits an atom that occurs either as a literal or as a fact's argument.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `atom`: The [`Atom`] that is being visited.
    #[inline]
    fn visit_atom<F, S>(&mut self, atom: &'ast Atom<F, S>) { atom.visit(self) }

    /// Visits a fact that is a non-variable atom.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `fact`: The [`Fact`] that is being visited.
    #[inline]
    fn visit_fact<F, S>(&mut self, fact: &'ast Fact<F, S>) { fact.visit(self) }

    /// Visits the argument-part of a fact.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `fact_args`: The [`FactArgs`] that is being visited.
    #[inline]
    fn visit_fact_args<F, S>(&mut self, fact_args: &'ast FactArgs<F, S>) { fact_args.visit(self) }



    /// Visits a good ol' identifier and/or variable name.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `ident`: The [`Ident`] that is being visited.
    #[inline]
    fn visit_ident<F, S>(&mut self, ident: &'ast Ident<F, S>) { ident.visit(self) }



    /// Visits an arrow.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `arrow`: The [`Arrow`] that is being visited.
    #[inline]
    fn visit_arrow<F, S>(&mut self, arrow: &'ast Arrow<F, S>) { arrow.visit(self) }

    /// Visits a comma.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `comma`: The [`Comma`] that is being visited.
    #[inline]
    fn visit_comma<F, S>(&mut self, comma: &'ast Comma<F, S>) { comma.visit(self) }

    /// Visits a dot.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `dot`: The [`Dot`] that is being visited.
    #[inline]
    fn visit_dot<F, S>(&mut self, dot: &'ast Dot<F, S>) { dot.visit(self) }

    /// Visits a not.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `not`: The [`Not`] that is being visited.
    #[inline]
    fn visit_not<F, S>(&mut self, not: &'ast Not<F, S>) { not.visit(self) }

    /// Visits a parens.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `parens`: The [`Parens`] that is being visited.
    #[inline]
    fn visit_parens<F, S>(&mut self, parens: &'ast Parens<F, S>) { parens.visit(self) }



    /// Visits the base of the whole AST, a span.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `span`: The [`Span`] that is being visited.
    #[inline]
    fn visit_span<F, S>(&mut self, span: &'ast Span<F, S>) { span.visit(self) }
}
