//  VISIT MUT.rs
//    by Lut99
//
//  Created:
//    07 Feb 2025, 16:33:29
//  Last edited:
//    04 Mar 2025, 14:45:10
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a visitor pattern interface for the Datalog AST.
//!   
//!   This version promises mutable access to all nodes.
//

use super::{
    Add, Arrow, Atom, BinOp, Comma, Dot, Expr, ExprBinOp, ExprLitInt, ExprParens, ExprUnOp, Fact, FactArgs, Ident, Literal, Minus, NegAtom, Not,
    Parens, Percent, Rule, RuleBody, Slash, Span, Spec, Star, UnOp,
};


/***** HELPER MACROS *****/
/// Implements a visitor function for the given token.
macro_rules! token_visitor_mut_impl {
    ($name:ident) => {
        impl<F, S> VisitableMut for $name<F, S> {
            #[inline]
            fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
                let Self { span } = self;
                visitor.visit_span_mut(span);
            }
        }
    };
}
pub(crate) use token_visitor_mut_impl;

/// Implements a visitor function for the given token.
macro_rules! delim_visitor_mut_impl {
    ($name:ident) => {
        impl<F, S> VisitableMut for $name<F, S> {
            #[inline]
            fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
                let Self { open, close } = self;
                visitor.visit_span_mut(open);
                visitor.visit_span_mut(close);
            }
        }
    };
}
pub(crate) use delim_visitor_mut_impl;





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
impl<F, S> VisitableMut for Spec<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { rules } = self;

        // Visit all the rules in-order
        for rule in rules {
            visitor.visit_rule_mut(rule);
        }
    }
}

impl<F, S> VisitableMut for Rule<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { consequents, tail, dot } = self;

        // Visit everything in the consequents first
        for (atom, comma) in consequents.pairs_mut() {
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
impl<F, S> VisitableMut for RuleBody<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { arrow_token, antecedents } = self;

        // Visit the token first, as a formality
        visitor.visit_arrow_mut(arrow_token);

        // Then visit all the antecedents
        for (lit, comma) in antecedents.pairs_mut() {
            visitor.visit_literal_mut(lit);
            if let Some(comma) = comma {
                visitor.visit_comma_mut(comma);
            }
        }
    }
}

impl<F, S> VisitableMut for Literal<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        match self {
            Self::Atom(a) => visitor.visit_atom_mut(a),
            Self::NegAtom(na) => visitor.visit_neg_atom_mut(na),
        }
    }
}
impl<F, S> VisitableMut for NegAtom<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { not_token, atom } = self;

        // Do the not-token first, to be kind.
        visitor.visit_not_mut(not_token);

        // Then the atom
        visitor.visit_atom_mut(atom)
    }
}

impl<F, S> VisitableMut for Atom<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        match self {
            Atom::Fact(f) => visitor.visit_fact_mut(f),
            Atom::Expr(e) => visitor.visit_expr_mut(e),
            Atom::Var(v) => visitor.visit_var_mut(v),
        }
    }
}
impl<F, S> VisitableMut for Fact<F, S> {
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
impl<F, S> VisitableMut for FactArgs<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { paren_tokens, args } = self;

        // Be sure to visit the parenthesis - both of them!
        visitor.visit_parens_mut(paren_tokens);

        // Then visit the fact's arguments (and commas)
        for (arg, comma) in args.pairs_mut() {
            visitor.visit_atom_mut(arg);
            if let Some(comma) = comma {
                visitor.visit_comma_mut(comma);
            }
        }
    }
}

impl<F, S> VisitableMut for Expr<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        match self {
            Self::LitInt(li) => visitor.visit_expr_lit_int_mut(li),
            Self::Var(v) => visitor.visit_var_mut(v),
            Self::UnOp(uo) => visitor.visit_expr_un_op_mut(uo),
            Self::BinOp(bo) => visitor.visit_expr_bin_op_mut(bo),
            Self::Parens(p) => visitor.visit_expr_parens_mut(p),
        }
    }
}
impl<F, S> VisitableMut for ExprLitInt<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { value: _, span } = self;

        // Visit the span
        visitor.visit_span_mut(span)
    }
}
impl<F, S> VisitableMut for ExprUnOp<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { op, expr } = self;

        // Visit the two things in-order
        visitor.visit_un_op_mut(op);
        visitor.visit_expr_mut(expr);
    }
}
impl<F, S> VisitableMut for ExprBinOp<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { op, lhs, rhs } = self;

        // Visit the two things in-order
        visitor.visit_expr_mut(lhs);
        visitor.visit_bin_op_mut(op);
        visitor.visit_expr_mut(rhs);
    }
}
impl<F, S> VisitableMut for ExprParens<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { paren_tokens, expr } = self;

        // Just visit 'em
        visitor.visit_parens_mut(paren_tokens);
        visitor.visit_expr_mut(expr);
    }
}
impl<F, S> VisitableMut for UnOp<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        match self {
            Self::Neg(n) => visitor.visit_minus_mut(n),
        }
    }
}
impl<F, S> VisitableMut for BinOp<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        match self {
            Self::Add(a) => visitor.visit_add_mut(a),
            Self::Sub(m) => visitor.visit_minus_mut(m),
            Self::Mul(s) => visitor.visit_star_mut(s),
            Self::Div(s) => visitor.visit_slash_mut(s),
            Self::Rem(p) => visitor.visit_percent_mut(p),
        }
    }
}

impl<F, S> VisitableMut for Ident<F, S> {
    #[inline]
    fn visit_mut<'ast>(&'ast mut self, visitor: &mut (impl ?Sized + VisitorMut<'ast>)) {
        let Self { value } = self;

        // Visit the span
        visitor.visit_span_mut(value)
    }
}

token_visitor_mut_impl!(Add);
token_visitor_mut_impl!(Arrow);
token_visitor_mut_impl!(Comma);
token_visitor_mut_impl!(Dot);
token_visitor_mut_impl!(Minus);
token_visitor_mut_impl!(Not);
token_visitor_mut_impl!(Percent);
token_visitor_mut_impl!(Slash);
token_visitor_mut_impl!(Star);
delim_visitor_mut_impl!(Parens);

impl<F, S> VisitableMut for Span<F, S> {
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
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `spec`: The (mutable reference to the) [`Spec`] that is being visited.
    #[inline]
    fn visit_spec_mut<F, S>(&mut self, spec: &'ast mut Spec<F, S>) { spec.visit_mut(self) }



    /// Visits a rule in the specification.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `rule`: The (mutable reference to the) [`Rule`] that is being visited.
    #[inline]
    fn visit_rule_mut<F, S>(&mut self, rule: &'ast mut Rule<F, S>) { rule.visit_mut(self) }

    /// Visits a rule's body in a rule.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `rule_body`: The (mutable reference to the) [`RuleBody`] that is being visited.
    #[inline]
    fn visit_rule_body_mut<F, S>(&mut self, rule_body: &'ast mut RuleBody<F, S>) { rule_body.visit_mut(self) }



    /// Visits a literal in a rule's body.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `literal`: The (mutable reference to the) [`Literal`] that is being visited.
    #[inline]
    fn visit_literal_mut<F, S>(&mut self, literal: &'ast mut Literal<F, S>) { literal.visit_mut(self) }

    /// Visits a negative atom in the more generic literal.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `neg_atom`: The (mutable reference to the) [`NegAtom`] that is being visited.
    #[inline]
    fn visit_neg_atom_mut<F, S>(&mut self, neg_atom: &'ast mut NegAtom<F, S>) { neg_atom.visit_mut(self) }



    /// Visits an atom that occurs either as a literal or as a fact's argument.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `atom`: The (mutable reference to the) [`Atom`] that is being visited.
    #[inline]
    fn visit_atom_mut<F, S>(&mut self, atom: &'ast mut Atom<F, S>) { atom.visit_mut(self) }

    /// Visits a fact that is a non-variable atom.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `fact`: The (mutable reference to the) [`Fact`] that is being visited.
    #[inline]
    fn visit_fact_mut<F, S>(&mut self, fact: &'ast mut Fact<F, S>) { fact.visit_mut(self) }

    /// Visits the argument-part of a fact.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `fact_args`: The (mutable reference to the) [`FactArgs`] that is being visited.
    #[inline]
    fn visit_fact_args_mut<F, S>(&mut self, fact_args: &'ast mut FactArgs<F, S>) { fact_args.visit_mut(self) }



    /// Visits any expression.
    ///
    /// By default, this function redirects to the node's [`VisitorMut::visit_ident_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The (mutable reference to the) [`Expr`] that is being visited.
    #[inline]
    fn visit_expr_mut<F, S>(&mut self, expr: &'ast mut Expr<F, S>) { expr.visit_mut(self) }

    /// Visits expression literals (_integer_ literals).
    ///
    /// By default, this function redirects to the node's [`VisitorMut::visit_ident_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The (mutable reference to the) [`ExprLitInt`] that is being visited.
    #[inline]
    fn visit_expr_lit_int_mut<F, S>(&mut self, expr: &'ast mut ExprLitInt<F, S>) { expr.visit_mut(self) }

    /// Visits unary expressions.
    ///
    /// By default, this function redirects to the node's [`VisitorMut::visit_ident_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The (mutable reference to the) [`ExprUnOp`] that is being visited.
    #[inline]
    fn visit_expr_un_op_mut<F, S>(&mut self, expr: &'ast mut ExprUnOp<F, S>) { expr.visit_mut(self) }

    /// Visits binary expressions.
    ///
    /// By default, this function redirects to the node's [`VisitorMut::visit_ident_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The (mutable reference to the) [`ExprBinOp`] that is being visited.
    #[inline]
    fn visit_expr_bin_op_mut<F, S>(&mut self, expr: &'ast mut ExprBinOp<F, S>) { expr.visit_mut(self) }

    /// Visits expressions wrapped in parenthesis.
    ///
    /// By default, this function redirects to the node's [`VisitorMut::visit_ident_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The (mutable reference to the) [`ExprParens`] that is being visited.
    #[inline]
    fn visit_expr_parens_mut<F, S>(&mut self, expr: &'ast mut ExprParens<F, S>) { expr.visit_mut(self) }

    /// Visits unary expression operators.
    ///
    /// By default, this function redirects to the node's [`VisitorMut::visit_ident_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `op`: The (mutable reference to the) [`UnOp`] that is being visited.
    #[inline]
    fn visit_un_op_mut<F, S>(&mut self, op: &'ast mut UnOp<F, S>) { op.visit_mut(self) }

    /// Visits binary expression operators.
    ///
    /// By default, this function redirects to the node's [`VisitorMut::visit_ident_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `op`: The (mutable reference to the) [`BinOp`] that is being visited.
    #[inline]
    fn visit_bin_op_mut<F, S>(&mut self, op: &'ast mut BinOp<F, S>) { op.visit_mut(self) }



    /// Visits an identifier but ONLY in variable position.
    ///
    /// By default, this function redirects to the [`VisitorMut::visit_ident_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `var`: The (mutable reference to the) [`Ident`] that is being visited.
    #[inline]
    fn visit_var_mut<F, S>(&mut self, var: &'ast mut Ident<F, S>) { self.visit_ident_mut(var) }

    /// Visits a good ol' identifier and/or variable name.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `ident`: The (mutable reference to the) [`Ident`] that is being visited.
    #[inline]
    fn visit_ident_mut<F, S>(&mut self, ident: &'ast mut Ident<F, S>) { ident.visit_mut(self) }



    /// Visits a plus terminal.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `add`: The (mutable reference to the) [`Add`] that is being visited.
    #[inline]
    fn visit_add_mut<F, S>(&mut self, add: &'ast mut Add<F, S>) { add.visit_mut(self) }

    /// Visits an arrow.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `arrow`: The (mutable reference to the) [`Arrow`] that is being visited.
    #[inline]
    fn visit_arrow_mut<F, S>(&mut self, arrow: &'ast mut Arrow<F, S>) { arrow.visit_mut(self) }

    /// Visits a comma.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `comma`: The (mutable reference to the) [`Comma`] that is being visited.
    #[inline]
    fn visit_comma_mut<F, S>(&mut self, comma: &'ast mut Comma<F, S>) { comma.visit_mut(self) }

    /// Visits a dot.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `dot`: The (mutable reference to the) [`Dot`] that is being visited.
    #[inline]
    fn visit_dot_mut<F, S>(&mut self, dot: &'ast mut Dot<F, S>) { dot.visit_mut(self) }

    /// Visits a minus.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `minus`: The (mutable reference to the) [`Minus`] that is being visited.
    #[inline]
    fn visit_minus_mut<F, S>(&mut self, minus: &'ast mut Minus<F, S>) { minus.visit_mut(self) }

    /// Visits a not.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `not`: The (mutable reference to the) [`Not`] that is being visited.
    #[inline]
    fn visit_not_mut<F, S>(&mut self, not: &'ast mut Not<F, S>) { not.visit_mut(self) }

    /// Visits a percent.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `percent`: The (mutable reference to the) [`Percent`] that is being visited.
    #[inline]
    fn visit_percent_mut<F, S>(&mut self, percent: &'ast mut Percent<F, S>) { percent.visit_mut(self) }

    /// Visits a slash.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `slash`: The (mutable reference to the) [`Slash`] that is being visited.
    #[inline]
    fn visit_slash_mut<F, S>(&mut self, slash: &'ast mut Slash<F, S>) { slash.visit_mut(self) }

    /// Visits a star.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `star`: The (mutable reference to the) [`Star`] that is being visited.
    #[inline]
    fn visit_star_mut<F, S>(&mut self, star: &'ast mut Star<F, S>) { star.visit_mut(self) }

    /// Visits a parens.
    ///
    /// By default, this function redirects to the node's [`VisitableMut::visit_mut()`]-implementation.
    ///
    /// # Arguments
    /// - `parens`: The (mutable reference to the) [`Parens`] that is being visited.
    #[inline]
    fn visit_parens_mut<F, S>(&mut self, parens: &'ast mut Parens<F, S>) { parens.visit_mut(self) }



    /// Visits the base of the whole AST, a span.
    ///
    /// By default, this function redirects to [`visit_span()`], which does nothing.
    ///
    /// # Arguments
    /// - `span`: The (mutable reference to the) [`Span`] that is being visited.
    #[inline]
    fn visit_span_mut<F, S>(&mut self, span: &'ast mut Span<F, S>) { span.visit_mut(self) }
}
