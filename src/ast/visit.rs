//  VISIT.rs
//    by Lut99
//
//  Created:
//    07 Feb 2025, 16:33:29
//  Last edited:
//    04 Mar 2025, 14:40:36
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a visitor pattern interface for the Datalog AST.
//

use super::{
    Add, Arrow, Atom, BinOp, Comma, Dot, Expr, ExprBinOp, ExprLitInt, ExprParens, ExprUnOp, Fact, FactArgs, Ident, Literal, Minus, NegAtom, Not,
    Parens, Percent, Rule, RuleBody, Slash, Span, Spec, Star, UnOp,
};


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
            Atom::Expr(e) => visitor.visit_expr(e),
            Atom::Var(v) => visitor.visit_var(v),
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

impl<F, S> Visitable for Expr<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        match self {
            Self::LitInt(li) => visitor.visit_expr_lit_int(li),
            Self::Var(v) => visitor.visit_var(v),
            Self::UnOp(uo) => visitor.visit_expr_un_op(uo),
            Self::BinOp(bo) => visitor.visit_expr_bin_op(bo),
            Self::Parens(p) => visitor.visit_expr_parens(p),
        }
    }
}
impl<F, S> Visitable for ExprLitInt<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { value: _, span } = self;

        // Visit the span
        visitor.visit_span(span)
    }
}
impl<F, S> Visitable for ExprUnOp<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { op, expr } = self;

        // Visit the two things in-order
        visitor.visit_un_op(op);
        visitor.visit_expr(expr);
    }
}
impl<F, S> Visitable for ExprBinOp<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { op, lhs, rhs } = self;

        // Visit the two things in-order
        visitor.visit_expr(lhs);
        visitor.visit_bin_op(op);
        visitor.visit_expr(rhs);
    }
}
impl<F, S> Visitable for ExprParens<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        let Self { paren_tokens, expr } = self;

        // Just visit 'em
        visitor.visit_parens(paren_tokens);
        visitor.visit_expr(expr);
    }
}
impl<F, S> Visitable for UnOp<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        match self {
            Self::Neg(n) => visitor.visit_minus(n),
        }
    }
}
impl<F, S> Visitable for BinOp<F, S> {
    #[inline]
    fn visit<'ast>(&'ast self, visitor: &mut (impl ?Sized + Visitor<'ast>)) {
        match self {
            Self::Add(a) => visitor.visit_add(a),
            Self::Sub(m) => visitor.visit_minus(m),
            Self::Mul(s) => visitor.visit_star(s),
            Self::Div(s) => visitor.visit_slash(s),
            Self::Rem(p) => visitor.visit_percent(p),
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

token_visitor_impl!(Add);
token_visitor_impl!(Arrow);
token_visitor_impl!(Comma);
token_visitor_impl!(Dot);
token_visitor_impl!(Minus);
token_visitor_impl!(Not);
token_visitor_impl!(Percent);
token_visitor_impl!(Slash);
token_visitor_impl!(Star);
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



    /// Visits any expression.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The [`Expr`] that is being visited.
    #[inline]
    fn visit_expr<F, S>(&mut self, expr: &'ast Expr<F, S>) { expr.visit(self) }

    /// Visits expression literals (_integer_ literals).
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The [`ExprLitInt`] that is being visited.
    #[inline]
    fn visit_expr_lit_int<F, S>(&mut self, expr: &'ast ExprLitInt<F, S>) { expr.visit(self) }

    /// Visits unary expressions.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The [`ExprUnOp`] that is being visited.
    #[inline]
    fn visit_expr_un_op<F, S>(&mut self, expr: &'ast ExprUnOp<F, S>) { expr.visit(self) }

    /// Visits binary expressions.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The [`ExprBinOp`] that is being visited.
    #[inline]
    fn visit_expr_bin_op<F, S>(&mut self, expr: &'ast ExprBinOp<F, S>) { expr.visit(self) }

    /// Visits expressions wrapped in parenthesis.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `expr`: The [`ExprParens`] that is being visited.
    #[inline]
    fn visit_expr_parens<F, S>(&mut self, expr: &'ast ExprParens<F, S>) { expr.visit(self) }

    /// Visits unary expression operators.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `op`: The [`UnOp`] that is being visited.
    #[inline]
    fn visit_un_op<F, S>(&mut self, op: &'ast UnOp<F, S>) { op.visit(self) }

    /// Visits binary expression operators.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `op`: The [`BinOp`] that is being visited.
    #[inline]
    fn visit_bin_op<F, S>(&mut self, op: &'ast BinOp<F, S>) { op.visit(self) }



    /// Visits an identifier but ONLY in variable position.
    ///
    /// By default, this function redirects to the [`Visitor::visit_ident()`]-implementation.
    ///
    /// # Arguments
    /// - `var`: The [`Ident`] that is being visited.
    #[inline]
    fn visit_var<F, S>(&mut self, var: &'ast Ident<F, S>) { self.visit_ident(var) }

    /// Visits a good ol' identifier and/or variable name.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `ident`: The [`Ident`] that is being visited.
    #[inline]
    fn visit_ident<F, S>(&mut self, ident: &'ast Ident<F, S>) { ident.visit(self) }



    /// Visits a plus terminal.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `add`: The [`Add`] that is being visited.
    #[inline]
    fn visit_add<F, S>(&mut self, add: &'ast Add<F, S>) { add.visit(self) }

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

    /// Visits a minus.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `minus`: The [`Minus`] that is being visited.
    #[inline]
    fn visit_minus<F, S>(&mut self, minus: &'ast Minus<F, S>) { minus.visit(self) }

    /// Visits a not.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `not`: The [`Not`] that is being visited.
    #[inline]
    fn visit_not<F, S>(&mut self, not: &'ast Not<F, S>) { not.visit(self) }

    /// Visits a percent.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `percent`: The [`Percent`] that is being visited.
    #[inline]
    fn visit_percent<F, S>(&mut self, percent: &'ast Percent<F, S>) { percent.visit(self) }

    /// Visits a slash.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `slash`: The [`Slash`] that is being visited.
    #[inline]
    fn visit_slash<F, S>(&mut self, slash: &'ast Slash<F, S>) { slash.visit(self) }

    /// Visits a star.
    ///
    /// By default, this function redirects to the node's [`Visitable::visit()`]-implementation.
    ///
    /// # Arguments
    /// - `star`: The [`Star`] that is being visited.
    #[inline]
    fn visit_star<F, S>(&mut self, star: &'ast Star<F, S>) { star.visit(self) }

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
