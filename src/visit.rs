//  VISIT.rs
//    by Lut99
//
//  Created:
//    07 Feb 2025, 16:33:29
//  Last edited:
//    07 Feb 2025, 17:39:46
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines a visitor pattern interface for the Datalog AST.
//

use crate::ast::{Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, NegAtom, Not, Parens, Rule, RuleBody, Span, Spec};


/***** HELPER MACROS *****/
/// Implements a visitor function for the given token.
macro_rules! token_visitor_impl {
    ($name:ident, $arg:ident) => {
        paste::paste! {
            #[doc = concat!("Implements the default visiting behaviour for [`", stringify!($name), "`]s.\n\n#Arguments\n- `visitor`: Some [`Visitor`] that we use to call the next step.\n- `", stringify!($arg), "`: A [`", stringify!($name), "`] to visit.")]
            #[inline]
            pub fn [<visit_ $arg>]<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), $arg: &'ast $name<F, S>) {
                let $name { span } = $arg;
                visitor.visit_span(span);
            }
        }
    };
}
pub(crate) use token_visitor_impl;

/// Implements a visitor function for the given token.
macro_rules! delim_visitor_impl {
    ($name:ident, $arg:ident) => {
        paste::paste! {
            #[doc = concat!("Implements the default visiting behaviour for [`", stringify!($name), "`]s.\n\n#Arguments\n- `visitor`: Some [`Visitor`] that we use to call the next step.\n- `", stringify!($arg), "`: A [`", stringify!($name), "`] to visit.")]
            #[inline]
            pub fn [<visit_ $arg>]<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), $arg: &'ast $name<F, S>) {
                let $name { open, close } = $arg;
                visitor.visit_span(open);
                visitor.visit_span(close);
            }
        }
    };
}
pub(crate) use delim_visitor_impl;





/***** LIBRARY FUNCTIONS *****/
/// Implements the default visiting behaviour for [`Spec`]s.
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `spec`: A [`Spec`] to visit.
#[inline]
pub fn visit_spec<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), spec: &'ast Spec<F, S>) {
    let Spec { rules } = spec;

    // Visit all the rules in-order
    for rule in rules {
        visitor.visit_rule(rule);
    }
}



/// Implements the default visiting behaviour for [`Rule`]s.
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `rule`: A [`Rule`] to visit.
#[inline]
pub fn visit_rule<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), rule: &'ast Rule<F, S>) {
    let Rule { consequents, tail, dot } = rule;

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
    visitor.visit_dot(dot);
}

/// Implements the default visiting behaviour for [`RuleBody`].
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `rule_body`: A [`RuleBody`] to visit.
#[inline]
pub fn visit_rule_body<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), rule_body: &'ast RuleBody<F, S>) {
    let RuleBody { arrow_token, antecedents } = rule_body;

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



/// Implements the default visiting behaviour for [`Literal`]s.
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `literal`: A [`Literal`] to visit.
#[inline]
pub fn visit_literal<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), literal: &'ast Literal<F, S>) {
    match literal {
        Literal::Atom(a) => visitor.visit_atom(a),
        Literal::NegAtom(na) => visitor.visit_neg_atom(na),
    }
}

/// Implements the default visiting behaviour for [`NegAtom`]s.
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `neg_atom`: A [`NegAtom`] to visit.
#[inline]
pub fn visit_neg_atom<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), neg_atom: &'ast NegAtom<F, S>) {
    let NegAtom { not_token, atom } = neg_atom;

    // Do the not-token first, to be kind.
    visitor.visit_not(not_token);

    // Then the atom
    visitor.visit_atom(atom);
}



/// Implements the default visiting behaviour for [`Atom`]s.
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `atom`: A [`Atom`] to visit.
#[inline]
pub fn visit_atom<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), atom: &'ast Atom<F, S>) {
    match atom {
        Atom::Fact(f) => visitor.visit_fact(f),
        Atom::Var(v) => visitor.visit_ident(v),
    }
}

/// Implements the default visiting behaviour for [`Fact`]s.
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `fact`: A [`Fact`] to visit.
#[inline]
pub fn visit_fact<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), fact: &'ast Fact<F, S>) {
    let Fact { ident, args } = fact;

    // We can visit the identifier first if we like.
    visitor.visit_ident(ident);

    // Then visit the fact's arguments, if any.
    if let Some(args) = args {
        visitor.visit_fact_args(args);
    }
}

/// Implements the default visiting behaviour for [`FactArgs`].
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `fact_args`: A [`FactArgs`] to visit.
#[inline]
pub fn visit_fact_args<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), fact_args: &'ast FactArgs<F, S>) {
    let FactArgs { paren_tokens, args } = fact_args;

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



/// Implements the default visiting behaviour for [`Ident`]s.
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `ident`: A [`Ident`] to visit.
#[inline]
pub fn visit_ident<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), ident: &'ast Ident<F, S>) {
    let Ident { value } = ident;

    // Visit the span
    visitor.visit_span(value);
}



token_visitor_impl!(Arrow, arrow);
token_visitor_impl!(Comma, comma);
token_visitor_impl!(Dot, dot);
token_visitor_impl!(Not, not);
delim_visitor_impl!(Parens, parens);



/// Implements the default visiting behaviour for [`Span`]s.
///
/// # Arguments
/// - `visitor`: Some [`Visitor`] that we use to call the next step.
/// - `span`: A [`Span`] to visit.
#[allow(unused_variables)]
#[inline]
pub fn visit_span<'ast, F, S>(visitor: &mut (impl ?Sized + Visitor<'ast, F, S>), span: &'ast Span<F, S>) {
    /* Nothing */
}





/***** LIBRARY *****/
/// Defines a set of methods that, together, allow one to walk an entire Datalog AST.
///
/// Usually, you implement this trait only for one or two of its methods, and you rely on all
/// others to walk the nodes you don't find interesting.
///
/// Even better, you can use one of the loose functions (e.g., [`visit_spec()`]) to handle the
/// traversal specific nodes you _are_ interested in after you are done with that node.
pub trait Visitor<'ast, F, S> {
    /// Visits the toplevel node, a [`Spec`].
    ///
    /// By default, this function redirects to [`visit_spec()`].
    ///
    /// # Arguments
    /// - `spec`: The [`Spec`] that is being visited.
    #[inline]
    fn visit_spec(&mut self, spec: &'ast Spec<F, S>) { visit_spec(self, spec); }



    /// Visits a rule in the specification.
    ///
    /// By default, this function redirects to [`visit_rule()`].
    ///
    /// # Arguments
    /// - `rule`: The [`Rule`] that is being visited.
    #[inline]
    fn visit_rule(&mut self, rule: &'ast Rule<F, S>) { visit_rule(self, rule); }

    /// Visits a rule's body in a rule.
    ///
    /// By default, this function redirects to [`visit_rule_body()`].
    ///
    /// # Arguments
    /// - `rule_body`: The [`RuleBody`] that is being visited.
    #[inline]
    fn visit_rule_body(&mut self, rule_body: &'ast RuleBody<F, S>) { visit_rule_body(self, rule_body); }



    /// Visits a literal in a rule's body.
    ///
    /// By default, this function redirects to [`visit_literal()`].
    ///
    /// # Arguments
    /// - `literal`: The [`Literal`] that is being visited.
    #[inline]
    fn visit_literal(&mut self, literal: &'ast Literal<F, S>) { visit_literal(self, literal); }

    /// Visits a negative atom in the more generic literal.
    ///
    /// By default, this function redirects to [`visit_neg_atom()`].
    ///
    /// # Arguments
    /// - `neg_atom`: The [`NegAtom`] that is being visited.
    #[inline]
    fn visit_neg_atom(&mut self, neg_atom: &'ast NegAtom<F, S>) { visit_neg_atom(self, neg_atom); }



    /// Visits an atom that occurs either as a literal or as a fact's argument.
    ///
    /// By default, this function redirects to [`visit_atom()`].
    ///
    /// # Arguments
    /// - `atom`: The [`Atom`] that is being visited.
    #[inline]
    fn visit_atom(&mut self, atom: &'ast Atom<F, S>) { visit_atom(self, atom); }

    /// Visits a fact that is a non-variable atom.
    ///
    /// By default, this function redirects to [`visit_fact()`].
    ///
    /// # Arguments
    /// - `fact`: The [`Fact`] that is being visited.
    #[inline]
    fn visit_fact(&mut self, fact: &'ast Fact<F, S>) { visit_fact(self, fact); }

    /// Visits the argument-part of a fact.
    ///
    /// By default, this function redirects to [`visit_fact_args()`].
    ///
    /// # Arguments
    /// - `fact_args`: The [`FactArgs`] that is being visited.
    #[inline]
    fn visit_fact_args(&mut self, fact_args: &'ast FactArgs<F, S>) { visit_fact_args(self, fact_args); }



    /// Visits a good ol' identifier and/or variable name.
    ///
    /// By default, this function redirects to [`visit_ident()`].
    ///
    /// # Arguments
    /// - `ident`: The [`Ident`] that is being visited.
    #[inline]
    fn visit_ident(&mut self, ident: &'ast Ident<F, S>) { visit_ident(self, ident); }



    /// Visits an arrow.
    ///
    /// By default, this function redirects to [`visit_arrow()`].
    ///
    /// # Arguments
    /// - `arrow`: The [`Arrow`] that is being visited.
    #[inline]
    fn visit_arrow(&mut self, arrow: &'ast Arrow<F, S>) { visit_arrow(self, arrow); }

    /// Visits a comma.
    ///
    /// By default, this function redirects to [`visit_comma()`].
    ///
    /// # Arguments
    /// - `comma`: The [`Comma`] that is being visited.
    #[inline]
    fn visit_comma(&mut self, comma: &'ast Comma<F, S>) { visit_comma(self, comma); }

    /// Visits a dot.
    ///
    /// By default, this function redirects to [`visit_dot()`].
    ///
    /// # Arguments
    /// - `dot`: The [`Dot`] that is being visited.
    #[inline]
    fn visit_dot(&mut self, dot: &'ast Dot<F, S>) { visit_dot(self, dot); }

    /// Visits a not.
    ///
    /// By default, this function redirects to [`visit_not()`].
    ///
    /// # Arguments
    /// - `not`: The [`Not`] that is being visited.
    #[inline]
    fn visit_not(&mut self, not: &'ast Not<F, S>) { visit_not(self, not); }

    /// Visits a parens.
    ///
    /// By default, this function redirects to [`visit_parens()`].
    ///
    /// # Arguments
    /// - `parens`: The [`Parens`] that is being visited.
    #[inline]
    fn visit_parens(&mut self, parens: &'ast Parens<F, S>) { visit_parens(self, parens); }



    /// Visits the base of the whole AST, a span.
    ///
    /// By default, this function redirects to [`visit_span()`], which does nothing.
    ///
    /// # Arguments
    /// - `span`: The [`Span`] that is being visited.
    #[inline]
    fn visit_span(&mut self, span: &'ast Span<F, S>) { visit_span(self, span); }
}



/// Implements a visitor that simply walks everything and does nothing.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NopVisitor;
impl<'ast, F, S> Visitor<'ast, F, S> for NopVisitor {}
