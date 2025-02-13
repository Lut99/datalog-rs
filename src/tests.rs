//  TESTS.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 14:32:43
//  Last edited:
//    11 Feb 2025, 16:06:35
//  Auto updated?
//    Yes
//
//  Description:
//!   Contains some common test functions.
//

#![allow(unused)]

use crate::ast::{Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, NegAtom, Not, Parens, Punctuated, Rule, RuleBody, Span};
#[cfg(feature = "ir")]
use crate::ir;
#[cfg(feature = "transitions")]
use crate::transitions::ast::Curly;


/***** LIBRARY *****/
/// Sets up a logger if wanted.
#[cfg(feature = "log")]
pub fn setup_logger() {
    use humanlog::{DebugMode, HumanLogger};

    // Figure out the desired debug level
    let mode: DebugMode = if let Ok(trace) = std::env::var("TRACE") {
        if trace == "1" || trace == "true" { DebugMode::Full } else { DebugMode::Debug }
    } else {
        DebugMode::Debug
    };

    // Check if the envs tell us to
    if let Ok(logger) = std::env::var("LOGGER") {
        if logger == "1" || logger == "true" {
            // Create the logger
            if let Err(err) = HumanLogger::terminal(mode).init() {
                eprintln!("WARNING: Failed to setup logger: {err} (no logging for this session)");
            }
        }
    }
}



/// Makes an [`ir::Rule`] conveniently.
#[cfg(feature = "interpreter")]
pub fn make_ir_rule<A>(
    consequents: impl IntoIterator<Item = A>,
    pos_antecedents: impl IntoIterator<Item = A>,
    neg_antecedents: impl IntoIterator<Item = A>,
) -> ir::Rule<A> {
    // Convert the consequents and antecedents first
    let consequents: Vec<A> = consequents.into_iter().collect();
    let pos_antecedents: Vec<A> = pos_antecedents.into_iter().collect();
    let neg_antecedents: Vec<A> = neg_antecedents.into_iter().collect();

    // Now build the rule
    ir::Rule { consequents, pos_antecedents, neg_antecedents }
}

/// Makes an [`ir::Atom`] conveniently.
#[cfg(feature = "interpreter")]
pub fn make_ir_atom(name: &'static str, args: impl IntoIterator<Item = &'static str>) -> ir::Atom<&'static str, &'static str> {
    // Make the punctuation
    let mut vals: Vec<ir::Atom<&'static str, &'static str>> = Vec::new();
    for arg in args {
        // Either push as atom or as variable
        vals.push(if arg.chars().next().unwrap_or_else(|| panic!("Empty argument given")).is_uppercase() {
            ir::Atom::Var(Ident { value: Span::new("make_ir_atom::var", arg) })
        } else {
            ir::Atom::Fact(ir::Fact { ident: Ident { value: Span::new("make_ir_atom::arg", arg) }, args: vec![] })
        })
    }

    // Make the atom
    ir::Atom::Fact(ir::Fact { ident: Ident { value: Span::new("make_ir_atom::name", name) }, args: vals })
}

/// Makes an [`ir::GroundAtom`] conveniently.
#[cfg(feature = "interpreter")]
pub fn make_ir_ground_atom(name: &'static str, args: impl IntoIterator<Item = &'static str>) -> ir::GroundAtom<&'static str, &'static str> {
    ir::GroundAtom {
        ident: Ident { value: Span::new("make_ir_ground_atom::name", name) },
        args:  args.into_iter().map(|a| ir::GroundAtom { ident: Ident { value: Span::new("make_ir_ground_atom::arg", a) }, args: vec![] }).collect(),
    }
}



/// Makes a [`Rule`] conveniently.
pub fn make_rule(
    consequents: impl IntoIterator<Item = Atom<&'static str, &'static str>>,
    antecedents: impl IntoIterator<Item = Literal<&'static str, &'static str>>,
) -> Rule<&'static str, &'static str> {
    // Convert the consequents and antecedents first
    let consequents: Punctuated<Atom<&'static str, &'static str>, Comma<&'static str, &'static str>> = consequents.into_iter().collect();
    let antecedents: Punctuated<Literal<&'static str, &'static str>, Comma<&'static str, &'static str>> = antecedents.into_iter().collect();

    // Now build the rule
    Rule {
        consequents,
        tail: if !antecedents.is_empty() {
            Some(RuleBody { arrow_token: Arrow { span: Span::new("make_rule::arrow", ":-") }, antecedents })
        } else {
            None
        },
        dot: Dot { span: Span::new("make_rule::dot", ".") },
    }
}



/// Makes a [`Literal`] conveniently.
pub fn make_lit(polarity: bool, name: &'static str, args: impl IntoIterator<Item = &'static str>) -> Literal<&'static str, &'static str> {
    if polarity {
        Literal::Atom(make_atom(name, args))
    } else {
        Literal::NegAtom(NegAtom { not_token: Not { span: Span::new("make_lit::not", "not") }, atom: make_atom(name, args) })
    }
}

/// Makes an [`Atom`] conveniently.
#[track_caller]
pub fn make_atom(name: &'static str, args: impl IntoIterator<Item = &'static str>) -> Atom<&'static str, &'static str> {
    // Make the punctuation
    let mut punct: Punctuated<Atom<&'static str, &'static str>, Comma<&'static str, &'static str>> = Punctuated::new();
    for (i, arg) in args.into_iter().enumerate() {
        // Either push as atom or as variable
        let arg: Atom<&'static str, &'static str> = if arg.chars().next().unwrap_or_else(|| panic!("Empty argument given")).is_uppercase() {
            Atom::Var(Ident { value: Span::new("make_atom::var", arg) })
        } else {
            Atom::Fact(Fact { ident: Ident { value: Span::new("make_atom::arg", arg) }, args: None })
        };

        // Then push with the correct punctuation
        if i == 0 {
            punct.push_first(arg);
        } else {
            punct.push(Comma { span: Span::new("make_atom::arg::comma", ",") }, arg);
        }
    }

    // Make the atom
    Atom::Fact(Fact {
        ident: Ident { value: Span::new("make_atom::name", name) },
        args:  if !punct.is_empty() {
            Some(FactArgs {
                paren_tokens: Parens { open: Span::new("make_atom::parens::open", "("), close: Span::new("make_atom::parens::close", ")") },
                args: punct,
            })
        } else {
            None
        },
    })
}



/// Makes an [`Ident`] conveniently.
pub fn make_ident(value: &'static str) -> Ident<&'static str, &'static str> {
    // Make the atom
    Ident { value: Span::new("make_ident", value) }
}

/// Makes a [`Curly`] conveniently.
#[cfg(feature = "transitions")]
pub fn make_curly() -> Curly<&'static str, &'static str> {
    // Make the atom
    Curly { open: Span::new("make_curly::open", "{"), close: Span::new("make_curly::close", "}") }
}
