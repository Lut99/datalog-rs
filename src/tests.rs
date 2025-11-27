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

use crate::ast::{
    Arrow, Atom, Comma, Dot, Fact, FactArgs, Ident, Literal, NegAtom, Not, Parens, ParensClose, ParensOpen, Punctuated, Rule, RuleBody, Span,
};
#[cfg(feature = "ir")]
use crate::ir;
// #[cfg(feature = "transitions")]
// use crate::transitions::ast::Curly;


/***** CONSTANTS *****/
/// Pretends all (relevant) sources are in the same source.
pub const GENERATED_SOURCE_ID: &'static str = "<GENERATED>";





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
pub fn make_ir_atom(name: &'static str, args: impl IntoIterator<Item = &'static str>) -> ir::Atom<(&'static str, &'static str)> {
    let mut factory = ir::Ident::<(&'static str, &'static str)>::factory();

    // Make the punctuation
    let mut vals: Vec<ir::Atom<(&'static str, &'static str)>> = Vec::new();
    for arg in args {
        // Either push as atom or as variable
        vals.push(if arg.chars().next().unwrap_or_else(|| panic!("Empty argument given")).is_uppercase() {
            ir::Atom::Var(factory.create(arg.into(), None))
        } else {
            ir::Atom::Fact(ir::Fact { ident: factory.create(arg.into(), None), args: vec![] })
        })
    }

    // Make the atom
    ir::Atom::Fact(ir::Fact { ident: factory.create(name.into(), None), args: vals })
}

/// Makes an [`ir::GroundAtom`] conveniently.
#[cfg(feature = "interpreter")]
pub fn make_ir_ground_atom(name: &'static str, args: impl IntoIterator<Item = &'static str>) -> ir::GroundAtom<(&'static str, &'static str)> {
    let mut factory = ir::Ident::<(&'static str, &'static str)>::factory();
    ir::GroundAtom {
        ident: factory.create(name.into(), None),
        args:  args.into_iter().map(|a| ir::GroundAtom { ident: factory.create(a.into(), None), args: vec![] }).collect(),
    }
}



/// Makes a [`Rule`] conveniently.
pub fn make_rule(
    cons: impl IntoIterator<Item = Atom<(&'static str, &'static str)>>,
    ants: impl IntoIterator<Item = Literal<(&'static str, &'static str)>>,
) -> Rule<(&'static str, &'static str)> {
    // Convert the consequents and antecedents first
    let mut consequents: Punctuated<Atom<(&'static str, &'static str)>, Comma<(&'static str, &'static str)>> = Punctuated::new();
    for (i, con) in cons.into_iter().enumerate() {
        if i > 0 {
            consequents.push_punct(Comma { span: None });
        }
        consequents.push_value(con);
    }
    let mut antecedents: Punctuated<Literal<(&'static str, &'static str)>, Comma<(&'static str, &'static str)>> = Punctuated::new();
    for (i, ant) in ants.into_iter().enumerate() {
        if i > 0 {
            antecedents.push_punct(Comma { span: None });
        }
        antecedents.push_value(ant);
    }

    // Now build the rule
    Rule {
        consequents,
        tail: if !antecedents.is_empty() { Some(RuleBody { arrow_token: Arrow { span: None }, antecedents }) } else { None },
        dot: Dot { span: None },
    }
}



/// Makes a [`Literal`] conveniently.
pub fn make_lit(polarity: bool, name: &'static str, args: impl IntoIterator<Item = &'static str>) -> Literal<(&'static str, &'static str)> {
    if polarity {
        Literal::Atom(make_atom(name, args))
    } else {
        Literal::NegAtom(NegAtom { not_token: Not { span: None }, atom: make_atom(name, args) })
    }
}

/// Makes an [`Atom`] conveniently.
#[track_caller]
pub fn make_atom(name: &'static str, args: impl IntoIterator<Item = &'static str>) -> Atom<(&'static str, &'static str)> {
    // Make the punctuation
    let mut punct: Punctuated<Atom<(&'static str, &'static str)>, Comma<(&'static str, &'static str)>> = Punctuated::new();
    for (i, arg) in args.into_iter().enumerate() {
        // Either push as atom or as variable
        let arg: Atom<(&'static str, &'static str)> = if arg.chars().next().unwrap_or_else(|| panic!("Empty argument given")).is_uppercase() {
            Atom::Var(Ident::new(arg.into()))
        } else {
            Atom::Fact(Fact { ident: Ident::new(arg.into()), args: None })
        };

        // Then push with the correct punctuation
        if i == 0 {
            punct.push_value(arg);
        } else {
            punct.push_punct(Comma { span: None });
            punct.push_value(arg);
        }
    }

    // Make the atom
    Atom::Fact(Fact {
        ident: Ident::new(name.into()),
        args:  if !punct.is_empty() {
            Some(FactArgs { paren_tokens: Parens { open: ParensOpen { span: None }, close: ParensClose { span: None } }, args: punct })
        } else {
            None
        },
    })
}



/// Makes an [`Ident`] conveniently.
pub fn make_ident(value: &'static str) -> Ident<(&'static str, &'static str)> {
    // Make the atom
    Ident::new(value.into())
}

// /// Makes a [`Curly`] conveniently.
// #[cfg(feature = "transitions")]
// pub fn make_curly() -> Curly<(&'static str, &'static str)> {
//     // Make the atom
//     Curly { open: Span::new(("make_curly::open", "{")).into(), close: Span::new(("make_curly::close", "}")).into() }
// }
