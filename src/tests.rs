//  TESTS.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 14:32:43
//  Last edited:
//    03 Dec 2024, 15:38:43
//  Auto updated?
//    Yes
//
//  Description:
//!   Contains some common test functions.
//

use crate::ast::{Arrow, Atom, AtomArg, AtomArgs, Comma, Dot, Ident, Literal, Parens, Punctuated, Rule, RuleAntecedents, Span};
use crate::transitions::ast::Curly;


/***** LIBRARY *****/
/// Sets up a logger if wanted.
#[cfg(feature = "log")]
pub fn setup_logger() {
    use humanlog::{DebugMode, HumanLogger};

    // Check if the envs tell us to
    if let Ok(logger) = std::env::var("LOGGER") {
        if logger == "1" || logger == "true" {
            // Create the logger
            if let Err(err) = HumanLogger::terminal(DebugMode::Full).init() {
                eprintln!("WARNING: Failed to setup logger: {err} (no logging for this session)");
            }
        }
    }
}



/// Makes a [`Rule`] convenient.
pub fn make_rule(
    consequents: impl IntoIterator<Item = Atom<&'static str, &'static str>>,
    antecedents: impl IntoIterator<Item = Literal<&'static str, &'static str>>,
) -> Rule<&'static str, &'static str> {
    // Convert the consequents and antecedents first
    let consequences: Punctuated<Atom<&'static str, &'static str>, Comma<&'static str, &'static str>> = consequents.into_iter().collect();
    let antecedents: Punctuated<Literal<&'static str, &'static str>, Comma<&'static str, &'static str>> = antecedents.into_iter().collect();

    // Now build the rule
    Rule {
        consequences,
        tail: if !antecedents.is_empty() {
            Some(RuleAntecedents { arrow_token: Arrow { span: Span::new("make_rule::arrow", ":-") }, antecedents })
        } else {
            None
        },
        dot: make_dot(),
    }
}

/// Makes an [`Atom`] conveniently.
pub fn make_atom(name: &'static str, args: impl IntoIterator<Item = &'static str>) -> Atom<&'static str, &'static str> {
    // Make the punctuation
    let mut punct: Punctuated<AtomArg<&'static str, &'static str>, Comma<&'static str, &'static str>> = Punctuated::new();
    for (i, arg) in args.into_iter().enumerate() {
        if i == 0 {
            punct.push_first(AtomArg::Atom(Ident { value: Span::new("make_atom::arg", arg) }));
        } else {
            punct.push(Comma { span: Span::new("make_atom::arg::comma", ",") }, AtomArg::Atom(Ident { value: Span::new("make_atom::arg", arg) }));
        }
    }

    // Make the atom
    Atom {
        ident: Ident { value: Span::new("make_atom::name", name) },
        args:  if !punct.is_empty() {
            Some(AtomArgs {
                paren_tokens: Parens { open: Span::new("make_atom::parens::open", "("), close: Span::new("make_atom::parens::close", ")") },
                args: punct,
            })
        } else {
            None
        },
    }
}

/// Makes an [`Ident`] conveniently.
pub fn make_ident(value: &'static str) -> Ident<&'static str, &'static str> {
    // Make the atom
    Ident { value: Span::new("make_ident", value) }
}

/// Makes a [`Curly`] conveniently.
pub fn make_curly() -> Curly<&'static str, &'static str> {
    // Make the atom
    Curly { open: Span::new("make_curly::open", "{"), close: Span::new("make_curly::close", "}") }
}

/// Makes a [`Dot`] conveniently.
pub fn make_dot() -> Dot<&'static str, &'static str> { Dot { span: Span::new("make_rule::dot", ".") } }