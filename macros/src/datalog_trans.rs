//  DATALOG TRANS.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 11:04:28
//  Last edited:
//    11 Feb 2025, 18:20:10
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the embedded DSL macro for datalog's transition dialect.
//

use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{ToTokens, quote_spanned};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned as _;
use syn::token::{Brace, Colon, Comma, Dot, Minus};
use syn::{Error, Ident, LitStr, Token, braced};

use crate::common::{Atom, CratePath, DatalogAttributes, FromStr, Literal, Rule, parse_punctuated, resolve_placeholders, serialize_punctuated};


/***** HELPER FUNCTIONS *****/
/// Serializes a not-token appropriately.
///
/// # Arguments
/// - `not`: The [`Not`] who's span we will use for the resulting span.
///
/// # Returns
/// A [`TokenStream2`] that represents the serialized curly brackets.
fn serialize_not(not: &Token![!]) -> TokenStream2 {
    let (crate_path, from_str): (CratePath, FromStr) = Default::default();
    quote_spanned! { not.span => #crate_path::transitions::ast::Exclaim {
        span: #crate_path::ast::Span::new(#from_str, "!"),
    } }
}

/// Serializes a brace-token appropriately.
///
/// # Arguments
/// - `brace`: The [`Brace`] who's span we will use for the resulting span.
///
/// # Returns
/// A [`TokenStream2`] that represents the serialized curly brackets.
fn serialize_brace(brace: &Brace) -> TokenStream2 {
    let (crate_path, from_str): (CratePath, FromStr) = Default::default();
    quote_spanned! { brace.span.join() => #crate_path::transitions::ast::Curly {
        open: #crate_path::ast::Span::new(#from_str, "{"),
        close: #crate_path::ast::Span::new(#from_str, "}"),
    } }
}





/***** AST *****/
/// One of the possible phrase types.
enum Phrase {
    Postulation(Postulation),
    Rule(Rule),
    Transition(Transition),
    Trigger(Trigger),
}
impl Parse for Phrase {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // They should all be unique, so just try
        match Postulation::parse(input) {
            Ok(pos) => return Ok(Self::Postulation(pos)),
            Err(_) => {},
        }
        match Rule::parse(input) {
            Ok(rule) => return Ok(Self::Rule(rule)),
            Err(_) => {},
        }
        match Transition::parse(input) {
            Ok(trans) => return Ok(Self::Transition(trans)),
            Err(_) => {},
        }
        Ok(Self::Trigger(Trigger::parse(input)?))
    }
}
impl ToTokens for Phrase {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let crate_path: CratePath = Default::default();

        tokens.extend(match self {
            Self::Postulation(p) => quote_spanned! { p.span() => #crate_path::transitions::ast::Phrase::Postulation(#p) },
            Self::Rule(r) => quote_spanned! { r.span() => #crate_path::transitions::ast::Phrase::Rule(#r) },
            Self::Transition(t) => quote_spanned! { t.span() => #crate_path::transitions::ast::Phrase::Transition(#t) },
            Self::Trigger(t) => quote_spanned! { t.span() => #crate_path::transitions::ast::Phrase::Trigger(#t) },
        });
    }
}

/// Represents a postulation.
struct Postulation {
    /// The symbol at the start of it.
    op: PostulationOp,
    /// The curly brackets wrapping...
    brace: Brace,
    /// The list of atoms to postulate.
    consequents: Punctuated<Atom, Comma>,
    /// Any antecedents
    antecedents: Option<((Colon, Minus), Punctuated<Literal, Comma>)>,
}
impl Parse for Postulation {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Parse the postulation op first
        let op: PostulationOp = input.parse()?;

        // Then the curly braces
        let content;
        let brace: Brace = braced!(content in input);

        // The bit in between is regular ol' identifiers
        let consequents = parse_punctuated(&content, Atom::parse)?;

        // Parse the antecedents, if any
        let antecedents = if let (Ok(colon), Ok(minus)) = (input.parse::<Colon>(), input.parse::<Minus>()) {
            // Parse a punctuated list of antecedents
            let antecedents: Punctuated<Literal, Comma> = parse_punctuated(input, Literal::parse)?;
            if antecedents.is_empty() {
                return Err(input.error("Expected at least one antecedent"));
            }
            Some(((colon, minus), antecedents))
        } else {
            None
        };

        // Parse the final dot
        let _dot: Dot = input.parse()?;

        // Done parsing!
        Ok(Self { op, brace, consequents, antecedents })
    }
}
impl ToTokens for Postulation {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let (crate_path, from_str): (CratePath, FromStr) = Default::default();

        // First, generate consequences
        let consequents_tokens: TokenStream2 = serialize_punctuated(self.consequents.iter());

        // Next, generate the antecedents
        let antecedents_tokens: TokenStream2 = if let Some(((colon, _), antecedents)) = &self.antecedents {
            // Generate all the antecedents
            let antecedents_tokens: TokenStream2 = serialize_punctuated(antecedents.iter());

            // Serialize them to a single RuleAntecedents
            quote_spanned! {
                colon.span =>
                Some(#crate_path::ast::RuleBody {
                    arrow_token: #crate_path::ast::Arrow { span: #crate_path::ast::Span::new(#from_str, ":-") },
                    antecedents: #antecedents_tokens,
                })
            }
        } else {
            quote_spanned! { consequents_tokens.span() => None }
        };

        // Finally, serialize the rule!
        let op: &PostulationOp = &self.op;
        let curly_tokens: TokenStream2 = serialize_brace(&self.brace);
        tokens.extend(quote_spanned! {
            consequents_tokens.span() =>
            #crate_path::transitions::ast::Postulation {
                op: #op,
                curly_tokens: #curly_tokens,
                consequents: #consequents_tokens,
                tail: #antecedents_tokens,
                dot: #crate_path::ast::Dot { span: #crate_path::ast::Span::new(#from_str, ".") },
            }
        });
    }
}

/// Represents a transition definition.
struct Transition {
    /// The identifier at the start of the transition.
    ident: TransIdent,
    /// The curly brackets wrapping...
    brace: Brace,
    /// The list of postulations within.
    posts: Vec<Postulation>,
}
impl Parse for Transition {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Parse the identifier first
        let ident: TransIdent = input.parse()?;

        // Then the curly braces
        let content;
        let brace: Brace = braced!(content in input);

        // Finally, parse the rest as a repeated bunch of postulations
        let mut posts: Vec<Postulation> = Vec::new();
        while !content.is_empty() {
            posts.push(Postulation::parse(&content)?);
        }

        // Parse the final dot
        let _dot: Dot = input.parse()?;

        // Done!
        Ok(Self { ident, brace, posts })
    }
}
impl ToTokens for Transition {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let (crate_path, from_str): (CratePath, FromStr) = Default::default();

        // OK, write the final struct
        let ident: &TransIdent = &self.ident;
        let curly_tokens: TokenStream2 = serialize_brace(&self.brace);
        let posts: Vec<TokenStream2> = self.posts.iter().map(Postulation::to_token_stream).collect();
        tokens.extend(quote_spanned! { Span::call_site() =>
            #crate_path::transitions::ast::Transition {
                ident: #ident,
                curly_tokens: #curly_tokens,
                postulations: ::std::vec![#(#posts),*],
                dot: #crate_path::ast::Dot { span: #crate_path::ast::Span::new(#from_str, ".") },
            }
        })
    }
}

/// Represents a transition trigger.
struct Trigger {
    /// The not token at the start.
    not:    Token![!],
    /// The curly brackets wrapping...
    brace:  Brace,
    /// The list of transition identifiers within.
    idents: Vec<TransIdent>,
}
impl Parse for Trigger {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Parse the not first
        let not: Token![!] = input.parse()?;

        // Then the curly braces
        let content;
        let brace: Brace = braced!(content in input);

        // Finally, parse the rest as a repeated bunch of postulations
        let mut idents: Vec<TransIdent> = Vec::new();
        while !content.is_empty() {
            idents.push(TransIdent::parse(&content)?);
        }

        // Parse the final dot
        let _dot: Dot = input.parse()?;

        // Done!
        Ok(Self { not, brace, idents })
    }
}
impl ToTokens for Trigger {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let (crate_path, from_str): (CratePath, FromStr) = Default::default();

        // OK, write the final struct
        let exclaim: TokenStream2 = serialize_not(&self.not);
        let curly_tokens: TokenStream2 = serialize_brace(&self.brace);
        let idents: Vec<TokenStream2> = self.idents.iter().map(TransIdent::to_token_stream).collect();
        tokens.extend(quote_spanned! { Span::call_site() =>
            #crate_path::transitions::ast::Trigger {
                exclaim_token: #exclaim,
                curly_tokens: #curly_tokens,
                idents: ::std::vec![#(#idents),*],
                dot: #crate_path::ast::Dot { span: #crate_path::ast::Span::new(#from_str, ".") },
            }
        })
    }
}



/// One of the two postulation tokens.
enum PostulationOp {
    Create(Token![+]),
    Obfuscate(Token![~]),
}
impl Parse for PostulationOp {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        match <Token![+]>::parse(input) {
            Ok(plus) => Ok(Self::Create(plus)),
            Err(_) => Ok(Self::Obfuscate(<Token![~]>::parse(input)?)),
        }
    }
}
impl ToTokens for PostulationOp {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let (crate_path, from_str): (CratePath, FromStr) = Default::default();

        // Write the appropriate postulation op
        match self {
            Self::Create(p) => tokens.extend(quote_spanned! { p.span() =>
                #crate_path::transitions::ast::PostulationOp::Create(#crate_path::transitions::ast::Add { span: #crate_path::ast::Span::new(#from_str, "+") })
            }),
            Self::Obfuscate(t) => tokens.extend(quote_spanned! { t.span() =>
                #crate_path::transitions::ast::PostulationOp::Obfuscate(#crate_path::transitions::ast::Squiggly { span: #crate_path::ast::Span::new(#from_str, "~") })
            }),
        }
    }
}

/// Special identifier for transitions.
struct TransIdent {
    /// The pound token preceding the identifier
    pound: Token![#],
    /// The identifier itself.
    ident: Ident,
}
impl Parse for TransIdent {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let pound: Token![#] = input.parse()?;
        let ident: Ident = input.parse()?;
        Ok(Self { pound, ident })
    }
}
impl ToTokens for TransIdent {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let (crate_path, from_str): (CratePath, FromStr) = Default::default();

        // Craft a string literal with the appropriate value
        let span: Span = self.pound.span().join(self.ident.span()).unwrap_or_else(Span::call_site);
        let value: LitStr = LitStr::new(&format!("#{}", self.ident.to_string()), span);

        // We can write it in one go
        tokens.extend(quote_spanned! { span => #crate_path::ast::Ident { value: #crate_path::ast::Span::new(#from_str, #value) } });
    }
}





/***** LIBRARY *****/
/// Implements the `datalog_trans!()`-macro.
///
/// # Arguments
/// - `input`: The input tokens to parse, as a [`ParseStream`].
///
/// # Returns
/// A [`TokenStream2`] that contains the translated tokens.
///
/// # Errors
/// This function may error if the input had an invalid stream of tokens for Datalog with negation
/// and transitions.
pub fn datalog_trans(input: ParseStream) -> Result<TokenStream2, Error> {
    let crate_path: CratePath = Default::default();

    // Parse from the input first: attributes
    let attrs: DatalogAttributes = input.parse()?;

    // Next, start building the tokens
    let mut phrases: Vec<TokenStream2> = Vec::new();
    while !input.is_empty() {
        phrases.push(input.parse::<Phrase>()?.into_token_stream());
    }

    // Write the remainder
    let span: Span = if let Some(first) = phrases.first() { first.span() } else { Span::call_site() };
    let res: TokenStream2 = quote_spanned! {
        span =>
        #crate_path::transitions::ast::TransitionSpec {
            phrases: ::std::vec![
                #(#phrases),*
            ]
        }
    };

    // Ensure that all the placeholders are correctly replaced
    Ok(resolve_placeholders(&attrs, res).into())
}
