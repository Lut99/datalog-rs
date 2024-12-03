//  DATALOG TRANS.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 11:04:28
//  Last edited:
//    03 Dec 2024, 12:12:32
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the embedded DSL macro for datalog's transition dialect.
//


/***** PARSE FUNCTIONS *****/

use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{ToTokens, quote, quote_spanned};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned as _;
use syn::token::{Brace, Minus, Plus, Pound};
use syn::{Error, Ident, LitStr, Path, Token, braced};

use crate::common::{DatalogAttributes, Rule};


/***** TYPE ALIASES *****/
/// Represents a Datalog postulation.
type Postulation = (PostulationOp, Brace, Vec<Rule>);

/// Represents a Datalog transition identifier.
type TransIdent = (Pound, Ident);

/// Represents a Datalog transition definition.
type Transition = (TransIdent, Brace, Vec<Postulation>);

/// Represents a Datalog trigger.
type Trigger = (Token![!], Brace, Vec<TransIdent>);





/***** HELPERS *****/
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
        match parse_postulation(input) {
            Ok(pos) => return Ok(Self::Postulation(pos)),
            Err(_) => {},
        }
        match Rule::parse(input) {
            Ok(rule) => return Ok(Self::Rule(rule)),
            Err(_) => {},
        }
        match parse_transition(input) {
            Ok(trans) => return Ok(Self::Transition(trans)),
            Err(_) => {},
        }
        Ok(Self::Trigger(parse_trigger(input)?))
    }
}

/// One of the two postulation tokens.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum PostulationOp {
    Create(Plus),
    Obfuscate(Minus),
}
impl Parse for PostulationOp {
    #[inline]
    fn parse(input: ParseStream) -> syn::Result<Self> {
        match Plus::parse(input) {
            Ok(plus) => Ok(Self::Create(plus)),
            Err(_) => Ok(Self::Obfuscate(Minus::parse(input)?)),
        }
    }
}
impl ToTokens for PostulationOp {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            Self::Create(p) => tokens.extend(quote! { #p }),
            Self::Obfuscate(m) => tokens.extend(quote! { #m }),
        }
    }
}





/***** PARSE FUNCTIONS *****/
/// Parses a transition definition.
///
/// # Arguments
/// - `input`: The [`ParseStream`] to parse from.
///
/// # Returns
/// The transition as a bunch of tokens.
///
/// # Errors
/// This function errors if we failed to parse the head of the input as a transition.
fn parse_transition(input: ParseStream) -> Result<Transition, Error> {
    // Parse the identifier first
    let ident: TransIdent = {
        let pound: Pound = input.parse()?;
        let ident: Ident = input.parse()?;
        (pound, ident)
    };

    // Then the curly braces
    let content;
    let brace: Brace = braced!(content in input);

    // Finally, parse the rest as a repeated bunch of postulations
    let mut posts: Vec<Postulation> = Vec::new();
    while !content.is_empty() {
        posts.push(parse_postulation(&content)?);
    }
    Ok((ident, brace, posts))
}

/// Parses a postulation.
///
/// # Arguments
/// - `input`: The [`ParseStream`] to parse from.
///
/// # Returns
/// The postulation as a bunch of tokens.
///
/// # Errors
/// This function errors if we failed to parse the head of the input as a postulation.
fn parse_postulation(input: ParseStream) -> Result<Postulation, Error> {
    // Parse the postulation op first
    let op: PostulationOp = input.parse()?;

    // Then the curly braces
    let content;
    let brace: Brace = braced!(content in input);

    // Finally, parse the rest as a repeated bunch of rules
    let mut rules: Vec<Rule> = Vec::new();
    while !content.is_empty() {
        rules.push(Rule::parse(&content)?);
    }
    Ok((op, brace, rules))
}

/// Parses a trigger.
///
/// # Arguments
/// - `input`: The [`ParseStream`] to parse from.
///
/// # Returns
/// The trigger as a bunch of tokens.
///
/// # Errors
/// This function errors if we failed to parse the head of the input as a trigger.
fn parse_trigger(input: ParseStream) -> Result<Trigger, Error> {
    // Parse the exclaim first
    let exclaim: Token![!] = input.parse()?;

    // Then the curly braces
    let content;
    let brace: Brace = braced!(content in input);

    // Finally, parse the rest as a repeated bunch of transition identifier
    let mut trans_idents: Vec<TransIdent> = Vec::new();
    while !content.is_empty() {
        let pound: Pound = content.parse()?;
        let ident: Ident = content.parse()?;
        trans_idents.push((pound, ident));
    }
    Ok((exclaim, brace, trans_idents))
}





/***** SERIALIZATION FUNCTIONS *****/
/// Serializes a given [transition](parse_transition()) into tokens representing a `datalog`
/// `Transition`.
///
/// # Arguments
/// - `crate_path`: A prefix that allows one to change where to get the datalog structs from.
/// - `from_str`: The string that is given as the from string in `Span` creations.
/// - `transition`: The parsed transition.
///
/// # Returns
/// A [`TokenStream2`] that encodes building the matching struct.
pub fn serialize_transition(crate_path: &Path, from_str: &LitStr) -> TokenStream2 { todo!() }





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
    // Parse from the input first: attributes
    let attrs: DatalogAttributes = input.parse()?;

    // Next, start building the tokens
    todo!()
}
