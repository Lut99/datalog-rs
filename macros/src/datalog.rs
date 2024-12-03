//  DATALOG.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 10:46:29
//  Last edited:
//    03 Dec 2024, 12:11:58
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the [`datalog!()`]-macro.
//

use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{ToTokens, quote_spanned};
use syn::Error;
use syn::parse::ParseStream;
use syn::spanned::Spanned as _;

use crate::common::{CratePath, DatalogAttributes, Rule, resolve_placeholders};


/***** LIBRARY *****/
/// Implements the `datalog!()`-macro.
///
/// # Arguments
/// - `input`: The input tokens to parse, as a [`ParseStream`].
///
/// # Returns
/// A [`TokenStream2`] that contains the translated tokens.
///
/// # Errors
/// This function may error if the input had an invalid stream of tokens for vanilla Datalog with
/// negation.
pub fn datalog(input: ParseStream) -> Result<TokenStream2, Error> {
    let crate_path: CratePath = Default::default();

    // Parse from the input first: attributes
    let attrs: DatalogAttributes = input.parse()?;

    // Next, start building the tokens
    let mut rules: Vec<TokenStream2> = Vec::new();
    while !input.is_empty() {
        rules.push(input.parse::<Rule>()?.into_token_stream());
    }

    // Write the remainder
    let span: Span = if let Some(first) = rules.first() { first.span() } else { Span::call_site() };
    let res: TokenStream2 = quote_spanned! {
        span =>
        #crate_path::ast::Spec {
            rules: ::std::vec![
                #(#rules),*
            ]
        }
    };

    // Ensure that all the placeholders are correctly replaced
    Ok(resolve_placeholders(&attrs, res).into())
}
