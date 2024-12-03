//  DATALOG.rs
//    by Lut99
//
//  Created:
//    03 Dec 2024, 10:46:29
//  Last edited:
//    03 Dec 2024, 11:02:52
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the [`datalog!()`]-macro.
//

use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote_spanned;
use syn::parse::ParseStream;
use syn::spanned::Spanned as _;
use syn::{Error, Path};

use crate::common::{DatalogAttributes, parse_rule, serialize_rule};


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
    // Parse from the input first: attributes
    let attrs: DatalogAttributes = input.parse()?;

    // Next, start building the tokens
    let crate_path: &Path = &attrs.crate_path;
    let mut rules: Vec<TokenStream2> = Vec::new();
    while !input.is_empty() {
        let (consequences, antecedents, _) = parse_rule(input)?;

        // Now we re-serialize.
        rules.push(serialize_rule(crate_path, &attrs.from, consequences, antecedents));
    }

    // Write the remainder
    let span: Span = if let Some(first) = rules.first() { first.span() } else { Span::call_site() };
    Ok(quote_spanned! {
        span =>
        #crate_path::ast::Spec {
            rules: ::std::vec![
                #(#rules),*
            ]
        }
    })
}
