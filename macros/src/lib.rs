//  LIB.rs
//    by Lut99
//
//  Created:
//    18 Mar 2024, 13:25:32
//  Last edited:
//    03 Dec 2024, 11:04:53
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements the `datalog!{}`-macro for the `justact-datalog`-crate.
//

// Modules
mod common;
mod datalog;
mod datalog_trans;

// Imports
use proc_macro::TokenStream;
use syn::parse::Parser as _;


/***** LIBRARY *****/
#[proc_macro]
pub fn datalog(input: TokenStream) -> TokenStream {
    match datalog::datalog.parse2(input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.into_compile_error().into(),
    }
}

#[proc_macro]
pub fn datalog_trans(input: TokenStream) -> TokenStream {
    match datalog_trans::datalog_trans.parse2(input.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.into_compile_error().into(),
    }
}
