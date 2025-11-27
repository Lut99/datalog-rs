//  TOKENS.rs
//    by Lut99
//
//  Created:
//    18 Mar 2024, 12:04:42
//  Last edited:
//    29 Nov 2024, 11:23:50
//  Auto updated?
//    Yes
//
//  Description:
//!   Defines parsers for additional keywords introduced by the transitions.
//

use super::super::ast::{Add, Curly, Exclaim, Squiggly};
use crate::parser::tokens::{delim_impl, token_impl};
use crate::transitions::ast::{CurlyClose, CurlyOpen};


/***** LIBRARY FUNCTIONS *****/
token_impl!(add(punct): "+" => {datalog::transitions} Add);
token_impl!(squiggly(punct): "~" => {datalog::transitions} Squiggly);
token_impl!(exclaim(punct): "!" => {datalog::transitions} Exclaim);

delim_impl!(curly(curly_open(punct): CurlyOpen, curly_close(punct): CurlyClose): "{", "}" => {datalog::transitions} Curly);
