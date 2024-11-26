//  PHRASES.rs
//    by Lut99
//
//  Created:
//    26 Nov 2024, 14:00:48
//  Last edited:
//    26 Nov 2024, 16:43:38
//  Auto updated?
//    Yes
//
//  Description:
//!   Parses things other than rules in case the feature is given.
//

use std::marker::PhantomData;


/***** LIBRARY *****/
/// Parses a single phrase.
pub const fn phrase<F, S>() -> Phrase<F, S> { Phrase { _f: PhantomData, _s: PhantomData } }
