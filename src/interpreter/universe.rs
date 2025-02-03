//  UNIVERSE.rs
//    by Lut99
//
//  Created:
//    03 Feb 2025, 16:44:01
//  Last edited:
//    03 Feb 2025, 17:09:12
//  Auto updated?
//    Yes
//
//  Description:
//!   Implements an abstraction over a set representing its Herbrand
//!   Universe.
//!   
//!   In a flat-atom world, the Herbrand universe is easy: it is simply all the unqiue atoms that
//!   occur, without arguments. E.g., in the spec `foo. bar :- foo. baz(quz).`, there are four
//!   constants: `foo`, `bar`, `baz` and `quz`. These are the things we want to quantify over for
//!   every variable.
//!   
//!   However, in a recursive-atom world, the answer is more complex. The question is: given any
//!   spec, what do we quantify over? Let's say:
//!     1. All unique grounded atoms (e.g., atoms without variables in them); this is a finite set.
//!     2. In the case we see an atom with a variable, it's that atom with the variable concretized.
//!         - What do we concretize it with? All #1 _plus_ anything in the knowledge base derived
//!           true which isn't in the knowledge base.
//
