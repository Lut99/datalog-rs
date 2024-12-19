//  LOG.rs
//    by Lut99
//
//  Created:
//    22 Mar 2024, 16:09:22
//  Last edited:
//    19 Dec 2024, 11:09:55
//  Auto updated?
//    Yes
//
//  Description:
//!   Provides [`log`]-macro counterparts that conditionally log if the
//!   appropriate feature is given.
//


/***** LIBRARY *****/
/// Mirrors the `warn!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature enabled, this macro has exactly the same behaviour.
#[cfg(feature = "log")]
#[allow(unused)]
macro_rules! warning {
    ($($t:tt)*) => {
        ::log::warn!($($t)*)
    };
}
/// Mirrors the `warn!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature disabled, this macro does nothing.
#[cfg(not(feature = "log"))]
#[allow(unused)]
macro_rules! warning {
    ($($t:tt)*) => {};
}
#[allow(unused)]
pub(crate) use warning as warn;

/// Mirrors the `debug!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature enabled, this macro has exactly the same behaviour.
#[cfg(feature = "log")]
#[allow(unused)]
macro_rules! debug {
    ($($t:tt)*) => {
        ::log::debug!($($t)*)
    };
}
/// Mirrors the `debug!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature disabled, this macro does nothing.
#[cfg(not(feature = "log"))]
#[allow(unused)]
macro_rules! debug {
    ($($t:tt)*) => {};
}
#[allow(unused)]
pub(crate) use debug;

/// Mirrors the `trace!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature enabled, this macro has exactly the same behaviour.
#[cfg(feature = "log")]
#[allow(unused)]
macro_rules! trace {
    ($($t:tt)*) => {
        ::log::trace!($($t)*)
    };
}
/// Mirrors the `trace!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature disabled, this macro does nothing.
#[cfg(not(feature = "log"))]
#[allow(unused)]
macro_rules! trace {
    ($($t:tt)*) => {};
}
#[allow(unused)]
pub(crate) use trace;
