//  LOG.rs
//    by Lut99
//
//  Created:
//    22 Mar 2024, 16:09:22
//  Last edited:
//    28 Mar 2024, 10:01:36
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
macro_rules! warning {
    ($($t:tt)*) => {
        ::log::warn!($($t)*)
    };
}
/// Mirrors the `warn!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature disabled, this macro does nothing.
#[cfg(not(feature = "log"))]
macro_rules! warning {
    ($($t:tt)*) => {};
}
pub(crate) use warning as warn;

/// Mirrors the `debug!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature enabled, this macro has exactly the same behaviour.
#[cfg(feature = "log")]
macro_rules! debug {
    ($($t:tt)*) => {
        ::log::debug!($($t)*)
    };
}
/// Mirrors the `debug!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature disabled, this macro does nothing.
#[cfg(not(feature = "log"))]
macro_rules! debug {
    ($($t:tt)*) => {};
}
pub(crate) use debug;

/// Mirrors the `trace!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature enabled, this macro has exactly the same behaviour.
#[cfg(feature = "log")]
macro_rules! trace {
    ($($t:tt)*) => {
        ::log::trace!($($t)*)
    };
}
/// Mirrors the `trace!()`-macro from the [`log`](https://github.com/rust-lang/log)-crate.
///
/// With the `log`-feature disabled, this macro does nothing.
#[cfg(not(feature = "log"))]
macro_rules! trace {
    ($($t:tt)*) => {};
}
pub(crate) use trace;
