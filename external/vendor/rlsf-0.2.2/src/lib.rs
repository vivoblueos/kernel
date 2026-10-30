#![doc = include_str!("../README.md")]
#![no_std]
#![cfg_attr(feature = "doc_cfg", feature(doc_cfg))]

#[cfg(doc)]
#[doc = include_str!("../CHANGELOG.md")]
pub mod _changelog_ {}

#[macro_use]
mod utils;

mod flex;
pub mod int;
mod tlsf;
pub use self::{
    flex::*,
    tlsf::{Tlsf, GRANULARITY},
};
#[cfg(feature = "unstable")]
pub use tlsf::BlockInfo;

/// Attaches `#[cfg(...)]` and `#[doc(cfg(...))]` to a given item definition
/// to conditionally compile it only when we have a `GlobalTlsf` implementation
/// for the current target.
macro_rules! if_supported_target {
    (
        $($tt:tt)*
    ) => {
        #[cfg(any(
            all(target_arch = "wasm32", not(target_feature = "atomics")),
            unix,
            doc,
        ))]
        #[cfg_attr(
            feature = "doc_cfg",
            doc(cfg(any(
                all(target_arch = "wasm32", not(target_feature = "atomics")),
                unix,
                // no `doc` here
            )))
        )]
        $($tt)*
    };
}

if_supported_target! { mod global; }
if_supported_target! { pub use self::global::*; }

#[cfg(any(test, feature = "std"))]
extern crate std;

#[cfg(test)]
mod tests;
