//! Embedded-friendly (i.e. `#![no_std]`) math library featuring fast, safe
//! floating point approximations for common arithmetic operations, as well as
//! 2D and 3D vector types, statistical analysis functions, and quaternions.
//!
//! ## Floating point approximations: `F32` and `F32Ext`
//!
//! `micromath` supports approximating many arithmetic operations on `f32`
//! using bitwise operations, providing great performance and small code size
//! at the cost of precision. For use cases like graphics and signal
//! processing, these approximations are often sufficient and the performance
//! gains worth the lost precision.
//!
//! These approximations are defined on the [`F32`] newtype wrapper.
//!
//! ### `F32Ext` extension trait
//!
//! Floating point approximations can used via the the [`F32Ext`] trait which
//! is impl'd for `f32`, providing a drop-in `std`-compatible API.
//!
//! ```
//! use micromath::F32Ext;
//!
//! let n = 2.0.sqrt();
//! assert_eq!(n, 1.5); // close enough
//! ```
//!
//! Since the `F32Ext` trait provides methods which are already defined in
//! `std`, in cases where your crate links `std` the `F32Ext` versions of
//! the same methods will not be used, in which case you will get an unused
//! import warning for `F32Ext`.
//!
//! If you encounter this, add an `#[allow(unused_imports)]` above the import.
//!
//! ```
//! #[allow(unused_imports)]
//! use micromath::F32Ext;
//! ```
//!
//! ## Vector types
//!
//! See the [`vector`] module for more information on vector types.
//!
//! The following vector types are available, all of which have `pub x` and
//! `pub y` (and on 3D vectors, `pub z`) members:
//!
//! | Rust  | 2D      | 3D      |
//! |-------|---------|---------|
//! | `i8`  | `I8x2`  | `I8x3`  |
//! | `i16` | `I16x2` | `I16x3` |
//! | `i32` | `I32x2` | `I32x3` |
//! | `u8`  | `U8x2`  | `U8x3`  |
//! | `u16` | `U16x2` | `U16x3` |
//! | `u32` | `U32x2` | `U32x3` |
//! | `f32` | `F32x2` | `F32x3` |
//!
//! ## Statistical analysis
//!
//! See the [`statistics`] module for more information on statistical analysis
//! traits and functionality.
//!
//! The following traits are available and impl'd for slices and iterators of
//! `f32` (and can be impl'd for other types):
//!
//! - [`Mean`][`statistics::Mean`] - compute arithmetic mean with the `mean()` method.
//! - [`StdDev`][`statistics::StdDev`] - compute standard deviation with the `stddev()` method.
//! - [`Trim`][`statistics::Trim`] - cull outliers from a sample slice with the `trim()` method.
//! - [`Variance`][`statistics::Variance`] - compute variance with the `variance()` method.

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/tarcieri/micromath/main/img/micromath-sq.png",
    html_root_url = "https://docs.rs/micromath/2.0.0"
)]
#![forbid(unsafe_code)]
#![warn(
    missing_docs,
    rust_2018_idioms,
    trivial_casts,
    trivial_numeric_casts,
    unused_qualifications
)]

#[cfg(feature = "statistics")]
#[cfg_attr(docsrs, doc(cfg(feature = "statistics")))]
pub mod statistics;

#[cfg(feature = "vector")]
#[cfg_attr(docsrs, doc(cfg(feature = "vector")))]
pub mod vector;

mod f32ext;
mod float;
#[cfg(feature = "quaternion")]
mod quaternion;

pub use crate::{f32ext::F32Ext, float::F32};

#[cfg(feature = "quaternion")]
pub use crate::quaternion::Quaternion;

#[cfg(feature = "num-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "num-traits")))]
pub use num_traits;
