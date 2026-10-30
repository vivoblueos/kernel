#![no_std]
#![deny(missing_docs)]
#![allow(clippy::missing_safety_doc)] // The safety requirement is "use the procedural derive".
#![allow(clippy::needless_range_loop)] // range loop style is clearer in most places in enumset
#![cfg_attr(docsrs, feature(doc_cfg))]

//! A library for defining enums that can be used in compact bit sets. It supports arbitrarily
//! large enums, and has very basic support for using them in constants.
//!
//! # Cargo Features
//!
//! The following cargo features are available for this crate:
//!
//! * `serde`: Allows serialization and deserialization of the types in this crate.
//! * `alloc`: Enables the use of functions that require an allocator.
//! * `proc-macro-crate`: Enables the use of the `proc-macro-crate` crate to allow the renaming of
//!   the `enumset` crate in your user crate. This feature increases the MSRV to 1.69.0
//!
//! # Defining enums for use with EnumSet
//!
//! Enums to be used with [`EnumSet`] should be defined using `#[derive(EnumSetType)]`:
//!
//! ```rust
//! # use enumset::*;
//! #[derive(EnumSetType, Debug)]
//! pub enum Enum {
//!    A, B, C, D, E, F, G,
//! }
//! ```
//!
//! For more information on more advanced use cases, see the documentation for
//! [`#[derive(EnumSetType)]`](./derive.EnumSetType.html).
//!
//! # Working with EnumSets
//!
//! EnumSets can be constructed via [`EnumSet::new()`] like a normal set. In addition,
//! `#[derive(EnumSetType)]` creates operator overloads that allow you to create EnumSets like so:
//!
//! ```rust
//! # use enumset::*;
//! # #[derive(EnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! let new_set = Enum::A | Enum::C | Enum::G;
//! assert_eq!(new_set.len(), 3);
//! ```
//!
//! All bitwise operations you would expect to work on bitsets also work on both EnumSets and
//! enums with `#[derive(EnumSetType)]`:
//! ```rust
//! # use enumset::*;
//! # #[derive(EnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! // Intersection of sets
//! assert_eq!((Enum::A | Enum::B) & Enum::C, EnumSet::empty());
//! assert_eq!((Enum::A | Enum::B) & Enum::A, Enum::A);
//! assert_eq!(Enum::A & Enum::B, EnumSet::empty());
//!
//! // Symmetric difference of sets
//! assert_eq!((Enum::A | Enum::B) ^ (Enum::B | Enum::C), Enum::A | Enum::C);
//! assert_eq!(Enum::A ^ Enum::C, Enum::A | Enum::C);
//!
//! // Difference of sets
//! assert_eq!((Enum::A | Enum::B | Enum::C) - Enum::B, Enum::A | Enum::C);
//!
//! // Complement of sets
//! assert_eq!(!(Enum::E | Enum::G), Enum::A | Enum::B | Enum::C | Enum::D | Enum::F);
//! ```
//!
//! The [`enum_set!`] macro allows you to create EnumSets in constant contexts:
//!
//! ```rust
//! # use enumset::*;
//! # #[derive(EnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! const CONST_SET: EnumSet<Enum> = enum_set!(Enum::A | Enum::B);
//! assert_eq!(CONST_SET, Enum::A | Enum::B);
//! ```
//!
//! Mutable operations on the [`EnumSet`] otherwise behave similarly to Rust's builtin sets:
//!
//! ```rust
//! # use enumset::*;
//! # #[derive(EnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! let mut set = EnumSet::new();
//! set.insert(Enum::A);
//! set.insert_all(Enum::E | Enum::G);
//! assert!(set.contains(Enum::A));
//! assert!(!set.contains(Enum::B));
//! assert_eq!(set, Enum::A | Enum::E | Enum::G);
//! ```

#[cfg(feature = "alloc")]
extern crate alloc;

mod macros;

#[macro_use]
mod impl_set_common;

mod derive;
mod impl_set;
mod impl_set_mixed;
mod repr;
mod traits;

pub use crate::derive::EnumSetType;
pub use crate::set::{EnumSet, EnumSetIter};
pub use crate::traits::{EnumSetType, EnumSetTypeWithRepr};

/// Contains the types used for sets of enums.
pub mod set {
    pub use crate::impl_set::{EnumSet, EnumSetIter};
    pub use crate::impl_set_mixed::{MixedEnumSet, MixedEnumSetIter, MixedValue};
}

pub use crate::macros::__internal;
