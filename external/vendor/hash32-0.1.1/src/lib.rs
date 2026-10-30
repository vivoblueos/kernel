//! 32-bit hashing machinery
//!
//! # Why?
//!
//! Because 32-bit architectures are a thing (e.g. ARM Cortex-M) and you don't want your hashing
//! function to pull in a bunch of slow 64-bit compiler intrinsics (software implementations of
//! 64-bit operations).
//!
//! # Relationship to `core::hash`
//!
//! This crate exposes the same interfaces you'll find in [`core::hash`]: `Hash`, `Hasher`,
//! `BuildHasher` and `BuildHasherDefault`. The main difference is that `hash32::Hasher::finish`
//! returns a `u32` instead of `u64`, and the contract of `hash32::Hasher` forbids the implementer
//! from performing 64-bit (or 128-bit) operations while computing the hash.
//!
//! [`core::hash`]: https://doc.rust-lang.org/std/hash/index.html
//!
//! # `#[derive(Hash32)]`
//!
//! The easiest way to implement `hash32::Hash` for a `struct` is to use the `#[derive(Hash32)]`.
//!
//! ```
//! #[macro_use]
//! extern crate hash32_derive;
//!
//! #[derive(Hash32)]
//! struct Ipv4Addr([u8; 4]);
//!
//! # fn main() {}
//! ```
//!
//! # Hashers
//!
//! This crate provides implementations of the following 32-bit hashing algorithms:
//!
//! - [Fowler-Noll-Vo](struct.FnvHasher.html)
//! - [MurmurHash3](struct.Murmur3Hasher.html)
//!
//! # Future
//!
//! In the future we'd like to deprecate this crate in favor of making `core::hash::Hasher` generic
//! over the size of the computed hash. Below is shown the planned change (but it doesn't work due
//! to limitations in the `associated_type_defaults` feature):
//!
//! ``` ignore
//! #![feature(associated_type_defaults)]
//!
//! trait Hasher {
//!     type Hash = u64; // default type for backwards compatibility
//!
//!     fn finish(&self) -> Self::Hash; // changed
//!     fn write(&mut self, bytes: &[u8]);
//! }
//! ```
//!
//! With this change a single `#[derive(Hash)]` would enough to make a type hashable with 32-bit and
//! 64-bit hashers.

#![deny(missing_docs)]
#![deny(warnings)]
#![cfg_attr(feature = "const-fn", feature(const_fn))]
#![no_std]

extern crate byteorder;

use core::marker::PhantomData;
use core::{mem, slice};

pub use fnv::Hasher as FnvHasher;
pub use murmur3::Hasher as Murmur3Hasher;

mod fnv;
mod murmur3;

/// See [`core::hash::BuildHasherDefault`][0] for details
///
/// [0]: https://doc.rust-lang.org/core/hash/struct.BuildHasherDefault.html
pub struct BuildHasherDefault<H>
where
    H: Default + Hasher,
{
    _marker: PhantomData<H>,
}

impl<H> Default for BuildHasherDefault<H>
where
    H: Default + Hasher,
{
    fn default() -> Self {
        BuildHasherDefault {
            _marker: PhantomData,
        }
    }
}

impl<H> BuildHasherDefault<H>
where
    H: Default + Hasher,
{
    /// `const` constructor
    #[cfg(feature = "const-fn")]
    pub const fn new() -> Self {
        BuildHasherDefault {
            _marker: PhantomData,
        }
    }
}

impl<H> BuildHasher for BuildHasherDefault<H>
where
    H: Default + Hasher,
{
    type Hasher = H;

    fn build_hasher(&self) -> Self::Hasher {
        H::default()
    }
}

/// See [`core::hash::BuildHasher`][0] for details
///
/// [0]: https://doc.rust-lang.org/core/hash/trait.BuildHasher.html
pub trait BuildHasher {
    /// See [`core::hash::BuildHasher::Hasher`][0]
    ///
    /// [0]: https://doc.rust-lang.org/std/hash/trait.BuildHasher.html#associatedtype.Hasher
    type Hasher: Hasher;

    /// See [`core::hash::BuildHasher.build_hasher`][0]
    ///
    /// [0]: https://doc.rust-lang.org/std/hash/trait.BuildHasher.html#tymethod.build_hasher
    fn build_hasher(&self) -> Self::Hasher;
}

/// See [`core::hash::Hasher`][0] for details
///
/// [0]: https://doc.rust-lang.org/core/hash/trait.Hasher.html
///
/// # Contract
///
/// Implementers of this trait must *not* perform any 64-bit (or 128-bit) operation while computing
/// the hash.
pub trait Hasher {
    /// See [`core::hash::Hasher.finish`][0]
    ///
    /// [0]: https://doc.rust-lang.org/std/hash/trait.Hasher.html#tymethod.finish
    fn finish(&self) -> u32;

    /// See [`core::hash::Hasher.write`][0]
    ///
    /// [0]: https://doc.rust-lang.org/std/hash/trait.Hasher.html#tymethod.write
    fn write(&mut self, bytes: &[u8]);
}

/// See [`core::hash::Hash`][0] for details
///
/// [0]: https://doc.rust-lang.org/core/hash/trait.Hash.html
pub trait Hash {
    /// Feeds this value into the given `Hasher`.
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher;

    /// Feeds a slice of this type into the given `Hasher`.
    fn hash_slice<H>(data: &[Self], state: &mut H)
    where
        H: Hasher,
        Self: Sized,
    {
        for piece in data {
            piece.hash(state);
        }
    }
}

macro_rules! int {
    ($ty:ident) => {
        impl Hash for $ty {
            fn hash<H>(&self, state: &mut H)
            where
                H: Hasher,
            {
                unsafe { state.write(&mem::transmute::<$ty, [u8; mem::size_of::<$ty>()]>(*self)) }
            }

            fn hash_slice<H>(data: &[Self], state: &mut H)
            where
                H: Hasher,
            {
                let newlen = data.len() * mem::size_of::<$ty>();
                let ptr = data.as_ptr() as *const u8;
                unsafe { state.write(slice::from_raw_parts(ptr, newlen)) }
            }
        }
    };
}

int!(i16);
int!(i32);
int!(i64);
int!(i8);
int!(isize);
int!(u16);
int!(u32);
int!(u64);
int!(u8);
int!(usize);

impl Hash for bool {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        (*self as u8).hash(state)
    }
}

impl Hash for char {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        (*self as u32).hash(state)
    }
}

impl Hash for str {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        state.write(self.as_bytes());
        state.write(&[0xff]);
    }
}

impl<T> Hash for [T]
where
    T: Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.len().hash(state);
        T::hash_slice(self, state);
    }
}

macro_rules! array {
    ($($n:expr),+) => {
        $(
            impl<T> Hash for [T; $n]
                where
                T: Hash,
            {
                fn hash<H>(&self, state: &mut H)
                    where
                    H: Hasher,
                {
                    Hash::hash(&self[..], state)
                }
            }
        )+
    };
}

array!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32
);

impl<'a, T: ?Sized + Hash> Hash for &'a T {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<'a, T: ?Sized + Hash> Hash for &'a mut T {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl Hash for () {
    fn hash<H: Hasher>(&self, _state: &mut H) {}
}

macro_rules! tuple {
    ( $($name:ident)+) => (
        impl<$($name: Hash),*> Hash for ($($name,)*)
            where
            last_type!($($name,)+): ?Sized
        {
            #[allow(non_snake_case)]
            fn hash<S: Hasher>(&self, state: &mut S) {
                let ($(ref $name,)*) = *self;
                $($name.hash(state);)*
            }
        }
    );
}

macro_rules! last_type {
    ($a:ident,) => { $a };
    ($a:ident, $($rest_a:ident,)+) => { last_type!($($rest_a,)+) };
}

tuple! { A }
tuple! { A B }
tuple! { A B C }
tuple! { A B C D }
tuple! { A B C D E }
tuple! { A B C D E F }
tuple! { A B C D E F G }
tuple! { A B C D E F G H }
tuple! { A B C D E F G H I }
tuple! { A B C D E F G H I J }
tuple! { A B C D E F G H I J K }
tuple! { A B C D E F G H I J K L }

#[cfg(test)]
mod test {
    use super::{Hash, Hasher, FnvHasher};
    #[test]
    fn hashes_tuples() {
        let mut h = FnvHasher::default();
        ().hash(&mut h);
        (1_usize,).hash(&mut h);
        (1_u8, 2_i8).hash(&mut h);
        (1_u16, 2_i16, 3_u32).hash(&mut h);
        (1_i32, 2_u64, 3_i64, true).hash(&mut h);
        (1_isize, 'a', "abc", [1u32, 2, 3, 4], false).hash(&mut h);
        h.finish();
    }
}
