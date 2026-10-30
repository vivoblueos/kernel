use crate::repr::EnumSetTypeRepr;
use crate::traits::{EnumSetConstHelper, EnumSetType};
use crate::EnumSetTypeWithRepr;
use core::cmp::Ordering;
use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::Sum;
use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// An efficient set type for enums.
///
/// It is implemented using a bitset stored using the smallest integer that can fit all bits
/// in the underlying enum. In general, an enum variant with a discriminant of `n` is stored in
/// the `n + 1`th least significant bit (corresponding with a mask of, e.g. `1 << enum as u32`).
///
/// # Numeric Representation
///
/// `EnumSet` is internally implemented using integer types, and as such can be easily converted
/// from and to numbers.
///
/// Each bit of the underlying integer corresponds to at most one particular enum variant. If the
/// corresponding bit for a variant is set, it is present in the set. Bits that do not correspond
/// to any variant are always unset.
///
/// By default, each enum variant is stored in a bit corresponding to its discriminant. An enum
/// variant with a discriminant of `n` is stored in the `n + 1`th least significant bit
/// (corresponding to a mask of, e.g. `1 << enum as u32`).
///
/// The [`#[enumset(map = "…")]`](derive@crate::EnumSetType#mapping-options) attribute can be used
/// to control this mapping.
///
/// # Array Representation
///
/// Sets with 64 or more variants are instead stored with an underlying array of `u64`s. This is
/// treated as if it was a single large integer. The `n`th least significant bit of this integer
/// is stored in the `n % 64`th least significant bit of the `n / 64`th element in the array.
///
/// # Serialization
///
/// When the `serde` feature is enabled, `EnumSet`s can be serialized and deserialized using
/// the `serde` crate.
///
/// By default, `EnumSet` is serialized by directly writing out a single integer containing the
/// numeric representation of the bitset. The integer type used is the smallest one that can fit
/// the largest variant in the enum. If no integer type is large enough, instead the `EnumSet` is
/// serialized as an array of `u64`s containing the array representation. Unknown bits are ignored
/// and silently removed from the bitset when deserializing.
///
/// The exact serialization format can be controlled with additional attributes on the enum type.
/// For more information, see the documentation for
/// [Serialization Options](derive@crate::EnumSetType#serialization-options).
///
/// # FFI Safety
///
/// By default, there are no guarantees about the underlying representation of an `EnumSet`. To use
/// them safely across FFI boundaries, the
/// [`#[enumset(repr = "…")]`](derive@crate::EnumSetType#representation-options) attribute must be
/// used with a primitive integer type. For example:
///
/// ```
/// # use enumset::*;
/// #
/// # mod ffi_impl {
/// #     // This example “foreign” function is actually written in Rust, but for the sake
/// #     // of example, we'll pretend it's written in C.
/// #     #[no_mangle]
/// #     extern "C" fn some_foreign_function(set: u32) -> u32 {
/// #         set & 0b100
/// #     }
/// # }
/// #
/// extern "C" {
///     // This function is written in C like:
///     // uint32_t some_foreign_function(uint32_t set) { … }
///     fn some_foreign_function(set: EnumSet<MyEnum>) -> EnumSet<MyEnum>;
/// }
///
/// #[derive(Debug, EnumSetType)]
/// #[enumset(repr = "u32")]
/// enum MyEnum { A, B, C }
///
/// let set: EnumSet<MyEnum> = enum_set!(MyEnum::A | MyEnum::C);
///
/// let new_set: EnumSet<MyEnum> = unsafe { some_foreign_function(set) };
/// assert_eq!(new_set, enum_set!(MyEnum::C));
/// ```
///
/// When an `EnumSet<T>` is received via FFI, all bits that don't correspond to an enum variant
/// of `T` must be set to `0`. Behavior is **undefined** if any of these bits are set to `1`.
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct EnumSet<T: EnumSetType> {
    pub(crate) repr: T::Repr,
}

//region EnumSet operations
impl<T: EnumSetType> EnumSet<T> {
    const EMPTY_REPR: Self = EnumSet { repr: T::Repr::EMPTY };
    const ALL_REPR: Self = EnumSet { repr: T::ALL_BITS };

    /// Creates an empty `EnumSet`.
    #[inline(always)]
    pub const fn new() -> Self {
        Self::EMPTY_REPR
    }

    /// Creates an empty `EnumSet`.
    ///
    /// This is an alias for [`EnumSet::new`].
    #[inline(always)]
    pub const fn empty() -> Self {
        Self::EMPTY_REPR
    }

    /// Returns an `EnumSet` containing all valid variants of the enum.
    #[inline(always)]
    pub const fn all() -> Self {
        Self::ALL_REPR
    }

    /// Total number of bits used by this type. Note that the actual amount of space used is
    /// rounded up to the next highest integer type (`u8`, `u16`, `u32`, `u64`, or `u128`).
    ///
    /// This is the same as [`EnumSet::variant_count`] except in enums with "sparse" variants.
    /// (e.g. `enum Foo { A = 10, B = 20 }`)
    #[inline(always)]
    pub const fn bit_width() -> u32 {
        T::BIT_WIDTH
    }

    /// The number of valid variants that this type can contain.
    ///
    /// This is the same as [`EnumSet::bit_width`] except in enums with "sparse" variants.
    /// (e.g. `enum Foo { A = 10, B = 20 }`)
    #[inline(always)]
    pub const fn variant_count() -> u32 {
        T::VARIANT_COUNT
    }

    // SEMVER: On semver major change, make the other parameter into a `impl Into<>`
    set_common_methods!(T, T::Repr, Self);

    /// Returns a set containing all enum variants not in this set.
    #[inline(always)]
    pub fn complement(&self) -> Self {
        Self { repr: !self.repr & T::ALL_BITS }
    }

    /// Adds all elements in another set to this one.
    #[inline(always)]
    pub fn insert_all(&mut self, other: Self) {
        self.repr = self.repr | other.repr
    }

    /// Removes all values in another set from this one.
    #[inline(always)]
    pub fn remove_all(&mut self, other: Self) {
        self.repr = self.repr.and_not(other.repr);
    }
}

/// A helper type used for constant evaluation of enum operations.
#[doc(hidden)]
pub struct EnumSetInitHelper;
impl EnumSetInitHelper {
    /// Just returns this value - the version for the enums themselves would wrap it into an
    /// enumset.
    pub const fn const_only<T>(&self, value: T) -> T {
        value
    }
}

#[doc(hidden)]
unsafe impl<T: EnumSetType> EnumSetConstHelper for EnumSet<T> {
    type ConstInitHelper = EnumSetInitHelper;
    const CONST_INIT_HELPER: Self::ConstInitHelper = EnumSetInitHelper;

    type ConstOpHelper = T::ConstOpHelper;
    const CONST_OP_HELPER: Self::ConstOpHelper = T::CONST_OP_HELPER;
}

set_common_impls!(EnumSet, EnumSetType);

#[cfg(feature = "defmt")]
impl<T: EnumSetType + defmt::Format> defmt::Format for EnumSet<T> {
    fn format(&self, f: defmt::Formatter) {
        let mut i = self.iter();
        if let Some(v) = i.next() {
            defmt::write!(f, "{}", v);
            for v in i {
                defmt::write!(f, " | {}", v);
            }
        }
    }
}

#[cfg(feature = "serde")]
impl<T: EnumSetType> Serialize for EnumSet<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        T::serialize(*self, serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: EnumSetType> Deserialize<'de> for EnumSet<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        T::deserialize(deserializer)
    }
}
//endregion

//region Deprecated functions
/// This impl contains all outdated or deprecated functions.
impl<T: EnumSetType> EnumSet<T> {
    /// An empty `EnumSet`.
    ///
    /// This is deprecated because [`EnumSet::empty`] is now `const`.
    #[deprecated = "Use `EnumSet::empty()` instead."]
    pub const EMPTY: Self = Self::EMPTY_REPR;

    /// An `EnumSet` containing all valid variants of the enum.
    ///
    /// This is deprecated because [`EnumSet::all`] is now `const`.
    #[deprecated = "Use `EnumSet::all()` instead."]
    pub const ALL: Self = Self::ALL_REPR;
}
//endregion

//region EnumSet conversions
impl<T: EnumSetType + EnumSetTypeWithRepr> EnumSet<T> {
    /// Returns a `T::Repr` representing the elements of this set.
    ///
    /// Unlike the other `as_*` methods, this method is zero-cost and guaranteed not to fail,
    /// panic or truncate any bits.
    ///
    /// In order to use this method, the definition of `T` must have an
    /// [`#[enumset(repr = "…")]`](derive@crate::EnumSetType#representation-options) annotation
    /// with a primitive integer type.
    #[inline(always)]
    pub const fn as_repr(&self) -> <T as EnumSetTypeWithRepr>::Repr {
        self.repr
    }

    /// Constructs a bitset from a `T::Repr` without checking for invalid bits.
    ///
    /// Unlike the other `from_*` methods, this method is zero-cost and guaranteed not to fail,
    /// panic or truncate any bits, provided the conditions under “Safety” are upheld.
    ///
    /// In order to use this method, the definition of `T` must have an
    /// [`#[enumset(repr = "…")]`](derive@crate::EnumSetType#representation-options) annotation
    /// with a primitive integer type.
    ///
    /// # Safety
    ///
    /// All bits in the provided parameter `bits` that don't correspond to an enum variant of
    /// `T` must be set to `0`. Behavior is **undefined** if any of these bits are set to `1`.
    #[inline(always)]
    pub unsafe fn from_repr_unchecked(bits: <T as EnumSetTypeWithRepr>::Repr) -> Self {
        Self { repr: bits }
    }

    /// Constructs a bitset from a `T::Repr`.
    ///
    /// If a bit that doesn't correspond to an enum variant is set, this
    /// method will panic.
    ///
    /// In order to use this method, the definition of `T` must have an
    /// [`#[enumset(repr = "…")]`](derive@crate::EnumSetType#representation-options) annotation
    /// with a primitive integer type.
    #[inline(always)]
    pub fn from_repr(bits: <T as EnumSetTypeWithRepr>::Repr) -> Self {
        Self::try_from_repr(bits).expect("Bitset contains invalid variants.")
    }

    /// Attempts to construct a bitset from a `T::Repr`.
    ///
    /// If a bit that doesn't correspond to an enum variant is set, this
    /// method will return `None`.
    ///
    /// In order to use this method, the definition of `T` must have an
    /// [`#[enumset(repr = "…")]`](derive@crate::EnumSetType#representation-options) annotation
    /// with a primitive integer type.
    #[inline(always)]
    pub fn try_from_repr(bits: <T as EnumSetTypeWithRepr>::Repr) -> Option<Self> {
        let mask = Self::all().repr;
        if bits.and_not(mask).is_empty() {
            Some(EnumSet { repr: bits })
        } else {
            None
        }
    }

    /// Constructs a bitset from a `T::Repr`, ignoring invalid variants.
    ///
    /// In order to use this method, the definition of `T` must have an
    /// [`#[enumset(repr = "…")]`](derive@crate::EnumSetType#representation-options) annotation
    /// with a primitive integer type.
    #[inline(always)]
    pub fn from_repr_truncated(bits: <T as EnumSetTypeWithRepr>::Repr) -> Self {
        let mask = Self::all().as_repr();
        let bits = bits & mask;
        EnumSet { repr: bits }
    }
}

/// Helper macro for generating conversion functions.
macro_rules! conversion_impls {
    (
        $(for_num!(
            $underlying:ty, $underlying_str:expr,
            $from_fn:ident $to_fn:ident $try_from_fn:ident $try_to_fn:ident,
            $from:ident $try_from:ident $from_truncated:ident $from_unchecked:ident,
            $to:ident $try_to:ident $to_truncated:ident
        );)*
    ) => {
        impl<T: EnumSetType> EnumSet<T> {$(
            #[doc = "Returns a `"]
            #[doc = $underlying_str]
            #[doc = "` representing the elements of this set.\n\nIf the underlying bitset will \
                     not fit in a `"]
            #[doc = $underlying_str]
            #[doc = "`, this method will panic."]
            #[inline(always)]
            pub fn $to(&self) -> $underlying {
                self.$try_to().expect("Bitset will not fit into this type.")
            }

            #[doc = "Tries to return a `"]
            #[doc = $underlying_str]
            #[doc = "` representing the elements of this set.\n\nIf the underlying bitset will \
                     not fit in a `"]
            #[doc = $underlying_str]
            #[doc = "`, this method will return `None`."]
            #[inline(always)]
            pub fn $try_to(&self) -> Option<$underlying> {
                EnumSetTypeRepr::$try_to_fn(&self.repr)
            }

            #[doc = "Returns a truncated `"]
            #[doc = $underlying_str]
            #[doc = "` representing the elements of this set.\n\nIf the underlying bitset will \
                     not fit in a `"]
            #[doc = $underlying_str]
            #[doc = "`, this method will truncate any bits that don't fit."]
            #[inline(always)]
            pub fn $to_truncated(&self) -> $underlying {
                EnumSetTypeRepr::$to_fn(&self.repr)
            }

            #[doc = "Constructs a bitset from a `"]
            #[doc = $underlying_str]
            #[doc = "`.\n\nIf a bit that doesn't correspond to an enum variant is set, this \
                     method will panic."]
            #[inline(always)]
            pub fn $from(bits: $underlying) -> Self {
                Self::$try_from(bits).expect("Bitset contains invalid variants.")
            }

            #[doc = "Attempts to construct a bitset from a `"]
            #[doc = $underlying_str]
            #[doc = "`.\n\nIf a bit that doesn't correspond to an enum variant is set, this \
                     method will return `None`."]
            #[inline(always)]
            pub fn $try_from(bits: $underlying) -> Option<Self> {
                let bits = T::Repr::$try_from_fn(bits);
                let mask = T::ALL_BITS;
                bits.and_then(|bits| if bits.and_not(mask).is_empty() {
                    Some(EnumSet { repr: bits })
                } else {
                    None
                })
            }

            #[doc = "Constructs a bitset from a `"]
            #[doc = $underlying_str]
            #[doc = "`, ignoring bits that do not correspond to a variant."]
            #[inline(always)]
            pub fn $from_truncated(bits: $underlying) -> Self {
                let mask = Self::all().$to_truncated();
                let bits = <T::Repr as EnumSetTypeRepr>::$from_fn(bits & mask);
                EnumSet { repr: bits }
            }

            #[doc = "Constructs a bitset from a `"]
            #[doc = $underlying_str]
            #[doc = "`, without checking for invalid bits."]
            ///
            /// # Safety
            ///
            /// All bits in the provided parameter `bits` that don't correspond to an enum variant
            /// of `T` must be set to `0`. Behavior is **undefined** if any of these bits are set
            /// to `1`.
            #[inline(always)]
            pub unsafe fn $from_unchecked(bits: $underlying) -> Self {
                EnumSet { repr: <T::Repr as EnumSetTypeRepr>::$from_fn(bits) }
            }
        )*}
    }
}
conversion_impls! {
    for_num!(u8, "u8",
             from_u8 to_u8 try_from_u8 try_to_u8,
             from_u8 try_from_u8 from_u8_truncated from_u8_unchecked,
             as_u8 try_as_u8 as_u8_truncated);
    for_num!(u16, "u16",
             from_u16 to_u16 try_from_u16 try_to_u16,
             from_u16 try_from_u16 from_u16_truncated from_u16_unchecked,
             as_u16 try_as_u16 as_u16_truncated);
    for_num!(u32, "u32",
             from_u32 to_u32 try_from_u32 try_to_u32,
             from_u32 try_from_u32 from_u32_truncated from_u32_unchecked,
             as_u32 try_as_u32 as_u32_truncated);
    for_num!(u64, "u64",
             from_u64 to_u64 try_from_u64 try_to_u64,
             from_u64 try_from_u64 from_u64_truncated from_u64_unchecked,
             as_u64 try_as_u64 as_u64_truncated);
    for_num!(u128, "u128",
             from_u128 to_u128 try_from_u128 try_to_u128,
             from_u128 try_from_u128 from_u128_truncated from_u128_unchecked,
             as_u128 try_as_u128 as_u128_truncated);
    for_num!(usize, "usize",
             from_usize to_usize try_from_usize try_to_usize,
             from_usize try_from_usize from_usize_truncated from_usize_unchecked,
             as_usize try_as_usize as_usize_truncated);
}

impl<T: EnumSetType> EnumSet<T> {
    /// Returns a `[u64; O]` representing the elements of this set.
    ///
    /// If the underlying bitset will not fit in a `[u64; O]`, this method will panic.
    pub fn as_array<const O: usize>(&self) -> [u64; O] {
        self.try_as_array()
            .expect("Bitset will not fit into this type.")
    }

    /// Returns a `[u64; O]` representing the elements of this set.
    ///
    /// If the underlying bitset will not fit in a `[u64; O]`, this method will instead return
    /// `None`.
    pub fn try_as_array<const O: usize>(&self) -> Option<[u64; O]> {
        self.repr.try_to_u64_array()
    }

    /// Returns a `[u64; O]` representing the elements of this set.
    ///
    /// If the underlying bitset will not fit in a `[u64; O]`, this method will truncate any bits
    /// that don't fit.
    pub fn as_array_truncated<const O: usize>(&self) -> [u64; O] {
        self.repr.to_u64_array()
    }

    /// Constructs a bitset from a `[u64; O]`.
    ///
    /// If a bit that doesn't correspond to an enum variant is set, this method will panic.
    pub fn from_array<const O: usize>(v: [u64; O]) -> Self {
        Self::try_from_array(v).expect("Bitset contains invalid variants.")
    }

    /// Attempts to construct a bitset from a `[u64; O]`.
    ///
    /// If a bit that doesn't correspond to an enum variant is set, this method will return `None`.
    pub fn try_from_array<const O: usize>(bits: [u64; O]) -> Option<Self> {
        let bits = T::Repr::try_from_u64_array::<O>(bits);
        let mask = T::ALL_BITS;
        bits.and_then(|bits| {
            if bits.and_not(mask).is_empty() {
                Some(EnumSet { repr: bits })
            } else {
                None
            }
        })
    }

    /// Constructs a bitset from a `[u64; O]`, ignoring bits that do not correspond to a variant.
    pub fn from_array_truncated<const O: usize>(bits: [u64; O]) -> Self {
        let bits = T::Repr::from_u64_array(bits) & T::ALL_BITS;
        EnumSet { repr: bits }
    }

    /// Constructs a bitset from a `[u64; O]`, without checking for invalid bits.
    ///
    /// # Safety
    ///
    /// All bits in the provided parameter `bits` that don't correspond to an enum variant
    /// of `T` must be set to `0`. Behavior is **undefined** if any of these bits are set
    /// to `1`.
    #[inline(always)]
    pub unsafe fn from_array_unchecked<const O: usize>(bits: [u64; O]) -> Self {
        EnumSet { repr: T::Repr::from_u64_array(bits) }
    }

    /// Returns a `Vec<u64>` representing the elements of this set.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn to_vec(&self) -> alloc::vec::Vec<u64> {
        let mut vec = alloc::vec![0; T::Repr::PREFERRED_ARRAY_LEN];
        self.repr.to_u64_slice(&mut vec);
        vec
    }

    /// Copies the elements of this set into a `&mut [u64]`.
    ///
    /// If the underlying bitset will not fit in the provided slice, this method will panic.
    pub fn copy_into_slice(&self, data: &mut [u64]) {
        self.try_copy_into_slice(data)
            .expect("Bitset will not fit into slice.")
    }

    /// Copies the elements of this set into a `&mut [u64]`.
    ///
    /// If the underlying bitset will not fit in the provided slice, this method will return
    /// `None`. Otherwise, it will return `Some(())`.
    #[must_use]
    pub fn try_copy_into_slice(&self, data: &mut [u64]) -> Option<()> {
        self.repr.try_to_u64_slice(data)
    }

    /// Copies the elements of this set into a `&mut [u64]`.
    ///
    /// If the underlying bitset will not fit in the provided slice, this method will truncate any
    /// bits that don't fit.
    pub fn copy_into_slice_truncated(&self, data: &mut [u64]) {
        self.repr.to_u64_slice(data)
    }

    /// Constructs a bitset from a `&[u64]`.
    ///
    /// If a bit that doesn't correspond to an enum variant is set, this method will panic.
    pub fn from_slice(v: &[u64]) -> Self {
        Self::try_from_slice(v).expect("Bitset contains invalid variants.")
    }

    /// Attempts to construct a bitset from a `&[u64]`.
    ///
    /// If a bit that doesn't correspond to an enum variant is set, this method will return `None`.
    pub fn try_from_slice(bits: &[u64]) -> Option<Self> {
        let bits = T::Repr::try_from_u64_slice(bits);
        let mask = T::ALL_BITS;
        bits.and_then(|bits| {
            if bits.and_not(mask).is_empty() {
                Some(EnumSet { repr: bits })
            } else {
                None
            }
        })
    }

    /// Constructs a bitset from a `&[u64]`, ignoring bits that do not correspond to a variant.
    pub fn from_slice_truncated(bits: &[u64]) -> Self {
        let bits = T::Repr::from_u64_slice(bits) & T::ALL_BITS;
        EnumSet { repr: bits }
    }

    /// Constructs a bitset from a `&[u64]`, without checking for invalid bits.
    ///
    /// # Safety
    ///
    /// All bits in the provided parameter `bits` that don't correspond to an enum variant
    /// of `T` must be set to `0`. Behavior is **undefined** if any of these bits are set
    /// to `1`.
    #[inline(always)]
    pub unsafe fn from_slice_unchecked(bits: &[u64]) -> Self {
        EnumSet { repr: T::Repr::from_u64_slice(bits) }
    }
}

impl<T: EnumSetType, const N: usize> From<[T; N]> for EnumSet<T> {
    fn from(value: [T; N]) -> Self {
        let mut new = EnumSet::new();
        for elem in value {
            new.insert(elem);
        }
        new
    }
}
//endregion

//region EnumSet iter
/// The iterator used by [`EnumSet`]s.
#[derive(Clone, Debug)]
pub struct EnumSetIter<T: EnumSetType> {
    iter: <T::Repr as EnumSetTypeRepr>::Iter,
}
impl<T: EnumSetType> EnumSetIter<T> {
    fn new(set: EnumSet<T>) -> EnumSetIter<T> {
        EnumSetIter { iter: set.repr.iter() }
    }
}

impl<T: EnumSetType> EnumSet<T> {
    /// Iterates the contents of the set in order from the least significant bit to the most
    /// significant bit.
    ///
    /// Note that iterator invalidation is impossible as the iterator contains a copy of this type,
    /// rather than holding a reference to it.
    pub fn iter(&self) -> EnumSetIter<T> {
        EnumSetIter::new(*self)
    }
}

impl<T: EnumSetType> Iterator for EnumSetIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|x| unsafe { T::enum_from_u32_checked(x) })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
impl<T: EnumSetType> DoubleEndedIterator for EnumSetIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|x| unsafe { T::enum_from_u32_checked(x) })
    }
}
impl<T: EnumSetType> ExactSizeIterator for EnumSetIter<T> {}

set_iterator_impls!(EnumSet, EnumSetType);

impl<T: EnumSetType> IntoIterator for EnumSet<T> {
    type Item = T;
    type IntoIter = EnumSetIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
//endregion
