use crate::repr::EnumSetTypeRepr;
use crate::traits::{EnumSetType, EnumSetTypePrivate};
use crate::{EnumSet, EnumSetTypeWithRepr};
use core::cmp::Ordering;
use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::Sum;
use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Used to return potentially invalid variants of a [`MixedEnumSet`].
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum MixedValue<T: EnumSetType> {
    /// A bit that is valid for the enum type.
    Valid(T),
    /// A bit that does not correspond to any variant of the enum.
    Invalid(u32),
}
impl<T: EnumSetType> MixedValue<T> {
    fn from_bit(b: u32) -> MixedValue<T> {
        if T::ALL_BITS.has_bit(b) {
            unsafe { MixedValue::Valid(T::enum_from_u32(b)) }
        } else {
            MixedValue::Invalid(b)
        }
    }
}
impl<T: EnumSetType> Debug for MixedValue<T>
where T: Debug
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            MixedValue::Valid(v) => v.fmt(f),
            MixedValue::Invalid(b) => write!(f, "[{b}]"),
        }
    }
}
impl<T: EnumSetType> Display for MixedValue<T>
where T: Display
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            MixedValue::Valid(v) => v.fmt(f),
            MixedValue::Invalid(b) => write!(f, "[{b}]"),
        }
    }
}
#[cfg(feature = "defmt")]
impl<T: EnumSetType + defmt::Format> defmt::Format for MixedValue<T> {
    fn format(&self, f: defmt::Formatter) {
        match self {
            MixedValue::Valid(v) => defmt::write!(f, "{}", v),
            MixedValue::Invalid(b) => defmt::write!(f, "[{}]", b),
        }
    }
}

/// A variant of [`EnumSet`] that preserves unknown bits.
///
/// It only works for enums with an
/// [`#[enumset(repr = "…")]`](derive@crate::EnumSetType#representation-options) attribute used
/// with a primitive integer type.
///
/// # Numeric Representation
///
/// `MixedEnumSet` uses the same underlying
/// [`numeric representation`](EnumSet#numeric-representation) as `EnumSet`. However, bits that do
/// not correspond to an enum variant can be set.
///
/// # Serialization
///
/// When the `serde` feature is enabled, `MixedEnumSet`s can be serialized and deserialized using
/// the `serde` crate. It is always serialized as a single integer of the underlying repr type.
///
/// Unlike `EnumSet`, it ignores all flags given to [`EnumSetType`](derive@crate::EnumSetType).
///
/// # FFI Safety
///
/// `MixedEnumSet` may be used interchangeably with the specified repr type in FFI.
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct MixedEnumSet<T: EnumSetTypeWithRepr> {
    pub(crate) repr: <T as EnumSetTypePrivate>::Repr,
}

//region MixedEnumSet operations
impl<T: EnumSetTypeWithRepr> MixedEnumSet<T> {
    const EMPTY_REPR: Self = MixedEnumSet { repr: <T as EnumSetTypePrivate>::Repr::EMPTY };
    const ALL_REPR: Self = MixedEnumSet { repr: T::ALL_BITS };

    /// Creates an empty `MixedEnumSet`.
    #[inline(always)]
    pub const fn new() -> Self {
        Self::EMPTY_REPR
    }

    /// Creates an empty `MixedEnumSet`.
    ///
    /// This is an alias for [`MixedEnumSet::new`].
    #[inline(always)]
    pub const fn empty() -> Self {
        Self::EMPTY_REPR
    }

    /// Returns a `MixedEnumSet` containing all valid variants of the enum.
    #[inline(always)]
    pub const fn all() -> Self {
        Self::ALL_REPR
    }

    /// The number of valid variants that this type can contain.
    #[inline(always)]
    pub const fn variant_count() -> u32 {
        T::VARIANT_COUNT
    }

    set_common_methods!(T, <T as EnumSetTypePrivate>::Repr, impl Into<Self>);

    /// Returns a set containing all enum variants not in this set.
    ///
    /// This method clears any unknown bits already existing in the set.
    #[inline(always)]
    pub fn complement(&self) -> Self {
        Self { repr: !self.repr & T::ALL_BITS }
    }

    /// Returns a set containing all bits not in this set.
    ///
    /// This method sets any unknown bits not already existing in the set.
    #[inline(always)]
    pub fn full_complement(&self) -> Self {
        Self { repr: !self.repr }
    }

    /// Returns the number of elements in this set, excluding unknown bits.
    #[inline(always)]
    pub fn valid_len(&self) -> usize {
        (self.repr & T::ALL_BITS).count_ones() as usize
    }

    /// Returns whether this bitset contains any bits that do not correspond to a valid variant.
    #[inline(always)]
    pub fn has_unknown_bits(&self) -> bool {
        !(self.repr & !T::ALL_BITS).is_empty()
    }

    /// Checks whether this set contains a specific bit.
    #[inline(always)]
    pub fn has_bit(&self, value: u32) -> bool {
        self.repr.has_bit(value)
    }

    /// Adds a specific bit to this set.
    ///
    /// If the set did not have this bit present, `true` is returned.
    ///
    /// If the set did have this bit present, `false` is returned.
    #[inline(always)]
    pub fn insert_bit(&mut self, value: u32) -> bool {
        let contains = !self.has_bit(value);
        self.repr.add_bit(value);
        contains
    }

    /// Removes a specific bit from this set. Returns whether the bit was present in the set.
    #[inline(always)]
    pub fn remove_bit(&mut self, value: u32) -> bool {
        let contains = self.has_bit(value);
        self.repr.remove_bit(value);
        contains
    }

    /// Adds all elements in another set to this one.
    #[inline(always)]
    pub fn insert_all(&mut self, other: impl Into<Self>) {
        self.repr = self.repr | other.into().repr
    }

    /// Removes all values in another set from this one.
    #[inline(always)]
    pub fn remove_all(&mut self, other: impl Into<Self>) {
        self.repr = self.repr.and_not(other.into().repr);
    }
}

set_common_impls!(MixedEnumSet, EnumSetTypeWithRepr);

impl<T: EnumSetTypeWithRepr> PartialEq<MixedEnumSet<T>> for EnumSet<T> {
    fn eq(&self, other: &MixedEnumSet<T>) -> bool {
        self.repr == other.repr
    }
}
impl<T: EnumSetTypeWithRepr> PartialEq<EnumSet<T>> for MixedEnumSet<T> {
    fn eq(&self, other: &EnumSet<T>) -> bool {
        self.repr == other.repr
    }
}

#[cfg(feature = "defmt")]
impl<T: EnumSetTypeWithRepr + defmt::Format> defmt::Format for MixedEnumSet<T> {
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
impl<T: EnumSetTypeWithRepr> Serialize for MixedEnumSet<T>
where <T as EnumSetTypeWithRepr>::Repr: Serialize
{
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.repr.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: EnumSetTypeWithRepr> Deserialize<'de> for MixedEnumSet<T>
where <T as EnumSetTypeWithRepr>::Repr: Deserialize<'de>
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        <T as EnumSetTypeWithRepr>::Repr::deserialize(deserializer).map(|x| Self { repr: x })
    }
}
//endregion

//region MixedEnumSet conversions
impl<T: EnumSetTypeWithRepr> MixedEnumSet<T> {
    /// Returns a `T::Repr` representing the elements of this set.
    ///
    /// Unlike the other `as_*` methods, this method is zero-cost and guaranteed not to fail,
    /// panic or truncate any bits.
    #[inline(always)]
    pub const fn as_repr(&self) -> <T as EnumSetTypeWithRepr>::Repr {
        self.repr
    }

    /// Constructs a bitset from a `T::Repr`.
    #[inline(always)]
    pub fn from_repr(bits: <T as EnumSetTypeWithRepr>::Repr) -> Self {
        Self { repr: bits }
    }

    /// Constructs a bitset from a `T::Repr`, ignoring invalid variants.
    #[inline(always)]
    pub fn from_repr_truncated(bits: <T as EnumSetTypeWithRepr>::Repr) -> Self {
        let mask = Self::all().as_repr();
        let bits = bits & mask;
        MixedEnumSet { repr: bits }
    }

    /// Converts this set into the corresponding [`EnumSet`].
    ///
    /// If any unknown bits are present in the set, this method will panic.
    pub fn as_enumset(&self) -> EnumSet<T> {
        self.try_as_enumset()
            .expect("Bitset contains invalid variants.")
    }

    /// Attempts to convert this set into the corresponding [`EnumSet`].
    ///
    /// If any unknown bits are present in the set, this method will return `None`.
    pub fn try_as_enumset(&self) -> Option<EnumSet<T>> {
        if self.has_unknown_bits() {
            None
        } else {
            Some(EnumSet { repr: self.repr })
        }
    }

    /// Converts this set into the corresponding [`EnumSet`], ignoring bits that do not correspond
    /// to a variant.
    pub fn as_enumset_truncate(&self) -> EnumSet<T> {
        EnumSet { repr: self.repr & T::ALL_BITS }
    }
}

impl<T: EnumSetTypeWithRepr, const N: usize> From<[T; N]> for MixedEnumSet<T> {
    fn from(value: [T; N]) -> Self {
        let mut new = MixedEnumSet::new();
        for elem in value {
            new.insert(elem);
        }
        new
    }
}

impl<T: EnumSetTypeWithRepr> From<EnumSet<T>> for MixedEnumSet<T> {
    fn from(value: EnumSet<T>) -> Self {
        MixedEnumSet { repr: value.repr }
    }
}
//endregion

//region EnumSet iter
/// The iterator used by [`MixedEnumSet`]s.
#[derive(Clone, Debug)]
pub struct MixedEnumSetIter<T: EnumSetType> {
    iter: <T::Repr as EnumSetTypeRepr>::Iter,
}
impl<T: EnumSetTypeWithRepr> MixedEnumSetIter<T> {
    fn new(set: MixedEnumSet<T>) -> MixedEnumSetIter<T> {
        MixedEnumSetIter { iter: set.repr.iter() }
    }
}

impl<T: EnumSetTypeWithRepr> MixedEnumSet<T> {
    /// Iterates the contents of the set in order from the least significant bit to the most
    /// significant bit.
    ///
    /// Note that iterator invalidation is impossible as the iterator contains a copy of this type,
    /// rather than holding a reference to it.
    pub fn iter(&self) -> MixedEnumSetIter<T> {
        MixedEnumSetIter::new(*self)
    }
}

impl<T: EnumSetTypeWithRepr> Iterator for MixedEnumSetIter<T> {
    type Item = MixedValue<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|x| MixedValue::from_bit(x))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
impl<T: EnumSetTypeWithRepr> DoubleEndedIterator for MixedEnumSetIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|x| MixedValue::from_bit(x))
    }
}
impl<T: EnumSetTypeWithRepr> ExactSizeIterator for MixedEnumSetIter<T> {}

set_iterator_impls!(MixedEnumSet, EnumSetTypeWithRepr);

impl<T: EnumSetTypeWithRepr> IntoIterator for MixedEnumSet<T> {
    type Item = MixedValue<T>;
    type IntoIter = MixedEnumSetIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: EnumSetTypeWithRepr> Extend<EnumSet<T>> for MixedEnumSet<T> {
    fn extend<I: IntoIterator<Item = EnumSet<T>>>(&mut self, iter: I) {
        iter.into_iter().for_each(|v| {
            self.insert_all(v);
        });
    }
}

impl<'a, T: EnumSetTypeWithRepr> Extend<&'a EnumSet<T>> for MixedEnumSet<T> {
    fn extend<I: IntoIterator<Item = &'a EnumSet<T>>>(&mut self, iter: I) {
        iter.into_iter().for_each(|v| {
            self.insert_all(*v);
        });
    }
}

impl<T: EnumSetTypeWithRepr> FromIterator<EnumSet<T>> for MixedEnumSet<T> {
    fn from_iter<I: IntoIterator<Item = EnumSet<T>>>(iter: I) -> Self {
        let mut set = MixedEnumSet::default();
        set.extend(iter);
        set
    }
}

impl<'a, T: 'a + EnumSetTypeWithRepr> FromIterator<&'a EnumSet<T>> for MixedEnumSet<T> {
    fn from_iter<I: IntoIterator<Item = &'a EnumSet<T>>>(iter: I) -> Self {
        let mut set = MixedEnumSet::default();
        set.extend(iter);
        set
    }
}

impl<'a, T: EnumSetTypeWithRepr> Sum<EnumSet<T>> for MixedEnumSet<T> {
    fn sum<I: Iterator<Item = EnumSet<T>>>(iter: I) -> Self {
        iter.fold(MixedEnumSet::empty(), |a, v| a | v)
    }
}

impl<'a, T: EnumSetTypeWithRepr> Sum<&'a EnumSet<T>> for MixedEnumSet<T> {
    fn sum<I: Iterator<Item = &'a EnumSet<T>>>(iter: I) -> Self {
        iter.fold(MixedEnumSet::empty(), |a, v| a | *v)
    }
}
//endregion
