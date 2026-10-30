macro_rules! set_common_methods {
    ($T:ty, $T_Repr:ty, $oper_Self:ty) => {
        /// Returns a set containing a single element.
        #[inline(always)]
        pub fn only(t: T) -> Self {
            let mut set = Self::new();
            set.insert(t);
            set
        }

        /// Returns the bit a given enum variant is stored in.
        ///
        /// If this returns `n`, it means the bit is stored in the `n + 1`th least significant bit
        /// of the underlying integer, corresponding to a mask of `1 << n`.
        pub fn bit_index(t: T) -> u32 {
            T::enum_into_u32(t)
        }

        /// Returns whether a given bit is valid for this set.
        pub fn is_bit_valid(bit: u32) -> bool {
            T::ALL_BITS.has_bit(bit)
        }

        /// Returns the number of elements in this set.
        #[inline(always)]
        pub fn len(&self) -> usize {
            self.repr.count_ones() as usize
        }
        /// Returns `true` if the set contains no elements.
        #[inline(always)]
        pub fn is_empty(&self) -> bool {
            self.repr.is_empty()
        }
        /// Removes all elements from the set.
        #[inline(always)]
        pub fn clear(&mut self) {
            self.repr = <$T_Repr>::EMPTY;
        }

        /// Checks whether this set contains a value.
        #[inline(always)]
        pub fn contains(&self, value: $T) -> bool {
            self.repr.has_bit(value.enum_into_u32())
        }

        /// Adds a value to this set.
        ///
        /// If the set did not have this value present, `true` is returned.
        ///
        /// If the set did have this value present, `false` is returned.
        #[inline(always)]
        pub fn insert(&mut self, value: $T) -> bool {
            let bit_value = value.enum_into_u32();
            let contains = self.repr.has_bit(bit_value);
            self.repr.add_bit(bit_value);
            !contains
        }
        /// Removes a value from this set. Returns whether the value was present in the set.
        #[inline(always)]
        pub fn remove(&mut self, value: $T) -> bool {
            let bit_value = value.enum_into_u32();
            let contains = self.repr.has_bit(bit_value);
            self.repr.remove_bit(bit_value);
            contains
        }

        /// Returns `true` if `self` has no elements in common with `other`. This is equivalent to
        /// checking for an empty intersection.
        #[inline(always)]
        pub fn is_disjoint(&self, other: $oper_Self) -> bool {
            let other: Self = other.into();
            (*self & other).is_empty()
        }
        /// Returns `true` if the set is a superset of another, i.e., `self` contains at least all the
        /// values in `other`.
        #[inline(always)]
        pub fn is_superset(&self, other: $oper_Self) -> bool {
            let other: Self = other.into();
            (*self & other).repr == other.repr
        }
        /// Returns `true` if the set is a subset of another, i.e., `other` contains at least all
        /// the values in `self`.
        #[inline(always)]
        pub fn is_subset(&self, other: $oper_Self) -> bool {
            let other: Self = other.into();
            other.is_superset(*self)
        }

        /// Returns a set containing any elements present in either set.
        #[inline(always)]
        pub fn union(&self, other: $oper_Self) -> Self {
            let other: Self = other.into();
            Self { repr: self.repr | other.repr }
        }
        /// Returns a set containing every element present in both sets.
        #[inline(always)]
        pub fn intersection(&self, other: $oper_Self) -> Self {
            let other: Self = other.into();
            Self { repr: self.repr & other.repr }
        }
        /// Returns a set containing every element present in `self` but not in `other`.
        #[inline(always)]
        pub fn difference(&self, other: $oper_Self) -> Self {
            let other: Self = other.into();
            Self { repr: self.repr.and_not(other.repr) }
        }

        /// Returns a set containing every element present in either `self` or `other`, but not
        /// present in both.
        #[inline(always)]
        pub fn symmetric_difference(&self, other: $oper_Self) -> Self {
            let other: Self = other.into();
            Self { repr: self.repr ^ other.repr }
        }

        /// Returns a set containing every element present in either `self` or `other`, but not
        /// present in both.
        ///
        /// This is a legacy name for this function, and should not be used.
        #[inline(always)]
        #[deprecated(since = "1.1.13", note = "use symmetric_difference instead")]
        pub fn symmetrical_difference(&self, other: $oper_Self) -> Self {
            self.symmetric_difference(other)
        }
    };
}

macro_rules! set_common_impls {
    ($name:ident, $set_trait:ident) => {
        impl<T: $set_trait> Default for $name<T> {
            /// Returns an empty set.
            fn default() -> Self {
                Self::new()
            }
        }

        impl<T: $set_trait, O: Into<$name<T>>> Sub<O> for $name<T> {
            type Output = Self;
            #[inline(always)]
            fn sub(self, other: O) -> Self::Output {
                self.difference(other.into())
            }
        }
        impl<T: $set_trait, O: Into<$name<T>>> BitAnd<O> for $name<T> {
            type Output = Self;
            #[inline(always)]
            fn bitand(self, other: O) -> Self::Output {
                self.intersection(other.into())
            }
        }
        impl<T: $set_trait, O: Into<$name<T>>> BitOr<O> for $name<T> {
            type Output = Self;
            #[inline(always)]
            fn bitor(self, other: O) -> Self::Output {
                self.union(other.into())
            }
        }
        impl<T: $set_trait, O: Into<$name<T>>> BitXor<O> for $name<T> {
            type Output = Self;
            #[inline(always)]
            fn bitxor(self, other: O) -> Self::Output {
                self.symmetric_difference(other.into())
            }
        }

        impl<T: $set_trait, O: Into<$name<T>>> SubAssign<O> for $name<T> {
            #[inline(always)]
            fn sub_assign(&mut self, rhs: O) {
                *self = *self - rhs;
            }
        }
        impl<T: $set_trait, O: Into<$name<T>>> BitAndAssign<O> for $name<T> {
            #[inline(always)]
            fn bitand_assign(&mut self, rhs: O) {
                *self = *self & rhs;
            }
        }
        impl<T: $set_trait, O: Into<$name<T>>> BitOrAssign<O> for $name<T> {
            #[inline(always)]
            fn bitor_assign(&mut self, rhs: O) {
                *self = *self | rhs;
            }
        }
        impl<T: $set_trait, O: Into<$name<T>>> BitXorAssign<O> for $name<T> {
            #[inline(always)]
            fn bitxor_assign(&mut self, rhs: O) {
                *self = *self ^ rhs;
            }
        }

        impl<T: $set_trait> Not for $name<T> {
            type Output = Self;
            #[inline(always)]
            fn not(self) -> Self::Output {
                self.complement()
            }
        }

        impl<T: $set_trait> From<T> for $name<T> {
            fn from(t: T) -> Self {
                $name::only(t)
            }
        }

        impl<T: $set_trait> PartialEq<T> for $name<T> {
            fn eq(&self, other: &T) -> bool {
                self.repr == $name::only(*other).repr
            }
        }

        #[allow(clippy::derived_hash_with_manual_eq)] // This impl exists to change trait bounds only.
        impl<T: $set_trait> Hash for $name<T> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.repr.hash(state)
            }
        }
        #[allow(clippy::non_canonical_partial_ord_impl)]
        impl<T: $set_trait> PartialOrd for $name<T> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.repr.partial_cmp(&other.repr)
            }
        }
        impl<T: $set_trait> Ord for $name<T> {
            fn cmp(&self, other: &Self) -> Ordering {
                self.repr.cmp(&other.repr)
            }
        }

        impl<T: $set_trait + Debug> Debug for $name<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                // Note: We don't use `.debug_struct` to avoid splitting lines when using `{:x}`
                f.write_str(concat!(stringify!($name), "("))?;
                let mut i = self.iter();
                if let Some(v) = i.next() {
                    Debug::fmt(&v, f)?;
                    for v in i {
                        f.write_str(" | ")?;
                        Debug::fmt(&v, f)?;
                    }
                }
                f.write_str(")")?;
                Ok(())
            }
        }

        impl<T: $set_trait + Display> Display for $name<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                let mut i = self.iter();
                if let Some(v) = i.next() {
                    Display::fmt(&v, f)?;
                    for v in i {
                        f.write_str(" | ")?;
                        Display::fmt(&v, f)?;
                    }
                }
                Ok(())
            }
        }
    };
}

macro_rules! set_iterator_impls {
    ($name:ident, $set_trait:ident) => {
        impl<T: $set_trait> Extend<T> for $name<T> {
            fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
                iter.into_iter().for_each(|v| {
                    self.insert(v);
                });
            }
        }

        impl<'a, T: $set_trait> Extend<&'a T> for $name<T> {
            fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
                iter.into_iter().for_each(|v| {
                    self.insert(*v);
                });
            }
        }

        impl<T: $set_trait> FromIterator<T> for $name<T> {
            fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
                let mut set = $name::default();
                set.extend(iter);
                set
            }
        }

        impl<'a, T: 'a + $set_trait> FromIterator<&'a T> for $name<T> {
            fn from_iter<I: IntoIterator<Item = &'a T>>(iter: I) -> Self {
                let mut set = $name::default();
                set.extend(iter);
                set
            }
        }

        impl<T: $set_trait> Extend<$name<T>> for $name<T> {
            fn extend<I: IntoIterator<Item = $name<T>>>(&mut self, iter: I) {
                iter.into_iter().for_each(|v| {
                    self.insert_all(v);
                });
            }
        }

        impl<'a, T: $set_trait> Extend<&'a $name<T>> for $name<T> {
            fn extend<I: IntoIterator<Item = &'a $name<T>>>(&mut self, iter: I) {
                iter.into_iter().for_each(|v| {
                    self.insert_all(*v);
                });
            }
        }

        impl<T: $set_trait> FromIterator<$name<T>> for $name<T> {
            fn from_iter<I: IntoIterator<Item = $name<T>>>(iter: I) -> Self {
                let mut set = $name::default();
                set.extend(iter);
                set
            }
        }

        impl<'a, T: 'a + $set_trait> FromIterator<&'a $name<T>> for $name<T> {
            fn from_iter<I: IntoIterator<Item = &'a $name<T>>>(iter: I) -> Self {
                let mut set = $name::default();
                set.extend(iter);
                set
            }
        }

        impl<T: $set_trait> Sum for $name<T> {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold($name::empty(), |a, v| a | v)
            }
        }
        impl<'a, T: $set_trait> Sum<&'a $name<T>> for $name<T> {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold($name::empty(), |a, v| a | *v)
            }
        }
        impl<T: $set_trait> Sum<T> for $name<T> {
            fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
                iter.fold($name::empty(), |a, v| a | v)
            }
        }
        impl<'a, T: $set_trait> Sum<&'a T> for $name<T> {
            fn sum<I: Iterator<Item = &'a T>>(iter: I) -> Self {
                iter.fold($name::empty(), |a, v| a | *v)
            }
        }
    };
}
