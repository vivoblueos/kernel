//! Provides [`BinInteger`], a trait for types like `u8` and `u32`.
#![allow(unstable_name_collisions)] // `$ty::BITS`
use core::{fmt, marker, ops};

/// Integral types with efficient binary operations.
pub trait BinInteger:
    Clone
    + Copy
    + PartialEq
    + Eq
    + Ord
    + PartialOrd
    + marker::Unpin
    + ops::Add<Output = Self>
    + ops::Sub<Output = Self>
    + ops::Mul<Output = Self>
    + ops::Div<Output = Self>
    + ops::Rem<Output = Self>
    + Sized
    + ops::AddAssign
    + ops::SubAssign
    + ops::MulAssign
    + ops::DivAssign
    + ops::RemAssign
    + fmt::Debug
    + Send
    + Sync
    + 'static
    + private::Sealed
{
    const ZERO: Self;
    const BITS: u32;

    fn ones(range: ops::Range<u32>) -> Self;

    fn ones_truncated(range: ops::Range<u32>) -> Self;

    /// Return the number of trailing zeros in its binary representation.
    fn trailing_zeros(&self) -> u32;

    /// Return the number of leading zeros in its binary representation.
    fn leading_zeros(&self) -> u32;

    /// Return the number of ones in its binary representation.
    fn count_ones(&self) -> u32;

    /// Return the position of the least significant set bit since the position
    /// `start`.
    ///
    /// Retruns `Self::BITS` if none was found.
    fn bit_scan_forward(&self, start: u32) -> u32;

    /// Slice a part of its binary representation as `u32`.
    fn extract_u32(&self, range: ops::Range<u32>) -> u32;

    /// Retrieve whether the specified bit is set or not.
    fn get_bit(&self, i: u32) -> bool;

    /// Set a single bit.
    fn set_bit(&mut self, i: u32);

    /// Clear a single bit.
    fn clear_bit(&mut self, i: u32);

    /// Perform `ceil` treating the value as a fixed point number with `fp`
    /// fractional part digits.
    fn checked_ceil_fix(self, fp: u32) -> Option<Self>;
}

macro_rules! impl_binary_integer {
    ($type:ty) => {
        impl private::Sealed for $type {}

        impl BinInteger for $type {
            const ZERO: Self = 0;
            const BITS: u32 = core::mem::size_of::<$type>() as u32 * 8;

            #[inline]
            fn ones(range: ops::Range<u32>) -> Self {
                assert!(range.end <= Self::BITS);
                Self::ones_truncated(range)
            }
            #[inline]
            fn ones_truncated(range: ops::Range<u32>) -> Self {
                assert!(range.start <= range.end);
                if range.end >= Self::BITS {
                    (0 as Self).wrapping_sub(1 << range.start)
                } else {
                    ((1 as Self) << range.end).wrapping_sub(1 << range.start)
                }
            }
            #[inline]
            fn trailing_zeros(&self) -> u32 {
                (*self).trailing_zeros()
            }
            #[inline]
            fn leading_zeros(&self) -> u32 {
                (*self).leading_zeros()
            }
            #[inline]
            fn count_ones(&self) -> u32 {
                (*self).count_ones()
            }
            #[inline]
            fn bit_scan_forward(&self, start: u32) -> u32 {
                if start >= Self::BITS {
                    Self::BITS
                } else {
                    (*self & !Self::ones(0..start)).trailing_zeros()
                }
            }
            #[inline]
            fn extract_u32(&self, range: ops::Range<u32>) -> u32 {
                let start = range.start;
                ((self & Self::ones_truncated(range)) >> start) as u32
            }
            #[inline]
            fn get_bit(&self, i: u32) -> bool {
                if i < Self::BITS {
                    self & ((1 as Self) << i) != 0
                } else {
                    false
                }
            }
            #[inline]
            fn set_bit(&mut self, i: u32) {
                if i < Self::BITS {
                    *self |= (1 as Self) << i;
                }
            }
            #[inline]
            fn clear_bit(&mut self, i: u32) {
                if i < Self::BITS {
                    *self &= !((1 as Self) << i);
                }
            }
            #[inline]
            fn checked_ceil_fix(self, fp: u32) -> Option<Self> {
                if fp >= Self::BITS {
                    if self == 0 {
                        Some(0)
                    } else {
                        None
                    }
                } else {
                    let mask = Self::ones(0..fp);
                    self.checked_add(mask).map(|x| x & !mask)
                }
            }
        }
    };
}

impl_binary_integer!(i8);
impl_binary_integer!(i16);
impl_binary_integer!(i32);
impl_binary_integer!(i64);
impl_binary_integer!(i128);
impl_binary_integer!(isize);

impl_binary_integer!(u8);
impl_binary_integer!(u16);
impl_binary_integer!(u32);
impl_binary_integer!(u64);
impl_binary_integer!(u128);
impl_binary_integer!(usize);

/// Implements [the sealed trait pattern], which protects [`BinInteger`] against
/// downstream implementations.
///
/// [the sealed trait pattern]: https://rust-lang.github.io/api-guidelines/future-proofing.html
mod private {
    pub trait Sealed {}
}
