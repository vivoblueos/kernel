//! Floating point operations

pub(crate) mod abs;
pub(crate) mod acos;
pub(crate) mod asin;
pub(crate) mod atan;
pub(crate) mod atan2;
pub(crate) mod ceil;
pub(crate) mod copysign;
pub(crate) mod cos;
pub(crate) mod div_euclid;
pub(crate) mod exp;
pub(crate) mod floor;
pub(crate) mod fract;
pub(crate) mod hypot;
pub(crate) mod inv;
pub(crate) mod invsqrt;
pub(crate) mod ln;
pub(crate) mod log;
pub(crate) mod log10;
pub(crate) mod log2;
pub(crate) mod mul_add;
pub(crate) mod powf;
pub(crate) mod powi;
pub(crate) mod recip;
pub(crate) mod rem_euclid;
pub(crate) mod round;
pub(crate) mod signum;
pub(crate) mod sin;
pub(crate) mod sin_cos;
pub(crate) mod sqrt;
pub(crate) mod tan;
pub(crate) mod trunc;

use core::{
    cmp::Ordering,
    fmt::{self, Display, LowerExp, UpperExp},
    iter::{Product, Sum},
    num::ParseFloatError,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
    str::FromStr,
};

#[cfg(feature = "num-traits")]
use num_traits::{Inv, Num, One, Zero};

/// Sign mask.
pub(crate) const SIGN_MASK: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;

/// Exponent mask.
pub(crate) const EXPONENT_MASK: u32 = 0b0111_1111_1000_0000_0000_0000_0000_0000;

/// Mantissa mask.
pub(crate) const MANTISSA_MASK: u32 = 0b0000_0000_0111_1111_1111_1111_1111_1111;

/// Exponent mask.
pub(crate) const EXPONENT_BIAS: u32 = 127;

/// Mantissa bits.
///
/// Note: `MANTISSA_DIGITS` is available in `core::f32`, but the actual bits taken up are 24 - 1.
pub(crate) const MANTISSA_BITS: u32 = 23;

/// 32-bit floating point wrapper which implements fast approximation-based
/// operations.
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd)]
pub struct F32(pub f32);

impl F32 {
    /// The value `0.0`.
    pub const ZERO: Self = Self(0.0);

    /// The value `1.0`.
    pub const ONE: Self = Self(1.0);

    /// The radix or base of the internal representation of `f32`.
    pub const RADIX: u32 = f32::RADIX;

    /// Number of significant digits in base 2.
    pub const MANTISSA_DIGITS: u32 = f32::MANTISSA_DIGITS;

    /// Approximate number of significant digits in base 10.
    pub const DIGITS: u32 = f32::DIGITS;

    /// [Machine epsilon] value for `f32`.
    ///
    /// This is the difference between `1.0` and the next larger representable number.
    ///
    /// [Machine epsilon]: https://en.wikipedia.org/wiki/Machine_epsilon
    pub const EPSILON: Self = Self(f32::EPSILON);

    /// Smallest finite `f32` value.
    pub const MIN: Self = Self(f32::MIN);

    /// Smallest positive normal `f32` value.
    pub const MIN_POSITIVE: Self = Self(f32::MIN_POSITIVE);

    /// Largest finite `f32` value.
    pub const MAX: Self = Self(f32::MAX);

    /// One greater than the minimum possible normal power of 2 exponent.
    pub const MIN_EXP: i32 = f32::MIN_EXP;

    /// Maximum possible power of 2 exponent.
    pub const MAX_EXP: i32 = f32::MAX_EXP;

    /// Minimum possible normal power of 10 exponent.
    pub const MIN_10_EXP: i32 = f32::MIN_10_EXP;

    /// Maximum possible power of 10 exponent.
    pub const MAX_10_EXP: i32 = f32::MAX_10_EXP;

    /// Not a Number (NaN).
    pub const NAN: Self = Self(f32::NAN);

    /// Infinity (∞).
    pub const INFINITY: Self = Self(f32::INFINITY);

    /// Negative infinity (−∞).
    pub const NEG_INFINITY: Self = Self(f32::NEG_INFINITY);

    /// Returns `true` if this value is `NaN`.
    #[inline]
    pub fn is_nan(self) -> bool {
        self.0.is_nan()
    }

    /// Returns `true` if this value is positive infinity or negative infinity, and
    /// `false` otherwise.
    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite()
    }

    /// Returns `true` if this number is neither infinite nor `NaN`.
    #[inline]
    pub fn is_finite(self) -> bool {
        self.0.is_finite()
    }

    /// Returns `true` if `self` has a positive sign, including `+0.0`, `NaN`s with
    /// positive sign bit and positive infinity.
    #[inline]
    pub fn is_sign_positive(self) -> bool {
        self.0.is_sign_positive()
    }

    /// Returns `true` if `self` has a negative sign, including `-0.0`, `NaN`s with
    /// negative sign bit and negative infinity.
    #[inline]
    pub fn is_sign_negative(self) -> bool {
        self.0.is_sign_negative()
    }

    /// Raw transmutation to `u32`.
    ///
    /// This is currently identical to `transmute::<f32, u32>(self)` on all platforms.
    ///
    /// See [`F32::from_bits`] for some discussion of the portability of this operation
    /// (there are almost no issues).
    #[inline]
    pub fn to_bits(self) -> u32 {
        self.0.to_bits()
    }

    /// Raw transmutation from `u32`.
    ///
    /// This is currently identical to `transmute::<u32, f32>(v)` on all platforms.
    /// It turns out this is incredibly portable, for two reasons:
    ///
    /// - Floats and Ints have the same endianness on all supported platforms.
    /// - IEEE-754 very precisely specifies the bit layout of floats.
    ///
    /// See [`f32::from_bits`] for more information.
    #[inline]
    pub fn from_bits(v: u32) -> Self {
        Self(f32::from_bits(v))
    }

    /// Extract exponent bits.
    pub(crate) fn extract_exponent_bits(self) -> u32 {
        (self.to_bits() & EXPONENT_MASK)
            .overflowing_shr(MANTISSA_BITS)
            .0
    }

    /// Extract the exponent of a float's value.
    pub(crate) fn extract_exponent_value(self) -> i32 {
        (self.extract_exponent_bits() as i32) - EXPONENT_BIAS as i32
    }

    /// Remove sign.
    pub(crate) fn without_sign(self) -> Self {
        Self::from_bits(self.to_bits() & !SIGN_MASK)
    }

    /// Set the exponent to the given value.
    pub(crate) fn set_exponent(self, exponent: i32) -> Self {
        debug_assert!(exponent <= 127 && exponent >= -128);
        let without_exponent: u32 = self.to_bits() & !EXPONENT_MASK;
        let only_exponent: u32 = ((exponent + EXPONENT_BIAS as i32) as u32)
            .overflowing_shl(MANTISSA_BITS)
            .0;

        Self::from_bits(without_exponent | only_exponent)
    }

    /// Is this floating point value equivalent to an integer?
    pub(crate) fn is_integer(&self) -> bool {
        let exponent = self.extract_exponent_value();
        let self_bits = self.to_bits();

        // if exponent is negative we shouldn't remove anything, this stops an opposite shift.
        let exponent_clamped = i32::max(exponent, 0) as u32;

        // find the part of the fraction that would be left over
        let fractional_part = (self_bits).overflowing_shl(exponent_clamped).0 & MANTISSA_MASK;

        // if fractional part contains anything, we know it *isn't* an integer.
        // if zero there will be nothing in the fractional part
        // if it is whole, there will be nothing in the fractional part
        fractional_part == 0
    }

    /// Is this floating point value even?
    fn is_even(&self) -> bool {
        // any floating point value that doesn't fit in an i32 range is even,
        // and will loose 1's digit precision at exp values of 23+
        if self.extract_exponent_value() >= 31 {
            true
        } else {
            (self.0 as i32) % 2 == 0
        }
    }
}

impl Add for F32 {
    type Output = F32;

    #[inline]
    fn add(self, rhs: F32) -> F32 {
        F32(self.0 + rhs.0)
    }
}

impl Add<f32> for F32 {
    type Output = F32;

    #[inline]
    fn add(self, rhs: f32) -> F32 {
        F32(self.0 + rhs)
    }
}

impl Add<F32> for f32 {
    type Output = F32;

    #[inline]
    fn add(self, rhs: F32) -> F32 {
        F32(self + rhs.0)
    }
}

impl AddAssign for F32 {
    #[inline]
    fn add_assign(&mut self, rhs: F32) {
        self.0 += rhs.0;
    }
}

impl AddAssign<f32> for F32 {
    #[inline]
    fn add_assign(&mut self, rhs: f32) {
        self.0 += rhs;
    }
}

impl AddAssign<F32> for f32 {
    #[inline]
    fn add_assign(&mut self, rhs: F32) {
        *self += rhs.0;
    }
}

impl Display for F32 {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.0)
    }
}

impl Div for F32 {
    type Output = F32;

    #[inline]
    fn div(self, rhs: F32) -> F32 {
        F32(self.0 / rhs.0)
    }
}

impl Div<f32> for F32 {
    type Output = F32;

    #[inline]
    fn div(self, rhs: f32) -> F32 {
        F32(self.0 / rhs)
    }
}

impl Div<F32> for f32 {
    type Output = F32;

    #[inline]
    fn div(self, rhs: F32) -> F32 {
        F32(self / rhs.0)
    }
}

impl DivAssign for F32 {
    #[inline]
    fn div_assign(&mut self, rhs: F32) {
        self.0 /= rhs.0;
    }
}

impl DivAssign<f32> for F32 {
    #[inline]
    fn div_assign(&mut self, rhs: f32) {
        self.0 /= rhs;
    }
}

impl DivAssign<F32> for f32 {
    #[inline]
    fn div_assign(&mut self, rhs: F32) {
        *self /= rhs.0;
    }
}

impl From<f32> for F32 {
    #[inline]
    fn from(n: f32) -> F32 {
        F32(n)
    }
}

impl From<F32> for f32 {
    #[inline]
    fn from(n: F32) -> f32 {
        n.0
    }
}

impl From<i8> for F32 {
    #[inline]
    fn from(n: i8) -> F32 {
        F32(n.into())
    }
}

impl From<i16> for F32 {
    #[inline]
    fn from(n: i16) -> F32 {
        F32(n.into())
    }
}

impl From<u8> for F32 {
    #[inline]
    fn from(n: u8) -> F32 {
        F32(n.into())
    }
}

impl From<u16> for F32 {
    #[inline]
    fn from(n: u16) -> F32 {
        F32(n.into())
    }
}

impl FromStr for F32 {
    type Err = ParseFloatError;

    #[inline]
    fn from_str(src: &str) -> Result<F32, ParseFloatError> {
        f32::from_str(src).map(F32)
    }
}

impl LowerExp for F32 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:e}", self.0)
    }
}

impl Mul for F32 {
    type Output = F32;

    #[inline]
    fn mul(self, rhs: F32) -> F32 {
        F32(self.0 * rhs.0)
    }
}

impl Mul<f32> for F32 {
    type Output = F32;

    #[inline]
    fn mul(self, rhs: f32) -> F32 {
        F32(self.0 * rhs)
    }
}

impl Mul<F32> for f32 {
    type Output = F32;

    #[inline]
    fn mul(self, rhs: F32) -> F32 {
        F32(self * rhs.0)
    }
}

impl MulAssign for F32 {
    #[inline]
    fn mul_assign(&mut self, rhs: F32) {
        self.0 *= rhs.0;
    }
}

impl MulAssign<f32> for F32 {
    #[inline]
    fn mul_assign(&mut self, rhs: f32) {
        self.0 *= rhs;
    }
}

impl MulAssign<F32> for f32 {
    #[inline]
    fn mul_assign(&mut self, rhs: F32) {
        *self *= rhs.0;
    }
}

impl Neg for F32 {
    type Output = F32;

    #[inline]
    fn neg(self) -> F32 {
        F32(-self.0)
    }
}

impl PartialEq<f32> for F32 {
    fn eq(&self, other: &f32) -> bool {
        self.0.eq(other)
    }
}

impl PartialEq<F32> for f32 {
    fn eq(&self, other: &F32) -> bool {
        self.eq(&other.0)
    }
}

impl PartialOrd<f32> for F32 {
    fn partial_cmp(&self, other: &f32) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }
}

impl PartialOrd<F32> for f32 {
    fn partial_cmp(&self, other: &F32) -> Option<Ordering> {
        self.partial_cmp(&other.0)
    }
}

impl Product for F32 {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = F32>,
    {
        F32(f32::product(iter.map(f32::from)))
    }
}

impl Rem for F32 {
    type Output = F32;

    #[inline]
    fn rem(self, rhs: F32) -> F32 {
        F32(self.0 % rhs.0)
    }
}

impl Rem<f32> for F32 {
    type Output = F32;

    #[inline]
    fn rem(self, rhs: f32) -> F32 {
        F32(self.0 % rhs)
    }
}

impl Rem<F32> for f32 {
    type Output = F32;

    #[inline]
    fn rem(self, rhs: F32) -> F32 {
        F32(self % rhs.0)
    }
}

impl RemAssign for F32 {
    #[inline]
    fn rem_assign(&mut self, rhs: F32) {
        self.0 %= rhs.0;
    }
}

impl RemAssign<f32> for F32 {
    #[inline]
    fn rem_assign(&mut self, rhs: f32) {
        self.0 %= rhs;
    }
}

impl Sub for F32 {
    type Output = F32;

    #[inline]
    fn sub(self, rhs: F32) -> F32 {
        F32(self.0 - rhs.0)
    }
}

impl Sub<f32> for F32 {
    type Output = F32;

    #[inline]
    fn sub(self, rhs: f32) -> F32 {
        F32(self.0 - rhs)
    }
}

impl Sub<F32> for f32 {
    type Output = F32;

    #[inline]
    fn sub(self, rhs: F32) -> F32 {
        F32(self - rhs.0)
    }
}

impl SubAssign for F32 {
    #[inline]
    fn sub_assign(&mut self, rhs: F32) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<f32> for F32 {
    #[inline]
    fn sub_assign(&mut self, rhs: f32) {
        self.0 -= rhs;
    }
}

impl SubAssign<F32> for f32 {
    #[inline]
    fn sub_assign(&mut self, rhs: F32) {
        *self -= rhs.0;
    }
}

impl Sum for F32 {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = F32>,
    {
        F32(f32::sum(iter.map(f32::from)))
    }
}

impl UpperExp for F32 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:E}", self.0)
    }
}

#[cfg(feature = "num-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "num-traits")))]
impl Zero for F32 {
    fn zero() -> Self {
        Self::ZERO
    }

    fn is_zero(&self) -> bool {
        Self::ZERO == *self
    }
}

#[cfg(feature = "num-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "num-traits")))]
impl One for F32 {
    fn one() -> Self {
        Self::ONE
    }

    fn is_one(&self) -> bool {
        Self::ONE == *self
    }
}

#[cfg(feature = "num-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "num-traits")))]
impl Num for F32 {
    type FromStrRadixErr = num_traits::ParseFloatError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        f32::from_str_radix(str, radix).map(Self)
    }
}

#[cfg(feature = "num-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "num-traits")))]
impl Inv for F32 {
    type Output = Self;

    fn inv(self) -> Self {
        self.inv()
    }
}

#[cfg(test)]
mod tests {
    #[allow(unused_imports)] // remove when we have more tests
    use super::F32;

    #[cfg(feature = "num-traits")]
    #[test]
    fn inv_trait() {
        assert_eq!(num_traits::Inv::inv(F32(2.0)), F32(0.5));
    }
}
