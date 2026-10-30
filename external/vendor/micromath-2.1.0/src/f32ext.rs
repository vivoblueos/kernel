//! `f32` extension

use crate::float::F32;

/// `f32` extension providing various arithmetic approximations and polyfills
/// for `std` functionality.
pub trait F32Ext: Sized {
    /// Compute absolute value with a constant-time, data-independent
    /// implementation.
    fn abs(self) -> f32;

    /// Approximates `acos(x)` in radians in the range `[0, pi]`
    fn acos(self) -> f32;

    /// Approximates `asin(x)` in radians in the range `[-pi/2, pi/2]`.
    fn asin(self) -> f32;

    /// Approximates `atan(x)` in radians with a maximum error of `0.002`.
    fn atan(self) -> f32;

    /// Approximates `atan(x)` normalized to the `[−1,1]` range with a maximum
    /// error of `0.1620` degrees.
    fn atan_norm(self) -> f32;

    /// Approximates the four quadrant arctangent `atan2(x)` in radians, with
    /// a maximum error of `0.002`.
    fn atan2(self, other: f32) -> f32;

    /// Approximates the four quadrant arctangent.
    /// Normalized to the `[0,4)` range with a maximum error of `0.1620` degrees.
    fn atan2_norm(self, other: f32) -> f32;

    /// Approximates floating point ceiling.
    fn ceil(self) -> f32;

    /// Copies the sign from one number to another and returns it.
    fn copysign(self, sign: f32) -> f32;

    /// Approximates cosine in radians with a maximum error of `0.002`.
    fn cos(self) -> f32;

    /// Calculates Euclidean division, the matching method for `rem_euclid`.
    fn div_euclid(self, other: f32) -> f32;

    /// Approximates `e^x`.
    fn exp(self) -> f32;

    /// Approximates floating point floor.
    fn floor(self) -> f32;

    /// Retrieve the fractional part of floating point with sign.
    fn fract(self) -> f32;

    /// Approximates the length of the hypotenuse of a right-angle triangle given
    /// legs of length `x` and `y`.
    fn hypot(self, other: f32) -> f32;

    /// Approximates `1/x` with an average deviation of ~8%.
    fn inv(self) -> f32;

    /// Approximates inverse square root with an average deviation of ~5%.
    fn invsqrt(self) -> f32;

    /// Approximates `ln(x)`.
    fn ln(self) -> f32;

    /// Approximates `log` with an arbitrary base.
    fn log(self, base: f32) -> f32;

    /// Approximates `log2`.
    fn log2(self) -> f32;

    /// Approximates `log10`.
    fn log10(self) -> f32;

    /// Computes `(self * a) + b`.
    fn mul_add(self, a: f32, b: f32) -> f32;

    /// Approximates `self^n`.
    fn powf(self, n: f32) -> f32;

    /// Approximates `self^n` where n is an `i32`
    fn powi(self, n: i32) -> f32;

    /// Returns the reciprocal (inverse) of a number, `1/x`.
    fn recip(self) -> f32;

    /// Calculates the least nonnegative remainder of `self (mod other)`.
    fn rem_euclid(self, other: f32) -> f32;

    /// Round the number part of floating point with sign.
    fn round(self) -> f32;

    /// Returns a number that represents the sign of `self`.
    fn signum(self) -> f32;

    /// Approximates sine in radians with a maximum error of `0.002`.
    fn sin(self) -> f32;

    /// Simultaneously computes the sine and cosine of the number, `x`.
    /// Returns `(sin(x), cos(x))`.
    fn sin_cos(self) -> (f32, f32);

    /// Approximates square root with an average deviation of ~5%.
    fn sqrt(self) -> f32;

    /// Approximates `tan(x)` in radians with a maximum error of `0.6`.
    fn tan(self) -> f32;

    /// Retrieve whole number part of floating point with sign.
    fn trunc(self) -> f32;
}

impl F32Ext for f32 {
    #[inline]
    fn abs(self) -> f32 {
        F32(self).abs().0
    }

    #[inline]
    fn acos(self) -> f32 {
        F32(self).acos().0
    }

    #[inline]
    fn asin(self) -> f32 {
        F32(self).asin().0
    }

    #[inline]
    fn atan(self) -> f32 {
        F32(self).atan().0
    }

    #[inline]
    fn atan_norm(self) -> f32 {
        F32(self).atan_norm().0
    }

    #[inline]
    fn atan2(self, other: f32) -> f32 {
        F32(self).atan2(F32(other)).0
    }

    #[inline]
    fn atan2_norm(self, other: f32) -> f32 {
        F32(self).atan2_norm(F32(other)).0
    }

    #[inline]
    fn ceil(self) -> f32 {
        F32(self).ceil().0
    }

    #[inline]
    fn copysign(self, sign: f32) -> f32 {
        F32(self).copysign(F32(sign)).0
    }

    #[inline]
    fn cos(self) -> f32 {
        F32(self).cos().0
    }

    #[inline]
    fn div_euclid(self, other: f32) -> f32 {
        F32(self).div_euclid(F32(other)).0
    }

    #[inline]
    fn exp(self) -> f32 {
        F32(self).exp().0
    }

    #[inline]
    fn floor(self) -> f32 {
        F32(self).floor().0
    }

    #[inline]
    fn fract(self) -> f32 {
        F32(self).fract().0
    }

    #[inline]
    fn hypot(self, other: f32) -> f32 {
        F32(self).hypot(other.into()).0
    }

    #[inline]
    fn inv(self) -> f32 {
        F32(self).inv().0
    }

    #[inline]
    fn invsqrt(self) -> f32 {
        F32(self).invsqrt().0
    }

    #[inline]
    fn ln(self) -> f32 {
        F32(self).ln().0
    }

    #[inline]
    fn log(self, base: f32) -> f32 {
        F32(self).log(F32(base)).0
    }

    #[inline]
    fn log2(self) -> f32 {
        F32(self).log2().0
    }

    #[inline]
    fn log10(self) -> f32 {
        F32(self).log10().0
    }

    #[inline]
    fn mul_add(self, a: f32, b: f32) -> f32 {
        F32(self).mul_add(F32(a), F32(b)).0
    }

    #[inline]
    fn powf(self, n: f32) -> f32 {
        F32(self).powf(F32(n)).0
    }

    #[inline]
    fn powi(self, n: i32) -> f32 {
        F32(self).powi(n).0
    }

    #[inline]
    fn recip(self) -> f32 {
        F32(self).recip().0
    }

    #[inline]
    fn rem_euclid(self, other: f32) -> f32 {
        F32(self).rem_euclid(F32(other)).0
    }

    #[inline]
    fn round(self) -> f32 {
        F32(self).round().0
    }

    #[inline]
    fn signum(self) -> f32 {
        F32(self).signum().0
    }

    #[inline]
    fn sin(self) -> f32 {
        F32(self).sin().0
    }

    #[inline]
    fn sin_cos(self) -> (f32, f32) {
        (F32(self).sin().0, F32(self).cos().0)
    }

    #[inline]
    fn sqrt(self) -> f32 {
        F32(self).sqrt().0
    }

    #[inline]
    fn tan(self) -> f32 {
        F32(self).tan().0
    }

    #[inline]
    fn trunc(self) -> f32 {
        F32(self).trunc().0
    }
}
