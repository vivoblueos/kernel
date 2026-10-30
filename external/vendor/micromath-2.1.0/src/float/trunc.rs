//! Floating point whole number for a single-precision float.

use super::{F32, MANTISSA_MASK};

impl F32 {
    /// Returns the integer part of a number.
    pub fn trunc(self) -> Self {
        let x_bits = self.to_bits();
        let exponent = self.extract_exponent_value();

        // exponent is negative, there is no whole number, just return zero
        if exponent < 0 {
            return F32::ZERO.copysign(self);
        }

        let exponent_clamped = i32::max(exponent, 0) as u32;

        // find the part of the fraction that would be left over
        let fractional_part = x_bits.overflowing_shl(exponent_clamped).0 & MANTISSA_MASK;

        // if there isn't a fraction we can just return the whole thing.
        if fractional_part == 0_u32 {
            return self;
        }

        let fractional_mask = fractional_part.overflowing_shr(exponent_clamped).0;

        Self::from_bits(x_bits & !fractional_mask)
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        assert_eq!(F32(-1.1).trunc(), F32(-1.0));
        assert_eq!(F32(-0.1).trunc(), F32(-0.0));
        assert_eq!(F32(0.0).trunc(), F32(0.0));
        assert_eq!(F32(1.0).trunc(), F32(1.0));
        assert_eq!(F32(1.1).trunc(), F32(1.0));
        assert_eq!(F32(2.9).trunc(), F32(2.0));

        assert_eq!(F32(-100_000_000.13425345345).trunc(), F32(-100_000_000.0));
        assert_eq!(F32(100_000_000.13425345345).trunc(), F32(100_000_000.0));
    }
}
