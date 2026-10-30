//! Compute the absolute value of a single-precision float.
//!
//! Method described at: <https://bits.stephan-brumme.com/absFloat.html>

use super::{F32, SIGN_MASK};

impl F32 {
    /// Computes the absolute value of `self`.
    ///
    /// Returns [`Self::NAN`] if the number is [`Self::NAN`].
    pub fn abs(self) -> Self {
        Self::from_bits(self.to_bits() & !SIGN_MASK)
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        assert_eq!(F32::ONE.abs(), 1.0);
        assert_eq!(F32::ZERO.abs(), 0.0);
        assert_eq!(F32(-1.0).abs(), 1.0);
    }

    #[test]
    fn nan() {
        assert!(F32::NAN.abs().is_nan());
    }
}
