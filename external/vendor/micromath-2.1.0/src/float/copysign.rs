//! Copy the sign over from another number.

use super::{F32, SIGN_MASK};

impl F32 {
    /// Returns a number composed of the magnitude of `self` and the sign of
    /// `sign`.
    pub fn copysign(self, sign: Self) -> Self {
        let source_bits = sign.to_bits();
        let source_sign = source_bits & SIGN_MASK;
        let signless_destination_bits = self.to_bits() & !SIGN_MASK;
        Self::from_bits(signless_destination_bits | source_sign)
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        assert_eq!(F32(1.0).copysign(F32(-1.0)).0, -1.0);
        assert_eq!(F32(-1.0).copysign(F32(1.0)).0, 1.0);
        assert_eq!(F32(1.0).copysign(F32(1.0)).0, 1.0);
        assert_eq!(F32(-1.0).copysign(F32(-1.0)).0, -1.0);

        let large_float = F32(100_000_000.13425345345);
        assert_eq!(large_float.copysign(-large_float), -large_float);
        assert_eq!((-large_float).copysign(large_float), large_float);
        assert_eq!(large_float.copysign(large_float), large_float);
        assert_eq!((-large_float).copysign(-large_float), -large_float);
    }
}
