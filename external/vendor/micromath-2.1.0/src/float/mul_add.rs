//! Fused multiply-add. Computes `(self * a) + b`

use super::F32;

impl F32 {
    /// Computes `(self * a) + b`.
    pub fn mul_add(self, a: Self, b: Self) -> Self {
        self * a + b
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        assert_eq!(F32(0.0).mul_add(F32(0.0), F32(1.0)), F32(1.0));
        assert_eq!(F32(1.0).mul_add(F32(2.0), F32(3.5)), F32(5.5));
        assert_eq!(F32(1.0).mul_add(F32(-1.0), F32(0.0)), F32(-1.0));
    }
}
