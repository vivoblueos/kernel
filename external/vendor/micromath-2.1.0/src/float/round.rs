//! Round a single-precision float.

use super::F32;

impl F32 {
    /// Returns the nearest integer to a number.
    pub fn round(self) -> Self {
        Self(((self.0 + Self(0.5).copysign(self).0) as i32) as f32)
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        assert_eq!(F32(0.0).round(), F32(0.0));
        assert_eq!(F32(-0.0).round(), F32(-0.0));

        assert_eq!(F32(0.49999).round(), F32(0.0));
        assert_eq!(F32(-0.49999).round(), F32(-0.0));

        assert_eq!(F32(0.5).round(), F32(1.0));
        assert_eq!(F32(-0.5).round(), F32(-1.0));

        assert_eq!(F32(9999.499).round(), F32(9999.0));
        assert_eq!(F32(-9999.499).round(), F32(-9999.0));

        assert_eq!(F32(9999.5).round(), F32(10000.0));
        assert_eq!(F32(-9999.5).round(), F32(-10000.0));
    }
}
