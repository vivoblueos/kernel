//! Returns a number that represents the sign of `self`.

use super::F32;

impl F32 {
    /// Returns a number that represents the sign of `self`.
    ///
    /// * `1.0` if the number is positive, `+0.0` or `INFINITY`
    /// * `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
    /// * `NAN` if the number is `NAN`
    pub fn signum(self) -> Self {
        if self.is_nan() {
            Self::NAN
        } else {
            F32(1.0).copysign(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        assert_eq!(F32::INFINITY.signum(), F32(1.0));
        assert_eq!(F32(0.0).signum(), F32(1.0));
        assert_eq!(F32(1.0).signum(), F32(1.0));
        assert_eq!(F32::NEG_INFINITY.signum(), F32(-1.0));
        assert_eq!(F32(-0.0).signum(), F32(-1.0));
        assert_eq!(F32(-1.0).signum(), F32(-1.0));
    }
}
