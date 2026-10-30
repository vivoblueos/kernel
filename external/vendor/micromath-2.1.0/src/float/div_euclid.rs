//! Calculates Euclidian division for a single-precision float.

use super::F32;

impl F32 {
    /// Calculates Euclidean division, the matching method for `rem_euclid`.
    pub fn div_euclid(self, rhs: Self) -> Self {
        let q = (self / rhs).trunc();

        if self % rhs >= Self::ZERO {
            q
        } else if rhs > Self::ZERO {
            q - Self::ONE
        } else {
            q + Self::ONE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        let a = F32(7.0);
        let b = F32(4.0);

        assert_eq!(a.div_euclid(b), F32(1.0));
        assert_eq!((-a).div_euclid(b), F32(-2.0));
        assert_eq!(a.div_euclid(-b), F32(-1.0));
        assert_eq!((-a).div_euclid(-b), F32(2.0));
    }
}
