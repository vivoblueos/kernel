//! Calculate Euclidian remainder for a single-precision float.

use super::F32;

impl F32 {
    /// Calculates the least non-negative remainder of `self (mod rhs)`.
    pub fn rem_euclid(self, rhs: Self) -> Self {
        let r = self % rhs;

        if r >= Self::ZERO {
            r
        } else {
            r + rhs.abs()
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

        assert_eq!(a.rem_euclid(b), F32(3.0));
        assert_eq!((-a).rem_euclid(b), F32(1.0));
        assert_eq!(a.rem_euclid(-b), F32(3.0));
        assert_eq!((-a).rem_euclid(-b), F32(1.0));
    }
}
