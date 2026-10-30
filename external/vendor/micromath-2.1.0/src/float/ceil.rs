//! Floating point ceiling approximation for a single-precision float.

use super::F32;

impl F32 {
    /// Returns the smallest integer greater than or equal to a number.
    pub fn ceil(self) -> Self {
        -(-self).floor()
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        assert_eq!(F32(-1.1).ceil().0, -1.0);
        assert_eq!(F32(-0.1).ceil().0, 0.0);
        assert_eq!(F32(0.0).ceil().0, 0.0);
        assert_eq!(F32(1.0).ceil().0, 1.0);
        assert_eq!(F32(1.1).ceil().0, 2.0);
        assert_eq!(F32(2.9).ceil().0, 3.0);
    }
}
