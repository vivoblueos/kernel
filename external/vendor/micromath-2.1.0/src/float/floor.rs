//! Floating point floor approximation for a single-precision float.

use super::F32;

impl F32 {
    /// Returns the largest integer less than or equal to a number.
    pub fn floor(self) -> Self {
        let mut res = (self.0 as i32) as f32;

        if self.0 < res {
            res -= 1.0;
        }

        Self(res)
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        assert_eq!(F32(-1.1).floor().0, -2.0);
        assert_eq!(F32(-0.1).floor().0, -1.0);
        assert_eq!(F32(0.0).floor().0, 0.0);
        assert_eq!(F32(1.0).floor().0, 1.0);
        assert_eq!(F32(1.1).floor().0, 1.0);
        assert_eq!(F32(2.9).floor().0, 2.0);
    }
}
