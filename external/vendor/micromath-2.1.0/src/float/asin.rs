//! arcsin approximation for a single-precision float.
//!
//! Method described at:
//! <https://dsp.stackexchange.com/questions/25770/looking-for-an-arcsin-algorithm>

use super::F32;

impl F32 {
    /// Computes `asin(x)` approximation in radians in the range `[-pi/2, pi/2]`.
    pub fn asin(self) -> Self {
        (self * (Self::ONE - self * self).invsqrt()).atan()
    }
}

#[cfg(test)]
mod tests {
    use super::F32;
    use core::f32::consts::FRAC_PI_2;

    #[test]
    fn sanity_check() {
        let difference = F32(FRAC_PI_2).sin().asin() - FRAC_PI_2;
        assert!(difference.abs() <= F32::EPSILON);
    }
}
