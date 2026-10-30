//! Calculate length of the hypotenuse of a right triangle.

use super::F32;

impl F32 {
    /// Calculate the length of the hypotenuse of a right-angle triangle.
    pub fn hypot(self, rhs: Self) -> Self {
        (self * self + rhs * rhs).sqrt()
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        let x = F32(3.0);
        let y = F32(4.0);
        let difference = x.hypot(y) - F32(25.0).sqrt();
        assert!(difference.abs() <= F32::EPSILON);
    }
}
