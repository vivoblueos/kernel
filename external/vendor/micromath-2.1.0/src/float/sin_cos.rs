//! Simultaneously computes the sine and cosine of the number, `x`.

use super::F32;

impl F32 {
    /// Simultaneously computes the sine and cosine of the number, `x`.
    /// Returns `(sin(x), cos(x))`.
    pub fn sin_cos(self) -> (Self, Self) {
        (self.sin(), self.cos())
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    const TEST_VECTORS: &[f32] = &[
        0.000, 0.140, 0.279, 0.419, 0.559, 0.698, 0.838, 0.977, 1.117, 1.257, 1.396, 1.536, 1.676,
        1.815, 1.955, 2.094, 2.234, 2.374, 2.513, 2.653, 2.793, 2.932, 3.072, 3.211, 3.351, 3.491,
        3.630, 3.770, 3.910, 4.049, 4.189, 4.328, 4.468, 4.608, 4.747, 4.887, 5.027, 5.166, 5.306,
        5.445, 5.585, 5.725, 5.864, 6.004, 6.144, 6.283,
    ];

    #[test]
    fn sanity_check() {
        for &x in TEST_VECTORS {
            let sin_x = F32(x).sin();
            let cos_x = F32(x).cos();

            assert_eq!(F32(x).sin_cos(), (sin_x, cos_x));
        }
    }
}
