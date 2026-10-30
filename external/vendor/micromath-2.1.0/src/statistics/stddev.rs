use super::variance::Variance;
#[allow(unused_imports)]
use crate::F32Ext;

/// Compute standard deviation
pub trait StdDev {
    /// Result type
    type Result;

    /// Compute standard deviation
    fn stddev(self) -> Self::Result;
}

impl<T> StdDev for &[T]
where
    T: Copy + Into<f32>,
{
    /// Result type
    type Result = f32;

    fn stddev(self) -> f32 {
        self.variance().sqrt()
    }
}

#[cfg(test)]
mod tests {
    use super::StdDev;

    #[test]
    fn stddev_test() {
        assert_eq!([1.0, 3.0, 5.0].as_ref().stddev(), 2.0);
        assert_eq!([1.0, 3.0, 5.0].as_ref().stddev(), 2.0);
    }
}
