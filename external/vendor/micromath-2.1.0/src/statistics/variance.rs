use super::mean::Mean;

/// Statistical variance
pub trait Variance {
    /// Result type
    type Result;

    /// Compute the statistical variance
    fn variance(self) -> Self::Result;
}

impl<T> Variance for &[T]
where
    T: Copy + Into<f32>,
{
    /// Result type
    type Result = f32;

    fn variance(self) -> f32 {
        let mean = self.iter().map(|n| (*n).into()).mean();
        let mut sum = 0.0;

        for item in self {
            let n = (*item).into() - mean;
            sum += n * n;
        }

        sum / (self.len() as f32 - 1.0)
    }
}

#[cfg(test)]
mod tests {
    use super::Variance;

    #[test]
    fn variance_test() {
        assert_eq!([1.0, 3.0, 5.0].as_ref().variance(), 4.0);
    }
}
