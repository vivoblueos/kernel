//! Iterate over input slices after culling statistical outliers.

use super::mean::Mean;
#[allow(unused_imports)]
use crate::F32Ext;
use core::{iter, slice};

/// Default number of standard deviations at which a value should be
/// considered an outlier.
pub const DEFAULT_THRESHOLD: f32 = 2.0;

/// Iterate over the given input after culling outliers.
pub trait Trim {
    /// Result type
    type Result: Copy + Into<f32>;

    /// Trim this collection (cull outliers) at the default threshold of 2 standard
    /// deviations.
    fn trim(&self) -> Iter<'_, Self::Result> {
        self.trim_at(DEFAULT_THRESHOLD)
    }

    /// Trim this collection (cull outliers) at the specified number of standard deviations.
    fn trim_at(&self, threshold: f32) -> Iter<'_, Self::Result>;
}

impl<N> Trim for &[N]
where
    N: Copy,
    f32: From<N>,
{
    type Result = N;

    fn trim_at(&self, threshold: f32) -> Iter<'_, Self::Result> {
        Iter::new(self, threshold)
    }
}

/// A "trimmed" iterator which culls outliers at a given number of standard
/// deviations from the mean.
pub struct Iter<'a, N: Copy> {
    /// Iterator over the input values
    input: iter::Cloned<slice::Iter<'a, N>>,

    /// Arithmetic mean of the input values as a float
    mean: f32,

    /// Standard deviation of the input values
    stddev: f32,

    /// Number of standard deviations at which values are considered outliers
    threshold: f32,
}

impl<'a, N> Iter<'a, N>
where
    N: Copy,
    f32: From<N>,
{
    /// Create a new trimmed iterator over an input slice.
    ///
    /// Inputs will be considered outliers at the given `threshold` number
    /// of standard deviations (e.g. `2.0`).
    pub fn new(input: &'a [N], threshold: f32) -> Self {
        let len = input.len() as f32;
        let input = input.iter().cloned();
        let input_f32 = input.clone().map(f32::from);

        // TODO(tarcieri): eliminate duplication with mean/variance/stddev in super
        let mean = input_f32.clone().mean();
        let sum = input_f32.fold(0.0, |sum, n| {
            let n = n - mean;
            sum + n * n
        });
        let variance = sum / (len - 1.0);
        let stddev = variance.sqrt();

        Self {
            input,
            mean,
            stddev,
            threshold,
        }
    }
}

impl<'a, N> Iterator for Iter<'a, N>
where
    N: Copy,
    f32: From<N>,
{
    type Item = N;

    fn next(&mut self) -> Option<N> {
        while let Some(n) = self.input.next() {
            let distance = (f32::from(n) - self.mean).abs();

            // TODO(tarcieri): better method for finding outliers? (e.g. MAD, IQD)
            if (distance / self.stddev) < self.threshold {
                return Some(n);
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::Trim;

    #[test]
    fn stddev_test() {
        let input: &[f32] = &[1.0, 2.0, 3.0, 999.0, 5.0];
        let mut trimmed = input.trim_at(1.0);

        assert_eq!(trimmed.next().unwrap(), 1.0);
        assert_eq!(trimmed.next().unwrap(), 2.0);
        assert_eq!(trimmed.next().unwrap(), 3.0);
        assert_eq!(trimmed.next().unwrap(), 5.0);
        assert_eq!(trimmed.next(), None);
    }
}
