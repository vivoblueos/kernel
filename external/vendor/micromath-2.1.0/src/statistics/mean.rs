/// Arithmetic mean
pub trait Mean {
    /// Result type
    type Result;

    /// Compute the arithmetic mean
    fn mean(self) -> Self::Result;
}

impl<I> Mean for I
where
    I: Iterator<Item = f32>,
{
    type Result = f32;

    fn mean(self) -> f32 {
        let mut num_items = 0;
        let mut sum = 0.0;

        for item in self {
            num_items += 1;
            sum += item;
        }

        sum / (num_items as f32)
    }
}

#[cfg(test)]
mod tests {
    use super::Mean;

    #[test]
    fn mean_test() {
        assert_eq!([1.0, 3.0, 5.0].iter().cloned().mean(), 3.0);
    }
}
