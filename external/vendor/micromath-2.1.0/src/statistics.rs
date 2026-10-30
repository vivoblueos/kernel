//! Statistical analysis support.
//!
//! The `statistics` Cargo feature must be enabled to use this functionality.
//!
//! The following traits are available and impl'd for slices and iterators of
//! `f32` (and can be impl'd for other types):
//!
//! - [Mean] - compute arithmetic mean with the `mean()` method.
//! - [StdDev] - compute standard deviation with the `stddev()` method
//! - [Trim] - cull outliers from a sample slice with the `trim()` method.
//! - [Variance] - compute variance with the `variance() method.
//!
//! [Mean]: https://docs.rs/micromath/latest/micromath/statistics/trait.Mean.html
//! [StdDev]: https://docs.rs/micromath/latest/micromath/statistics/trait.StdDev.html
//! [Trim]: https://docs.rs/micromath/latest/micromath/statistics/trim/trait.Trim.html
//! [Variance]: https://docs.rs/micromath/latest/micromath/statistics/trait.Variance.html

mod mean;
mod stddev;
pub mod trim;
mod variance;

pub use self::{mean::Mean, stddev::StdDev, trim::Trim, variance::Variance};
