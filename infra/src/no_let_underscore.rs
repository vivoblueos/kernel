//! Helpers for explicitly ignoring `#[must_use]` return values.
//!
//! Replaces the `let _ = #[must_use];` pattern with `expr.ignore_xxx();`
//! to make the intent explicit

pub trait IgnoreResult {
    fn ignore_result(self)
    where
        Self: Sized,
    {
    }
}

pub trait IgnoreAny {
    fn ignore_old_value(self)
    where
        Self: Sized,
    {
    }
}

impl<T, E> IgnoreResult for core::result::Result<T, E> {}
impl<T> IgnoreAny for T {}
