use std::ops::Range;

use proc_macro2::Span;
use quote::ToTokens;

#[cfg(doc)]
use crate::ErrorMessage;

/// Get a [`Range`](std::ops::Range)[`<Span>`](proc_macro2::Span) from a
/// type that **either** implements [`SpanRanged`] or [`ToTokens`] (**NOT**
/// both).
#[macro_export]
macro_rules! span_range {
    ($span:expr) => {{
        // Warning is triggered if span is incorrect type
        #[allow(unused_imports)]
        use $crate::__private::*;
        ($span).FIRST_ARG_MUST_IMPLEMENT_SpanRanged_OR_ToTokens()
    }};
}

/// Returns the [`Range`](Range)[`<Span>`](Span) from the start to the end of
/// multi-token structures.
///
/// `start` and `end` can be the same when called on single Tokens or [`Span`].
///
/// Due to compiler limitations, it is currently not possible to implement
/// `SpanRanged for T: ToTokens`, therefor there is
/// [`to_tokens_span_range()`].
///
/// For types that **either** implement [`SpanRanged`] or [`ToTokens`] (but
/// **NOT** both) the [`span_range!`] macro can be used as well.
///
/// # Motivation
/// This is superior to a normal [`Span`] (at least until [`Span::join`] works
/// on stable), because it leads to better error messages:
///
/// Given the following expression
/// ```
/// let a = |something: usize| something;
/// ```
///
/// [`ErrorMessage::new(first_pipe_span, "error message")`](ErrorMessage::new)
/// would result in something like
///
/// ```text
/// error: error message
///
/// let a = |something: usize| something;
///         ^
/// ```
///
/// While [`ErrorMessage::new(first_pipe_span..something_span,
/// "error message")`](ErrorMessage::new) would improve the error message to:
/// ```text
/// error: error message
///
/// let a = |something: usize| something;
///         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
/// ```
pub trait SpanRanged {
    /// Returns the [`Range`](Range)[`<Span>`](Span) fully encompasing `self`
    fn span_range(&self) -> Range<Span>;

    /// Returns [`Self::span_range`] as a single span if possible, currently
    /// only possible on nightly. [more](proc_macro2::Span::join)
    fn span_joined(&self) -> Option<Span> {
        let range = self.span_range();
        range.start.join(range.end)
    }

    #[doc(hidden)]
    #[deprecated]
    fn joined(&self) -> Option<Span> {
        self.span_joined()
    }
}

impl<T: SpanRanged> SpanRanged for &T {
    fn span_range(&self) -> Range<Span> {
        (*self).span_range()
    }
}

impl<T: SpanRanged> SpanRanged for Option<T> {
    fn span_range(&self) -> Range<Span> {
        self.as_ref()
            .map_or_else(|| Span::call_site().span_range(), SpanRanged::span_range)
    }
}

impl<A: SpanRanged, B: SpanRanged> SpanRanged for (A, B) {
    fn span_range(&self) -> Range<Span> {
        (self.0.span_range().start)..(self.1.span_range().end)
    }
}

impl SpanRanged for Span {
    fn span_range(&self) -> Range<Span> {
        *self..*self
    }
}
impl SpanRanged for proc_macro::Span {
    fn span_range(&self) -> Range<Span> {
        (*self).into()..(*self).into()
    }
}

impl<T: SpanRanged> SpanRanged for Range<T> {
    fn span_range(&self) -> Range<Span> {
        self.start.span_range().start..self.end.span_range().end
    }
}

impl SpanRanged for proc_macro::TokenStream {
    fn span_range(&self) -> Range<Span> {
        let mut this = self.clone().into_iter();
        let first = this
            .next()
            .as_ref()
            .map_or_else(proc_macro::Span::call_site, proc_macro::TokenTree::span);

        let last = this
            .last()
            .as_ref()
            .map_or(first, proc_macro::TokenTree::span);
        first.into()..last.into()
    }
}

/// Implementation of [`SpanRanged`](SpanRanged)` for T: `[`ToTokens`]
///
/// This is necessary to put in a standalone function due to compiler
/// limitations.
pub fn to_tokens_span_range(tokens: impl ToTokens) -> Range<Span> {
    proc_macro::TokenStream::from(tokens.to_token_stream()).span_range()
}

#[doc(hidden)]
pub trait SpanRangedToSpanRange {
    #[allow(non_snake_case)]
    fn FIRST_ARG_MUST_IMPLEMENT_SpanRanged_OR_ToTokens(&self) -> Range<Span>;
}
impl<T: SpanRanged> SpanRangedToSpanRange for T {
    #[allow(non_snake_case)]
    fn FIRST_ARG_MUST_IMPLEMENT_SpanRanged_OR_ToTokens(&self) -> Range<Span> {
        self.span_range()
    }
}

#[doc(hidden)]
pub trait ToTokensToSpanRange {
    #[allow(non_snake_case)]
    fn FIRST_ARG_MUST_IMPLEMENT_SpanRanged_OR_ToTokens(&self) -> Range<Span>;
}
impl<T: ToTokens> ToTokensToSpanRange for T {
    #[allow(non_snake_case)]
    fn FIRST_ARG_MUST_IMPLEMENT_SpanRanged_OR_ToTokens(&self) -> Range<Span> {
        let mut this = self.to_token_stream().into_iter();
        let first = this
            .next()
            .as_ref()
            .map_or_else(proc_macro2::Span::call_site, proc_macro2::TokenTree::span);

        let last = this
            .last()
            .as_ref()
            .map_or(first, proc_macro2::TokenTree::span);
        first..last
    }
}

#[doc(hidden)]
pub trait ToTokensTupleToSpanRange {
    #[allow(non_snake_case)]
    fn FIRST_ARG_MUST_IMPLEMENT_SpanRanged_OR_ToTokens(&self) -> Range<Span>;
}
impl<A: ToTokens, B: ToTokens> ToTokensTupleToSpanRange for (A, B) {
    #[allow(non_snake_case)]
    fn FIRST_ARG_MUST_IMPLEMENT_SpanRanged_OR_ToTokens(&self) -> Range<Span> {
        let first = self
            .0
            .to_token_stream()
            .into_iter()
            .next()
            .as_ref()
            .map_or_else(proc_macro2::Span::call_site, proc_macro2::TokenTree::span);

        let last = self
            .1
            .to_token_stream()
            .into_iter()
            .last()
            .as_ref()
            .map_or(first, proc_macro2::TokenTree::span);

        first..last
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test() {
        span_range!(1);
        span_range!((1, 2));
    }
}
