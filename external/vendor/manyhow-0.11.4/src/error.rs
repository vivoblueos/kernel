#![allow(clippy::missing_errors_doc)]
use std::convert::Infallible;
use std::fmt::{Debug, Display};
use std::mem;
use std::ops::{Add, AddAssign, Range};

#[cfg(feature = "darling")]
use darling_core::Error as DarlingError;
use proc_macro2::{Span, TokenStream};
use quote::{quote_spanned, ToTokens};
#[cfg(feature = "syn1")]
use syn1::Error as Syn1Error;
#[cfg(feature = "syn2")]
use syn2::Error as Syn2Error;

#[cfg(doc)]
use crate::MacroOutput;
use crate::{to_tokens_span_range, SpanRanged};

/// An alias for [`Result`](std::result::Result) suited for use with this crate
pub type Result<T = TokenStream, E = Error> = std::result::Result<T, E>;

/// Error that does not expand to any [`compile_error!`] and therefor does not
/// cause compilation to fail.
#[derive(Debug)]
pub struct SilentError;

/// This crates Error type
#[derive(Debug)]
#[must_use]
pub struct Error(Vec<Box<dyn ToTokensError>>);
#[cfg(feature = "syn1")]
impl From<Syn1Error> for Error {
    fn from(error: Syn1Error) -> Self {
        Self::from(error)
    }
}
#[cfg(feature = "syn2")]
impl From<Syn2Error> for Error {
    fn from(error: Syn2Error) -> Self {
        Self::from(error)
    }
}
#[cfg(feature = "darling")]
impl From<DarlingError> for Error {
    fn from(error: DarlingError) -> Self {
        Self::from(error)
    }
}
impl From<ErrorMessage> for Error {
    fn from(error: ErrorMessage) -> Self {
        Self::from(error)
    }
}
impl From<SilentError> for Error {
    fn from(_: SilentError) -> Self {
        Self(Vec::new())
    }
}

impl<T: ToTokensError + 'static> Add<T> for Error {
    type Output = Error;

    fn add(self, rhs: T) -> Self::Output {
        self.join(rhs)
    }
}

impl<T: ToTokensError + 'static> AddAssign<T> for Error {
    fn add_assign(&mut self, rhs: T) {
        self.push(rhs);
    }
}

impl Error {
    /// Mimics [`From<impl ToTokensError> for Error`](From) implementation to
    /// not conflict std's `From<T> for T`
    pub fn from(error: impl ToTokensError + 'static) -> Self {
        Self(vec![Box::new(error)])
    }

    /// Pushes an additional `Error`
    ///
    /// Alternatively errors can also be "added":
    ///
    /// ```
    /// use manyhow::{Error, error_message};
    /// let mut error = Error::from(error_message!("Hello Rust!"));
    /// error += error_message!("Hello 🦀!");
    /// # use manyhow::ToTokensError;
    /// # proc_macro_utils::assert_tokens!(error.into_token_stream(), 
    /// #     { ::core::compile_error!{"Hello Rust!"} ::core::compile_error!{"Hello 🦀!"} });
    /// ```
    pub fn push(&mut self, error: impl ToTokensError + 'static) {
        self.0.push(Box::new(error));
    }
}

impl<I: ToTokensError + 'static> Extend<I> for Error {
    fn extend<T: IntoIterator<Item = I>>(&mut self, iter: T) {
        self.0.extend(
            iter.into_iter()
                .map(|i| Box::new(i) as Box<dyn ToTokensError>),
        );
    }
}

/// A single error message
///
/// Can take additional attachments like [`help`](Self::help) or
/// [`note`](Self::note).
///
/// Implements `ToTokensError` and can therefore be used with
/// [`MacroOutput`]s.
#[derive(Debug)]
#[must_use]
pub struct ErrorMessage {
    span: Range<Span>,
    msg: String,
    attachments: Vec<(&'static str, String)>,
}
impl Display for ErrorMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg.trim_end())?;
        if !self.attachments.is_empty() {
            write!(f, "\n\n")?;
        }
        for (label, attachment) in &self.attachments {
            let mut attachment = attachment.lines();
            writeln!(
                f,
                "  = {label}: {}",
                attachment.next().expect("should return at least one line")
            )?;
            for line in attachment {
                // `labels` should always be one char per cell
                writeln!(f, "    {1:2$}  {}", line, "", label.len())?;
            }
        }
        Ok(())
    }
}
impl ToTokensError for ErrorMessage {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let msg = self.to_string();
        let msg = quote_spanned!(self.span.end => {#msg});
        quote_spanned! {self.span.start =>
            ::core::compile_error! #msg
        }
        .to_tokens(tokens);
    }
}

#[cfg(feature = "syn1")]
impl From<ErrorMessage> for Syn1Error {
    fn from(value: ErrorMessage) -> Self {
        Self::new_spanned(value.to_token_stream(), value)
    }
}
#[cfg(feature = "syn2")]
impl From<ErrorMessage> for Syn2Error {
    fn from(value: ErrorMessage) -> Self {
        Self::new_spanned(value.to_token_stream(), value)
    }
}

impl<T: ToTokensError + 'static> Add<T> for ErrorMessage {
    type Output = Error;

    fn add(self, rhs: T) -> Self::Output {
        self.join(rhs)
    }
}

impl ErrorMessage {
    /// Creates a new error message at the specified span
    ///
    /// This function takes a [`SpanRanged`] meaning you can also pass a
    /// [`Range`](Range)[`<Span>`](Span) (i.e. `first..last`) for better error
    /// messages on multi token values, for details see
    /// [SpanRanged#motivation](SpanRanged#motivation)
    ///
    /// If your type implements [`ToTokens`] use [`ErrorMessage::spanned`]
    /// instead.
    pub fn new(span: impl SpanRanged, msg: impl Display) -> Self {
        Self {
            span: span.span_range(),
            msg: msg.to_string(),
            attachments: Vec::new(),
        }
    }

    /// Creates an error message pointing to the complete token stream `tokens`
    /// expands to
    pub fn spanned(tokens: impl ToTokens, msg: impl Display) -> Self {
        Self {
            span: to_tokens_span_range(tokens),
            msg: msg.to_string(),
            attachments: Vec::new(),
        }
    }

    /// Creates a new error message at [`Span::call_site`] prefer
    /// [`ErrorMessage::new`] or [`ErrorMessage::spanned`] with the correct span
    /// for a more helpful output.
    pub fn call_site(msg: impl Display) -> Self {
        Self::new(Span::call_site(), msg)
    }

    /// Attaches an additional message to `self` reusing the same
    /// span, and the specified `label`.
    pub fn attachment(mut self, label: &'static str, msg: impl Display) -> Self {
        self.attachments.push((label, msg.to_string()));
        self
    }

    /// Attaches a new `error` message to `self` reusing the same span
    pub fn error(self, msg: impl Display) -> Self {
        self.attachment("error", msg)
    }

    /// Attaches a new `warning` message to `self` reusing the same span
    pub fn warning(self, msg: impl Display) -> Self {
        self.attachment("warning", msg)
    }

    /// Attaches a new `note` message to `self` reusing the same span
    pub fn note(self, msg: impl Display) -> Self {
        self.attachment("note", msg)
    }

    /// Attaches a new `help` message to `self` reusing the same span
    pub fn help(self, msg: impl Display) -> Self {
        self.attachment("help", msg)
    }
}

/// Exposes [`ErrorMessage::attachment`] as a trait to allow
/// [`ResultExt::attachment`].
pub trait Attachment: Sized {
    /// Attaches an additional message to `self` reusing the same
    /// span, and the specified `label`.
    #[must_use]
    fn attachment(self, label: &'static str, msg: impl Display) -> Self;
}

impl Attachment for ErrorMessage {
    fn attachment(mut self, label: &'static str, msg: impl Display) -> Self {
        self.attachments.push((label, msg.to_string()));
        self
    }
}

/// Allows emitting errors without returning.
#[derive(Default, Debug)]
pub struct Emitter(Vec<Box<dyn ToTokensError>>);

impl<T: ToTokensError + 'static> AddAssign<T> for Emitter {
    fn add_assign(&mut self, rhs: T) {
        self.emit(rhs);
    }
}

impl Emitter {
    /// Creates an `Emitter`, this can be used to collect errors than can later
    /// be converted with [`Emitter::into_result()`].
    #[must_use]
    pub fn new() -> Self {
        Emitter(Vec::new())
    }

    pub(crate) fn to_tokens(&self, tokens: &mut TokenStream) {
        for error in &self.0 {
            error.to_tokens(tokens);
        }
    }

    /// Emits an error
    ///
    /// Alternatively errors can also be "added":
    ///
    /// ```
    /// let mut emitter = manyhow::Emitter::new();
    /// emitter += manyhow::error_message!("Hello World!");
    /// # use manyhow::ToTokensError;
    /// # proc_macro_utils::assert_tokens!(emitter.into_result().unwrap_err().into_token_stream(), { ::core::compile_error!{"Hello World!"} });
    /// ```
    pub fn emit(&mut self, error: impl ToTokensError + 'static) {
        self.0.push(Box::new(error));
    }

    /// Checks if any errors were emitted
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Removes all emitted errors
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Returns emitted errors if not [`Self::is_empty`].
    ///
    /// If no errors where emitted, returns `Ok(())`.
    ///
    /// *Note:* This clears the emitter to avoid returning duplicate errors.
    pub fn into_result(&mut self) -> Result<(), Error> {
        if self.is_empty() {
            Ok(())
        } else {
            Err(Error(mem::take(&mut self.0)))
        }
    }
}

impl<I: ToTokensError + 'static> Extend<I> for Emitter {
    fn extend<T: IntoIterator<Item = I>>(&mut self, iter: T) {
        self.0.extend(
            iter.into_iter()
                .map(|i| Box::new(i) as Box<dyn ToTokensError>),
        );
    }
}

/// Error that can be converted to a [`TokenStream`] required to be used with
/// [`MacroOutput`]
///
/// This trait is equivalent to [`ToTokens`].
pub trait ToTokensError: Debug {
    /// Equivalent to [`ToTokens::to_tokens`]
    fn to_tokens(&self, tokens: &mut TokenStream);
    /// Equivalent to [`ToTokens::to_token_stream`]
    fn to_token_stream(&self) -> TokenStream {
        let mut tokens = TokenStream::new();
        self.to_tokens(&mut tokens);
        tokens
    }
    /// Equivalent to [`ToTokens::into_token_stream`]
    fn into_token_stream(self) -> TokenStream
    where
        Self: Sized,
    {
        self.to_token_stream()
    }
}

/// Allows to call `.join(..)` on any `impl ToTokensError`
pub trait JoinToTokensError {
    /// Joins two `Error`s
    ///
    /// ```
    /// use manyhow::error_message;
    /// # use crate::manyhow::JoinToTokensError;
    ///
    /// error_message!("test").join(error_message!("another"));
    /// ```
    ///
    /// Some errors like [`manyhow::Error`] and [`manyhow::ErrorMessage`] can
    /// also be "added":
    ///
    /// ```
    /// # use manyhow::ToTokensError;
    /// use manyhow::{error_message, Error};
    /// # proc_macro_utils::assert_tokens!((
    /// error_message!("Hello Rust!") + error_message!("Hello 🦀!")
    /// # ).into_token_stream(), { ::core::compile_error!{"Hello Rust!"} ::core::compile_error!{"Hello 🦀!"} });
    /// # proc_macro_utils::assert_tokens!((
    /// Error::from(error_message!("Hello Rust!")) + error_message!("Hello 🦀!")
    /// # ).into_token_stream(), { ::core::compile_error!{"Hello Rust!"} ::core::compile_error!{"Hello 🦀!"} });
    /// ```
    fn join(self, error: impl ToTokensError + 'static) -> Error;
}

impl<T: Sized + ToTokensError + 'static> JoinToTokensError for T {
    fn join(self, error: impl ToTokensError + 'static) -> Error {
        let mut this = Error::from(self);
        this.push(error);
        this
    }
}

impl ToTokensError for Infallible {
    fn to_tokens(&self, _: &mut TokenStream) {
        unreachable!()
    }
}
#[cfg(feature = "syn1")]
impl ToTokensError for Syn1Error {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.to_compile_error().to_tokens(tokens);
    }
}
#[cfg(feature = "syn")]
impl ToTokensError for Syn2Error {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.to_compile_error().to_tokens(tokens);
    }
}
#[cfg(feature = "darling")]
impl ToTokensError for DarlingError {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.clone().write_errors().to_tokens(tokens);
    }
}
impl ToTokensError for Error {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for error in &self.0 {
            error.to_tokens(tokens);
        }
    }
}
impl ToTokensError for SilentError {
    fn to_tokens(&self, _: &mut TokenStream) {}
}

/// Some utilities on [`Result<T, impl ToTokensError>`](ToTokensError)
pub trait ResultExt<T, E>: Sized {
    /// If self is error, attaches another error
    fn context(self, error: impl ToTokensError + 'static) -> Result<T, Error> {
        self.context_with(|| error)
    }

    /// If self is error, attaches another error, closure is only executed if
    /// the `Result` is `Err`
    fn context_with<C: ToTokensError + 'static>(
        self,
        error: impl FnOnce() -> C,
    ) -> Result<T, Error>;
    /// If self is error, extend error message
    ///
    /// Only works if `E` implements [`Attachment`] which is the case for
    /// [`ErrorMessage`]
    #[must_use]
    fn attachment(self, label: &'static str, msg: impl Display) -> Self
    where
        E: Attachment;

    /// Attaches a new `error` message to `self` reusing the same span
    #[must_use]
    fn error(self, msg: impl Display) -> Self
    where
        E: Attachment,
    {
        self.attachment("error", msg)
    }

    /// Attaches a new `warning` message to `self` reusing the same span
    #[must_use]
    fn warning(self, msg: impl Display) -> Self
    where
        E: Attachment,
    {
        self.attachment("warning", msg)
    }

    /// Attaches a new `note` message to `self` reusing the same span
    #[must_use]
    fn note(self, msg: impl Display) -> Self
    where
        E: Attachment,
    {
        self.attachment("note", msg)
    }

    /// Attaches a new `help` message to `self` reusing the same span
    #[must_use]
    fn help(self, msg: impl Display) -> Self
    where
        E: Attachment,
    {
        self.attachment("help", msg)
    }
}

impl<T, E: ToTokensError + 'static> ResultExt<T, E> for Result<T, E> {
    fn context_with<C: ToTokensError + 'static>(
        self,
        error: impl FnOnce() -> C,
    ) -> Result<T, Error> {
        self.map_err(|e| {
            let mut e = Error::from(e);
            e.push(error());
            e
        })
    }

    fn attachment(self, label: &'static str, msg: impl Display) -> Result<T, E>
    where
        E: Attachment,
    {
        self.map_err(|e| e.attachment(label, msg))
    }
}

#[cfg(test)]
mod test {
    use proc_macro_utils::assert_tokens;

    use super::*;

    #[test]
    fn error_message() {
        let error_message = ErrorMessage::new(Span::call_site(), "test message")
            .help("try to call your dog")
            .note("you could use the banana phone")
            .warning("be careful")
            .error("you cannot reach them");
        assert_tokens! {error_message.to_token_stream(), {
            ::core::compile_error! {
                "test message\n\n  = help: try to call your dog\n  = note: you could use the banana phone\n  = warning: be careful\n  = error: you cannot reach them\n"
            }
        }}
    }
}
