use std::ops::{Bound, RangeBounds};
use std::str::FromStr;
use std::{iter, mem};

#[cfg(doc)]
use proc_macro2::Spacing;
use proc_macro2::{token_stream, Group, Ident, Literal, Punct, Span, TokenStream, TokenTree};
use smallvec::{smallvec, SmallVec};

use crate::{Delimited, TokenStream2Ext, TokenTree2Ext, TokenTreeLiteral, TokenTreePunct};

// TODO move implementation in a trait implemented on both
// Peekable<token_stream::IntoIter>s
/// Trait that allows to peek a constant number of tokens.
pub trait Peeker {
    /// Number of tokens this peeker checks.
    fn len(&self) -> usize;

    /// Test if the tokens match.
    ///
    /// # Panics
    ///
    /// Implementations can panic if `tokens.len() < Self::LENGTH`.
    #[must_use]
    fn peek(self, tokens: &[TokenTree]) -> bool;
}

impl<T: FnOnce(&TokenTree) -> bool> Peeker for T {
    fn len(&self) -> usize {
        1
    }

    #[must_use]
    fn peek(self, parser: &[TokenTree]) -> bool {
        self(&parser[0])
    }
}

macro_rules! impl_peeker {
    ($(($($T:ident $idx:tt),+$(,)?),$len:literal;)*) => {
        $(
            impl<$($T: FnOnce(&TokenTree) -> bool),+> Peeker for ($($T,)+) {
                fn len(&self) -> usize { $len }
                fn peek(self, parser: &[TokenTree]) -> bool {
                    $(self.$idx(&parser[$idx]))&&+
                }
            }
        )*
    };
}

impl_peeker![
    (T1 0,), 1;
    (T1 0, T2 1), 2;
    (T1 0, T2 1, T3 2), 3;
];

struct PeekLen(usize);

impl Peeker for PeekLen {
    fn len(&self) -> usize {
        self.0
    }

    fn peek(self, _: &[TokenTree]) -> bool {
        true
    }
}

/// Wrapper for [`TokenStream::into_iter`] allowing not only to iterate on
/// tokens but also to parse simple structures like types or expressions, though
/// it does not make any claims about their correctness.
///
/// ```
/// # use proc_macro2::TokenStream;
/// # use proc_macro_utils::{TokenParser, assert_tokens};
/// # use quote::quote;
/// let mut token_parser = TokenParser::new(quote! {a + b, c});
/// assert_tokens!(token_parser.next_expression().unwrap(), { a + b });
/// ```
///
/// # Construction
///
/// In most cases use [`new()`](TokenParser::new) to avoid specifying the
/// generics. To change the on-stack size of the peek-buffer use
/// [`new_generic()`](TokenParser::new_generic) or
/// [`From::from`](#impl-From<T>-for-TokenParser<I,+PEEKER_LEN>).
///
/// # Peeking
///
/// The `TokenParser` allows peeking an arbitrary amount of tokens using
/// [`peek_n()`](Self::peek_n) and the token specific variants. This uses a
/// [`SmallVec`] with its capacity specified via `PEEKER_LEN` (default is 6).
/// This means peeking up to `6` tokens ahead happens without heap allocation.
/// Token groups can need up to `3` tokens of additional space e.g.
/// [`peek_n_tt_dot_dot_eq()`](Self::peek_n_tt_dot_dot_eq) can, with the default
/// allocation free be called with up to `3`, and
/// [`peek_n_tt_plus_eq()`](Self::peek_n_tt_plus_eq) up to `4`.
///
/// **Warning**: Setting `PEEKER_LEN = 0` means even
/// [`is_empty()`](Self::is_empty) and [`peek()`](Self::peek) allocate, and a
/// value below `3` will make some of the
/// [`peek_{punctuation}`](#impl-TokenParser<I,+PEEKER_LEN>-3) allocate
/// additionally. But do also refrain from setting `PEEKER_LEN` too high, as
/// this is the stack allocation used.
#[allow(clippy::module_name_repetitions)]
#[derive(Clone)]
#[must_use]
pub struct TokenParser<
    I: Iterator<Item = TokenTree> = token_stream::IntoIter,
    const PEEKER_LEN: usize = 6,
> {
    peek: SmallVec<[TokenTree; PEEKER_LEN]>,
    iter: I,
}

impl TokenParser {
    /// Creates a new [`TokenParser`] from a [`TokenTree`] iterator.
    ///
    /// This sets the default length for the peeker buffer. Use
    /// [`new_generic()`](Self::new_generic) to change it.
    pub fn new<T, I>(value: T) -> TokenParser<I, 6>
    where
        T: IntoIterator<Item = TokenTree, IntoIter = I>,
        I: Iterator<Item = TokenTree>,
    {
        TokenParser::new_generic(value)
    }

    /// Creates a new [`TokenParser`] from a [`TokenTree`] iterator, allowing
    /// to specify the size of the peeker buffer.
    ///
    /// See [Peeking](#Peeking) for implications.
    pub fn new_generic<const PEEKER_LEN: usize, T, I>(value: T) -> TokenParser<I, PEEKER_LEN>
    where
        T: IntoIterator<Item = TokenTree, IntoIter = I>,
        I: Iterator<Item = TokenTree>,
    {
        TokenParser {
            peek: smallvec![],
            iter: value.into_iter(),
        }
    }
}

impl<T, I, const PEEKER_LEN: usize> From<T> for TokenParser<I, PEEKER_LEN>
where
    T: IntoIterator<Item = TokenTree, IntoIter = I>,
    I: Iterator<Item = TokenTree>,
{
    fn from(value: T) -> Self {
        TokenParser::new_generic(value)
    }
}

impl<I, const PEEKER_LEN: usize> From<TokenParser<I, PEEKER_LEN>> for TokenStream
where
    I: Iterator<Item = TokenTree>,
{
    #[must_use]
    fn from(value: TokenParser<I, PEEKER_LEN>) -> Self {
        value.peek.into_iter().chain(value.iter).collect()
    }
}

impl<I, const PEEKER_LEN: usize> Iterator for TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    type Item = TokenTree;

    #[must_use]
    fn next(&mut self) -> Option<Self::Item> {
        if self.peek.is_empty() {
            self.iter.next()
        } else {
            Some(self.peek.remove(0))
        }
    }
}

impl FromStr for TokenParser {
    type Err = <TokenStream as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        TokenStream::from_str(s).map(Self::new)
    }
}

#[cfg(feature = "quote")]
impl<I, const PEEKER_LEN: usize> quote::ToTokens for TokenParser<I, PEEKER_LEN>
where
    I: Clone + Iterator<Item = TokenTree>,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(self.clone());
    }

    #[must_use]
    fn to_token_stream(&self) -> TokenStream {
        self.clone().collect()
    }

    #[must_use]
    fn into_token_stream(self) -> TokenStream
    where
        Self: Sized,
    {
        self.collect()
    }
}

macro_rules! next_punct {
    ($self:ident, $only:ident) => {
        $self.next_if(TokenTree::$only).map(TokenTree::alone).map(iter::once).map(Iterator::collect)
    };
    ($self:ident, $($joint:ident),+ $(!$($not:ident),+)?) => {
        next_punct!($self, 0, $($joint),+ $(!$($not),+)?;true)
    };
    ($self:ident, $idx:expr, $first:ident, $($joint:ident),+ $(!$($not:ident),*)?;$($cond:tt)*) => {
        next_punct!($self, $idx+1, $($joint),+ $(!$($not),+)?; $($cond)* && matches!($self.peek_n($idx), Some(tt) if tt.$first() && tt.is_joint()))
    };
    ($self:ident, $idx:expr, $last:ident;$($cond:tt)*) => {
        ($($cond)* && matches!($self.peek_n($idx), Some(tt) if tt.$last())).then(|| $self.next_n_alone($idx+1).expect("peeked n"))
    };
    ($self:ident, $idx:expr, $last:ident !$($not:ident),+;$($cond:tt)*) => {
        ($($cond)* && matches!($self.peek_n($idx), Some(tt) if tt.$last())
         && (matches!($self.peek_n($idx), Some(tt) if tt.is_alone()) ||
         !(matches!($self.peek_n($idx+1), Some(tt) if false $(|| tt.$not())*))))
            .then(|| $self.next_n_alone($idx+1).expect("peeked n"))
    };
}

macro_rules! peek_punct {
    ($offset:expr, $self:ident, $only:ident) => {
        $self.peek_n($offset).filter(|t| t.$only()).cloned().map(TokenTree::alone).map(iter::once).map(Iterator::collect)
    };
    ($offset:expr, $self:ident, $($joint:ident),+ $(!$($not:ident),+)?) => {
        peek_punct!($offset, $self, $offset, $($joint),+ $(!$($not),+)?;true)
    };
    ($offset:expr, $self:ident, $idx:expr, $first:ident, $($joint:ident),+ $(!$($not:ident),*)?;$($cond:tt)*) => {
        peek_punct!($offset, $self, $idx+1, $($joint),+ $(!$($not),+)?; $($cond)* && matches!($self.peek_n($idx), Some(tt) if tt.$first() && tt.is_joint()))
    };
    ($offset:expr, $self:ident, $idx:expr, $last:ident;$($cond:tt)*) => {
        ($($cond)* && matches!($self.peek_n($idx), Some(tt) if tt.$last())).then(|| $self.peek_range_alone($offset..$idx+1).expect("peeked n"))
    };
    ($offset:expr, $self:ident, $idx:expr, $last:ident !$($not:ident),+;$($cond:tt)*) => {
        ($($cond)* && matches!($self.peek_n($idx), Some(tt) if tt.$last())
         && (matches!($self.peek_n($idx), Some(tt) if tt.is_alone()) ||
         !(matches!($self.peek_n($idx+1), Some(tt) if false $(|| tt.$not())*))))
            .then(|| $self.peek_range_alone($offset..$idx+1).expect("peeked n"))
    };
}

macro_rules! punct_tt {
    ($($punct:literal, [$($cond:tt)*], $peek:ident, $peek_n:ident, $name:ident);*$(;)?) => {
        $(#[doc = concat!("Returns the next token if it is a [punctuation token tree](https://doc.rust-lang.org/reference/tokens.html#punctuation) `", $punct ,"` following the same rules as [macro_rule's tt](https://doc.rust-lang.org/reference/macros-by-example.html#metavariables).")]
        #[doc = concat!("```
use proc_macro_utils::{assert_tokens, TokenParser};
use quote::quote;
let mut parser = TokenParser::new(quote!(", $punct, " 1 b));
assert_tokens!(parser.", stringify!($name), "().unwrap(), { ", $punct, " });
assert_tokens!(parser, { 1 b });
```")]
        #[must_use]
        pub fn $name(&mut self) -> Option<TokenStream> {
            next_punct!(self, $($cond)*)
        }
        #[doc = concat!("Returns the next token if it is a [punctuation token tree](https://doc.rust-lang.org/reference/tokens.html#punctuation) `", $punct ,"` following the same rules as [macro_rule's tt](https://doc.rust-lang.org/reference/macros-by-example.html#metavariables) without advancing the parser")]
        #[doc = concat!("```
use proc_macro_utils::{assert_tokens, TokenParser};
use quote::quote;
let mut parser = TokenParser::new(quote!(", $punct, " 1 b));
assert_tokens!(parser.", stringify!($peek), "().unwrap(), { ", $punct, " });
```")]
        #[must_use]
        pub fn $peek(&mut self) -> Option<TokenStream> {
            peek_punct!(0, self, $($cond)*)
        }
        #[doc = concat!("Returns the `n`th token if it is a [punctuation token tree](https://doc.rust-lang.org/reference/tokens.html#punctuation) `", $punct ,"` following the same rules as [macro_rule's tt](https://doc.rust-lang.org/reference/macros-by-example.html#metavariables) without advancing the parser")]
        #[doc = concat!("```
use proc_macro_utils::{assert_tokens, TokenParser};
use quote::quote;
let mut parser = TokenParser::new(quote!(b ", $punct, " 1));
assert_tokens!(parser.", stringify!($peek_n), "(1).unwrap(), { ", $punct, " });
```")]
        #[must_use]
        pub fn $peek_n(&mut self, n: usize) -> Option<TokenStream> {
            peek_punct!(n, self, $($cond)*)
        })*
        /// Returns the next token tree as interpreted by the `tt` type in `macro_rules`, i.e., any literal, group,
        /// or [composed punctuation](https://doc.rust-lang.org/reference/tokens.html#punctuation).
        pub fn next_tt(&mut self) -> Option<TokenStream> {
            self.next_if_each(TokenTree::is_group)
                .or_else(|| self.next_if_each(TokenTree::is_literal))
                $(.or_else(|| self.$name()))*
        }
        /// Peeks the next token tree as interpreted by the `tt` type in `macro_rules`, i.e., any literal, group,
        /// or [composed punctuation](https://doc.rust-lang.org/reference/tokens.html#punctuation).
        pub fn peek_tt(&mut self) -> Option<TokenStream> {
            self.peek_n_tt(0)
        }
        /// Peeks the next token tree from the `n`th token as interpreted by the `tt` type in `macro_rules`, i.e., any literal, group,
        /// or [composed punctuation](https://doc.rust-lang.org/reference/tokens.html#punctuation).
        pub fn peek_n_tt(&mut self, n: usize) -> Option<TokenStream> {
            self.peek_if_each(TokenTree::is_group)
                .or_else(|| self.peek_if_each(TokenTree::is_literal))
            $(.or_else(|| self.$peek_n(n)))*
        }
    };
    ([$test:ident $($tests:ident)*]) => {
        matches!(self.peek(), Some(token) if token.$test()) && punct!([$($tests)*])
    }
}

macro_rules! token_tree {
    ($($a:literal, $test:ident, $peek_as:ident, $as:ident, $peek:ident, $peek_n:ident, $name:ident, $token:ident);*$(;)?) => {
        $(#[doc = concat!("Returns the next token if it is ", $a, " [`", stringify!($token) ,"`].")]
        #[must_use]
        pub fn $name(&mut self) -> Option<$token> {
            self.$peek().is_some().then(|| self.next().expect("token should be present").$as().expect(concat!("should be ", stringify!($token))))
        })*

        $(#[doc = concat!("Returns the next token if it is ", $a, " [`", stringify!($token) ,"`] without advancing the parser.")]
        #[must_use]
        pub fn $peek(&mut self) -> Option<&$token> {
            self.$peek_n(0)
        })*

        $(#[doc = concat!("Returns the `n`th token if it is ", $a, " [`", stringify!($token) ,"`] without advancing the parser.")]
        #[must_use]
        pub fn $peek_n(&mut self, n: usize) -> Option<&$token> {
            self.peek_n(n).and_then(TokenTree::$peek_as)
        })*
    };
}

macro_rules! delimited {
    ($($test:ident, $peek:ident, $peek_n:ident, $name:ident, $doc:literal;)*) => {
        $(#[doc = concat!("Returns the next token if it is a ", $doc ," group.")]
        #[must_use]
        pub fn $name(&mut self) -> Option<Group> {
            self.$peek().is_some().then(|| {
                self.next_group().unwrap()
            })
        })*
        $(#[doc = concat!("Returns the next token if it is a", $doc ," group, without advancing the parser.")]
        #[must_use]
        pub fn $peek(&mut self) -> Option<&Group> {
            self.$peek_n(0)
        })*
        $(#[doc = concat!("Returns the `n`th token if it is a ", $doc ," group, without advancing the parser.")]
        #[must_use]
        pub fn $peek_n(&mut self, n: usize) -> Option<&Group> {
            self.peek_n_group(n).filter(|g| g.$test())
        })*
    };
}

/// Some Iterator utilities
impl<I, const PEEKER_LEN: usize> TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    /// Returns span of the next token or [`Span::call_site()`].
    #[must_use]
    pub fn span(&mut self) -> Span {
        self.peek().map_or_else(Span::call_site, TokenTree::span)
    }

    /// Checks if there are remaining tokens
    /// ```
    /// use proc_macro_utils::TokenParser;
    /// use quote::quote;
    ///
    /// let mut parser = TokenParser::new(quote!(token));
    /// assert!(!parser.is_empty());
    /// _ = parser.next();
    /// assert!(parser.is_empty())
    /// ```
    #[must_use]
    pub fn is_empty(&mut self) -> bool {
        self.peek().is_none()
    }

    /// Peeks the next token without advancing the parser
    /// ```
    /// use proc_macro_utils::{assert_tokens, TokenParser};
    /// use quote::quote;
    ///
    /// let mut parser = TokenParser::new(quote!(token));
    /// assert_tokens!(parser.peek().cloned(), { token });
    /// _ = parser.next();
    /// assert!(parser.peek().is_none())
    /// ```
    #[must_use]
    pub fn peek(&mut self) -> Option<&TokenTree> {
        if self.peek.is_empty() {
            self.peek.push(self.iter.next()?);
        }
        self.peek.first()
    }

    /// Peeks the `n`th token without advancing the parser
    /// ```
    /// use proc_macro_utils::{assert_tokens, TokenParser};
    /// use quote::quote;
    ///
    /// let mut parser = TokenParser::new(quote!(token , third));
    /// assert_tokens!(parser.peek_n(2).cloned(), { third });
    /// assert_tokens!(parser.peek_n(1).cloned(), { , });
    /// assert!(parser.peek_n(3).is_none())
    /// ```
    #[must_use]
    pub fn peek_n(&mut self, n: usize) -> Option<&TokenTree> {
        for _ in self.peek.len()..=n {
            self.peek.push(self.iter.next()?);
        }
        self.peek.get(n)
    }

    /// Returns the next token if it fulfills the condition otherwise returns
    /// None and doesn't advance the parser
    /// ```
    /// use proc_macro_utils::{assert_tokens, TokenParser, TokenTreePunct};
    /// use quote::quote;
    ///
    /// let mut parser = TokenParser::new(quote!(::));
    /// assert!(parser.next_if(TokenTreePunct::is_alone).is_none());
    /// _ = parser.next();
    /// assert_tokens!(parser.next_if(TokenTreePunct::is_alone), { : });
    /// ```
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn next_if(&mut self, test: impl FnOnce(&TokenTree) -> bool) -> Option<TokenTree> {
        test(self.peek()?).then(|| self.next().expect("was peeked"))
    }

    /// Returns the next tokens if they fulfill the conditions
    /// otherwise returns None and doesn't advance the parser.
    /// ```
    /// use proc_macro_utils::{assert_tokens, TokenParser, TokenTreePunct};
    /// use quote::quote;
    ///
    /// let mut parser = TokenParser::new(quote!( -->));
    /// assert!(parser.next_if_each((TokenTreePunct::is_minus, TokenTreePunct::is_greater_than)).is_none());
    /// _ = parser.next();
    /// assert_tokens!(parser.next_if_each((TokenTreePunct::is_minus, TokenTreePunct::is_greater_than)).unwrap(), { -> });
    /// ```
    #[must_use]
    pub fn next_if_each<P: Peeker>(&mut self, tests: P) -> Option<TokenStream> {
        let len = tests.len();
        // Ensure peek is filled;
        self.peek_n(len - 1)?;
        tests
            .peek(&self.peek[..len])
            .then(|| self.peek.drain(0..len).collect())
    }

    /// Returns the next tokens if they fulfill the conditions
    /// otherwise returns None and doesn't advance the parser. If the last token
    /// is a punct it's [`spacing`](Punct::spacing()) is set to
    /// [`Alone`](Spacing::Alone).
    #[must_use]
    pub fn next_if_each_alone<P: Peeker>(&mut self, tests: P) -> Option<TokenStream> {
        let len = tests.len();
        // Ensure peek is filled;
        self.peek_n(len - 1)?;
        tests.peek(&self.peek[..len]).then(|| {
            if self.peek[len - 1].is_punct() {
                self.peek[len - 1] = self.peek[len - 1].clone().alone();
            }
            self.peek.drain(0..len).collect()
        })
    }

    /// Returns the next tokens if they fulfill the conditions
    /// otherwise returns None, without advancing the parser
    #[must_use]
    pub fn peek_if_each<P: Peeker>(&mut self, tests: P) -> Option<TokenStream> {
        // Ensure peek is filled;
        self.peek_n_if_each(0, tests)
    }

    /// Returns the next tokens from `n` if they fulfill the
    /// conditions otherwise returns None, without advancing the parser
    #[must_use]
    pub fn peek_n_if_each<P: Peeker>(&mut self, n: usize, tests: P) -> Option<TokenStream> {
        let len = tests.len();
        // Ensure peek is filled;
        self.peek_n(len + n)?;
        let peeked = &self.peek[n..len + n];
        tests.peek(peeked).then(|| peeked.iter().cloned().collect())
    }

    /// Returns the next tokens from `n` if they fulfill the conditions
    /// otherwise returns None, without advancing the parser. If the last token
    /// is a punct it's [`spacing`](Punct::spacing()) is set to
    /// [`Alone`](Spacing::Alone).
    #[must_use]
    pub fn peek_n_if_each_alone<P: Peeker>(&mut self, n: usize, tests: P) -> Option<TokenStream> {
        let len = tests.len();
        if len == 0 {
            return Some(TokenStream::new());
        }
        // Ensure peek is filled;
        self.peek_n(len + n - 1)?;
        let peeked = &self.peek[n..len + n];
        tests.peek(peeked).then(|| {
            peeked[..len - 1]
                .iter()
                .cloned()
                .chain(iter::once(peeked[len - 1].clone().alone()))
                .collect()
        })
    }

    /// Returns all tokens while `test` evaluates to true.
    ///
    /// Returns `None` if empty or `test(first_token) == false`
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn next_while(&mut self, mut test: impl FnMut(&TokenTree) -> bool) -> Option<TokenStream> {
        if self.peek().is_none() || !test(self.peek().expect("was peeked")) {
            None
        } else {
            let mut token_stream = TokenStream::new();
            token_stream.push(self.next().expect("was peeked"));
            while let Some(token) = self.next_if(&mut test) {
                token_stream.push(token);
            }
            Some(token_stream)
        }
    }

    /// Returns all tokens while `test` evaluates to true. If the last token
    /// is a punct it's [`spacing`](Punct::spacing()) is set to
    /// [`Alone`](Spacing::Alone).
    ///
    /// Returns `None` if empty or `test(first_token) == false`
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn next_while_alone(
        &mut self,
        mut test: impl FnMut(&TokenTree) -> bool,
    ) -> Option<TokenStream> {
        if self.peek().is_none() || !test(self.peek().expect("was peeked")) {
            None
        } else {
            let mut token_stream = TokenStream::new();
            let mut last = self.next().expect("was peeked");
            while let Some(token) = self.next_if(&mut test) {
                token_stream.push(mem::replace(&mut last, token));
            }
            token_stream.push(last.alone());
            Some(token_stream)
        }
    }

    /// Returns all tokens while `test` evaluates to false.
    ///
    /// Returns `None` if empty or `test(first_token) == true`.
    #[must_use]
    pub fn next_until(&mut self, mut test: impl FnMut(&TokenTree) -> bool) -> Option<TokenStream> {
        self.next_while(|token| !test(token))
    }

    /// Returns all tokens while `test` evaluates to false. If the last token is
    /// a punct it's [`spacing`](Punct::spacing()) is set to
    /// [`Alone`](Spacing::Alone).
    ///
    /// Returns `None` if empty or `test(first_token) == true`.
    #[must_use]
    pub fn next_until_alone(
        &mut self,
        mut test: impl FnMut(&TokenTree) -> bool,
    ) -> Option<TokenStream> {
        self.next_while_alone(|token| !test(token))
    }

    /// Returns the next `n` tokens.
    ///
    /// Returns `None` if the parser contains less than `n` tokens.
    ///
    /// **Note:** This should only be used for small `n` ideally less than
    /// `PEEKER_LEN`. Otherwise, something like this would be more performant:
    /// ```
    /// use proc_macro2::TokenStream;
    /// use proc_macro_utils::{TokenParser, assert_tokens};
    /// use quote::quote;
    ///
    /// let mut parser = TokenParser::new(quote!(1 2 3 /*...*/ 1000 1001 1002 1003));
    /// let n = 1000;
    /// # let n = 4;
    /// // This does not ensure that `next_up_to_n` contains exactly n tokens
    /// let next_up_to_n: TokenStream = parser.by_ref().take(n).collect();
    /// assert_tokens!(next_up_to_n, { 1 2 3 /* ...*/ 1000 });
    /// assert_tokens!(parser, { 1001 1002 1003 });
    /// ```
    #[must_use]
    pub fn next_n(&mut self, n: usize) -> Option<TokenStream> {
        self.next_if_each(PeekLen(n))
    }

    /// Returns the next `n` tokens. If the last token is a punct it's
    /// [`spacing`](Punct::spacing()) is set to [`Alone`](Spacing::Alone).
    ///
    /// Returns `None` if the parser contains less than `n` tokens.
    ///
    /// **Note:** This should only be used for small `n` ideally less than
    /// `PEEKER_LEN`. Otherwise, something like this would be more performant:
    /// ```
    /// use proc_macro2::TokenStream;
    /// use proc_macro_utils::{TokenParser, assert_tokens, TokenTreePunct};
    /// use quote::quote;
    ///
    /// let mut parser = TokenParser::new(quote!(1 2 3 /*...*/ 1000 1001 1002 1003));
    /// let n = 1000;
    /// # let n = 4;
    /// // This does not ensure that `next_up_to_n` contains exactly n tokens
    /// let mut next_up_to_n: TokenStream = parser.by_ref().take(n - 1).collect();
    /// next_up_to_n.extend(parser.next().map(TokenTreePunct::alone));
    /// assert_tokens!(next_up_to_n, { 1 2 3 /* ...*/ 1000 });
    /// assert_tokens!(parser, { 1001 1002 1003 });
    /// ```
    #[must_use]
    pub fn next_n_alone(&mut self, n: usize) -> Option<TokenStream> {
        self.next_if_each_alone(PeekLen(n))
    }

    /// Returns the specified `range` of tokens.
    ///
    /// Returns `None` if the parser does not contain these `range` tokens.
    ///
    /// **Note:** This should only be used for small and close to start `range`s
    /// ideally less than `PEEKER_LEN`. Otherwise, something like this could be
    /// more performant:
    /// ```
    /// use proc_macro2::TokenStream;
    /// use proc_macro_utils::{TokenParser, assert_tokens};
    /// use quote::quote;
    ///
    /// let parser = TokenParser::new(quote!(0 1 2 3 /*...*/ 1000 1001 1002 1003));
    /// let start = 1000;
    /// # let start = 4;
    /// let end = 1003;
    /// # let end = 7;
    /// // This does not ensure that `peeked_range` contains any tokens
    /// let peeked_range: TokenStream = parser.clone().skip(start).take(end -
    /// start).collect();
    /// assert_tokens!(peeked_range, { 1000 1001 1002 });
    /// assert_tokens!(parser, { 0 1 2 3 /*...*/ 1000 1001 1002 1003 });
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if used without upper bound i.e. `start..`.
    #[must_use]
    pub fn peek_range(&mut self, range: impl RangeBounds<usize>) -> Option<TokenStream> {
        let start = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };
        let len = match range.end_bound() {
            Bound::Included(&n) if n < start => return None,
            Bound::Included(&n) => n - start + 1,
            Bound::Excluded(&n) if n <= start => return None,
            Bound::Excluded(&n) => n - start,
            Bound::Unbounded => {
                panic!("unbounded range not supported, use `clone().skip()` instead")
            }
        };

        self.peek_n_if_each(start, PeekLen(len))
    }

    /// Returns the specified `range` of tokens. If the last token is a punct
    /// it's [`spacing`](Punct::spacing()) is set to
    /// [`Alone`](Spacing::Alone).
    ///
    /// Returns `None` if the parser does not contain these `range` tokens.
    ///
    /// **Note:** This should only be used for small and close to start `range`s
    /// ideally less than `PEEKER_LEN`. Otherwise, something like this could be
    /// more performant:
    ///
    /// ```
    /// use proc_macro2::TokenStream;
    /// use proc_macro_utils::{assert_tokens, TokenParser, TokenTreePunct};
    /// use quote::quote;
    ///
    /// let parser = TokenParser::new(quote!(0 1 2 3 /*...*/ 1000 1001 1002 1003));
    /// let start = 1000;
    /// # let start = 4;
    /// let end = 1003;
    /// # let end = 7;
    /// // This does not ensure that `peeked_range` contains any tokens
    /// let mut cloned = parser.clone().skip(start);
    /// let mut peeked_range: TokenStream = cloned.by_ref().take(end - start - 1).collect();
    /// peeked_range.extend(cloned.next().map(TokenTreePunct::alone));
    ///
    /// assert_tokens!(peeked_range, { 1000 1001 1002 });
    /// assert_tokens!(parser, { 0 1 2 3 /*...*/ 1000 1001 1002 1003 });
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if used without upper bound i.e. `start..`.
    #[must_use]
    pub fn peek_range_alone(&mut self, range: impl RangeBounds<usize>) -> Option<TokenStream> {
        let start = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };
        let len = match range.end_bound() {
            Bound::Included(&n) if n < start => return None,
            Bound::Included(&n) => n - start + 1,
            Bound::Excluded(&n) if n <= start => return None,
            Bound::Excluded(&n) => n - start,
            Bound::Unbounded => {
                panic!("unbounded range not supported, use `clone().skip()` instead")
            }
        };

        self.peek_n_if_each_alone(start, PeekLen(len))
    }
}

impl<I, const PEEKER_LEN: usize> TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    /// Collects remaining tokens back into a [`TokenStream`]
    #[must_use]
    pub fn into_token_stream(self) -> TokenStream {
        self.into()
    }

    /// Returns the next group of punctuation with [`Punct::spacing`]
    /// [`Spacing::Joint`]
    #[must_use]
    pub fn next_punctuation_group(&mut self) -> Option<TokenStream> {
        let mut joined = true;
        self.next_while(move |token| {
            let ret = joined && token.is_punct();
            joined = token.is_joint();
            ret
        })
    }

    /// Returns the next ident if it matches the specified keyword without
    /// advancing the parser.
    ///
    /// While this is called `peek_keyword` it is not restricted to rust
    /// keywords, it can be used with any ident.
    /// ```
    /// # use proc_macro_utils::TokenParser;
    /// # use quote::quote;
    /// let mut parser = TokenParser::new(quote!( in out ));
    /// assert_eq!(parser.peek_keyword("in").unwrap().to_string(), "in");
    /// assert_eq!(parser.peek_keyword("in").unwrap().to_string(), "in");
    /// assert!(parser.peek_keyword("out").is_none());
    /// parser.next().unwrap();
    /// assert_eq!(parser.peek_keyword("out").unwrap().to_string(), "out");
    /// ```
    #[must_use]
    pub fn peek_keyword<K: ?Sized>(&mut self, keyword: &K) -> Option<&Ident>
    where
        Ident: PartialEq<K>,
    {
        self.peek_n_keyword(0, keyword)
    }

    /// Returns the nth token if it matches the specified keyword without
    /// advancing the parser.
    ///
    /// While this is called `peek_n_keyword` it is not restricted to rust
    /// keywords, it can be used with any ident.
    /// ```
    /// # use proc_macro_utils::TokenParser;
    /// # use quote::quote;
    /// let mut parser = TokenParser::new(quote!( in out ));
    /// assert_eq!(parser.peek_keyword("in").unwrap().to_string(), "in");
    /// assert_eq!(parser.peek_n_keyword(1, "out").unwrap().to_string(), "out");
    /// assert!(parser.peek_keyword("out").is_none());
    /// ```
    #[must_use]
    pub fn peek_n_keyword<K: ?Sized>(&mut self, n: usize, keyword: &K) -> Option<&Ident>
    where
        Ident: PartialEq<K>,
    {
        self.peek_n_ident(n).filter(|&ident| ident == keyword)
    }

    /// Returns the next ident if it matches the specified keyword.
    ///
    /// While this is called `next_keyword` it is not restricted to rust
    /// keywords, it can be used with any ident.
    /// ```
    /// # use proc_macro_utils::TokenParser;
    /// # use quote::quote;
    /// let mut parser = TokenParser::new(quote!( in out ));
    /// assert_eq!(parser.next_keyword("in").unwrap().to_string(), "in");
    /// assert!(parser.next_keyword("in").is_none());
    /// assert_eq!(parser.next_keyword("out").unwrap().to_string(), "out");
    /// assert!(parser.next_keyword("anything").is_none());
    /// ```
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn next_keyword<K: ?Sized>(&mut self, keyword: &K) -> Option<Ident>
    where
        Ident: PartialEq<K>,
    {
        self.next_if(|token| matches!(token.ident(), Some(ident) if ident == keyword))
            .map(|token| token.into_ident().expect("is ident"))
    }

    /// "Parses" a type expression
    ///
    /// This just means it collects all the tokens that should belong to the
    /// type, until it reaches either:
    /// - a `;`
    /// - a `,` or `>` and all `<>` pairs are closed
    /// - the end of the token stream
    ///
    /// If the token stream is empty, or starts with `,`, `>` or `;` [`None`] is
    /// returned otherwise, [`Some(TokenStream)`](TokenStream) containing
    /// every token up to but excluding the terminator.
    ///
    /// ```
    /// # use proc_macro_utils::{TokenParser, assert_tokens};
    /// # use proc_macro2::TokenStream;
    /// # use quote::quote;
    ///
    /// let mut tokens = TokenParser::new(quote! {A<Test, B>, remainder});
    /// assert_tokens!(tokens.next_type().unwrap(), { A<Test, B> });
    /// assert!(tokens.next_type().is_none());
    /// assert_tokens!(tokens, { , remainder });
    /// ```
    #[must_use]
    pub fn next_type(&mut self) -> Option<TokenStream> {
        let first = self.peek()?;
        if first.is_comma() || first.is_semi() {
            return None;
        };

        let mut chevron_level: u32 = 0;

        self.next_while_alone(|token| {
            if token.is_less_than() {
                chevron_level += 1;
            } else if token.is_greater_than() {
                if chevron_level == 0 {
                    return false;
                }
                chevron_level -= 1;
            }
            !(chevron_level == 0 && token.is_comma() || token.is_semi())
        })
    }

    /// "Parses" an expression
    ///
    /// This just means it collects all the tokens that should belong to the
    /// expression, until it reaches (outside a group like `()` or `{}`) either:
    /// - a `=>`
    /// - a `;`
    /// - a `,` outside a type
    /// - the end of the token stream
    ///
    /// If the token stream is empty, or starts with `=>`, `,` or `;` [`None`]
    /// is returned otherwise, [`Some(TokenStream)`](TokenStream) containing
    /// every token up to but excluding the terminator.
    ///
    /// ```
    /// # use proc_macro_utils::{TokenParser, assert_tokens};
    /// # use proc_macro2::TokenStream;
    /// # use quote::quote;
    ///
    /// let mut tokens = TokenParser::new(quote! {A + c ::<a, b>::a < b + <C as Trait<A, B>::C>::nice(), next_token});
    /// assert_tokens!(tokens.next_expression().unwrap(), { A + c::<a, b>::a < b + <C as Trait<A, B>::C>::nice()});
    /// assert!(tokens.next_expression().is_none());
    /// assert_tokens!(tokens, { , next_token });
    /// ```
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn next_expression(&mut self) -> Option<TokenStream> {
        if self.peek().is_none()
            || matches!(self.peek(), Some(token) if token.is_comma() || token.is_semi())
            || self.peek_tt_fat_arrow().is_some()
        {
            return None;
        }

        let mut start = true;

        let mut tokens = TokenStream::new();
        let mut last = None;

        // <a> * <a>
        // <a> => <a>
        'outer: while let Some(token) = self.peek() {
            if token.is_semi() || token.is_comma() || self.peek_tt_fat_arrow().is_some() {
                break;
            }
            let token = self.peek().unwrap();
            if start && token.is_less_than() {
                tokens.extend(mem::replace(
                    &mut last,
                    Some(self.next().expect("token was peeked")),
                ));
                loop {
                    if let Some(ty) = self.next_type() {
                        for token in ty {
                            tokens.extend(mem::replace(&mut last, Some(token)));
                        }
                    }
                    // next token can only be `,;>` or None
                    let Some(token) = self.peek() else {
                        break 'outer;
                    }; // Invalid expression
                    if token.is_semi() {
                        break 'outer;
                    }
                    if token.is_greater_than() {
                        tokens.extend(mem::replace(
                            &mut last,
                            Some(self.next().expect("token was peeked")),
                        ));
                        break;
                    } else if token.is_comma() {
                        tokens.extend(mem::replace(
                            &mut last,
                            Some(self.next().expect("token was peeked")),
                        ));
                        continue; // Another type
                    };
                }
            }
            if let Some(token) = self.next() {
                // TODO this might be too simplistic
                start = token.is_punct();
                tokens.extend(mem::replace(&mut last, Some(token)));
            }
        }

        // ensure that the last punctuation is not joined (i.e. was touching the
        // terminator, mainly possible in `1..,`)
        tokens.extend(last.map(TokenTree::alone));

        Some(tokens.into_iter().collect())
    }

    /// Returns the next string literal
    #[must_use]
    pub fn next_string(&mut self) -> Option<String> {
        let lit = self.peek().and_then(TokenTreeLiteral::string)?;
        self.next();
        Some(lit)
    }

    /// Returns the next boolean literal
    #[must_use]
    pub fn next_bool(&mut self) -> Option<bool> {
        self.next_if(|t| {
            t.ident()
                .map_or(false, |ident| ident == "true" || ident == "false")
        })
        .map(|t| matches!(t.ident(), Some(ident) if ident == "true"))
    }
}

impl<I, const PEEKER_LEN: usize> TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    token_tree!(
        "a", is_group, group, into_group, peek_group, peek_n_group, next_group, Group;
        "an", is_ident, ident, into_ident, peek_ident, peek_n_ident, next_ident, Ident;
        "a", is_punct, punct, into_punct, peek_punct, peek_n_punct, next_punct, Punct;
        "a", is_literal, literal, into_literal, peek_literal, peek_n_literal, next_literal, Literal;
    );

    delimited!(
        is_parenthesized, peek_parenthesized, peek_n_parenthesized, next_parenthesized, "parenthesized";
        is_braced, peek_braced, peek_n_braced, next_braced, "braced";
        is_bracketed, peek_bracketed, peek_n_bracketed, next_bracketed, "bracketed";
    );
}
/// For now the naming of the tokens follow the names used in the
/// [rust reference](https://doc.rust-lang.org/reference/tokens.html#punctuation)
/// even though they diverge from the names used at [`TokenTreePunct`].
///
/// Note that they only match the token with correct [spacing](Spacing), i.e.
/// [`next_plus`](Self::next_tt_plus) will match `+ =` and `+a` but not `+=`.
// TODO figure out what the single token ones should return, TokenStream or
// TokenTree
impl<I, const PEEKER_LEN: usize> TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    punct_tt!(
        "+", [is_plus !is_equals], peek_tt_plus, peek_n_tt_plus, next_tt_plus;
        "-", [is_minus !is_equals], peek_tt_minus, peek_n_tt_minus, next_tt_minus;
        "*", [is_asterix !is_equals], peek_tt_star, peek_n_tt_star, next_tt_star;
        "/", [is_slash !is_equals], peek_tt_slash, peek_n_tt_slash, next_tt_slash;
        "%", [is_percent !is_equals], peek_tt_percent, peek_n_tt_percent, next_tt_percent;
        "^", [is_caret !is_equals], peek_tt_caret, peek_n_tt_caret, next_tt_caret;
        "!", [is_exclamation !is_equals], peek_tt_not, peek_n_tt_not, next_tt_not;
        "&", [is_and !is_equals, is_and], peek_tt_and, peek_n_tt_and, next_tt_and;
        "|", [is_pipe !is_equals, is_pipe], peek_tt_or, peek_n_tt_or, next_tt_or;
        "&&", [is_and, is_and !is_equals], peek_tt_and_and, peek_n_tt_and_and, next_tt_and_and;
        "||", [is_pipe, is_pipe !is_equals], peek_tt_or_or, peek_n_tt_or_or, next_tt_or_or;
        "<<", [is_less_than, is_less_than !is_equals], peek_tt_shl, peek_n_tt_shl, next_tt_shl;
        ">>", [is_greater_than, is_greater_than !is_equals], peek_tt_shr, peek_n_tt_shr, next_tt_shr;
        "+=", [is_plus, is_equals], peek_tt_plus_eq, peek_n_tt_plus_eq, next_tt_plus_eq;
        "-=", [is_minus, is_equals], peek_tt_minus_eq, peek_n_tt_minus_eq, next_tt_minus_eq;
        "*=", [is_asterix, is_equals], peek_tt_star_eq, peek_n_tt_star_eq, next_tt_star_eq;
        "/=", [is_slash, is_equals], peek_tt_slash_eq, peek_n_tt_slash_eq, next_tt_slash_eq;
        "%=", [is_percent, is_equals], peek_tt_percent_eq, peek_n_tt_percent_eq, next_tt_percent_eq;
        "^=", [is_caret, is_equals], peek_tt_caret_eq, peek_n_tt_caret_eq, next_tt_caret_eq;
        "&=", [is_and, is_equals], peek_tt_and_eq, peek_n_tt_and_eq, next_tt_and_eq;
        "|=", [is_pipe, is_equals], peek_tt_or_eq, peek_n_tt_or_eq, next_tt_or_eq;
        "<<=", [is_less_than, is_less_than, is_equals], peek_tt_shl_eq, peek_n_tt_shl_eq, next_tt_shl_eq;
        ">>=", [is_greater_than, is_greater_than, is_equals], peek_tt_shr_eq, peek_n_tt_shr_eq, next_tt_shr_eq;
        "=", [is_equals !is_equals], peek_tt_eq, peek_n_tt_eq, next_tt_eq;
        "==", [is_equals, is_equals], peek_tt_eq_eq, peek_n_tt_eq_eq, next_tt_eq_eq;
        "!=", [is_exclamation, is_equals], peek_tt_ne, peek_n_tt_ne, next_tt_ne;
        ">", [is_greater_than !is_equals], peek_tt_gt, peek_n_tt_gt, next_tt_gt;
        "<", [is_less_than !is_equals], peek_tt_lt, peek_n_tt_lt, next_tt_lt;
        ">=", [is_greater_than, is_equals], peek_tt_ge, peek_n_tt_ge, next_tt_ge;
        "<=", [is_less_than, is_equals], peek_tt_le, peek_n_tt_le, next_tt_le;
        "@", [is_at], peek_tt_at, peek_n_tt_at, next_tt_at;
        ".", [is_dot !is_dot], peek_tt_dot, peek_n_tt_dot, next_tt_dot;
        "..", [is_dot, is_dot !is_dot, is_equals], peek_tt_dot_dot, peek_n_tt_dot_dot, next_tt_dot_dot;
        "...", [is_dot, is_dot, is_dot], peek_tt_dot_dot_dot, peek_n_tt_dot_dot_dot, next_tt_dot_dot_dot;
        "..=", [is_dot, is_dot, is_equals], peek_tt_dot_dot_eq, peek_n_tt_dot_dot_eq, next_tt_dot_dot_eq;
        ",", [is_comma], peek_tt_comma, peek_n_tt_comma, next_tt_comma;
        ";", [is_semi], peek_tt_semi, peek_n_tt_semi, next_tt_semi;
        ":", [is_colon !is_colon], peek_tt_colon, peek_n_tt_colon, next_tt_colon;
        "::", [is_colon, is_colon], peek_tt_path_sep, peek_n_tt_path_sep, next_tt_path_sep;
        "->", [is_minus, is_greater_than], peek_tt_r_arrow, peek_n_tt_r_arrow, next_tt_r_arrow;
        "=>", [is_equals, is_greater_than], peek_tt_fat_arrow, peek_n_tt_fat_arrow, next_tt_fat_arrow;
        "#", [is_pound], peek_tt_pound, peek_n_tt_pound, next_tt_pound;
        "$", [is_dollar], peek_tt_dollar, peek_n_tt_dollar, next_tt_dollar;
        "?", [is_question], peek_tt_question, peek_n_tt_question, next_tt_question;
        "~", [is_tilde], peek_tt_tilde, peek_n_tt_tilde, next_tt_tilde;
    );

    /// Returns the next token if it is a [punctuation token tree](https://doc.rust-lang.org/reference/tokens.html#punctuation) following the same rules as [macro_rule's `tt`](https://doc.rust-lang.org/reference/macros-by-example.html#metavariables).
    ///
    /// ```
    /// use proc_macro_utils::{assert_tokens, TokenParser};
    /// use quote::quote;
    /// let mut parser = TokenParser::new(quote!(.. =. 1 b));
    /// assert_tokens!(parser.next_macro_rules_tt().unwrap(), { .. });
    /// assert_tokens!(parser.next_macro_rules_tt().unwrap(), { = });
    /// assert_tokens!(parser, { . 1 b });
    /// ```
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn next_macro_rules_tt(&mut self) -> Option<TokenStream> {
        // ensure that the next 3 tokens are peeked if possible
        _ = self.peek_n(2);
        let first = self.peek.first().and_then(TokenTree::punct)?;
        let second = first
            .is_joint()
            .then(|| self.peek.get(1).and_then(TokenTree::punct))
            .flatten();
        let third = second
            .is_some_and(TokenTreePunct::is_joint)
            .then(|| self.peek.get(2).and_then(TokenTree::punct))
            .flatten();
        let chars = [
            first.as_char(),
            second.map_or('_', Punct::as_char),
            third.map_or('_', Punct::as_char),
        ];
        if matches!(
            chars,
            ['.', '.', '.' | '='] | ['<', '<', '='] | ['>', '>', '=']
        ) {
            self.next_n_alone(3)
        } else if matches!(
            &chars[0..2],
            ['&', '&' | '=']
                | ['|', '|' | '=']
                | ['<', '<' | '=']
                | ['>' | '-' | '=', '>']
                | ['+' | '-' | '*' | '/' | '%' | '^' | '=' | '!' | '>', '=']
                | ['.', '.']
                | [':', ':']
        ) {
            self.next_n_alone(2)
        } else {
            self.next_n_alone(1)
        }
    }
}

#[cfg(test)]
mod test {
    use quote::quote;

    use super::*;
    use crate::assert_tokens;

    #[test]
    fn ty() {
        let mut at = TokenParser::new(quote! {Name, <Some, Generic, Type>});
        assert_tokens!(at.next_type().unwrap(), { Name });
        at.next();
        assert_tokens!(
            at.next_type().unwrap(),
            { < Some , Generic , Type > }
        );
    }

    #[test]
    fn expr() {
        let mut at = TokenParser::new(
            quote! {a + b, <Some, Generic, Type>::something + <a,b> * a < b, "hi" => hello},
        );
        assert_tokens!(at.next_expression().unwrap(), { a + b });
        at.next();
        assert_tokens!(
            at.next_expression().unwrap(), { <Some, Generic, Type>::something + <a,b> * a < b }
        );
        at.next();
        assert_tokens!(at.next_expression().unwrap(), { "hi" });
        at.next();
        at.next();
        assert_tokens!(at.next_expression().unwrap(), { hello });

        let mut at = TokenParser::from_str("1..,").unwrap();
        let expr: Vec<_> = at.next_expression().unwrap().into_iter().collect();
        assert!(expr.last().unwrap().is_alone());
        assert_tokens!(expr, { 1.. });
    }

    #[test]
    fn combined_tokens() {
        // using from_str to be able to verify behavior of splitting the input correctly
        // into tts
        let mut parser = TokenParser::from_str("->&&..=>=+,-..,+=").unwrap();
        assert_tokens!(parser.next_tt_r_arrow().unwrap(), { -> });
        assert_tokens!(parser.next_tt_and_and().unwrap(), { && });
        assert_tokens!(parser.next_tt_dot_dot_eq().unwrap(), { ..= });
        assert_tokens!(parser.next_tt_ge().unwrap(), { >= });
        assert_tokens!(parser.next_tt_plus().unwrap(), { + });
        assert_tokens!(parser.next_tt_comma().unwrap(), { , });
        assert_tokens!(parser.next_tt_minus().unwrap(), { - });
        assert_tokens!(parser.next_tt_dot_dot().unwrap(), { .. });
        assert_tokens!(parser.next_tt_comma().unwrap(), { , });
        assert_tokens!(parser.next_tt_plus_eq().unwrap(), { += });
    }

    #[test]
    fn peek() {
        let mut parser = TokenParser::new(quote! {
            0 {} 2 3 += .. =
        });
        assert_eq!(parser.peek().unwrap().to_string(), "0");
        assert_eq!(parser.peek_n(0).unwrap().to_string(), "0");
        assert_eq!(parser.peek_n(1).unwrap().to_string().replace(' ', ""), "{}");
        assert_eq!(parser.peek_n(2).unwrap().to_string(), "2");

        assert_eq!(parser.peek_literal().unwrap().to_string(), "0");
        assert!(parser.peek_group().is_none());
        parser.next().unwrap();
        assert!(parser.peek_group().is_some());
        assert!(parser.peek_n_tt_plus_eq(3).is_some());
        assert!(parser.peek_n_tt_dot_dot(5).is_some());
    }

    #[test]
    fn keyword() {
        let mut parser: TokenParser<_, 4> = TokenParser::from(quote! {
            in out and or
        });
        assert_eq!(parser.next_keyword("in").unwrap().to_string(), "in");
        assert_eq!(parser.next_keyword("out").unwrap().to_string(), "out");
        assert!(parser.next_keyword("or").is_none());
        assert_eq!(parser.next_keyword("and").unwrap().to_string(), "and");
        assert_eq!(parser.next_keyword("or").unwrap().to_string(), "or");
        assert!(parser.next_keyword("or").is_none());
    }
}
