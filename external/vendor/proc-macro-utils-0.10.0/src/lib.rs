//! Some useful functions on [`proc_macro`] and [`proc_macro2`] types
//!
//! E.g. [pushing tokens onto `TokenStream`](TokenStreamExt::push) and [testing
//! for specific punctuation on `TokenTree` and `Punct`](TokenTreePunct)
//!
//! It also adds the [`assert_tokens!`] and [`assert_expansion!`] macros to
//! improve unit testability for `proc-macros`.
#![warn(clippy::pedantic, missing_docs)]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![deny(rustdoc::all)]

#[cfg(doc)]
use proc_macro2::{Punct, Spacing};

#[cfg(feature = "proc-macro")]
extern crate proc_macro;

/// Parsing of simple rust structures without syn
#[cfg(feature = "parser")]
mod parser;
#[cfg(feature = "parser")]
pub use parser::TokenParser;

#[cfg(feature = "parser")]
#[macro_use]
mod assert;

#[cfg(feature = "parser")]
#[doc(hidden)]
pub mod __private;

mod sealed {
    pub trait Sealed {}

    macro_rules! sealed {
        [$($ty:ident),* $(,)?] => {$(
            impl Sealed for proc_macro::$ty {}
            impl Sealed for proc_macro2::$ty {}
        )*};
    }

    sealed![TokenStream, TokenTree, Punct, Literal, Group];
}

macro_rules! once {
    (($($tts:tt)*) $($tail:tt)*) => {
        $($tts)*
    };
}

macro_rules! attr {
    (($($attr:tt)*), $($item:tt)+) => {
        $(#$attr)* $($item)+
    };
}

macro_rules! trait_def {
    ($item_attr:tt, $trait:ident, $($fn_attr:tt, $fn:ident, $({$($gen:tt)*})?, $args:tt, $($ret:ty)?),*) => {
        attr!($item_attr,
        pub trait $trait: crate::sealed::Sealed {
            $(attr!($fn_attr, fn $fn $($($gen)*)? $args $(-> $ret)?;);)*
        });
    };
}

macro_rules! trait_impl {
    ($trait:ident, $type:ident, $($fn_attr:tt, $fn:ident, $({$($gen:tt)*})?, $args:tt, $($ret:ty)?, $stmts:tt),*) => {
        impl $trait for $type {
            $(attr!($fn_attr, fn $fn $($($gen)*)? $args $(-> $ret)? $stmts);)*
        }
    };
}

macro_rules! impl_via_trait {
    ($(
        $(#$trait_attr:tt)*
        impl $trait:ident for $type:ident {
            $($(#$fn_attr:tt)*
            fn $fn:ident $({$($gen:tt)*})? ($($args:tt)*)  $(-> $ret:ty)? { $($stmts:tt)* })*
        }
    )+) => {
        once!($((trait_def!(($($trait_attr)*), $trait, $(($($fn_attr)*), $fn,$({$($gen)*})?, ($($args)*), $($ret)?),*);))+);
        #[cfg(feature = "proc-macro")]
        const _: () = {
            use proc_macro::*;
            $(trait_impl!($trait, $type, $(($($fn_attr)*), $fn, $({$($gen)*})?, ($($args)*), $($ret)?, {$($stmts)*}),*);)+
        };
        #[cfg(feature = "proc-macro2")]
        const _:() = {
            use proc_macro2::*;
            $(trait_impl!($trait, $type, $(($($fn_attr)*), $fn, $({$($gen)*})?, ($($args)*), $($ret)?, {$($stmts)*}),*);)+
        };
    };
    (
        mod $mod:ident, $mod2:ident {
            $(
                $(#$trait_attr:tt)*
                impl $trait:ident$($doc:literal)?, $trait2:ident$($doc2:literal)?  for $type:ident {
                    $($(#$fn_attr:tt)*
                    fn $fn:ident $({$($gen:tt)*})? ($($args:tt)*) $(-> $ret:ty)? { $($stmts:tt)* })*
                }
            )+
        }
    ) => {
        #[cfg(feature = "proc-macro")]
        once!(($(pub use $mod::$trait;)+));
        #[cfg(feature = "proc-macro")]
        mod $mod {
            use proc_macro::*;
            once!($((trait_def!(($($trait_attr)* $([doc=$doc])?), $trait, $(($($fn_attr)*), $fn, $({$($gen)*})?, ($($args)*), $($ret)?),*);))+);
            $(trait_impl!($trait, $type, $(($($fn_attr)*), $fn, $({$($gen)*})?, ($($args)*), $($ret)?, {$($stmts)*}),*);)+
        }
        #[cfg(feature = "proc-macro2")]
        once!(($(pub use $mod2::$trait2;)+));
        #[cfg(feature = "proc-macro2")]
        mod $mod2 {
            use proc_macro2::*;
            once!($((trait_def!(($($trait_attr)*$([doc=$doc2])?), $trait2, $(($($fn_attr)*), $fn, $({$($gen)*})?, ($($args)*), $($ret)?),*);))+);
            $(trait_impl!($trait2, $type, $(($($fn_attr)*), $fn, $({$($gen)*})?, ($($args)*), $($ret)?, {$($stmts)*}),*);)+
        }
    };
}

impl_via_trait! {
    mod token_stream_ext, token_stream2_ext {
        /// Generic extensions for
        impl TokenStreamExt "[`proc_macro::TokenStream`]", TokenStream2Ext "[`proc_macro2::TokenStream`]" for TokenStream {
            /// Pushes a single [`TokenTree`] onto the token stream.
            fn push(&mut self, token: TokenTree) {
                self.extend(std::iter::once(token))
            }
            /// Creates a [`TokenParser`](crate::TokenParser) from this token stream.
            #[cfg(feature = "parser")]
            fn parser(self) -> crate::TokenParser<proc_macro2::token_stream::IntoIter> {
                #[allow(clippy::useless_conversion)]
                proc_macro2::TokenStream::from(self).into()
            }

            /// Creates a [`TokenParser`](crate::TokenParser) from this token stream.
            ///
            /// Allows to specify the length of the [peeker buffer](crate::TokenParser#peeking).
            #[cfg(feature = "parser")]
            fn parser_generic{<const PEEKER_LEN: usize>}(self) -> crate::TokenParser<proc_macro2::token_stream::IntoIter, PEEKER_LEN> {
                #[allow(clippy::useless_conversion)]
                proc_macro2::TokenStream::from(self).into()
            }
        }
    }
}

macro_rules! token_tree_ext {
    ($($a:literal, $token:literal, $is:ident, $as:ident, $into:ident, $variant:ident);+$(;)?) => {
        impl_via_trait! {
            mod token_tree_ext, token_tree2_ext {
                /// Generic extensions for
                impl TokenTreeExt "[`proc_macro::TokenTree`]", TokenTree2Ext "[`proc_macro2::TokenTree`]"  for TokenTree {
                    $(
                        #[doc = concat!("Tests if the token tree is ", $a, " ", $token, ".")]
                        #[must_use]
                        fn $is(&self) -> bool {
                            matches!(self, Self::$variant(_))
                        }
                        #[doc = concat!("Get the [`", stringify!($variant), "`] inside this token tree, or [`None`] if it isn't ", $a, " ", $token, ".")]
                        #[must_use]
                        fn $as(&self) -> Option<&$variant> {
                            if let Self::$variant(inner) = &self {
                                Some(inner)
                            } else {
                                None
                            }
                        }
                        #[doc = concat!("Get the [`", stringify!($variant), "`] inside this token tree, or [`None`] if it isn't ", $a, " ", $token, ".")]
                        #[must_use]
                        fn $into(self) -> Option<$variant> {
                            if let Self::$variant(inner) = self {
                                Some(inner)
                            } else {
                                None
                            }
                        }
                    )*
                }
            }
        }
    };
}

token_tree_ext!(
    "a", "group", is_group, group, into_group, Group;
    "an", "ident", is_ident, ident, into_ident, Ident;
    "a", "punctuation", is_punct, punct, into_punct, Punct;
    "a", "literal", is_literal, literal, into_literal, Literal;
);

macro_rules! punctuations {
    ($($char:literal as $name:ident),*) => {
        impl_via_trait!{
            /// Trait to test for punctuation
            impl TokenTreePunct for TokenTree {
                $(#[doc = concat!("Tests if the token is `", $char, "`")]
                #[must_use]
                fn $name(&self) -> bool {
                    matches!(self, TokenTree::Punct(punct) if punct.$name())
                })*
                /// Tests if token is followed by some none punctuation token or whitespace.
                #[must_use]
                fn is_alone(&self) -> bool {
                    matches!(self, TokenTree::Punct(punct) if punct.is_alone())
                }
                /// Tests if token is followed by another punct and can potentially be combined into
                /// a multi-character operator.
                #[must_use]
                fn is_joint(&self) -> bool {
                    matches!(self, TokenTree::Punct(punct) if punct.is_joint())
                }
                /// If sets the [`spacing`](Punct::spacing) of a punct to [`Alone`](Spacing::Alone).
                #[must_use]
                fn alone(self) -> Self {
                    match self {
                        Self::Punct(p) => Self::Punct(p.alone()),
                        it => it
                    }
                }
            }
            impl TokenTreePunct for Punct {
                $(fn $name(&self) -> bool {
                    self.as_char() == $char
                })*
                fn is_alone(&self) -> bool {
                    self.spacing() == Spacing::Alone
                }
                fn is_joint(&self) -> bool {
                    self.spacing() == Spacing::Joint
                }
                fn alone(self) -> Self {
                    if self.is_alone() {
                        self
                    } else {
                        let mut this = Punct::new(self.as_char(), Spacing::Alone);
                        this.set_span(self.span());
                        this
                    }
                }
            }
        }
    };
}

punctuations![
    '=' as is_equals,
    '<' as is_less_than,
    '>' as is_greater_than,
    '!' as is_exclamation,
    '~' as is_tilde,
    '+' as is_plus,
    '-' as is_minus,
    '*' as is_asterix, // TODO naming
    '/' as is_slash,
    '%' as is_percent,
    '^' as is_caret,
    '&' as is_and,
    '|' as is_pipe,
    '@' as is_at,
    '.' as is_dot,
    ',' as is_comma,
    ';' as is_semi,
    ':' as is_colon,
    '#' as is_pound,
    '$' as is_dollar,
    '?' as is_question,
    '\'' as is_quote // TODO naming
];

macro_rules! delimited {
    ($($delimiter:ident as $name:ident : $doc:literal),*) => {
        impl_via_trait!{
            /// Trait to test for delimiters of groups
            impl Delimited for TokenTree {
                $(#[doc = concat!("Tests if the token is a group with ", $doc)]
                #[must_use]
                fn $name(&self) -> bool {
                    matches!(self, TokenTree::Group(group) if group.$name())
                })*
            }
            impl Delimited for Group {
                $(#[doc = concat!("Tests if a group has ", $doc)]
                #[must_use]
                fn $name(&self) -> bool {
                    matches!(self.delimiter(), Delimiter::$delimiter)
                })*
            }
        }
    };
}

delimited![
    Parenthesis as is_parenthesized: " parentheses (`( ... )`)",
    Brace as is_braced: " braces (`{ ... }`)",
    Bracket as is_bracketed: " brackets (`[ ... ]`)",
    None as is_implicitly_delimited: " no delimiters (`Ø ... Ø`)"
];

impl_via_trait! {
    /// Trait to parse literals
    impl TokenTreeLiteral for TokenTree {
        /// Tests if the token is a string literal.
        #[must_use]
        fn is_string(&self) -> bool {
            self.literal().is_some_and(TokenTreeLiteral::is_string)
        }

        /// Returns the string contents if it is a string literal.
        #[must_use]
        fn string(&self) -> Option<String> {
            self.literal().and_then(TokenTreeLiteral::string)
        }
    }

    impl TokenTreeLiteral for Literal {
        fn is_string(&self) -> bool {
            let s = self.to_string();
            s.starts_with('"') || s.starts_with("r\"") || s.starts_with("r#")
        }
        fn string(&self) -> Option<String> {
            let lit = self.to_string();
            if lit.starts_with('"') {
                Some(resolve_escapes(&lit[1..lit.len() - 1]))
            } else if lit.starts_with('r') {
                let pounds = lit.chars().skip(1).take_while(|&c| c == '#').count();
                Some(lit[2 + pounds..lit.len() - pounds - 1].to_owned())
            } else {
                None
            }
        }
    }
}

// Implemented following https://doc.rust-lang.org/reference/tokens.html#string-literals
// #[allow(clippy::needless_continue)]
fn resolve_escapes(mut s: &str) -> String {
    let mut out = String::new();
    while !s.is_empty() {
        if s.starts_with('\\') {
            match s.as_bytes()[1] {
                b'x' => {
                    out.push(
                        char::from_u32(u32::from_str_radix(&s[2..=3], 16).expect("valid escape"))
                            .expect("valid escape"),
                    );
                    s = &s[4..];
                }
                b'u' => {
                    let len = s[3..].find('}').expect("valid escape");
                    out.push(
                        char::from_u32(u32::from_str_radix(&s[3..len], 16).expect("valid escape"))
                            .expect("valid escape"),
                    );
                    s = &s[3 + len..];
                }
                b'n' => {
                    out.push('\n');
                    s = &s[2..];
                }
                b'r' => {
                    out.push('\r');
                    s = &s[2..];
                }
                b't' => {
                    out.push('\t');
                    s = &s[2..];
                }
                b'\\' => {
                    out.push('\\');
                    s = &s[2..];
                }
                b'0' => {
                    out.push('\0');
                    s = &s[2..];
                }
                b'\'' => {
                    out.push('\'');
                    s = &s[2..];
                }
                b'"' => {
                    out.push('"');
                    s = &s[2..];
                }
                b'\n' => {
                    s = &s[..s[2..]
                        .find(|c: char| !c.is_ascii_whitespace())
                        .unwrap_or(s.len())];
                }
                c => unreachable!(
                    "TokenStream string literals should only contain valid escapes, found `\\{c}`"
                ),
            }
        } else {
            let len = s.find('\\').unwrap_or(s.len());
            out.push_str(&s[..len]);
            s = &s[len..];
        }
    }
    out
}

#[cfg(all(test, feature = "proc-macro2"))]
mod test {
    use proc_macro2::{Punct, Spacing, TokenTree};
    use quote::quote;

    use super::*;

    #[test]
    fn punctuation() {
        let mut tokens = quote! {=<>!$~+-*/%^|@.,;:#$?'a}.into_iter();
        assert!(tokens.next().unwrap().is_equals());
        assert!(tokens.next().unwrap().is_less_than());
        assert!(tokens.next().unwrap().is_greater_than());
        assert!(tokens.next().unwrap().is_exclamation());
        assert!(tokens.next().unwrap().is_dollar());
        assert!(tokens.next().unwrap().is_tilde());
        assert!(tokens.next().unwrap().is_plus());
        assert!(tokens.next().unwrap().is_minus());
        assert!(tokens.next().unwrap().is_asterix());
        assert!(tokens.next().unwrap().is_slash());
        assert!(tokens.next().unwrap().is_percent());
        assert!(tokens.next().unwrap().is_caret());
        assert!(tokens.next().unwrap().is_pipe());
        assert!(tokens.next().unwrap().is_at());
        assert!(tokens.next().unwrap().is_dot());
        assert!(tokens.next().unwrap().is_comma());
        assert!(tokens.next().unwrap().is_semi());
        assert!(tokens.next().unwrap().is_colon());
        assert!(tokens.next().unwrap().is_pound());
        assert!(tokens.next().unwrap().is_dollar());
        assert!(tokens.next().unwrap().is_question());
        assert!(tokens.next().unwrap().is_quote());
    }

    #[test]
    fn token_stream_ext() {
        let mut tokens = quote!(a);
        tokens.push(TokenTree::Punct(Punct::new(',', Spacing::Alone)));
        assert_eq!(tokens.to_string(), "a ,");
    }

    #[test]
    fn token_tree_ext() {
        let mut tokens = quote!({group} ident + "literal").into_iter().peekable();
        assert!(tokens.peek().unwrap().is_group());
        assert!(matches!(
            tokens.next().unwrap().group().unwrap().to_string().as_str(),
            "{ group }" | "{group}"
        ));
        assert!(tokens.peek().unwrap().is_ident());
        assert_eq!(tokens.next().unwrap().ident().unwrap().to_string(), "ident");
        assert!(tokens.peek().unwrap().is_punct());
        assert_eq!(tokens.next().unwrap().punct().unwrap().to_string(), "+");
        assert!(tokens.peek().unwrap().is_literal());
        assert_eq!(
            tokens.next().unwrap().literal().unwrap().to_string(),
            "\"literal\""
        );
    }

    #[test]
    fn test() {}
}
