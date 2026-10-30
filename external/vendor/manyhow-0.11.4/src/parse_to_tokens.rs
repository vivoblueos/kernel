#![allow(missing_docs, clippy::pedantic)]
use std::convert::Infallible;
use std::marker::PhantomData;

use proc_macro2::TokenStream;

use crate::{
    AnyTokenStream, AttributeMacroHandler, DeriveMacroHandler, Emitter, FunctionMacroHandler,
    ToTokensError,
};
pub trait ManyhowParse<T> {
    fn manyhow_parse(&self, input: impl AnyTokenStream, attr: bool) -> Result<T, TokenStream>;
}
pub trait ManyhowToTokens<T> {
    fn manyhow_to_tokens(&self, input: T, tokens: &mut TokenStream);
}
pub trait ManyhowTry<T> {
    type Ok;
    type Err;
    fn manyhow_try(&self, value: T) -> Result<Self::Ok, Self::Err>;
}

pub struct WhatType<T>(PhantomData<T>);

impl<T> WhatType<T> {
    /// Always panics
    pub fn identify(&self) -> Result<T, TokenStream> {
        unimplemented!("DON'T YOU DARE CALL ME")
    }

    pub fn from(_ty: &T) -> Self {
        Self(PhantomData)
    }

    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<T> Clone for WhatType<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for WhatType<T> {}

impl<T: Into<TokenStream> + From<TokenStream>> ManyhowParse<T> for WhatType<T> {
    fn manyhow_parse(&self, input: impl AnyTokenStream, _attr: bool) -> Result<T, TokenStream> {
        Ok(input.into().into())
    }
}

impl ManyhowToTokens<TokenStream> for WhatType<TokenStream> {
    fn manyhow_to_tokens(&self, input: TokenStream, tokens: &mut TokenStream) {
        tokens.extend(input);
    }
}

impl ManyhowToTokens<proc_macro::TokenStream> for WhatType<proc_macro::TokenStream> {
    fn manyhow_to_tokens(&self, input: proc_macro::TokenStream, tokens: &mut TokenStream) {
        tokens.extend(TokenStream::from(input));
    }
}

impl<E: ToTokensError> ManyhowToTokens<E> for WhatType<E> {
    fn manyhow_to_tokens(&self, input: E, tokens: &mut TokenStream) {
        input.to_tokens(tokens);
    }
}

impl<T, E> ManyhowTry<Result<T, E>> for WhatType<Result<T, E>> {
    type Err = E;
    type Ok = T;

    fn manyhow_try(&self, value: Result<T, E>) -> Result<Self::Ok, Self::Err> {
        value
    }
}

impl<T> ManyhowTry<T> for &WhatType<T> {
    type Err = Infallible;
    type Ok = T;

    fn manyhow_try(&self, value: T) -> Result<Self::Ok, Self::Err> {
        Ok(value)
    }
}

#[cfg(feature = "syn2")]
impl<T: syn2::parse::Parse> ManyhowParse<T> for &WhatType<T> {
    fn manyhow_parse(&self, input: impl AnyTokenStream, attr: bool) -> Result<T, TokenStream> {
        let input = input.into();
        let empty = input.is_empty();
        syn2::parse2(input).map_err(|e| {
            let mut e = e.into_compile_error();
            if attr && empty {
                error_message!("while parsing attribute argument (`#[... (...)]`)")
                    .to_tokens(&mut e)
            }
            e
        })
    }
}
#[cfg(feature = "syn2")]
impl<T: quote::ToTokens> ManyhowToTokens<T> for &WhatType<T> {
    fn manyhow_to_tokens(&self, input: T, tokens: &mut TokenStream) {
        input.to_tokens(tokens);
    }
}

#[cfg(feature = "syn2")]
#[test]
#[allow(unused)]
fn test_inference() {
    use syn2::parse::Parse;

    if false {
        let wt = &WhatType::new();
        let ts: proc_macro::TokenStream = wt.manyhow_parse(quote::quote!(test), false).unwrap();
        let wt = &WhatType::new();
        if false {
            let wt: Result<syn2::Ident, _> = wt.identify();
        }
        let ts: syn2::Ident = wt.manyhow_parse(quote::quote!(test), false).unwrap();

        struct Parsable;
        impl Parse for Parsable {
            fn parse(input: syn2::parse::ParseStream) -> syn2::Result<Self> {
                todo!()
            }
        }
        let wt = &WhatType::new();
        let _: Result<Parsable, _> = wt.identify();
        let ts = wt.manyhow_parse(quote::quote!(test), false).unwrap();
    }
}

macro_rules! transparent_handlers {
    ($name:ident; $MacroInput:ident; $($input:ident: $Input:ident $($context:expr)?),*; $($dummy:ident)?) => {
        /// Internal implementation for macro.
        pub fn $name<$($Input,)* Dummy: AnyTokenStream, Output, Function,>(
            $($input: Result<$Input, TokenStream>,)*
            $($dummy: Option<impl AnyTokenStream>,)?
            body: impl $MacroInput<Function, $($Input = $Input,)* Dummy = Dummy, Output = Output>,
        ) -> Result<(Output, TokenStream, TokenStream), TokenStream> {
            // use $crate::ToTokensError as _;
            #[allow(unused)]
            let mut dummy = TokenStream::new();
            $(let mut dummy = $dummy.unwrap_or_default().into();)?
            $(let $input = match $input {
                Ok($input) => $input,
                Err(tokens) => {
                    dummy.extend(tokens);
                    $($crate::error_message!($context).to_tokens(&mut dummy);)?
                    return Err(dummy);
                }
            };)*
            let mut dummy = dummy.into();
            let mut emitter = Emitter::new();
            let output = body.call($($input,)+ &mut dummy, &mut emitter);
            let mut tokens = TokenStream::new();
            emitter.to_tokens(&mut tokens);
            Ok((output, tokens, dummy.into()))
        }
    };
}

transparent_handlers! { function_transparent; FunctionMacroHandler; input: Input; dummy }
transparent_handlers! { derive_transparent; DeriveMacroHandler; item: Item;}
transparent_handlers! { attribute_transparent; AttributeMacroHandler; input: Input, item: Item; dummy }
