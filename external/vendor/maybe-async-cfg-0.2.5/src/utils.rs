use proc_macro2::{Span, TokenStream as TokenStream2};
use syn::{
    parenthesized,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    token::Comma,
    Expr,
    Ident,
    Meta,
    NestedMeta,
    Token,
};

use quote::ToTokens;

////////////////////////////////////////////////////////////////////////////////////////////////////

pub(crate) fn make_path(name: &str) -> syn::Path {
    let mut segments = Punctuated::<syn::PathSegment, syn::token::Colon2>::new();
    segments.push_value(syn::PathSegment {
        ident: Ident::new(name, Span::call_site()),
        arguments: syn::PathArguments::None,
    });

    syn::Path {
        leading_colon: None,
        segments,
    }
}

pub(crate) fn make_nestedmeta_namevalue(name: &str, value: &str) -> syn::NestedMeta {
    NestedMeta::Meta(Meta::NameValue(syn::MetaNameValue {
        path: make_path(name),
        eq_token: Token![=](Span::call_site()),
        lit: syn::Lit::Str(syn::LitStr::new(value, Span::call_site())),
    }))
}

pub(crate) fn make_nestedmeta_list(
    name: &str,
    nested: Punctuated<NestedMeta, syn::token::Comma>,
) -> syn::NestedMeta {
    NestedMeta::Meta(Meta::List(syn::MetaList {
        path: make_path(name),
        paren_token: syn::token::Paren(proc_macro2::Span::call_site()),
        nested,
    }))
}

pub(crate) fn make_attr_from_str<S: AsRef<str>>(s: S, span: Span) -> syn::Result<syn::Attribute> {
    let stream: TokenStream2 = format!("#[{}]", s.as_ref()).parse()?;
    let mut attrs: VecOfAttrs = syn::parse(stream.into())?;
    let attr = match attrs.attrs.len() {
        1 => attrs.attrs.remove(0),
        _ => return Err(syn::Error::new(span, "Expected attribute")),
    };

    Ok(attr)
}

pub(crate) fn make_attr_ts_from_str<S: AsRef<str>>(s: S, span: Span) -> syn::Result<TokenStream2> {
    Ok(make_attr_from_str(s, span)?.to_token_stream())
}

////////////////////////////////////////////////////////////////////////////////////////////////////

struct VecOfAttrs {
    pub attrs: Vec<syn::Attribute>,
}

impl syn::parse::Parse for VecOfAttrs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(VecOfAttrs {
            attrs: input.call(syn::Attribute::parse_outer)?,
        })
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct AttributeArgsInParens {
    _paren: syn::token::Paren,
    pub args: Punctuated<NestedMeta, Token![,]>,
}

impl syn::parse::Parse for AttributeArgsInParens {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        Ok(Self {
            _paren: parenthesized!(content in input),
            args: content.parse_terminated(NestedMeta::parse)?,
        })
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct PunctuatedList {
    pub list: Punctuated<Expr, Comma>,
}

impl Parse for PunctuatedList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(PunctuatedList {
            list: Punctuated::<Expr, Comma>::parse_terminated(input)?,
        })
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct DebugByDisplay<T: std::fmt::Display>(pub T);

impl<T: std::fmt::Display> std::fmt::Debug for DebugByDisplay<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(&self.0, f)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct OptionToTokens<T: ToTokens>(pub Option<T>);

impl<T: ToTokens> std::fmt::Debug for OptionToTokens<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {    
        self.0.as_ref().map(|m| DebugByDisplay(m.to_token_stream())).fmt(f)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct EqStr {
    #[allow(dead_code)]
    pub eq: Token![=],
    pub str: syn::LitStr,
}

impl Parse for EqStr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(EqStr {
            eq: input.parse()?,
            str: input.parse()?,
        })
    }
}

