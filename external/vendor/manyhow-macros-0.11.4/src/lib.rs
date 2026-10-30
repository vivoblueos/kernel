use std::fmt::{Display, Write};
use std::mem;

use proc_macro2::{Group, Ident, Span, TokenStream, TokenTree};
use proc_macro_utils::{Delimited, TokenStream2Ext, TokenStreamExt, TokenTree2Ext, TokenTreePunct};
use quote::{format_ident, quote, quote_spanned, ToTokens};

#[derive(PartialEq, Eq, Clone, Copy)]
enum ProcMacroType {
    Function,
    Derive,
    Attribute,
}
impl ProcMacroType {
    fn to_signature(self, tokens: &mut TokenStream) {
        match self {
            ProcMacroType::Function | ProcMacroType::Derive => quote! {
                (__input: ::proc_macro::TokenStream) -> ::proc_macro::TokenStream
            },
            ProcMacroType::Attribute => quote! {
                (__input: ::proc_macro::TokenStream, __item: ::proc_macro::TokenStream) -> ::proc_macro::TokenStream
            },
        }
        .to_tokens(tokens)
    }

    fn dummy_flag(self) -> &'static str {
        match self {
            ProcMacroType::Function => "input_as_dummy",
            ProcMacroType::Derive => "",
            ProcMacroType::Attribute => "item_as_dummy",
        }
    }
}
impl ProcMacroType {
    fn to_tokens(self, impl_path: TokenStream, as_dummy: bool) -> TokenStream {
        let mut as_dummy = if as_dummy {
            quote!(#[as_dummy])
        } else {
            quote!()
        };

        let fn_name = match self {
            ProcMacroType::Function => quote!(function),
            ProcMacroType::Derive => quote!(derive),
            ProcMacroType::Attribute => quote!(attribute),
        };

        let item = if self == ProcMacroType::Attribute {
            let as_dummy = mem::take(&mut as_dummy);
            quote!(, #as_dummy __item)
        } else {
            quote!()
        };
        quote! {
            ::manyhow::#fn_name!(#as_dummy __input #item, #impl_path)
        }
    }
}

enum Param {
    Flag(Ident),
    Complex(Ident, Group),
}

impl Param {
    fn span(&self) -> Span {
        self.ident().span()
    }

    fn ident(&self) -> &Ident {
        let (Param::Flag(ident) | Param::Complex(ident, _)) = self;
        ident
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Param::Flag(ident) => ident.fmt(f),
            Param::Complex(ident, tokens) => ident.fmt(f).and(tokens.fmt(f)),
        }
    }
}

/// Attribute macro to remove boilerplate from proc macro entry points.
///
/// See [the documentation at the crate root for more
/// details](https://docs.rs/manyhow#using-the-manyhow-macro).
#[proc_macro_attribute]
pub fn manyhow(
    input: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let mut parser = item.clone().parser();
    let mut output = TokenStream::default();

    // For now, we will keep all attributes on the outer function
    let mut kind = None;
    let mut kind_attribute = None;
    let mut set_kind = |ident: &Ident, create_attribute: bool| {
        let new_kind = match ident.to_string().as_str() {
            "proc_macro" => ProcMacroType::Function,
            "proc_macro_attribute" => ProcMacroType::Attribute,
            "proc_macro_derive" => ProcMacroType::Derive,
            _ => return Ok(()),
        };
        if let Some((_, span)) = kind {
            Err(with_helpful_error(
                with_helpful_error(
                    item.clone(),
                    span,
                    "proc_macro kind specified multiple times",
                    "try removing this",
                ),
                ident.span(),
                "proc_macro kind specified multiple times",
                "try removing this",
            ))
        } else {
            kind = Some((new_kind, ident.span()));
            if create_attribute {
                kind_attribute = Some(quote!(#[#ident]));
            }
            Ok(())
        }
    };
    while let Some(pound) = parser.next_tt_pound() {
        output.extend(pound);
        let attribute_content = parser
            .next_bracketed()
            .expect("rust should only allow valid attributes");
        let ident = attribute_content
            .stream()
            .parser()
            .next_ident()
            .expect("rust should only allow valid attributes");
        output.push(attribute_content.into());
        if let Err(err) = set_kind(&ident, false) {
            return err;
        }
    }

    let mut flags = Vec::new();
    let mut input = input.parser();
    while !input.is_empty() {
        let Some(ident) = input.next_ident() else {
            return with_helpful_error(
                item,
                input.next().unwrap().span(),
                "manyhow expects a comma seperated list of flags",
                format_args!("try `#[manyhow(impl_fn)]`"),
            );
        };
        if ident == "proc_macro_derive" {
            let Some(group) = input.next_group() else {
                return with_helpful_error(
                    item,
                    input.next().unwrap_or(ident.into()).span(),
                    "`proc_macro_derive` expects `(TraitName)`",
                    format_args!("try `#[manyhow(proc_macro_derive(YourTraitName))]`"),
                );
            };
            // We set it manually here
            if let Err(error) = set_kind(&ident, false) {
                return error;
            }
            quote!(#[#ident #group]).to_tokens(&mut output);
            flags.push(Param::Complex(ident, group));
        } else {
            if let Err(error) = set_kind(&ident, true) {
                return error;
            }
            flags.push(Param::Flag(ident));
        }
        // This technically allows `flag flag flag` but it's fine IMO
        _ = input.next_tt_comma();
    }

    output.extend(kind_attribute);

    let Some((kind, _)) = kind else {
        return with_helpful_error(
            item,
            Span::call_site(),
            "expected proc_macro* attribute below `#[manyhow]` or a flag as parameter of the \
             attribute",
            "try adding `#[proc_macro]`, `#[proc_macro_attribute]`, or `#[proc_macro_derive]` \
             below `#[manyhow]` or adding a flag to `#[manyhow]`, i.e., `#[manyhow(proc_macro)]`, \
             `#[manyhow(proc_macro_attribute)]` or `#[manyhow(proc_macro_derive)]` ",
        );
    };

    let flags_replace = |i: usize, replacement: Option<&str>| {
        let mut flags = flags.iter().map(ToString::to_string).collect::<Vec<_>>();
        if let Some(replacement) = replacement {
            replacement.clone_into(&mut flags[i]);
        } else {
            flags.remove(i);
        }
        if flags.is_empty() {
            "".to_owned()
        } else {
            format!("({})", flags.join(", "))
        }
    };

    let mut as_dummy = false;
    let mut create_impl_fn = None;
    for (i, param) in flags.iter().enumerate() {
        let ident = param.ident();
        match (ident.to_string().as_str(), kind) {
            ("impl_fn", _) => create_impl_fn = Some((param.ident(), i)),
            ("item_as_dummy", ProcMacroType::Attribute) => as_dummy = true,
            ("item_as_dummy", ProcMacroType::Function) => {
                return with_helpful_error(
                    item,
                    param.span(),
                    format_args!(
                        "`item_as_dummy` is only supported with `#[proc_macro_attribute]`"
                    ),
                    format_args!(
                        "try `#[manyhow{}]` instead",
                        flags_replace(i, Some("input_as_dummy"))
                    ),
                );
            }
            ("input_as_dummy", ProcMacroType::Function) => as_dummy = true,
            ("input_as_dummy", ProcMacroType::Attribute) => {
                return with_helpful_error(
                    item,
                    param.span(),
                    format_args!("`input_as_dummy` is only supported with `#[proc_macro]`"),
                    format_args!(
                        "try `#[manyhow{}]` instead",
                        flags_replace(i, Some("item_as_dummy"))
                    ),
                );
            }
            ("input_as_dummy" | "item_as_dummy", ProcMacroType::Derive) => {
                return with_helpful_error(
                    item,
                    param.span(),
                    format_args!(
                        "only `#[proc_macro]` and `#[proc_macro_attribute]` support `*_as_dummy` \
                         flags"
                    ),
                    format_args!("try `#[manyhow{}]` instead", flags_replace(i, None)),
                );
            }
            ("proc_macro" | "proc_macro_attribute" | "proc_macro_derive", _) => {}
            _ => {
                return with_helpful_error(
                    item,
                    param.span(),
                    format_args!(
                        "only `proc_macro`, `proc_macro_attribute`, `proc_macro_derive`, `{}`, \
                         and `impl_fn` are supported",
                        kind.dummy_flag(),
                    ),
                    format_args!("try `#[manyhow{}]", flags_replace(i, None)),
                );
            }
        }
    }
    // All attributes are parsed now there should only be a public function

    // vis
    output.extend(parser.next_if(|tt| matches!(tt, TokenTree::Ident(ident) if ident == "pub")));

    let outer_impl_fn: Option<TokenStream>;
    let impl_fn_path: TokenStream;
    let inner_impl_fn: Option<TokenStream>;

    // we support both use and fn
    if parser.next_keyword("use").is_some() {
        if let Some((ident, i)) = create_impl_fn {
            return with_helpful_error(
                item,
                ident.span(),
                "`impl_fn` is not supported on use statements",
                format_args!("try `#[manyhow{}]", flags_replace(i, None)),
            );
        }

        let mut path = parser.collect::<Vec<_>>();
        assert!(
            path.pop().as_ref().is_some_and(TokenTreePunct::is_semi),
            "use statement should end with semi"
        );

        let fn_name = path
            .last()
            .expect("use statement should contain at least on item");

        let Some(mut fn_name) = fn_name.ident().cloned() else {
            return with_helpful_error(
                item,
                fn_name.span(),
                "only use statements for a single function, i.e., `use ...::fn_name;` are \
                 supported",
                "try splitting the use statment",
            );
        };

        fn_name.set_span(Span::call_site());

        quote!(fn #fn_name).to_tokens(&mut output);
        impl_fn_path = path.into_iter().collect();

        outer_impl_fn = None;
        inner_impl_fn = None;
    } else {
        // fn
        output.push(match parser.next() {
            Some(TokenTree::Ident(ident)) if ident == "fn" => ident.into(),
            token => {
                return with_error(
                    item,
                    token.as_ref().map_or_else(Span::call_site, TokenTree::span),
                    "expected function",
                );
            }
        });
        let Some(fn_name) = parser.next_ident() else {
            return with_error(
                item,
                parser
                    .next()
                    .as_ref()
                    .map_or_else(Span::call_site, TokenTree::span),
                "expected function name",
            );
        };
        // function name
        fn_name.to_tokens(&mut output);

        // there should not be any generics
        match parser.next_tt_lt() {
            None => {}
            Some(lt) => {
                return with_error(
                    item,
                    lt.into_iter().next().unwrap().span(),
                    "proc macros cannot have generics",
                );
            }
        }
        // (...)
        let params = parser.next_group().expect("params");
        // ->
        let Some(arrow) = parser.next_tt_r_arrow() else {
            return with_helpful_error(
                item,
                params.span_close(),
                "expected return type",
                "try adding either `-> TokenStream` or `-> manyhow::Result`",
            );
        };
        // return type
        let ret_ty = parser
            .next_until(|tt| tt.is_braced())
            .expect("return type after ->");
        // {...}
        let body = parser.next_group().expect("body");
        assert!(parser.is_empty(), "no tokens after function body");

        if create_impl_fn.is_some() {
            impl_fn_path = format_ident!("{fn_name}_impl").to_token_stream();
            outer_impl_fn = Some(quote!(fn #impl_fn_path #params #arrow #ret_ty #body));
            inner_impl_fn = None;
        } else {
            impl_fn_path = fn_name.to_token_stream();
            inner_impl_fn = Some(quote!(fn #fn_name #params #arrow #ret_ty #body));
            outer_impl_fn = None;
        }
    }

    kind.to_signature(&mut output);

    let kind = kind.to_tokens(impl_fn_path, as_dummy);

    quote! {
        {
            #inner_impl_fn
            #kind
        }
    }
    .to_tokens(&mut output);

    outer_impl_fn.to_tokens(&mut output);
    output.into()
}

fn with_error(
    item: proc_macro::TokenStream,
    span: Span,
    error: impl Display,
) -> proc_macro::TokenStream {
    let mut item = item.into();
    self::error(span, error).to_tokens(&mut item);
    item.into()
}

fn with_helpful_error(
    item: proc_macro::TokenStream,
    span: Span,
    error: impl Display,
    help: impl Display,
) -> proc_macro::TokenStream {
    let mut item = item.into();
    self::error_help(span, error, help).to_tokens(&mut item);
    item.into()
}

fn error(span: Span, error: impl Display) -> TokenStream {
    let error = error.to_string();
    quote_spanned! {span=>
        ::core::compile_error!{ #error }
    }
}

fn error_help(span: Span, error: impl Display, help: impl Display) -> TokenStream {
    let mut error = error.to_string();
    write!(error, "\n\n  = help: {help}").unwrap();
    quote_spanned! {span=>
        ::core::compile_error!{ #error }
    }
}
