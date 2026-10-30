use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{Attribute, LitStr, Meta, Result};

#[derive(Clone)]
pub(crate) struct Display {
    pub(crate) fmt: LitStr,
    pub(crate) args: TokenStream,
}

pub(crate) struct VariantDisplay {
    pub(crate) r#enum: Option<Display>,
    pub(crate) variant: Display,
}

impl ToTokens for Display {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let fmt = &self.fmt;
        let args = &self.args;
        tokens.extend(quote! {
            write!(formatter, #fmt #args)
        });
    }
}

impl ToTokens for VariantDisplay {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        if let Some(ref r#enum) = self.r#enum {
            r#enum.to_tokens(tokens);
            tokens.extend(quote! { ?; write!(formatter, ": ")?; });
        }
        self.variant.to_tokens(tokens);
    }
}

pub(crate) struct AttrsHelper {
    ignore_extra_doc_attributes: bool,
    prefix_enum_doc_attributes: bool,
}

impl AttrsHelper {
    pub(crate) fn new(attrs: &[Attribute]) -> Self {
        let ignore_extra_doc_attributes = Self::has_attr(attrs, "ignore_extra_doc_attributes");
        let prefix_enum_doc_attributes = Self::has_attr(attrs, "prefix_enum_doc_attributes");

        Self {
            ignore_extra_doc_attributes,
            prefix_enum_doc_attributes,
        }
    }

    fn get_attr<'a>(attrs: &'a [Attribute], name: &str) -> Option<&'a Attribute> {
        attrs.iter().find(|attr| attr.path().is_ident(name))
    }

    fn has_attr(attrs: &[Attribute], name: &str) -> bool {
        Self::get_attr(attrs, name).is_some()
    }

    pub(crate) fn display(&self, attrs: &[Attribute]) -> Result<Option<Display>> {
        if let Some(display_attr) = Self::get_attr(attrs, "display") {
            let lit = display_attr
                .parse_args()
                .expect("#[display(\"foo\")] must contain string arguments");
            let mut display = Display {
                fmt: lit,
                args: TokenStream::new(),
            };

            display.expand_shorthand();
            return Ok(Some(display));
        }

        let ignore_extra_doc_attributes = Self::has_attr(attrs, "ignore_extra_doc_attributes")
            || self.ignore_extra_doc_attributes;

        let mut displays = vec![];
        for attr in attrs {
            if attr.path().is_ident("doc") {
                let lit = match &attr.meta {
                    Meta::NameValue(syn::MetaNameValue {
                        value:
                            syn::Expr::Lit(syn::ExprLit {
                                lit: syn::Lit::Str(lit),
                                ..
                            }),
                        ..
                    }) => lit,
                    _ => unimplemented!(),
                };

                // Make an attempt at cleaning up multiline doc comments.
                let doc_str = lit
                    .value()
                    .lines()
                    .map(|line| line.trim().trim_start_matches('*').trim())
                    .collect::<Vec<&str>>()
                    .join("\n");

                let lit = LitStr::new(doc_str.trim(), lit.span());

                let mut display = Display {
                    fmt: lit,
                    args: TokenStream::new(),
                };

                display.expand_shorthand();

                if ignore_extra_doc_attributes {
                    return Ok(Some(display));
                }

                displays.push(display);
            }
        }

        Ok(merge_displays(displays))
    }

    pub(crate) fn display_with_input(
        &self,
        r#enum: &[Attribute],
        variant: &[Attribute],
    ) -> Result<Option<VariantDisplay>> {
        let r#enum = if self.prefix_enum_doc_attributes {
            let result = self
                .display(r#enum)?
                .expect("Missing doc comment on enum with #[prefix_enum_doc_attributes]. Please remove the attribute or add a doc comment to the enum itself.");

            Some(result)
        } else {
            None
        };

        Ok(self
            .display(variant)?
            .map(|variant| VariantDisplay { r#enum, variant }))
    }
}

fn merge_displays(displays: Vec<Display>) -> Option<Display> {
    let mut fmt;
    let mut span;
    let first_span;
    let mut args;

    let mut iter = displays.into_iter();

    if let Some(display) = iter.next() {
        fmt = display.fmt.value();

        span = Some(display.fmt.span());
        first_span = Some(display.fmt.span());

        args = display.args;
    } else {
        return None;
    }

    for Display {
        fmt: display_fmt,
        args: display_args,
    } in iter
    {
        fmt.push('\n');
        fmt.push_str(&display_fmt.value());

        if let Some(s) = span.take() {
            span = s.join(display_fmt.span());
        }

        if !display_args.is_empty() {
            args.extend(display_args);
        }
    }

    Some(Display {
        fmt: LitStr::new(fmt.trim(), span.or(first_span).unwrap()),
        args,
    })
}
