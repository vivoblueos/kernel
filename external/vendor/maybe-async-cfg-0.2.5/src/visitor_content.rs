#[allow(unused_imports)]
use std::iter::FromIterator;

#[allow(unused_imports)]
use proc_macro::TokenStream;
use proc_macro2::{Delimiter, Group, TokenStream as TokenStream2, TokenTree};
use quote::quote;

use crate::{
    params::MacroParameters,
    visit_ext::{VisitMutExt, Visitor},
    DEFAULT_CRATE_NAME, MACRO_MAYBE_NAME, MACRO_DEFAULT_NAME,
};

pub struct ContentVisitor {
    pub params: MacroParameters,
}

impl ContentVisitor {
    pub fn new() -> Self {
        Self {
            params: MacroParameters::new(),
        }
    }

    fn process_attribute_maybe(&mut self, node: &mut syn::Attribute) -> syn::Result<()> {
        let mut params = MacroParameters::from_tokens_in_parens(node.tokens.clone().into())?;

        MacroParameters::apply_parent(&mut params, &self.params)?;

        let tokens = params.to_tokens(None);
        node.tokens = quote!((#tokens));

        Ok(())
    }

    fn process_file(&mut self, node: &mut syn::File) -> syn::Result<()> {
        node.attrs.retain(|attr| {
            if let Some(prefix) = is_default_attr(attr) {
                // TODO: This bit may not be right
                if MacroParameters::from_tokens_in_parens(attr.tokens.clone().into()).is_err() {
                    return false
                };
                self.params.prefix_set(prefix);
                false
            } else {
                true
            }
        });

        Ok(())
    }

    fn process_attribute(&mut self, node: &mut syn::Attribute) -> syn::Result<()> {
        if let Some(name) = self.params.is_our_attr(node) {
            match name.as_str() {
                MACRO_MAYBE_NAME => self.process_attribute_maybe(node)?,
                _ => {}
            }
        }

        Ok(())
    }

    fn extend_with_group(parent: &mut TokenStream2, child: TokenStream2, delim: Delimiter) {
        let g = TokenTree::Group(Group::new(delim, child));
        parent.extend(vec![g]);
    }

    fn search_maybe_in_tokenstream(&self, ts: TokenStream2, initial_state: u8) -> TokenStream2 {
        let mut state: u8 = initial_state;
        let mut result = TokenStream2::new();

        if state == 7 {
            let mut params = match MacroParameters::from_tokens(ts.clone().into()) {
                Ok(p) => p,
                Err(_) => return ts,
            };

            match MacroParameters::apply_parent(&mut params, &self.params) {
                Ok(p) => p,
                Err(_) => return ts,
            };

            return params.to_tokens(None).into();
        }

        let mut iter = ts.into_iter();
        while let Some(tt) = iter.next() {
            match state {
                0 => {
                    match &tt {
                        TokenTree::Punct(p) if p.as_char() == '#' => {
                            result.extend(vec![tt]);
                            state = 1;
                            continue;
                        }
                        TokenTree::Group(g) => {
                            Self::extend_with_group(
                                &mut result,
                                self.search_maybe_in_tokenstream(g.stream(), 0),
                                g.delimiter(),
                            );
                            state = 0;
                            continue;
                        }
                        _ => {}
                    };
                }
                1 => {
                    if let TokenTree::Group(g) = &tt {
                        if g.delimiter() == Delimiter::Bracket {
                            Self::extend_with_group(
                                &mut result,
                                self.search_maybe_in_tokenstream(g.stream(), 2),
                                g.delimiter(),
                            );
                            state = 0;
                            continue;
                        }
                    }
                }
                2 => {
                    if let TokenTree::Ident(ident) = &tt {
                        if ident.to_string() == DEFAULT_CRATE_NAME {
                            result.extend(vec![tt]);
                            state = 3;
                            continue;
                        }
                    }
                }
                3 => {
                    if let TokenTree::Punct(p) = &tt {
                        if p.as_char() == ':' {
                            result.extend(vec![tt]);
                            state = 4;
                            continue;
                        }
                    };
                }
                4 => {
                    if let TokenTree::Punct(p) = &tt {
                        if p.as_char() == ':' {
                            result.extend(vec![tt]);
                            state = 5;
                            continue;
                        }
                    };
                }
                5 => {
                    if let TokenTree::Ident(ident) = &tt {
                        if ident.to_string() == MACRO_MAYBE_NAME {
                            result.extend(vec![tt]);
                            state = 6;
                            continue;
                        }
                    }
                }
                6 => {
                    if let TokenTree::Group(g) = &tt {
                        if g.delimiter() == Delimiter::Parenthesis {
                            Self::extend_with_group(
                                &mut result,
                                self.search_maybe_in_tokenstream(g.stream(), 7),
                                g.delimiter(),
                            );

                            state = 0;
                            continue;
                        }
                    }
                }
                _ => unreachable!(),
            };
            result.extend(vec![tt]);
            state = 0;
        }

        result
    }
}

impl VisitMutExt for Visitor<ContentVisitor> {
    fn process_attribute(&mut self, node: &mut syn::Attribute) -> syn::Result<()> {
        self.inner.process_attribute(node)
    }

    fn process_file(&mut self, node: &mut syn::File) -> syn::Result<()> {
        self.inner.process_file(node)
    }

    fn process_macro(&mut self, node: &mut syn::Macro) -> syn::Result<()> {
        if node.path.is_ident("macro_rules") {
            node.tokens = self
                .inner
                .search_maybe_in_tokenstream(node.tokens.clone(), 0);
        }

        Ok(())
    }
}

fn is_default_attr(attr: &syn::Attribute) -> Option<String> {
    if let syn::AttrStyle::Inner(_) = attr.style {
        if attr.path.leading_colon.is_none() && attr.path.segments.len() == 2 {
            let first_segment = &attr.path.segments[0];
            let last_segment = &attr.path.segments[1];
            if first_segment.arguments == syn::PathArguments::None
                && last_segment.arguments == syn::PathArguments::None
            {
                let first = first_segment.ident.to_string();
                let last = last_segment.ident.to_string();

                if last == MACRO_DEFAULT_NAME {
                    return Some(first);
                }
            }
        }
    };
    None
}
