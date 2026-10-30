use defmt_parser::{Level, ParserMode};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use proc_macro_error2::abort;
use quote::quote;
use syn::{parse_macro_input, parse_quote};

use crate::construct;

use self::env_filter::EnvFilter;
pub(crate) use self::{args::Args, codegen::Codegen};

mod args;
mod codegen;
mod env_filter;

pub(crate) fn expand(level: Level, args: TokenStream) -> TokenStream {
    expand_parsed(level, parse_macro_input!(args as Args)).into()
}

pub(crate) fn expand_parsed(level: Level, args: Args) -> TokenStream2 {
    let format_string = args.format_string.value();
    let fragments = match defmt_parser::parse(&format_string, ParserMode::Strict) {
        Ok(args) => args,
        Err(e) => abort!(args.format_string, "{}", e),
    };

    let formatting_exprs = args
        .formatting_args
        .map(|punctuated| punctuated.into_iter().collect::<Vec<_>>())
        .unwrap_or_default();

    let Codegen { patterns, exprs } = Codegen::new(
        &fragments,
        formatting_exprs.len(),
        args.format_string.span(),
    );

    let header = construct::interned_string(
        &format_string,
        level.as_str(),
        true,
        Some(level.as_str()),
        &parse_quote!(defmt),
    );
    let env_filter = EnvFilter::from_env_var();

    if let Some(filter_check) = env_filter.path_check(level) {
        let content = if exprs.is_empty() {
            quote!(
                defmt::export::acquire_header_and_release(&#header);
            )
        } else {
            quote!(
                // safety: will be released a few lines further down
                unsafe { defmt::export::acquire_and_header(&#header); };
                #(#exprs;)*
                // safety: acquire() was called a few lines above
                unsafe { defmt::export::release() }
            )
        };

        quote!(
            {
                option_env!("DEFMT_LOG");
                match (#(&(#formatting_exprs)),*) {
                    (#(#patterns),*) => {
                        if #filter_check {
                            #content
                        }
                    }
                }
            }
        )
    } else {
        // if logging is disabled match args, so they are not considered "unused"
        quote!(
            {
                option_env!("DEFMT_LOG");
                match (#(&(#formatting_exprs)),*) {
                    _ => {}
                }
            }
        )
    }
}
