use defmt_parser::ParserMode;
use proc_macro::TokenStream;
use proc_macro_error2::abort;
use quote::quote;
use syn::{parse_macro_input, parse_quote};

use crate::{construct, function_like::log};

use self::args::Args;

mod args;

pub(crate) fn expand(args: TokenStream) -> TokenStream {
    let Args {
        formatter,
        log_args,
        ..
    } = parse_macro_input!(args as Args);

    let format_string = log_args.format_string.value();
    let fragments = match defmt_parser::parse(&format_string, ParserMode::Strict) {
        Ok(args) => args,
        Err(e) => abort!(log_args.format_string, "{}", e),
    };

    let formatting_exprs: Vec<_> = log_args
        .formatting_args
        .map(|punctuated| punctuated.into_iter().collect())
        .unwrap_or_default();

    let log::Codegen { patterns, exprs } = log::Codegen::new(
        &fragments,
        formatting_exprs.len(),
        log_args.format_string.span(),
    );

    let format_tag =
        construct::interned_string(&format_string, "write", false, None, &parse_quote!(defmt));
    quote!({
        let _typecheck_formatter: defmt::Formatter<'_> = #formatter;
        match (#(&(#formatting_exprs)),*) {
            (#(#patterns),*) => {
                defmt::export::istr(&#format_tag);
                #(#exprs;)*
            }
        }
    })
    .into()
}
