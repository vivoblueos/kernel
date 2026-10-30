use defmt_parser::ParserMode;
use proc_macro::TokenStream;
use proc_macro_error2::abort;
use quote::format_ident;
use quote::quote;
use syn::parse_macro_input;

use crate::{construct, function_like::log};

pub(crate) fn expand(args: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as log::Args);

    let format_string = args.format_string.value();

    let fragments = match defmt_parser::parse(&format_string, ParserMode::Strict) {
        Ok(args) => args,
        Err(e) => abort!(args.format_string, "{}", e),
    };

    let formatting_exprs: Vec<_> = args
        .formatting_args
        .map(|punctuated| punctuated.into_iter().collect())
        .unwrap_or_default();

    let log::Codegen { patterns, exprs } = log::Codegen::new(
        &fragments,
        formatting_exprs.len(),
        args.format_string.span(),
    );

    let var_name = format_ident!("S");
    let var_item = construct::static_variable(&var_name, &format_string, "timestamp", None);

    quote!(
        const _: () = {
            #[export_name = "_defmt_timestamp"]
            #[inline(never)]
            fn defmt_timestamp(fmt: defmt::Formatter<'_>) {
                match (#(&(#formatting_exprs)),*) {
                    (#(#patterns),*) => {
                    // NOTE: No format string index, and no finalize call.
                        #(#exprs;)*
                    }
                }
            }

            #var_item;

            // Unique symbol name to prevent multiple `timestamp!` invocations in the crate graph.
            // Uses `#var_name` to ensure it is not discarded by the linker.
            // This symbol itself is retained via a `EXTERN` directive in the linker script.
            #[no_mangle]
            #[cfg_attr(target_os = "macos", link_section = ".defmt,end.timestamp")]
            #[cfg_attr(not(target_os = "macos"), link_section = ".defmt.end.timestamp")]
            static __DEFMT_MARKER_TIMESTAMP_WAS_DEFINED: &u8 = &#var_name;
        };
    )
    .into()
}
