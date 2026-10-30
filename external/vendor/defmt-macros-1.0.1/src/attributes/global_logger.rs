use proc_macro::TokenStream;
use proc_macro_error2::{abort, abort_call_site};
use quote::quote;
use syn::{parse_macro_input, Fields, ItemStruct};

pub(crate) fn expand(args: TokenStream, item: TokenStream) -> TokenStream {
    if !args.is_empty() {
        abort_call_site!("`#[global_logger]` attribute takes no arguments")
    }

    let strukt = parse_macro_input!(item as ItemStruct);

    validate(&strukt);

    codegen(&strukt)
}

fn validate(strukt: &ItemStruct) {
    let is_unit_struct = matches!(strukt.fields, Fields::Unit);

    if !strukt.generics.params.is_empty()
        || strukt.generics.where_clause.is_some()
        || !is_unit_struct
    {
        abort!(
            strukt,
            "struct must be a non-generic unit struct (e.g. `struct S;`)"
        );
    }
}

fn codegen(strukt: &ItemStruct) -> TokenStream {
    let attrs = &strukt.attrs;
    let ident = &strukt.ident;
    let vis = &strukt.vis;

    quote!(
        #(#attrs)*
        #vis struct #ident;

        #[inline(never)]
        #[no_mangle]
        unsafe fn _defmt_acquire()  {
            <#ident as defmt::Logger>::acquire()
        }

        #[inline(never)]
        #[no_mangle]
        unsafe fn _defmt_flush()  {
            <#ident as defmt::Logger>::flush()
        }

        #[inline(never)]
        #[no_mangle]
        unsafe fn _defmt_release()  {
            <#ident as defmt::Logger>::release()
        }

        #[inline(never)]
        #[no_mangle]
        unsafe fn _defmt_write(bytes: &[u8])  {
            <#ident as defmt::Logger>::write(bytes)
        }
    )
    .into()
}
