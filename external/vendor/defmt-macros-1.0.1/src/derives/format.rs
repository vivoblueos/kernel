use proc_macro::TokenStream;
use proc_macro_error2::{abort, abort_call_site};
use quote::{quote, ToTokens};
use syn::{parse_macro_input, parse_quote, Data, DeriveInput};

mod codegen;

pub(crate) fn expand(input: TokenStream) -> TokenStream {
    let DeriveInput {
        attrs,
        vis: _,
        ident,
        mut generics,
        data,
    } = parse_macro_input!(input as DeriveInput);

    let defmt_path = match defmt_crate_path(&attrs) {
        Ok(defmt_path) => defmt_path,
        Err(e) => abort!(e),
    };

    let encode_data = match &data {
        Data::Enum(data) => codegen::encode_enum_data(&ident, data, &defmt_path),
        Data::Struct(data) => codegen::encode_struct_data(&ident, data, &defmt_path),
        Data::Union(_) => abort_call_site!("`#[derive(Format)]` does not support unions"),
    };

    let codegen::EncodeData {
        format_tag,
        stmts,
        where_predicates,
    } = match encode_data {
        Ok(data) => data,
        Err(e) => return e.into_compile_error().into(),
    };

    let codegen::Generics {
        impl_generics,
        type_generics,
        where_clause,
    } = codegen::Generics::codegen(&mut generics, where_predicates);

    quote!(
        #[automatically_derived]
        impl #impl_generics #defmt_path::Format for #ident #type_generics #where_clause {
            fn format(&self, f: #defmt_path::Formatter) {
                use #defmt_path as defmt;
                #defmt_path::unreachable!()
            }

            fn _format_tag() -> #defmt_path::Str {
                #format_tag
            }

            fn _format_data(&self) {
                #(#stmts)*
            }
        }
    )
    .into()
}

fn defmt_crate_path(attrs: &[syn::Attribute]) -> Result<syn::Path, syn::Error> {
    let mut defmt_path = parse_quote!(defmt);
    let res = attrs
        .iter()
        .filter(|attr| attr.path().is_ident("defmt"))
        .try_for_each(|attr| {
            attr.parse_nested_meta(|meta| {
                if meta.path.get_ident().is_some_and(|ident| ident == "crate") {
                    meta.input.parse::<syn::Token![=]>()?;
                    defmt_path = meta.input.parse::<syn::Path>()?;
                    Ok(())
                } else {
                    let path = meta.path.to_token_stream().to_string().replace(' ', "");
                    Err(meta.error(format_args!("unknown defmt attribute `{path}`")))
                }
            })
        });
    res.map(|()| defmt_path)
}
