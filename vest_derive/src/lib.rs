use proc_macro::TokenStream;

mod deep_view;

#[proc_macro_derive(DeepView)]
pub fn derive_deep_view(input: TokenStream) -> TokenStream {
    deep_view::derive(input)
}
