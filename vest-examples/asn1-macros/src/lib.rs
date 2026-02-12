use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, spanned::Spanned, Data, DeriveInput, Fields};

/// Given a struct like struct NewType<A1, ..., An>(B1, ..., Bn)
/// where each Bi either implements View, or is a type parameter,
///
/// generate a View impl for NewType that looks like the following
/// impl<A1: View, ..., An: View> View for NewType
/// {
///     type V = NewType<A1::V, ..., An::V>;
///     open spec fn view(&self) -> Self::V {
///         NewType(self.0@, ..., self.n@)
///     }
/// }
///
/// Supports unit and named structs too
#[proc_macro_derive(View)]
pub fn derive_view(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident; // The name of the struct/enum

    // Get type parameters A1, A2, ..., An
    // TODO: collect trait bounds here?
    let generic_idents: Vec<_> = input
        .generics
        .params
        .iter()
        .map(|g| match g {
            syn::GenericParam::Type(ty) => &ty.ident,
            _ => panic!("derive(View) only supports type parameters"),
        })
        .collect();

    // Generate A1::V, ..., An::V
    let generic_view_types = generic_idents.iter().map(|ident| {
        quote! { <#ident as View>::V }
    });

    // Map to A1: View, ... An: View
    let view_generic_idents: Vec<_> = generic_idents
        .iter()
        .map(|ident| {
            quote! { #ident: View }
        })
        .collect();

    // Generate `impl View` body
    let view_body = match input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Unnamed(fields) => {
                    // Generate self.0@, ..., self.n@
                    let field_view = (0..fields.unnamed.len()).map(|i| {
                        let i = syn::Index::from(i);
                        quote! { self.#i@ }
                    });

                    // Generate the implementation
                    quote! {
                        ::vstd::prelude::verus! {
                            impl<#(#view_generic_idents),*> View for #name<#(#generic_idents),*> {
                                type V = #name<#(#generic_view_types),*>;

                                open spec fn view(&self) -> Self::V {
                                    #name(#(#field_view),*)
                                }
                            }
                        }
                    }
                }
                Fields::Named(fields) => {
                    // Handle named structs
                    let field_view = fields.named.iter().map(|f| {
                        let name = &f.ident;
                        quote! { #name: self.#name@ }
                    });

                    // Generate the implementation for named struct
                    quote! {
                        ::vstd::prelude::verus! {
                            impl<#(#view_generic_idents),*> View for #name<#(#generic_idents),*> {
                                type V = #name<#(#generic_view_types),*>;

                                open spec fn view(&self) -> Self::V {
                                    #name {
                                        #(#field_view),*
                                    }
                                }
                            }
                        }
                    }
                }
                Fields::Unit => {
                    quote! {
                        ::vstd::prelude::verus! {
                            impl<#(#view_generic_idents),*> View for #name<#(#generic_idents),*> {
                                type V = #name<#(#generic_view_types),*>;

                                open spec fn view(&self) -> Self::V {
                                    #name
                                }
                            }
                        }
                    }
                }
            }
        }
        Data::Enum(data) => {
            // Generate match branches
            let variant_matches = data.variants.iter().map(|variant| {
                let variant_ident = &variant.ident;

                match &variant.fields {
                    Fields::Unnamed(fields) => {
                        let field_bindings = (0..fields.unnamed.len()).map(|i| {
                            let id = syn::Ident::new(&format!("f{}", i), fields.span());
                            quote! { #id }
                        });
                        let field_view = (0..fields.unnamed.len()).map(|i| {
                            let id = syn::Ident::new(&format!("f{}", i), fields.span());
                            quote! { #id@ }
                        });

                        quote! {
                            #name::#variant_ident(#(#field_bindings),*) => {
                                #name::#variant_ident(#(#field_view),*)
                            }
                        }
                    }
                    Fields::Unit => {
                        quote! {
                            #name::#variant_ident => {
                                #name::#variant_ident
                            }
                        }
                    }
                    _ => panic!("derive(View) only supports unnamed and unit enum variants"),
                }
            });

            quote! {
                ::vstd::prelude::verus! {
                    impl<#(#view_generic_idents),*> View for #name<#(#generic_idents),*> {
                        type V = #name<#(#generic_view_types),*>;

                        open spec fn view(&self) -> Self::V {
                            match self {
                                #(#variant_matches),*
                            }
                        }
                    }
                }
            }
        }
        _ => panic!("derive(View) only supports structs and enums"),
    };

    // eprintln!("Generated code:\n{}", view_body.to_string());

    // Convert the output into a TokenStream
    TokenStream::from(view_body)
}

/// Similar to derive(View), but for PolyfillClone
#[proc_macro_derive(PolyfillClone)]
pub fn derive_polyfill_clone(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident; // The name of the struct/enum

    // Get type parameters A1, A2, ..., An
    // TODO: collect trait bounds here?
    let generic_params: Vec<_> = input
        .generics
        .params
        .iter()
        .map(|g| match g {
            syn::GenericParam::Type(ty) => quote! { #ty },
            syn::GenericParam::Lifetime(lt) => quote! { #lt },
            syn::GenericParam::Const(..) => {
                panic!("derive(PolyfillClone) does not support const generics")
            }
        })
        .collect();

    // Map to A1: PolyfillClone, ... An: PolyfillClone (along with any lifetime params)
    let impl_generic_params: Vec<_> = input
        .generics
        .params
        .iter()
        .map(|g| match g {
            syn::GenericParam::Type(ty) => quote! { #ty: PolyfillClone },
            syn::GenericParam::Lifetime(lt) => quote! { #lt },
            syn::GenericParam::Const(..) => {
                panic!("derive(PolyfillClone) only supports type parameters")
            }
        })
        .collect();

    // Generate `impl PolyfillClone` body
    let view_body = match input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Unnamed(fields) => {
                    // Generate self.0@, ..., self.n@
                    let field_view = (0..fields.unnamed.len()).map(|i| {
                        let i = syn::Index::from(i);
                        quote! { PolyfillClone::clone(&self.#i) }
                    });

                    // Generate the implementation
                    quote! {
                        ::vstd::prelude::verus! {
                            impl<#(#impl_generic_params),*> PolyfillClone for #name<#(#generic_params),*> {
                                #[inline(always)]
                                fn clone(&self) -> Self {
                                    #name(#(#field_view),*)
                                }
                            }
                        }
                    }
                }
                Fields::Named(fields) => {
                    // Handle named structs
                    let field_view = fields.named.iter().map(|f| {
                        let name = &f.ident;
                        quote! { #name: PolyfillClone::clone(&self.#name) }
                    });

                    // Generate the implementation for named struct
                    quote! {
                        ::vstd::prelude::verus! {
                            impl<#(#impl_generic_params),*> PolyfillClone for #name<#(#generic_params),*> {
                                #[inline(always)]
                                fn clone(&self) -> Self {
                                    #name {
                                        #(#field_view),*
                                    }
                                }
                            }
                        }
                    }
                }
                Fields::Unit => {
                    quote! {
                        ::vstd::prelude::verus! {
                            impl<#(#impl_generic_params),*> PolyfillClone for #name<#(#generic_params),*> {
                                #[inline(always)]
                                fn clone(&self) -> Self {
                                    #name
                                }
                            }
                        }
                    }
                }
            }
        }
        Data::Enum(data) => {
            // Generate match branches
            let variant_matches = data.variants.iter().map(|variant| {
                let variant_ident = &variant.ident;

                match &variant.fields {
                    Fields::Unnamed(fields) => {
                        let field_bindings = (0..fields.unnamed.len()).map(|i| {
                            let id = syn::Ident::new(&format!("f{}", i), fields.span());
                            quote! { #id }
                        });
                        let field_view = (0..fields.unnamed.len()).map(|i| {
                            let id = syn::Ident::new(&format!("f{}", i), fields.span());
                            quote! { PolyfillClone::clone(&#id) }
                        });

                        quote! {
                            #name::#variant_ident(#(#field_bindings),*) => {
                                #name::#variant_ident(#(#field_view),*)
                            }
                        }
                    }
                    Fields::Unit => {
                        quote! {
                            #name::#variant_ident => {
                                #name::#variant_ident
                            }
                        }
                    }
                    _ => {
                        panic!("derive(PolyfillClone) only supports unnamed and unit enum variants")
                    }
                }
            });

            quote! {
                ::vstd::prelude::verus! {
                    impl<#(#impl_generic_params),*> PolyfillClone for #name<#(#generic_params),*> {
                        #[inline(always)]
                        fn clone(&self) -> Self {
                            match &self {
                                #(#variant_matches),*
                            }
                        }
                    }
                }
            }
        }
        _ => panic!("derive(PolyfillClone) only supports structs"),
    };

    // eprintln!("Generated code:\n{}", view_body.to_string());

    // Convert the output into a TokenStream
    TokenStream::from(view_body)
}
