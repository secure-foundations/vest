use super::common::Analysis;
use super::writer::render_ts;
use crate::vestir::ParamDefn;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

impl<'a> Analysis<'a> {
    pub(crate) fn gen_top_level_proofs_section(
        &self,
        name: &str,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_proofs_section_impl(name, param_defns)
    }

    pub(crate) fn gen_proofs_section(&self, name: &str, param_defns: &[ParamDefn]) -> String {
        self.gen_proofs_section_impl(name, param_defns)
    }

    fn gen_proofs_section_impl(&self, name: &str, param_defns: &[ParamDefn]) -> String {
        let info = self.info(name);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let inner_ident = info.names.spec_ctor_ident();
        let generics = self.wrapper_generics(param_defns);
        let wrapper_call_args = self.wrapper_spec_call_args(param_defns);

        let safe =
            self.gen_safe_parser_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args);
        let productive =
            self.gen_productive_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args);
        let sound = if info.non_malleable {
            self.gen_sound_parser_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args)
        } else {
            TokenStream::new()
        };
        let non_tail = if info.non_tail {
            self.gen_non_tail_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args)
        } else {
            TokenStream::new()
        };
        let good =
            self.gen_good_serializer_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args);
        let roundtrip =
            self.gen_sp_roundtrip_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args);
        let non_malleable = if info.non_malleable {
            self.gen_non_malleable_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args)
        } else {
            TokenStream::new()
        };
        let equiv_general = if info.non_tail {
            self.gen_equiv_general_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args)
        } else {
            TokenStream::new()
        };
        let equiv = self.gen_equiv_impl(&fmt_ident, &inner_ident, &generics, &wrapper_call_args);

        render_ts(quote! {
            #safe
            #productive
            #sound
            #non_tail
            #good
            #roundtrip
            #non_malleable
            #equiv_general
            #equiv
        })
    }

    fn gen_productive_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics Productive for #fmt_ident #generics {
                open spec fn productive_inv(&self) -> bool {
                    #fmt_ident::#inner_ident(#(#wrapper_call_args),*).productive_inv()
                }

                proof fn lemma_productive(&self, s: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.productive_inv());
                    fmt.lemma_productive(s);
                }
            }
        }
    }

    fn gen_safe_parser_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics SafeParser for #fmt_ident #generics {
                proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    #fmt_ident::#inner_ident(#(#wrapper_call_args),*).lemma_parse_safe(ibuf);
                }
            }
        }
    }

    fn gen_sound_parser_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics SoundParser for #fmt_ident #generics {
                proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    reveal(<#reveal_ty as SpecByteLen>::byte_len);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.sound_inv());
                    fmt.lemma_parse_sound_consumption(ibuf);
                }

                proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    reveal(<#reveal_ty as Consistency>::consistent);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.sound_inv());
                    fmt.lemma_parse_sound_value(ibuf);
                }
            }
        }
    }

    fn gen_non_tail_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics NonTailFmt for #fmt_ident #generics {
                proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.serialize_dps_inv());
                    fmt.lemma_serialize_dps_prepend(v, obuf);
                }

                proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps);
                    reveal(<#reveal_ty as SpecByteLen>::byte_len);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.serialize_dps_inv());
                    fmt.lemma_serialize_dps_len(v, obuf);
                }
            }
        }
    }

    fn gen_good_serializer_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics GoodSerializer for #fmt_ident #generics {
                proof fn lemma_serialize_len(&self, v: Self::SVal) {
                    reveal(<#reveal_ty as SpecSerializer>::spec_serialize);
                    reveal(<#reveal_ty as SpecByteLen>::byte_len);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.serialize_inv());
                    fmt.lemma_serialize_len(v);
                }
            }
        }
    }

    fn gen_sp_roundtrip_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics SPRoundTripDps for #fmt_ident #generics {
                proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps);
                    reveal(<#reveal_ty as Consistency>::consistent);
                    reveal(<#reveal_ty as SpecByteLen>::byte_len);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.unambiguous());
                    fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
                }
            }
        }
    }

    fn gen_non_malleable_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics NonMalleable for #fmt_ident #generics {
                proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.nonmal_inv());
                    fmt.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
    }

    fn gen_equiv_general_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics EquivSerializersGeneral for #fmt_ident #generics {
                proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps);
                    reveal(<#reveal_ty as SpecSerializer>::spec_serialize);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.equiv_general_inv());
                    fmt.lemma_serialize_equiv(v, obuf);
                }
            }
        }
    }

    fn gen_equiv_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
    ) -> TokenStream {
        let reveal_ty = fmt_ident;
        quote! {
            impl #generics EquivSerializers for #fmt_ident #generics {
                proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
                    reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps);
                    reveal(<#reveal_ty as SpecSerializer>::spec_serialize);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.equiv_inv());
                    fmt.lemma_serialize_equiv_on_empty(v);
                }
            }
        }
    }
}
