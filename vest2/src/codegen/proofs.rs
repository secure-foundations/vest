use super::common::Analysis;
use super::writer::render_ts;
use crate::vestir::ParamDefn;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

impl<'a> Analysis<'a> {
    pub(crate) fn gen_bits_proofs_section(&self, name: &str, param_defns: &[ParamDefn]) -> String {
        let info = self.info(name);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let inner_ident = info.names.spec_ctor_ident();
        let generics = self.wrapper_generics(param_defns);
        let wrapper_call_args = self.wrapper_spec_call_args(param_defns);
        let inner_expr = quote! { Self::spec_inner(#(#wrapper_call_args),*) };
        let opaque = generics.is_empty();
        let lemma_unpack_pack = format_ident!("lemma_{}_unpack_pack", name);
        let lemma_pack_unpack = format_ident!("lemma_{}_pack_unpack", name);
        let lemma_wf = format_ident!("lemma_{}_mapper_wf_in_out", name);

        let safe =
            self.gen_safe_parser_impl(&fmt_ident, &generics, &generics, &inner_expr, opaque);
        let productive =
            self.gen_productive_impl(&fmt_ident, &generics, &generics, &inner_expr, opaque);
        let non_tail =
            self.gen_non_tail_impl(&fmt_ident, &generics, &generics, &inner_expr, opaque);
        let good = self.gen_good_serializer_impl(
            &fmt_ident,
            &generics,
            &generics,
            &inner_expr,
            opaque,
        );
        let equiv_general =
            self.gen_equiv_general_impl(&fmt_ident, &generics, &generics, &inner_expr, opaque);
        let equiv =
            self.gen_equiv_impl(&fmt_ident, &generics, &generics, &inner_expr, opaque);
        let reveal_ty = &fmt_ident;

        let sound = quote! {
            impl #generics SoundParser for #fmt_ident #generics {
                proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    reveal(<#reveal_ty as SpecByteLen>::byte_len);
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    broadcast use #lemma_unpack_pack, #lemma_wf;

                    assert(fmt.1.sound_inv());
                    fmt.lemma_parse_sound_consumption(ibuf);
                }

                proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    reveal(<#reveal_ty as Consistency>::consistent);
                    broadcast use #lemma_unpack_pack, #lemma_wf;
                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);

                    assert(fmt.1.sound_inv());
                    fmt.lemma_parse_sound_value(ibuf);
                }
            }
        };

        let roundtrip = quote! {
            impl #generics SPRoundTripDps for #fmt_ident #generics {
                proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
                    reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps);
                    reveal(<#reveal_ty as SpecByteLen>::byte_len);
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    broadcast use #lemma_pack_unpack;

                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    assert(fmt.1.unambiguous());
                    fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
                }
            }
        };

        let non_malleable = quote! {
            impl #generics NonMalleable for #fmt_ident #generics {
                proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
                    reveal(<#reveal_ty as SpecParser>::spec_parse);
                    broadcast use #lemma_unpack_pack, #lemma_wf;

                    let fmt = #fmt_ident::#inner_ident(#(#wrapper_call_args),*);
                    fmt.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        };

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
        let generics = self.wrapper_generics(param_defns);
        let wrapper_call_args = self.wrapper_spec_call_args(param_defns);
        let inner_expr = quote! { Self::spec_inner(#(#wrapper_call_args),*) };
        let opaque = generics.is_empty();
        let type_generics = generics.clone();

        let safe =
            self.gen_safe_parser_impl(&fmt_ident, &generics, &type_generics, &inner_expr, opaque);
        let productive = self.gen_productive_impl(
            &fmt_ident,
            &generics,
            &type_generics,
            &inner_expr,
            opaque,
        );
        let sound = if info.non_malleable {
            self.gen_sound_parser_impl(&fmt_ident, &generics, &type_generics, &inner_expr, opaque)
        } else {
            TokenStream::new()
        };
        let non_tail = if info.non_tail {
            self.gen_non_tail_impl(&fmt_ident, &generics, &type_generics, &inner_expr, opaque)
        } else {
            TokenStream::new()
        };
        let good = self.gen_good_serializer_impl(
            &fmt_ident,
            &generics,
            &type_generics,
            &inner_expr,
            opaque,
        );
        let roundtrip = self.gen_sp_roundtrip_impl(
            &fmt_ident,
            &generics,
            &type_generics,
            &inner_expr,
            opaque,
        );
        let non_malleable = if info.non_malleable {
            self.gen_non_malleable_impl(
                &fmt_ident,
                &generics,
                &type_generics,
                &inner_expr,
                opaque,
            )
        } else {
            TokenStream::new()
        };
        let equiv_general = if info.non_tail {
            self.gen_equiv_general_impl(
                &fmt_ident,
                &generics,
                &type_generics,
                &inner_expr,
                opaque,
            )
        } else {
            TokenStream::new()
        };
        let equiv = self.gen_equiv_impl(
            &fmt_ident,
            &generics,
            &type_generics,
            &inner_expr,
            opaque,
        );

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

    pub(crate) fn gen_productive_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_spec_parse = if opaque {
            quote! { reveal(<#reveal_ty as SpecParser>::spec_parse); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics Productive for #fmt_ident #type_generics {
                open spec fn productive_inv(&self) -> bool {
                    #inner_expr.productive_inv()
                }

                proof fn lemma_productive(&self, s: Seq<u8>) {
                    #reveal_spec_parse
                    let fmt = #inner_expr;
                    assert(fmt.productive_inv());
                    fmt.lemma_productive(s);
                }
            }
        }
    }

    pub(crate) fn gen_safe_parser_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_spec_parse = if opaque {
            quote! { reveal(<#reveal_ty as SpecParser>::spec_parse); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics SafeParser for #fmt_ident #type_generics {
                proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
                    #reveal_spec_parse
                    #inner_expr.lemma_parse_safe(ibuf);
                }
            }
        }
    }

    pub(crate) fn gen_sound_parser_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_spec_parse = if opaque {
            quote! { reveal(<#reveal_ty as SpecParser>::spec_parse); }
        } else {
            quote! {}
        };
        let reveal_byte_len = if opaque {
            quote! { reveal(<#reveal_ty as SpecByteLen>::byte_len); }
        } else {
            quote! {}
        };
        let reveal_consistent = if opaque {
            quote! { reveal(<#reveal_ty as Consistency>::consistent); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics SoundParser for #fmt_ident #type_generics {
                proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
                    #reveal_spec_parse
                    #reveal_byte_len
                    let fmt = #inner_expr;
                    assert(fmt.sound_inv());
                    fmt.lemma_parse_sound_consumption(ibuf);
                }

                proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                    #reveal_spec_parse
                    #reveal_consistent
                    let fmt = #inner_expr;
                    assert(fmt.sound_inv());
                    fmt.lemma_parse_sound_value(ibuf);
                }
            }
        }
    }

    pub(crate) fn gen_non_tail_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_serialize_dps = if opaque {
            quote! { reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps); }
        } else {
            quote! {}
        };
        let reveal_byte_len = if opaque {
            quote! { reveal(<#reveal_ty as SpecByteLen>::byte_len); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics NonTailFmt for #fmt_ident #type_generics {
                proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
                    #reveal_serialize_dps
                    let fmt = #inner_expr;
                    assert(fmt.serialize_dps_inv());
                    fmt.lemma_serialize_dps_prepend(v, obuf);
                }

                proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
                    #reveal_serialize_dps
                    #reveal_byte_len
                    let fmt = #inner_expr;
                    assert(fmt.serialize_dps_inv());
                    fmt.lemma_serialize_dps_len(v, obuf);
                }
            }
        }
    }

    pub(crate) fn gen_good_serializer_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_serialize = if opaque {
            quote! { reveal(<#reveal_ty as SpecSerializer>::spec_serialize); }
        } else {
            quote! {}
        };
        let reveal_byte_len = if opaque {
            quote! { reveal(<#reveal_ty as SpecByteLen>::byte_len); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics GoodSerializer for #fmt_ident #type_generics {
                proof fn lemma_serialize_len(&self, v: Self::SVal) {
                    #reveal_serialize
                    #reveal_byte_len
                    let fmt = #inner_expr;
                    assert(fmt.serialize_inv());
                    fmt.lemma_serialize_len(v);
                }
            }
        }
    }

    pub(crate) fn gen_sp_roundtrip_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_spec_parse = if opaque {
            quote! { reveal(<#reveal_ty as SpecParser>::spec_parse); }
        } else {
            quote! {}
        };
        let reveal_serialize_dps = if opaque {
            quote! { reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps); }
        } else {
            quote! {}
        };
        let reveal_consistent = if opaque {
            quote! { reveal(<#reveal_ty as Consistency>::consistent); }
        } else {
            quote! {}
        };
        let reveal_byte_len = if opaque {
            quote! { reveal(<#reveal_ty as SpecByteLen>::byte_len); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics SPRoundTripDps for #fmt_ident #type_generics {
                proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
                    #reveal_spec_parse
                    #reveal_serialize_dps
                    #reveal_consistent
                    #reveal_byte_len
                    let fmt = #inner_expr;
                    assert(fmt.unambiguous());
                    fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
                }
            }
        }
    }

    pub(crate) fn gen_non_malleable_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_spec_parse = if opaque {
            quote! { reveal(<#reveal_ty as SpecParser>::spec_parse); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics NonMalleable for #fmt_ident #type_generics {
                proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
                    #reveal_spec_parse
                    let fmt = #inner_expr;
                    assert(fmt.nonmal_inv());
                    fmt.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
    }

    pub(crate) fn gen_equiv_general_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_serialize_dps = if opaque {
            quote! { reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps); }
        } else {
            quote! {}
        };
        let reveal_serialize = if opaque {
            quote! { reveal(<#reveal_ty as SpecSerializer>::spec_serialize); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics EquivSerializersGeneral for #fmt_ident #type_generics {
                proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
                    #reveal_serialize_dps
                    #reveal_serialize
                    let fmt = #inner_expr;
                    assert(fmt.equiv_general_inv());
                    fmt.lemma_serialize_equiv(v, obuf);
                }
            }
        }
    }

    pub(crate) fn gen_equiv_impl(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        inner_expr: &TokenStream,
        opaque: bool,
    ) -> TokenStream {
        let reveal_ty = quote! { #fmt_ident #type_generics };
        let reveal_serialize_dps = if opaque {
            quote! { reveal(<#reveal_ty as SpecSerializerDps>::spec_serialize_dps); }
        } else {
            quote! {}
        };
        let reveal_serialize = if opaque {
            quote! { reveal(<#reveal_ty as SpecSerializer>::spec_serialize); }
        } else {
            quote! {}
        };
        quote! {
            impl #impl_generics EquivSerializers for #fmt_ident #type_generics {
                proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
                    #reveal_serialize_dps
                    #reveal_serialize
                    let fmt = #inner_expr;
                    assert(fmt.equiv_inv());
                    fmt.lemma_serialize_equiv_on_empty(v);
                }
            }
        }
    }
}
