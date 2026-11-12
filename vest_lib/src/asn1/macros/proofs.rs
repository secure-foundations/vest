//! Opaque codec specifications and their proof-trait implementations.
//!
//! Nominal invariants use the traits' default `true`: each implementation proves
//! its inner obligations locally, rather than exposing the schema to parents.
//! Tagged DER formats establish tag consistency only after a successful parse;
//! fixed formats establish their parser invariants without that assumption.
#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_specs_and_proofs {
    ($fmt:ident, $spec:ty) => {
        verus! {

        impl SpecParser for $fmt {
            type PVal = $spec;

            #[verifier::opaque]
            open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
                self.spec_inner().spec_parse(ibuf)
            }
        }

        impl Consistency for $fmt {
            type Val = $spec;

            #[verifier::opaque]
            open spec fn consistent(&self, value: Self::Val) -> bool {
                self.spec_inner().consistent(value)
            }
        }

        impl SpecSerializerDps for $fmt {
            type SValue = $spec;

            #[verifier::opaque]
            open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
                self.spec_inner().spec_serialize_dps(value, obuf)
            }
        }

        impl SpecSerializer for $fmt {
            type SVal = $spec;

            #[verifier::opaque]
            open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
                self.spec_inner().spec_serialize(value)
            }
        }

        impl SpecByteLen for $fmt {
            type T = $spec;

            #[verifier::opaque]
            open spec fn byte_len(&self, value: Self::T) -> nat {
                self.spec_inner().byte_len(value)
            }
        }

        // The nominal boundary keeps the default `true` invariants. Each proof establishes the
        // concrete inner obligation locally before delegating.
        impl SafeParser for $fmt {
            proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                self.spec_inner().lemma_parse_safe(ibuf);
            }
        }

        impl Productive for $fmt {
            proof fn lemma_productive(&self, input: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                self.spec_inner().lemma_productive(input);
            }
        }

        impl NonTailFmt for $fmt {
            proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, obuf: Seq<u8>) {
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                self.spec_inner().lemma_serialize_dps_prepend(value, obuf);
            }

            proof fn lemma_serialize_dps_len(&self, value: Self::SValue, obuf: Seq<u8>) {
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                reveal(<$fmt as SpecByteLen>::byte_len);
                self.spec_inner().lemma_serialize_dps_len(value, obuf);
            }
        }

        impl GoodSerializer for $fmt {
            proof fn lemma_serialize_len(&self, value: Self::SVal) {
                // Keep the nominal equations opaque outside this pointwise bridge.
                let inner = self.spec_inner();
                assert(self.spec_serialize(value) == inner.spec_serialize(value)
                    && self.byte_len(value) == inner.byte_len(value)) by {
                    reveal(<$fmt as SpecSerializer>::spec_serialize);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                }
                inner.lemma_serialize_len(value);
            }
        }

        impl SPRoundTripDps for $fmt {
            proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as Consistency>::consistent);
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                reveal(<$fmt as SpecByteLen>::byte_len);
                self.lemma_schema_unambiguous();
                self.spec_inner().theorem_serialize_dps_parse_roundtrip(value, obuf);
            }
        }

        impl EquivSerializersGeneral for $fmt {
            proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
                reveal(<$fmt as SpecSerializer>::spec_serialize);
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                self.spec_inner().lemma_serialize_equiv(value, obuf);
            }
        }

        impl EquivSerializers for $fmt {
            proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
                reveal(<$fmt as SpecSerializer>::spec_serialize);
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                self.spec_inner().lemma_serialize_equiv_on_empty(value);
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_der_tagged_proofs {
    ($fmt:ident, $spec:ty $(, $forward:ty, $reverse:ty)?) => {
        verus! {

        impl $fmt {
            proof fn lemma_successful_parse_inner_invariants(&self, input: Seq<u8>)
                requires
                    self.spec_parse(input) is Some,
                ensures
                    self.spec_inner().safe_inv(),
                    self.spec_inner().sound_inv(),
                    self.spec_inner().strict_inv(),
                    self.spec_inner().nonmal_inv(),
            {
                $(
                    assert forall|input: <$forward as $crate::combinators::mapped::spec::SpecMap>::Input| #[trigger]
                        self.spec_inner().inner.consistent(input) implies
                            self.spec_inner().mapper.lossless(input) by {
                        <$spec>::lemma_into_from(input);
                    }
                )?
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal($fmt::spec_inner);
                broadcast use $crate::asn1::tag::lemma_tag_wf_implies_tag_consistent;
                self.spec_inner().lemma_parse_implies_asn1_start(input);
                reveal($crate::asn1::disjoint::input_starts_with);
                TagFmt.lemma_parse_sound_value(input);
            }
        }

        impl SoundParser for $fmt {
            proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as Consistency>::consistent);
                if self.spec_parse(ibuf) is Some {
                    self.lemma_successful_parse_inner_invariants(ibuf);
                    self.spec_inner().lemma_parse_sound_value(ibuf);
                }
            }
        }

        impl StrictParser for $fmt {
            proof fn lemma_parse_strict_consumption(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as SpecByteLen>::byte_len);
                if self.spec_parse(ibuf) is Some {
                    self.lemma_successful_parse_inner_invariants(ibuf);
                    self.spec_inner().lemma_parse_strict_consumption(ibuf);
                }
            }
        }

        impl NonMalleable for $fmt {
            proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                if self.spec_parse(buf1) is Some && self.spec_parse(buf2) is Some {
                    self.lemma_successful_parse_inner_invariants(buf1);
                    self.spec_inner().lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_der_fixed_proofs {
    ($fmt:ident, $spec:ty $(, $forward:ty, $reverse:ty)?) => {
        verus! {

        impl $fmt {
            proof fn lemma_parser_invariants(&self)
                ensures
                    self.spec_inner().sound_inv(),
                    self.spec_inner().strict_inv(),
                    self.spec_inner().nonmal_inv(),
            {
                $(
                    assert forall|input: <$forward as $crate::combinators::mapped::spec::SpecMap>::Input| #[trigger]
                        self.spec_inner().inner.consistent(input) implies
                            self.spec_inner().mapper.lossless(input) by {
                        <$spec>::lemma_into_from(input);
                    }
                )?
                broadcast use $crate::asn1::tag::lemma_tag_wf_implies_tag_consistent;
            }
        }

        impl SoundParser for $fmt {
            proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as Consistency>::consistent);
                self.lemma_parser_invariants();
                self.spec_inner().lemma_parse_sound_value(ibuf);
            }
        }

        impl StrictParser for $fmt {
            proof fn lemma_parse_strict_consumption(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as SpecByteLen>::byte_len);
                self.lemma_parser_invariants();
                self.spec_inner().lemma_parse_strict_consumption(ibuf);
            }
        }

        impl NonMalleable for $fmt {
            proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                self.lemma_parser_invariants();
                self.spec_inner().lemma_parse_non_malleable(buf1, buf2);
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_ber_sound {
    ($fmt:ident, $spec:ty $(, $forward:ty, $reverse:ty)?) => {
        verus! {
        impl SoundParser for $fmt {
            proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as Consistency>::consistent);
                if self.spec_parse(input) is Some {
                    $(
                        assert forall|value: <$forward as $crate::combinators::mapped::spec::SpecMap>::Input| #[trigger]
                            self.spec_inner().inner.consistent(value) implies
                                self.spec_inner().mapper.lossless(value) by {
                            <$spec>::lemma_into_from(value);
                        }
                    )?
                    broadcast use $crate::asn1::tag::lemma_tag_wf_implies_tag_consistent;
                    TagFmt.lemma_parse_sound_value(input);
                    self.spec_inner().lemma_parse_sound_value(input);
                }
            }
        }
        } // verus!
    };
}
