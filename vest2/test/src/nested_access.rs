#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::*;
use vest_lib2::core::exec::input::{InputBuf, InputSlice};
use vest_lib2::core::exec::parser::*;
use vest_lib2::core::exec::serializer::*;
use vest_lib2::core::exec::ParseError;
use vest_lib2::core::exec::{DeepEq, SelfView};
use vest_lib2::core::{proof::*, spec::*};
use vest_lib2::macros::impl_self_view_for;
use vest_lib2::primitives::btcvarint::VarInt;
use vest_lib2::primitives::leb128::ULeb128;
use vstd::prelude::*;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `generic_header`."]
# [derive (Debug , PartialEq , Eq)]
pub struct GenericHeader {
    pub next_type: u8,
    pub reserved: u8,
    pub payload_length: u16,
}

# [verifier :: ext_equal]
pub struct GenericHeaderSpec {
    pub next_type: u8,
    pub reserved: u8,
    pub payload_length: u16,
}

pub type GenericHeaderInner = (u8, (u8, u16));

impl DeepView for GenericHeader {
    type V = GenericHeaderSpec;

    open spec fn deep_view(&self) -> Self::V {
        GenericHeaderSpec {
            next_type: self.next_type.deep_view(),
            reserved: self.reserved.deep_view(),
            payload_length: self.payload_length.deep_view(),
        }
    }
}

# [doc = "data type for `outer_header`."]
# [derive (Debug , PartialEq , Eq)]
pub struct OuterHeader {
    pub magic: u32,
    pub inner: GenericHeader,
}

# [verifier :: ext_equal]
pub struct OuterHeaderSpec {
    pub magic: u32,
    pub inner: GenericHeaderSpec,
}

pub type OuterHeaderInner = (u32, GenericHeaderSpec);

impl DeepView for OuterHeader {
    type V = OuterHeaderSpec;

    open spec fn deep_view(&self) -> Self::V {
        OuterHeaderSpec { magic: self.magic.deep_view(), inner: self.inner.deep_view() }
    }
}

# [doc = "data type for `payload_with_header`."]
# [derive (Debug , PartialEq , Eq)]
pub struct PayloadWithHeader<'i> {
    pub hdr: GenericHeader,
    pub body: &'i [u8],
}

# [verifier :: ext_equal]
pub struct PayloadWithHeaderSpec {
    pub hdr: GenericHeaderSpec,
    pub body: Seq<u8>,
}

pub type PayloadWithHeaderInner = (GenericHeaderSpec, Seq<u8>);

impl<'i> DeepView for PayloadWithHeader<'i> {
    type V = PayloadWithHeaderSpec;

    open spec fn deep_view(&self) -> Self::V {
        PayloadWithHeaderSpec { hdr: self.hdr.deep_view(), body: self.body.deep_view() }
    }
}

# [doc = "data type for `deep_nested`."]
# [derive (Debug , PartialEq , Eq)]
pub struct DeepNested<'i> {
    pub outer: OuterHeader,
    pub data: &'i [u8],
}

# [verifier :: ext_equal]
pub struct DeepNestedSpec {
    pub outer: OuterHeaderSpec,
    pub data: Seq<u8>,
}

pub type DeepNestedInner = (OuterHeaderSpec, Seq<u8>);

impl<'i> DeepView for DeepNested<'i> {
    type V = DeepNestedSpec;

    open spec fn deep_view(&self) -> Self::V {
        DeepNestedSpec { outer: self.outer.deep_view(), data: self.data.deep_view() }
    }
}

# [doc = "data type for `combined_example`."]
# [derive (Debug , PartialEq , Eq)]
pub struct CombinedExample<'i> {
    pub header: GenericHeader,
    pub body: &'i [u8],
}

# [verifier :: ext_equal]
pub struct CombinedExampleSpec {
    pub header: GenericHeaderSpec,
    pub body: Seq<u8>,
}

pub type CombinedExampleInner = (GenericHeaderSpec, Seq<u8>);

impl<'i> DeepView for CombinedExample<'i> {
    type V = CombinedExampleSpec;

    open spec fn deep_view(&self) -> Self::V {
        CombinedExampleSpec { header: self.header.deep_view(), body: self.body.deep_view() }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `generic_header`."]
pub struct GenericHeaderFmt;

pub type GenericHeaderFmtSpec = Named<
    Mapped<
        Pair<U8, Pair<U8, Refined<U16Le, PredFnSpec<u16>>>>,
        FnSpecMapper<GenericHeaderInner, GenericHeaderSpec>,
    >,
>;

# [doc = "specification constructor for `generic_header`."]
pub open spec fn generic_header_fmt() -> GenericHeaderFmtSpec {
    Named(
        "generic_header",
        Mapped {
            inner: Pair(U8, Pair(U8, Refined(U16Le, |x: u16| x >= 8 && x <= 65535))),
            mapper: (
                |parsed: GenericHeaderInner| -> GenericHeaderSpec
                    {
                        let (next_type, (reserved, payload_length)) = parsed;
                        GenericHeaderSpec { next_type, reserved, payload_length }
                    },
                |value: GenericHeaderSpec| -> GenericHeaderInner
                    {
                        let GenericHeaderSpec { next_type, reserved, payload_length } = value;
                        (next_type, (reserved, payload_length))
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `outer_header`."]
pub struct OuterHeaderFmt;

pub type OuterHeaderFmtSpec = Named<
    Mapped<Pair<U32Le, GenericHeaderFmt>, FnSpecMapper<OuterHeaderInner, OuterHeaderSpec>>,
>;

# [doc = "specification constructor for `outer_header`."]
pub open spec fn outer_header_fmt() -> OuterHeaderFmtSpec {
    Named(
        "outer_header",
        Mapped {
            inner: Pair(U32Le, GenericHeaderFmt),
            mapper: (
                |parsed: OuterHeaderInner| -> OuterHeaderSpec
                    {
                        let (magic, inner) = parsed;
                        OuterHeaderSpec { magic, inner }
                    },
                |value: OuterHeaderSpec| -> OuterHeaderInner
                    {
                        let OuterHeaderSpec { magic, inner } = value;
                        (magic, inner)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `payload_with_header`."]
pub struct PayloadWithHeaderFmt;

pub type PayloadWithHeaderFmtSpec = Named<
    Mapped<
        Bind<GenericHeaderFmt, spec_fn(GenericHeaderSpec) -> Varied<usize>>,
        FnSpecMapper<PayloadWithHeaderInner, PayloadWithHeaderSpec>,
    >,
>;

# [doc = "specification constructor for `payload_with_header`."]
pub open spec fn payload_with_header_fmt() -> PayloadWithHeaderFmtSpec {
    Named(
        "payload_with_header",
        Mapped {
            inner: Bind(
                GenericHeaderFmt,
                |hdr: GenericHeaderSpec| Varied((((hdr.payload_length as usize) - 4) as usize)),
            ),
            mapper: (
                |parsed: PayloadWithHeaderInner| -> PayloadWithHeaderSpec
                    {
                        let (hdr, body) = parsed;
                        PayloadWithHeaderSpec { hdr, body }
                    },
                |value: PayloadWithHeaderSpec| -> PayloadWithHeaderInner
                    {
                        let PayloadWithHeaderSpec { hdr, body } = value;
                        (hdr, body)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `deep_nested`."]
pub struct DeepNestedFmt;

pub type DeepNestedFmtSpec = Named<
    Mapped<
        Bind<OuterHeaderFmt, spec_fn(OuterHeaderSpec) -> Varied<usize>>,
        FnSpecMapper<DeepNestedInner, DeepNestedSpec>,
    >,
>;

# [doc = "specification constructor for `deep_nested`."]
pub open spec fn deep_nested_fmt() -> DeepNestedFmtSpec {
    Named(
        "deep_nested",
        Mapped {
            inner: Bind(
                OuterHeaderFmt,
                |outer: OuterHeaderSpec|
                    Varied((((outer.inner.payload_length as usize) - 8) as usize)),
            ),
            mapper: (
                |parsed: DeepNestedInner| -> DeepNestedSpec
                    {
                        let (outer, data) = parsed;
                        DeepNestedSpec { outer, data }
                    },
                |value: DeepNestedSpec| -> DeepNestedInner
                    {
                        let DeepNestedSpec { outer, data } = value;
                        (outer, data)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `combined_example`."]
pub struct CombinedExampleFmt {
    pub total_len: u32,
}

pub type CombinedExampleFmtSpec = Named<
    Mapped<
        Bind<GenericHeaderFmt, spec_fn(GenericHeaderSpec) -> Varied<usize>>,
        FnSpecMapper<CombinedExampleInner, CombinedExampleSpec>,
    >,
>;

# [doc = "specification constructor for `combined_example`."]
pub open spec fn combined_example_fmt(total_len: u32) -> CombinedExampleFmtSpec {
    Named(
        "combined_example",
        Mapped {
            inner: Bind(
                GenericHeaderFmt,
                |header: GenericHeaderSpec|
                    Varied((((total_len as usize) - (header.payload_length as usize)) as usize)),
            ),
            mapper: (
                |parsed: CombinedExampleInner| -> CombinedExampleSpec
                    {
                        let (header, body) = parsed;
                        CombinedExampleSpec { header, body }
                    },
                |value: CombinedExampleSpec| -> CombinedExampleInner
                    {
                        let CombinedExampleSpec { header, body } = value;
                        (header, body)
                    },
            ),
        },
    )
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for GenericHeaderFmt {
        type PVal = GenericHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            generic_header_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for GenericHeaderFmt {
        type Val = GenericHeaderSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            generic_header_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for GenericHeaderFmt {
        type SValue = GenericHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            generic_header_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for GenericHeaderFmt {
        type SVal = GenericHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            generic_header_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for GenericHeaderFmt {
        type T = GenericHeaderSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            generic_header_fmt().byte_len(v)
        }
    }

    impl SpecParser for OuterHeaderFmt {
        type PVal = OuterHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            outer_header_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for OuterHeaderFmt {
        type Val = OuterHeaderSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            outer_header_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for OuterHeaderFmt {
        type SValue = OuterHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            outer_header_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OuterHeaderFmt {
        type SVal = OuterHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            outer_header_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for OuterHeaderFmt {
        type T = OuterHeaderSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            outer_header_fmt().byte_len(v)
        }
    }

    impl SpecParser for PayloadWithHeaderFmt {
        type PVal = PayloadWithHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            payload_with_header_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for PayloadWithHeaderFmt {
        type Val = PayloadWithHeaderSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            payload_with_header_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for PayloadWithHeaderFmt {
        type SValue = PayloadWithHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            payload_with_header_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for PayloadWithHeaderFmt {
        type SVal = PayloadWithHeaderSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            payload_with_header_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for PayloadWithHeaderFmt {
        type T = PayloadWithHeaderSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            payload_with_header_fmt().byte_len(v)
        }
    }

    impl SpecParser for DeepNestedFmt {
        type PVal = DeepNestedSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            deep_nested_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for DeepNestedFmt {
        type Val = DeepNestedSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            deep_nested_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for DeepNestedFmt {
        type SValue = DeepNestedSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            deep_nested_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DeepNestedFmt {
        type SVal = DeepNestedSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            deep_nested_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for DeepNestedFmt {
        type T = DeepNestedSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            deep_nested_fmt().byte_len(v)
        }
    }

    impl SpecParser for CombinedExampleFmt {
        type PVal = CombinedExampleSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            combined_example_fmt(self.total_len.deep_view()).spec_parse(ibuf)
        }
    }

    impl Consistency for CombinedExampleFmt {
        type Val = CombinedExampleSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            combined_example_fmt(self.total_len.deep_view()).consistent(v)
        }
    }

    impl SpecSerializerDps for CombinedExampleFmt {
        type SValue = CombinedExampleSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            combined_example_fmt(self.total_len.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CombinedExampleFmt {
        type SVal = CombinedExampleSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            combined_example_fmt(self.total_len.deep_view()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CombinedExampleFmt {
        type T = CombinedExampleSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            combined_example_fmt(self.total_len.deep_view()).byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for GenericHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            generic_header_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for GenericHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            generic_header_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            let fmt = generic_header_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for GenericHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = generic_header_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeaderFmt as Consistency>::consistent);
            let fmt = generic_header_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for GenericHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = generic_header_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = generic_header_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for GenericHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = generic_header_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for GenericHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as Consistency>::consistent);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = generic_header_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for GenericHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            let fmt = generic_header_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for GenericHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = generic_header_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for GenericHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = generic_header_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for OuterHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            outer_header_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for OuterHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            outer_header_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            let fmt = outer_header_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for OuterHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = outer_header_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeaderFmt as Consistency>::consistent);
            let fmt = outer_header_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for OuterHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = outer_header_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = outer_header_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for OuterHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = outer_header_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for OuterHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as Consistency>::consistent);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = outer_header_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OuterHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            let fmt = outer_header_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for OuterHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = outer_header_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for OuterHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = outer_header_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for PayloadWithHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            payload_with_header_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for PayloadWithHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            payload_with_header_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let fmt = payload_with_header_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for PayloadWithHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = payload_with_header_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as Consistency>::consistent);
            let fmt = payload_with_header_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for PayloadWithHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = payload_with_header_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = payload_with_header_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for PayloadWithHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = payload_with_header_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for PayloadWithHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as Consistency>::consistent);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = payload_with_header_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for PayloadWithHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let fmt = payload_with_header_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for PayloadWithHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = payload_with_header_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for PayloadWithHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = payload_with_header_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DeepNestedFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            deep_nested_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DeepNestedFmt {
        open spec fn productive_inv(&self) -> bool {
            deep_nested_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            let fmt = deep_nested_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DeepNestedFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = deep_nested_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNestedFmt as Consistency>::consistent);
            let fmt = deep_nested_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DeepNestedFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = deep_nested_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = deep_nested_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DeepNestedFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = deep_nested_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DeepNestedFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as Consistency>::consistent);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = deep_nested_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DeepNestedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            let fmt = deep_nested_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DeepNestedFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            let fmt = deep_nested_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DeepNestedFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            let fmt = deep_nested_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CombinedExampleFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            combined_example_fmt(self.total_len.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CombinedExampleFmt {
        open spec fn productive_inv(&self) -> bool {
            combined_example_fmt(self.total_len.deep_view()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CombinedExampleFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExampleFmt as Consistency>::consistent);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CombinedExampleFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CombinedExampleFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CombinedExampleFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as Consistency>::consistent);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CombinedExampleFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CombinedExampleFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CombinedExampleFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            let fmt = combined_example_fmt(self.total_len.deep_view());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
impl<'i> Parser<&'i [u8]> for GenericHeaderFmt {
    type PT = GenericHeader;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, next_type) = (U8).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, reserved) = (U8).parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, payload_length) = (U16Le).parse(&rest)?;
        if !(payload_length >= 8 && payload_length <= 65535) {
            return Err(ParseError::predicate_failed());
        }
        let rest = rest.skip(n3);
        let total_n = n1 + n2 + n3;
        let final_v = GenericHeader { next_type, reserved, payload_length };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for OuterHeaderFmt {
    type PT = OuterHeader;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, magic) = (U32Le).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, inner) = (GenericHeaderFmt).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = OuterHeader { magic, inner };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for PayloadWithHeaderFmt {
    type PT = PayloadWithHeader<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, hdr) = (GenericHeaderFmt).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, body) = (Varied((((hdr.payload_length as usize) - 4 as usize) as usize))).parse(
            &rest,
        )?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = PayloadWithHeader { hdr, body };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for DeepNestedFmt {
    type PT = DeepNested<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<DeepNestedFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, outer) = (OuterHeaderFmt).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, data) = (Varied(
            (((outer.inner.payload_length as usize) - 8 as usize) as usize),
        )).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = DeepNested { outer, data };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for CombinedExampleFmt {
    type PT = CombinedExample<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, header) = (GenericHeaderFmt).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, body) = (Varied(
            (((self.total_len as usize) - (header.payload_length as usize)) as usize),
        )).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = CombinedExample { header, body };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

} // verus!
