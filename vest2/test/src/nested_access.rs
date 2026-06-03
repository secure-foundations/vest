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
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `nested_complex`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct NestedComplex<'i> {
    pub flag: u32,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct NestedComplexSpec {
    pub flag: u32,
    pub data: Seq<u8>,
}

pub type NestedComplexInner = (u32, Seq<u8>);

impl<'i> DeepView for NestedComplex<'i> {
    type V = NestedComplexSpec;

    open spec fn deep_view(&self) -> Self::V {
        NestedComplexSpec { flag: self.flag.deep_view(), data: self.data.deep_view() }
    }
}

# [doc = "data type for `generic_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct GenericHeader {
    pub next_type: u8,
    pub reserved: u8,
    pub payload_length: u32,
}

pub type GenericHeaderSpec = GenericHeader;

pub type GenericHeaderInner = (u8, (u8, u32));

impl DeepView for GenericHeader {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `combined_example`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CombinedExample<'i> {
    pub header: GenericHeader,
    pub body: &'i [u8],
}

# [verifier::ext_equal]
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

# [doc = "data type for `payload_with_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct PayloadWithHeader<'i> {
    pub hdr: GenericHeader,
    pub body: &'i [u8],
}

# [verifier::ext_equal]
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

# [doc = "data type for `final_msg`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct FinalMsg<'i> {
    pub total_len: u32,
    pub body: CombinedExample<'i>,
    pub hdr_payload: PayloadWithHeader<'i>,
    pub nested: NestedComplex<'i>,
}

# [verifier::ext_equal]
pub struct FinalMsgSpec {
    pub total_len: u32,
    pub body: CombinedExampleSpec,
    pub hdr_payload: PayloadWithHeaderSpec,
    pub nested: NestedComplexSpec,
}

pub type FinalMsgInner = (u32, (CombinedExampleSpec, (PayloadWithHeaderSpec, NestedComplexSpec)));

impl<'i> DeepView for FinalMsg<'i> {
    type V = FinalMsgSpec;

    open spec fn deep_view(&self) -> Self::V {
        FinalMsgSpec {
            total_len: self.total_len.deep_view(),
            body: self.body.deep_view(),
            hdr_payload: self.hdr_payload.deep_view(),
            nested: self.nested.deep_view(),
        }
    }
}

# [doc = "data type for `outer_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct OuterHeader {
    pub magic: u32,
    pub inner: GenericHeader,
}

pub type OuterHeaderSpec = OuterHeader;

pub type OuterHeaderInner = (u32, GenericHeaderSpec);

impl DeepView for OuterHeader {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `deep_nested`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct DeepNested<'i> {
    pub outer: OuterHeader,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
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

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `nested_complex`."]
# [derive (Clone, Copy)]
pub struct NestedComplexFmt<'i> {
    hdr_payload: PayloadWithHeader<'i>,
}

impl<'i> NestedComplexFmt<'i> {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        PayloadWithHeaderFmt.consistent(self.hdr_payload.deep_view())
    }

    pub closed spec fn hdr_payload_spec(&self) -> PayloadWithHeaderSpec {
        self.hdr_payload.deep_view()
    }

    pub closed spec fn spec(hdr_payload: PayloadWithHeader<'i>) -> Self {
        NestedComplexFmt { hdr_payload }
    }
}

pub type NestedComplexFmtSpec = Named<
    Mapped<
        Pair<Const<U32Le, u32>, Varied<u32>>,
        FnSpecMapper<NestedComplexInner, NestedComplexSpec>,
    >,
>;

impl<'i> NestedComplexFmt<'i> {
    # [doc = "specification constructor for `nested_complex`."]
    pub open spec fn spec_inner(hdr_payload: PayloadWithHeaderSpec) -> NestedComplexFmtSpec {
        Named(
            "nested_complex",
            Mapped {
                inner: Pair(Const(U32Le, 0), Varied(((hdr_payload.hdr.payload_length - 8) as u32))),
                mapper: (
                    |parsed: NestedComplexInner| -> NestedComplexSpec
                        {
                            let (flag, data) = parsed;
                            NestedComplexSpec { flag, data }
                        },
                    |value: NestedComplexSpec| -> NestedComplexInner
                        {
                            let NestedComplexSpec { flag, data } = value;
                            (flag, data)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `generic_header`."]
# [derive (Clone, Copy)]
pub struct GenericHeaderFmt;

pub type GenericHeaderFmtSpec = Named<
    Mapped<
        Pair<U8, Pair<U8, Refined<U32Le, PredFnSpec<u32>>>>,
        FnSpecMapper<GenericHeaderInner, GenericHeaderSpec>,
    >,
>;

impl GenericHeaderFmt {
    # [doc = "specification constructor for `generic_header`."]
    pub open spec fn spec_inner() -> GenericHeaderFmtSpec {
        Named(
            "generic_header",
            Mapped {
                inner: Pair(U8, Pair(U8, Refined(U32Le, |x: u32| x >= 8 && x <= 65535))),
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
}

# [doc = "named format combinator for `combined_example`."]
# [derive (Clone, Copy)]
pub struct CombinedExampleFmt {
    total_len: u32,
}

impl CombinedExampleFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.total_len >= 65535 && self.total_len <= 4294967295
    }

    pub closed spec fn total_len_spec(&self) -> u32 {
        self.total_len.deep_view()
    }

    pub closed spec fn spec(total_len: u32) -> Self {
        CombinedExampleFmt { total_len }
    }
}

pub type CombinedExampleFmtSpec = Named<
    Mapped<
        Bind<GenericHeaderFmt, spec_fn(GenericHeaderSpec) -> Varied<u32>>,
        FnSpecMapper<CombinedExampleInner, CombinedExampleSpec>,
    >,
>;

impl CombinedExampleFmt {
    # [doc = "specification constructor for `combined_example`."]
    pub open spec fn spec_inner(total_len: u32) -> CombinedExampleFmtSpec {
        Named(
            "combined_example",
            Mapped {
                inner: Bind(
                    GenericHeaderFmt,
                    |header: GenericHeaderSpec|
                        Varied(((total_len - header.payload_length) as u32)),
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
}

# [doc = "named format combinator for `payload_with_header`."]
# [derive (Clone, Copy)]
pub struct PayloadWithHeaderFmt;

pub type PayloadWithHeaderFmtSpec = Named<
    Mapped<
        Bind<GenericHeaderFmt, spec_fn(GenericHeaderSpec) -> Varied<u32>>,
        FnSpecMapper<PayloadWithHeaderInner, PayloadWithHeaderSpec>,
    >,
>;

impl PayloadWithHeaderFmt {
    # [doc = "specification constructor for `payload_with_header`."]
    pub open spec fn spec_inner() -> PayloadWithHeaderFmtSpec {
        Named(
            "payload_with_header",
            Mapped {
                inner: Bind(
                    GenericHeaderFmt,
                    |hdr: GenericHeaderSpec| Varied(((hdr.payload_length - 4) as u32)),
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
}

# [doc = "named format combinator for `final_msg`."]
# [derive (Clone, Copy)]
pub struct FinalMsgFmt;

pub type FinalMsgFmtSpec = Named<
    Mapped<
        Bind<
            Refined<U32Le, PredFnSpec<u32>>,
            spec_fn(u32) -> Pair<
                CombinedExampleFmt,
                Bind<PayloadWithHeaderFmt, spec_fn(PayloadWithHeaderSpec) -> NestedComplexFmtSpec>,
            >,
        >,
        FnSpecMapper<FinalMsgInner, FinalMsgSpec>,
    >,
>;

impl FinalMsgFmt {
    # [doc = "specification constructor for `final_msg`."]
    pub open spec fn spec_inner() -> FinalMsgFmtSpec {
        Named(
            "final_msg",
            Mapped {
                inner: Bind(
                    Refined(U32Le, |x: u32| x >= 16777215 && x <= 4294967295),
                    |total_len: u32|
                        Pair(
                            CombinedExampleFmt::spec(total_len),
                            Bind(
                                PayloadWithHeaderFmt,
                                |hdr_payload: PayloadWithHeaderSpec|
                                    NestedComplexFmt::spec_inner(hdr_payload),
                            ),
                        ),
                ),
                mapper: (
                    |parsed: FinalMsgInner| -> FinalMsgSpec
                        {
                            let (total_len, (body, (hdr_payload, nested))) = parsed;
                            FinalMsgSpec { total_len, body, hdr_payload, nested }
                        },
                    |value: FinalMsgSpec| -> FinalMsgInner
                        {
                            let FinalMsgSpec { total_len, body, hdr_payload, nested } = value;
                            (total_len, (body, (hdr_payload, nested)))
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `outer_header`."]
# [derive (Clone, Copy)]
pub struct OuterHeaderFmt;

pub type OuterHeaderFmtSpec = Named<
    Mapped<Pair<U32Le, GenericHeaderFmt>, FnSpecMapper<OuterHeaderInner, OuterHeaderSpec>>,
>;

impl OuterHeaderFmt {
    # [doc = "specification constructor for `outer_header`."]
    pub open spec fn spec_inner() -> OuterHeaderFmtSpec {
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
}

# [doc = "named format combinator for `deep_nested`."]
# [derive (Clone, Copy)]
pub struct DeepNestedFmt;

pub type DeepNestedFmtSpec = Named<
    Mapped<
        Bind<OuterHeaderFmt, spec_fn(OuterHeaderSpec) -> Varied<u32>>,
        FnSpecMapper<DeepNestedInner, DeepNestedSpec>,
    >,
>;

impl DeepNestedFmt {
    # [doc = "specification constructor for `deep_nested`."]
    pub open spec fn spec_inner() -> DeepNestedFmtSpec {
        Named(
            "deep_nested",
            Mapped {
                inner: Bind(
                    OuterHeaderFmt,
                    |outer: OuterHeaderSpec| Varied(((outer.inner.payload_length - 8) as u32)),
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
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl<'i> SpecParser for NestedComplexFmt<'i> {
        type PVal = NestedComplexSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            NestedComplexFmt::spec_inner(self.hdr_payload_spec()).spec_parse(ibuf)
        }
    }

    impl<'i> Consistency for NestedComplexFmt<'i> {
        type Val = NestedComplexSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            NestedComplexFmt::spec_inner(self.hdr_payload_spec()).consistent(v)
        }
    }

    impl<'i> SpecSerializerDps for NestedComplexFmt<'i> {
        type SValue = NestedComplexSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            NestedComplexFmt::spec_inner(self.hdr_payload_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<'i> SpecSerializer for NestedComplexFmt<'i> {
        type SVal = NestedComplexSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            NestedComplexFmt::spec_inner(self.hdr_payload_spec()).spec_serialize(v)
        }
    }

    impl<'i> SpecByteLen for NestedComplexFmt<'i> {
        type T = NestedComplexSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            NestedComplexFmt::spec_inner(self.hdr_payload_spec()).byte_len(v)
        }
    }

    impl SpecParser for GenericHeaderFmt {
        type PVal = GenericHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            GenericHeaderFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for GenericHeaderFmt {
        type Val = GenericHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            GenericHeaderFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for GenericHeaderFmt {
        type SValue = GenericHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            GenericHeaderFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for GenericHeaderFmt {
        type SVal = GenericHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            GenericHeaderFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for GenericHeaderFmt {
        type T = GenericHeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            GenericHeaderFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CombinedExampleFmt {
        type PVal = CombinedExampleSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            CombinedExampleFmt::spec_inner(self.total_len_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CombinedExampleFmt {
        type Val = CombinedExampleSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            CombinedExampleFmt::spec_inner(self.total_len_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CombinedExampleFmt {
        type SValue = CombinedExampleSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            CombinedExampleFmt::spec_inner(self.total_len_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CombinedExampleFmt {
        type SVal = CombinedExampleSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            CombinedExampleFmt::spec_inner(self.total_len_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CombinedExampleFmt {
        type T = CombinedExampleSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            CombinedExampleFmt::spec_inner(self.total_len_spec()).byte_len(v)
        }
    }

    impl SpecParser for PayloadWithHeaderFmt {
        type PVal = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            PayloadWithHeaderFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for PayloadWithHeaderFmt {
        type Val = PayloadWithHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            PayloadWithHeaderFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for PayloadWithHeaderFmt {
        type SValue = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            PayloadWithHeaderFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for PayloadWithHeaderFmt {
        type SVal = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            PayloadWithHeaderFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for PayloadWithHeaderFmt {
        type T = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            PayloadWithHeaderFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for FinalMsgFmt {
        type PVal = FinalMsgSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            FinalMsgFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for FinalMsgFmt {
        type Val = FinalMsgSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            FinalMsgFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for FinalMsgFmt {
        type SValue = FinalMsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            FinalMsgFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for FinalMsgFmt {
        type SVal = FinalMsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            FinalMsgFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for FinalMsgFmt {
        type T = FinalMsgSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            FinalMsgFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for OuterHeaderFmt {
        type PVal = OuterHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            OuterHeaderFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for OuterHeaderFmt {
        type Val = OuterHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            OuterHeaderFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for OuterHeaderFmt {
        type SValue = OuterHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            OuterHeaderFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OuterHeaderFmt {
        type SVal = OuterHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            OuterHeaderFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for OuterHeaderFmt {
        type T = OuterHeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            OuterHeaderFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for DeepNestedFmt {
        type PVal = DeepNestedSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            DeepNestedFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DeepNestedFmt {
        type Val = DeepNestedSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            DeepNestedFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for DeepNestedFmt {
        type SValue = DeepNestedSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            DeepNestedFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DeepNestedFmt {
        type SVal = DeepNestedSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            DeepNestedFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DeepNestedFmt {
        type T = DeepNestedSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            DeepNestedFmt::spec_inner().byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl<'i> SafeParser for NestedComplexFmt<'i> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecParser>::spec_parse);
            NestedComplexFmt::spec_inner(self.hdr_payload_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<'i> Productive for NestedComplexFmt<'i> {
        open spec fn productive_inv(&self) -> bool {
            NestedComplexFmt::spec_inner(self.hdr_payload_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecParser>::spec_parse);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl<'i> SoundParser for NestedComplexFmt<'i> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecParser>::spec_parse);
            reveal(<NestedComplexFmt as SpecByteLen>::byte_len);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecParser>::spec_parse);
            reveal(<NestedComplexFmt as Consistency>::consistent);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<'i> NonTailFmt for NestedComplexFmt<'i> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedComplexFmt as SpecByteLen>::byte_len);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<'i> GoodSerializer for NestedComplexFmt<'i> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NestedComplexFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedComplexFmt as SpecByteLen>::byte_len);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<'i> SPRoundTripDps for NestedComplexFmt<'i> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecParser>::spec_parse);
            reveal(<NestedComplexFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedComplexFmt as Consistency>::consistent);
            reveal(<NestedComplexFmt as SpecByteLen>::byte_len);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<'i> NonMalleable for NestedComplexFmt<'i> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecParser>::spec_parse);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<'i> EquivSerializersGeneral for NestedComplexFmt<'i> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<NestedComplexFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedComplexFmt as SpecSerializer>::spec_serialize);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<'i> EquivSerializers for NestedComplexFmt<'i> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NestedComplexFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedComplexFmt as SpecSerializer>::spec_serialize);
            let fmt = NestedComplexFmt::spec_inner(self.hdr_payload_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for GenericHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            GenericHeaderFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for GenericHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            GenericHeaderFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for GenericHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeaderFmt as Consistency>::consistent);
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for GenericHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for GenericHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = GenericHeaderFmt::spec_inner();
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
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for GenericHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for GenericHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for GenericHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = GenericHeaderFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CombinedExampleFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            CombinedExampleFmt::spec_inner(self.total_len_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CombinedExampleFmt {
        open spec fn productive_inv(&self) -> bool {
            CombinedExampleFmt::spec_inner(self.total_len_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CombinedExampleFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExampleFmt as Consistency>::consistent);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CombinedExampleFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CombinedExampleFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
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
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CombinedExampleFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CombinedExampleFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CombinedExampleFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            let fmt = CombinedExampleFmt::spec_inner(self.total_len_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for PayloadWithHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            PayloadWithHeaderFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for PayloadWithHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            PayloadWithHeaderFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for PayloadWithHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as Consistency>::consistent);
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for PayloadWithHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for PayloadWithHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = PayloadWithHeaderFmt::spec_inner();
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
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for PayloadWithHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for PayloadWithHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for PayloadWithHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = PayloadWithHeaderFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for FinalMsgFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            FinalMsgFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for FinalMsgFmt {
        open spec fn productive_inv(&self) -> bool {
            FinalMsgFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for FinalMsgFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            reveal(<FinalMsgFmt as Consistency>::consistent);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for FinalMsgFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for FinalMsgFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<FinalMsgFmt as SpecSerializer>::spec_serialize);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for FinalMsgFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FinalMsgFmt as Consistency>::consistent);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for FinalMsgFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for FinalMsgFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FinalMsgFmt as SpecSerializer>::spec_serialize);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for FinalMsgFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FinalMsgFmt as SpecSerializer>::spec_serialize);
            let fmt = FinalMsgFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for OuterHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            OuterHeaderFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for OuterHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            OuterHeaderFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for OuterHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeaderFmt as Consistency>::consistent);
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for OuterHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for OuterHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = OuterHeaderFmt::spec_inner();
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
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OuterHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for OuterHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for OuterHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = OuterHeaderFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DeepNestedFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            DeepNestedFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DeepNestedFmt {
        open spec fn productive_inv(&self) -> bool {
            DeepNestedFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DeepNestedFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNestedFmt as Consistency>::consistent);
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DeepNestedFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DeepNestedFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = DeepNestedFmt::spec_inner();
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
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DeepNestedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DeepNestedFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DeepNestedFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            let fmt = DeepNestedFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for NestedComplexFmt<'i> {
        type PT = NestedComplex<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedComplexFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, flag) = Const(U32Le, 0).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, data) = Varied((self.hdr_payload.hdr.payload_length - 8)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = NestedComplex { flag, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<NestedComplex<'i>> for NestedComplexFmt<'i> {
        fn serialize(&self, v: &NestedComplex<'i>, obuf: &mut Vec<u8>) {
            reveal(<NestedComplexFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let NestedComplex { flag, data } = v;
            Const(U32Le, 0).serialize(flag, obuf);
            Varied((self.hdr_payload.hdr.payload_length - 8)).serialize(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for GenericHeaderFmt {
        type PT = GenericHeader;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, next_type) = U8.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, reserved) = U8.parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, payload_length) = U32Le.parse(&rest)?;
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

    impl<'i> Serializer<GenericHeader> for GenericHeaderFmt {
        fn serialize(&self, v: &GenericHeader, obuf: &mut Vec<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let GenericHeader { next_type, reserved, payload_length } = v;
            U8.serialize(next_type, obuf);
            U8.serialize(reserved, obuf);
            U32Le.serialize(payload_length, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for CombinedExampleFmt {
        type PT = CombinedExample<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, header) = GenericHeaderFmt.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, body) = Varied((self.total_len - header.payload_length)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CombinedExample { header, body };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<CombinedExample<'i>> for CombinedExampleFmt {
        fn serialize(&self, v: &CombinedExample<'i>, obuf: &mut Vec<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let CombinedExample { header, body } = v;
            GenericHeaderFmt.serialize(header, obuf);
            Varied((self.total_len - header.payload_length)).serialize(body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for PayloadWithHeaderFmt {
        type PT = PayloadWithHeader<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = GenericHeaderFmt.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, body) = Varied((hdr.payload_length - 4)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = PayloadWithHeader { hdr, body };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<PayloadWithHeader<'i>> for PayloadWithHeaderFmt {
        fn serialize(&self, v: &PayloadWithHeader<'i>, obuf: &mut Vec<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let PayloadWithHeader { hdr, body } = v;
            GenericHeaderFmt.serialize(hdr, obuf);
            Varied((hdr.payload_length - 4)).serialize(body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for FinalMsgFmt {
        type PT = FinalMsg<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, total_len) = U32Le.parse(&rest)?;
            if !(total_len >= 16777215 && total_len <= 4294967295) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, body) = CombinedExampleFmt { total_len: total_len }.parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, hdr_payload) = PayloadWithHeaderFmt.parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, nested) = NestedComplexFmt { hdr_payload: hdr_payload }.parse(&rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = FinalMsg { total_len, body, hdr_payload, nested };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<FinalMsg<'i>> for FinalMsgFmt {
        fn serialize(&self, v: &FinalMsg<'i>, obuf: &mut Vec<u8>) {
            reveal(<FinalMsgFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let FinalMsg { total_len, body, hdr_payload, nested } = v;
            U32Le.serialize(total_len, obuf);
            CombinedExampleFmt { total_len: *total_len }.serialize(body, obuf);
            PayloadWithHeaderFmt.serialize(hdr_payload, obuf);
            NestedComplexFmt { hdr_payload: *hdr_payload }.serialize(nested, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for OuterHeaderFmt {
        type PT = OuterHeader;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, magic) = U32Le.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, inner) = GenericHeaderFmt.parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = OuterHeader { magic, inner };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<OuterHeader> for OuterHeaderFmt {
        fn serialize(&self, v: &OuterHeader, obuf: &mut Vec<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let OuterHeader { magic, inner } = v;
            U32Le.serialize(magic, obuf);
            GenericHeaderFmt.serialize(inner, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for DeepNestedFmt {
        type PT = DeepNested<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, outer) = OuterHeaderFmt.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, data) = Varied((outer.inner.payload_length - 8)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = DeepNested { outer, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<DeepNested<'i>> for DeepNestedFmt {
        fn serialize(&self, v: &DeepNested<'i>, obuf: &mut Vec<u8>) {
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let DeepNested { outer, data } = v;
            OuterHeaderFmt.serialize(outer, obuf);
            Varied((outer.inner.payload_length - 8)).serialize(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

}

} // verus!
