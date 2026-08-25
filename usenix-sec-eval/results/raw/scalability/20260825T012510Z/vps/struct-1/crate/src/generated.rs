# ! [allow (warnings)] use vest_lib2::combinators::mapped::spec::* ;
use vest_lib2::combinators::* ;
use vest_lib2::combinators::recursive::* ;
use Sum::Inl as L ;
use Sum::Inr as R ;
use vest_lib2::Never ;
use vest_lib2::core::exec::input::{
    InputBuf,
    InputSlice
}
;
use vest_lib2::core::exec::output::OutputBuf ;
use vest_lib2::core::exec::parser::* ;
use vest_lib2::core::exec::serializer::* ;
use vest_lib2::core::exec::ParseError ;
use vest_lib2::core::exec::bytes_eq ;
use vest_lib2::core::{
    proof::*,
    spec::*
}
;
use vest_lib2::primitives::btcvarint::VarInt ;
use vest_lib2::primitives::leb128::ULeb128 ;
use vstd::prelude::* ;
verus! {
// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `struct_width1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct StructWidth1 {
    pub field0: u8,
}
# [verifier::ext_equal]
pub struct StructWidth1Spec < T0 = u8 > {
    pub field0: T0,
}
pub type StructWidth1Inner = u8 ;
impl DeepView for StructWidth1 {
    type V = StructWidth1Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        StructWidth1Spec {
            field0: self.field0.deep_view(),
        }
    }
}
impl StructWidth1 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().field0 == self.field0.deep_view(),
    {
        reveal(< StructWidth1 as DeepView>::deep_view) ;
    }
}
impl < T0 > StructWidth1Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let field0 = input ;
        Self {
            field0
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            field0
        }
        = self ;
        field0
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(StructWidth1Spec::from_structural) ;
        reveal(StructWidth1Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(StructWidth1Spec::from_structural) ;
        reveal(StructWidth1Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            field0
        }
        => field0,
    }
   ,
    {
        reveal(StructWidth1Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct StructWidth1Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct StructWidth1Reverse ;
impl SpecMap for StructWidth1Forward {
    type Input = StructWidth1Inner ;
    type Output = StructWidth1Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        StructWidth1Spec::from_structural (input)
    }
}
impl SpecMap for StructWidth1Reverse {
    type Input = StructWidth1Spec ;
    type Output = StructWidth1Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `struct_width1`."]
# [derive (Clone, Copy)]
pub struct StructWidth1Fmt ;

pub type StructWidth1FmtSpec = Named < Mapped < U8, BiMap < StructWidth1Forward, StructWidth1Reverse >> > ;

impl StructWidth1Fmt {
    # [doc = "specification constructor for `struct_width1`."] pub open spec fn spec_inner() -> StructWidth1FmtSpec {
        Named ("struct_width1",
        Mapped {
            inner: U8,
            mapper: BiMap (StructWidth1Forward,
            StructWidth1Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for StructWidth1Fmt {
        type PVal = StructWidth1Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for StructWidth1Fmt {
        type Val = StructWidth1Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for StructWidth1Fmt {
        type SValue = StructWidth1Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for StructWidth1Fmt {
        type SVal = StructWidth1Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for StructWidth1Fmt {
        type T = StructWidth1Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }
}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;
    broadcast use {
        vest_lib2::combinators::disjoint::disjointness_lemmas,
        StructWidth1Spec::lemma_from_into,
        StructWidth1Spec::lemma_into_from,
    };

    impl SafeParser for StructWidth1Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for StructWidth1Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for StructWidth1Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth1Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for StructWidth1Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for StructWidth1Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< StructWidth1Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< StructWidth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for StructWidth1Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth1Fmt as Consistency>::consistent) ;
            reveal(< StructWidth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: StructWidth1Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                StructWidth1Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for StructWidth1Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for StructWidth1Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< StructWidth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth1Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for StructWidth1Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< StructWidth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth1Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }
}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for StructWidth1Fmt {
        type PT = StructWidth1;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<StructWidth1Fmt as SpecParser>::spec_parse);
            reveal(<StructWidth1 as DeepView>::deep_view);
            reveal(StructWidth1Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, field0) = (U8).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = StructWidth1 {
                field0,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, StructWidth1> for StructWidth1Fmt {
        fn serialize_into(&self, v: &StructWidth1, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;
            reveal(<StructWidth1Fmt as SpecSerializer>::spec_serialize);
            reveal(<StructWidth1Fmt as SpecByteLen>::byte_len);
            reveal(<StructWidth1 as DeepView>::deep_view);
            reveal(StructWidth1Spec::into_structural);
            let ghost old_obuf = obuf@;

            let StructWidth1 {
                field0,
            } = v;
            U8.serialize_into(field0, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<StructWidth1> for StructWidth1Fmt {
        fn prepare(&self, v: &StructWidth1) -> Result<usize, PreSerializeError> {
            reveal(<StructWidth1Fmt as SpecByteLen>::byte_len);
            reveal(<StructWidth1 as DeepView>::deep_view);
            reveal(StructWidth1Spec::into_structural);
            let StructWidth1 {
                field0,
            } = v;
            let l1 = (U8).prepare (field0) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }

}
}
