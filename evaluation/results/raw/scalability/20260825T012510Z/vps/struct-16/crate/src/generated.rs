# ! [allow (warnings)] use vps_lib::combinators::mapped::spec::* ;
use vps_lib::combinators::* ;
use vps_lib::combinators::recursive::* ;
use Sum::Inl as L ;
use Sum::Inr as R ;
use vps_lib::Never ;
use vps_lib::core::exec::input::{
    InputBuf,
    InputSlice
}
;
use vps_lib::core::exec::output::OutputBuf ;
use vps_lib::core::exec::parser::* ;
use vps_lib::core::exec::serializer::* ;
use vps_lib::core::exec::ParseError ;
use vps_lib::core::exec::bytes_eq ;
use vps_lib::core::{
    proof::*,
    spec::*
}
;
use vps_lib::primitives::btcvarint::VarInt ;
use vps_lib::primitives::leb128::ULeb128 ;
use vstd::prelude::* ;
verus! {
// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `struct_width16`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct StructWidth16 {
    pub field0: u8,
    pub field1: u8,
    pub field2: u8,
    pub field3: u8,
    pub field4: u8,
    pub field5: u8,
    pub field6: u8,
    pub field7: u8,
    pub field8: u8,
    pub field9: u8,
    pub field10: u8,
    pub field11: u8,
    pub field12: u8,
    pub field13: u8,
    pub field14: u8,
    pub field15: u8,
}
# [verifier::ext_equal]
pub struct StructWidth16Spec < T0 = u8, T1 = u8, T2 = u8, T3 = u8, T4 = u8, T5 = u8, T6 = u8, T7 = u8, T8 = u8, T9 = u8, T10 = u8, T11 = u8, T12 = u8, T13 = u8, T14 = u8, T15 = u8 > {
    pub field0: T0,
    pub field1: T1,
    pub field2: T2,
    pub field3: T3,
    pub field4: T4,
    pub field5: T5,
    pub field6: T6,
    pub field7: T7,
    pub field8: T8,
    pub field9: T9,
    pub field10: T10,
    pub field11: T11,
    pub field12: T12,
    pub field13: T13,
    pub field14: T14,
    pub field15: T15,
}
pub type StructWidth16Inner = (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8))))))))))))))) ;
impl DeepView for StructWidth16 {
    type V = StructWidth16Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        StructWidth16Spec {
            field0: self.field0.deep_view(),
            field1: self.field1.deep_view(),
            field2: self.field2.deep_view(),
            field3: self.field3.deep_view(),
            field4: self.field4.deep_view(),
            field5: self.field5.deep_view(),
            field6: self.field6.deep_view(),
            field7: self.field7.deep_view(),
            field8: self.field8.deep_view(),
            field9: self.field9.deep_view(),
            field10: self.field10.deep_view(),
            field11: self.field11.deep_view(),
            field12: self.field12.deep_view(),
            field13: self.field13.deep_view(),
            field14: self.field14.deep_view(),
            field15: self.field15.deep_view(),
        }
    }
}
impl StructWidth16 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().field0 == self.field0.deep_view(),
    self.deep_view().field1 == self.field1.deep_view(),
    self.deep_view().field2 == self.field2.deep_view(),
    self.deep_view().field3 == self.field3.deep_view(),
    self.deep_view().field4 == self.field4.deep_view(),
    self.deep_view().field5 == self.field5.deep_view(),
    self.deep_view().field6 == self.field6.deep_view(),
    self.deep_view().field7 == self.field7.deep_view(),
    self.deep_view().field8 == self.field8.deep_view(),
    self.deep_view().field9 == self.field9.deep_view(),
    self.deep_view().field10 == self.field10.deep_view(),
    self.deep_view().field11 == self.field11.deep_view(),
    self.deep_view().field12 == self.field12.deep_view(),
    self.deep_view().field13 == self.field13.deep_view(),
    self.deep_view().field14 == self.field14.deep_view(),
    self.deep_view().field15 == self.field15.deep_view(),
    {
        reveal(< StructWidth16 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 > StructWidth16Spec < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    (T7,
    (T8,
    (T9,
    (T10,
    (T11,
    (T12,
    (T13,
    (T14,
    T15)))))))))))))))) -> Self {
        let (field0,
        (field1,
        (field2,
        (field3,
        (field4,
        (field5,
        (field6,
        (field7,
        (field8,
        (field9,
        (field10,
        (field11,
        (field12,
        (field13,
        (field14,
        field15))))))))))))))) = input ;
        Self {
            field0,
            field1,
            field2,
            field3,
            field4,
            field5,
            field6,
            field7,
            field8,
            field9,
            field10,
            field11,
            field12,
            field13,
            field14,
            field15
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    (T7,
    (T8,
    (T9,
    (T10,
    (T11,
    (T12,
    (T13,
    (T14,
    T15))))))))))))))) {
        let Self {
            field0,
            field1,
            field2,
            field3,
            field4,
            field5,
            field6,
            field7,
            field8,
            field9,
            field10,
            field11,
            field12,
            field13,
            field14,
            field15
        }
        = self ;
        (field0,
        (field1,
        (field2,
        (field3,
        (field4,
        (field5,
        (field6,
        (field7,
        (field8,
        (field9,
        (field10,
        (field11,
        (field12,
        (field13,
        (field14,
        field15)))))))))))))))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(StructWidth16Spec::from_structural) ;
        reveal(StructWidth16Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    (T7,
    (T8,
    (T9,
    (T10,
    (T11,
    (T12,
    (T13,
    (T14,
    T15)))))))))))))))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(StructWidth16Spec::from_structural) ;
        reveal(StructWidth16Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            field0,
            field1,
            field2,
            field3,
            field4,
            field5,
            field6,
            field7,
            field8,
            field9,
            field10,
            field11,
            field12,
            field13,
            field14,
            field15
        }
        => (field0,
        (field1,
        (field2,
        (field3,
        (field4,
        (field5,
        (field6,
        (field7,
        (field8,
        (field9,
        (field10,
        (field11,
        (field12,
        (field13,
        (field14,
        field15))))))))))))))),
    }
   ,
    {
        reveal(StructWidth16Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct StructWidth16Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct StructWidth16Reverse ;
impl SpecMap for StructWidth16Forward {
    type Input = StructWidth16Inner ;
    type Output = StructWidth16Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        StructWidth16Spec::from_structural (input)
    }
}
impl SpecMap for StructWidth16Reverse {
    type Input = StructWidth16Spec ;
    type Output = StructWidth16Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `struct_width16`."]
# [derive (Clone, Copy)]
pub struct StructWidth16Fmt ;

pub type StructWidth16FmtSpec = Named < Mapped < Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, U8 > > > > > > > > > > > > > > >, BiMap < StructWidth16Forward, StructWidth16Reverse >> > ;

impl StructWidth16Fmt {
    # [doc = "specification constructor for `struct_width16`."] pub open spec fn spec_inner() -> StructWidth16FmtSpec {
        Named ("struct_width16",
        Mapped {
            inner: Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            U8))))))))))))))),
            mapper: BiMap (StructWidth16Forward,
            StructWidth16Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for StructWidth16Fmt {
        type PVal = StructWidth16Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for StructWidth16Fmt {
        type Val = StructWidth16Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for StructWidth16Fmt {
        type SValue = StructWidth16Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for StructWidth16Fmt {
        type SVal = StructWidth16Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for StructWidth16Fmt {
        type T = StructWidth16Spec ;
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
        vps_lib::combinators::disjoint::disjointness_lemmas,
        StructWidth16Spec::lemma_from_into,
        StructWidth16Spec::lemma_into_from,
    };

    impl SafeParser for StructWidth16Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for StructWidth16Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for StructWidth16Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth16Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for StructWidth16Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for StructWidth16Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< StructWidth16Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< StructWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for StructWidth16Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth16Fmt as Consistency>::consistent) ;
            reveal(< StructWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: StructWidth16Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                StructWidth16Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for StructWidth16Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for StructWidth16Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth16Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for StructWidth16Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth16Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for StructWidth16Fmt {
        type PT = StructWidth16;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<StructWidth16Fmt as SpecParser>::spec_parse);
            reveal(<StructWidth16 as DeepView>::deep_view);
            reveal(StructWidth16Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, field0) = (U8).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, field1) = (U8).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, field2) = (U8).parse (& rest) ?;
            let rest = rest.skip(n3);
            let (n4, field3) = (U8).parse (& rest) ?;
            let rest = rest.skip(n4);
            let (n5, field4) = (U8).parse (& rest) ?;
            let rest = rest.skip(n5);
            let (n6, field5) = (U8).parse (& rest) ?;
            let rest = rest.skip(n6);
            let (n7, field6) = (U8).parse (& rest) ?;
            let rest = rest.skip(n7);
            let (n8, field7) = (U8).parse (& rest) ?;
            let rest = rest.skip(n8);
            let (n9, field8) = (U8).parse (& rest) ?;
            let rest = rest.skip(n9);
            let (n10, field9) = (U8).parse (& rest) ?;
            let rest = rest.skip(n10);
            let (n11, field10) = (U8).parse (& rest) ?;
            let rest = rest.skip(n11);
            let (n12, field11) = (U8).parse (& rest) ?;
            let rest = rest.skip(n12);
            let (n13, field12) = (U8).parse (& rest) ?;
            let rest = rest.skip(n13);
            let (n14, field13) = (U8).parse (& rest) ?;
            let rest = rest.skip(n14);
            let (n15, field14) = (U8).parse (& rest) ?;
            let rest = rest.skip(n15);
            let (n16, field15) = (U8).parse (& rest) ?;
            let rest = rest.skip(n16);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 + n11 + n12 + n13 + n14 + n15 + n16;
            let final_v = StructWidth16 {
                field0,
                field1,
                field2,
                field3,
                field4,
                field5,
                field6,
                field7,
                field8,
                field9,
                field10,
                field11,
                field12,
                field13,
                field14,
                field15,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, StructWidth16> for StructWidth16Fmt {
        fn serialize_into(&self, v: &StructWidth16, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<StructWidth16Fmt as SpecSerializer>::spec_serialize);
            reveal(<StructWidth16Fmt as SpecByteLen>::byte_len);
            reveal(<StructWidth16 as DeepView>::deep_view);
            reveal(StructWidth16Spec::into_structural);
            let ghost old_obuf = obuf@;

            let StructWidth16 {
                field0,
                field1,
                field2,
                field3,
                field4,
                field5,
                field6,
                field7,
                field8,
                field9,
                field10,
                field11,
                field12,
                field13,
                field14,
                field15,
            } = v;
            U8.serialize_into(field0, obuf);
            U8.serialize_into(field1, obuf);
            U8.serialize_into(field2, obuf);
            U8.serialize_into(field3, obuf);
            U8.serialize_into(field4, obuf);
            U8.serialize_into(field5, obuf);
            U8.serialize_into(field6, obuf);
            U8.serialize_into(field7, obuf);
            U8.serialize_into(field8, obuf);
            U8.serialize_into(field9, obuf);
            U8.serialize_into(field10, obuf);
            U8.serialize_into(field11, obuf);
            U8.serialize_into(field12, obuf);
            U8.serialize_into(field13, obuf);
            U8.serialize_into(field14, obuf);
            U8.serialize_into(field15, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<StructWidth16> for StructWidth16Fmt {
        fn prepare(&self, v: &StructWidth16) -> Result<usize, PreSerializeError> {
            reveal(<StructWidth16Fmt as SpecByteLen>::byte_len);
            reveal(<StructWidth16 as DeepView>::deep_view);
            reveal(StructWidth16Spec::into_structural);
            let StructWidth16 {
                field0,
                field1,
                field2,
                field3,
                field4,
                field5,
                field6,
                field7,
                field8,
                field9,
                field10,
                field11,
                field12,
                field13,
                field14,
                field15,
            } = v;
            let l1 = (U8).prepare (field0) ?;
            let l2 = (U8).prepare (field1) ?;
            let l3 = (U8).prepare (field2) ?;
            let l4 = (U8).prepare (field3) ?;
            let l5 = (U8).prepare (field4) ?;
            let l6 = (U8).prepare (field5) ?;
            let l7 = (U8).prepare (field6) ?;
            let l8 = (U8).prepare (field7) ?;
            let l9 = (U8).prepare (field8) ?;
            let l10 = (U8).prepare (field9) ?;
            let l11 = (U8).prepare (field10) ?;
            let l12 = (U8).prepare (field11) ?;
            let l13 = (U8).prepare (field12) ?;
            let l14 = (U8).prepare (field13) ?;
            let l15 = (U8).prepare (field14) ?;
            let l16 = (U8).prepare (field15) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l4).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l5).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l6).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l7).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l8).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l9).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l10).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l11).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l12).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l13).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l14).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l15).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l16).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
