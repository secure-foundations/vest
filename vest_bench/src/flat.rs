# ! [allow (warnings)] use vest_lib::combinators::mapped::spec::* ;
use vest_lib::combinators::* ;
use vest_lib::combinators::recursive::* ;
use Sum::Inl as L ;
use Sum::Inr as R ;
use vest_lib::Never ;
use vest_lib::core::exec::input::{
    InputBuf,
    InputSlice
}
;
use vest_lib::core::exec::output::OutputBuf ;
use vest_lib::core::exec::parser::* ;
use vest_lib::core::exec::serializer::* ;
use vest_lib::core::exec::ParseError ;
use vest_lib::core::exec::bytes_eq ;
use vest_lib::core::{
    proof::*,
    spec::*
}
;
use vest_lib::primitives::btcvarint::VarInt ;
use vest_lib::primitives::leb128::ULeb128 ;
use vstd::prelude::* ;
verus! {
// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `flat_record`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct FlatRecord<'i> {
    pub id: u64,
    pub key: &'i [u8],
    pub payload_len: u32,
    pub payload: &'i [u8],
}
# [verifier::ext_equal]
pub struct FlatRecordSpec < T0 = u64, T1 = Seq < u8 >, T2 = u32, T3 = Seq < u8 > > {
    pub id: T0,
    pub key: T1,
    pub payload_len: T2,
    pub payload: T3,
}
pub type FlatRecordInner = (u64, (Seq < u8 >, (u32, Seq < u8 >))) ;
impl<'i> DeepView for FlatRecord<'i> {
    type V = FlatRecordSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        FlatRecordSpec {
            id: self.id.deep_view(),
            key: self.key.deep_view(),
            payload_len: self.payload_len.deep_view(),
            payload: self.payload.deep_view(),
        }
    }
}
impl<'i> FlatRecord<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().id == self.id.deep_view(),
    self.deep_view().key == self.key.deep_view(),
    self.deep_view().payload_len == self.payload_len.deep_view(),
    self.deep_view().payload == self.payload.deep_view(),
    {
        reveal(< FlatRecord as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3 > FlatRecordSpec < T0, T1, T2, T3 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    (T2,
    T3)))) -> Self {
        let (id,
        (key,
        (payload_len,
        payload))) = input ;
        Self {
            id,
            key,
            payload_len,
            payload
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    (T2,
    T3))) {
        let Self {
            id,
            key,
            payload_len,
            payload
        }
        = self ;
        (id,
        (key,
        (payload_len,
        payload)))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(FlatRecordSpec::from_structural) ;
        reveal(FlatRecordSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    (T2,
    T3)))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(FlatRecordSpec::from_structural) ;
        reveal(FlatRecordSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            id,
            key,
            payload_len,
            payload
        }
        => (id,
        (key,
        (payload_len,
        payload))),
    }
   ,
    {
        reveal(FlatRecordSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct FlatRecordForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct FlatRecordReverse ;
impl SpecMap for FlatRecordForward {
    type Input = FlatRecordInner ;
    type Output = FlatRecordSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        FlatRecordSpec::from_structural (input)
    }
}
impl SpecMap for FlatRecordReverse {
    type Input = FlatRecordSpec ;
    type Output = FlatRecordInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `flat_record`."]
# [derive (Clone, Copy)]
pub struct FlatRecordFmt ;

pub type FlatRecordFmtSpec = Named < Mapped < Pair < U64Be, Pair < Fixed < 32 >, Bind < U32Be, spec_fn (u32) -> Varied < u32 > > > >, BiMap < FlatRecordForward, FlatRecordReverse >> > ;

impl FlatRecordFmt {
    # [doc = "specification constructor for `flat_record`."] pub open spec fn spec_inner() -> FlatRecordFmtSpec {
        Named ("flat_record",
        Mapped {
            inner: Pair (U64Be,
            Pair (Fixed::< 32 >,
            Bind (U32Be,
            | payload_len: u32 | Varied (payload_len)))),
            mapper: BiMap (FlatRecordForward,
            FlatRecordReverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for FlatRecordFmt {
        type PVal = FlatRecordSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for FlatRecordFmt {
        type Val = FlatRecordSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for FlatRecordFmt {
        type SValue = FlatRecordSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for FlatRecordFmt {
        type SVal = FlatRecordSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for FlatRecordFmt {
        type T = FlatRecordSpec ;
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
        vest_lib::combinators::disjoint::disjointness_lemmas,
        FlatRecordSpec::lemma_from_into,
        FlatRecordSpec::lemma_into_from,
    };

    impl SafeParser for FlatRecordFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for FlatRecordFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for FlatRecordFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecParser>::spec_parse) ;
            reveal(< FlatRecordFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: FlatRecordInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                FlatRecordSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecParser>::spec_parse) ;
            reveal(< FlatRecordFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: FlatRecordInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                FlatRecordSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for FlatRecordFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FlatRecordFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for FlatRecordFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< FlatRecordFmt as SpecSerializer>::spec_serialize) ;
            reveal(< FlatRecordFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for FlatRecordFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecParser>::spec_parse) ;
            reveal(< FlatRecordFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FlatRecordFmt as Consistency>::consistent) ;
            reveal(< FlatRecordFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: FlatRecordSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                FlatRecordSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for FlatRecordFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: FlatRecordInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                FlatRecordSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for FlatRecordFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< FlatRecordFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FlatRecordFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for FlatRecordFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< FlatRecordFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FlatRecordFmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for FlatRecordFmt {
        type PT = FlatRecord<'i>;

        fn min_byte_len(&self) -> usize {
            44
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<FlatRecordFmt as SpecParser>::spec_parse);
            reveal(<FlatRecord as DeepView>::deep_view);
            reveal(FlatRecordSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, id) = (U64Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, key) = (Fixed::< 32 >).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, payload_len) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let (n4, payload) = (Varied (payload_len)).parse (& rest) ?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = FlatRecord {
                id,
                key,
                payload_len,
                payload,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, FlatRecord<'i>> for FlatRecordFmt {
        fn serialize_into(&self, v: &FlatRecord<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<FlatRecordFmt as SpecSerializer>::spec_serialize);
            reveal(<FlatRecordFmt as SpecByteLen>::byte_len);
            reveal(<FlatRecord as DeepView>::deep_view);
            reveal(FlatRecordSpec::into_structural);
            let ghost old_obuf = obuf@;

            let FlatRecord {
                id,
                key,
                payload_len,
                payload,
            } = v;
            U64Be.serialize_into(id, obuf);
            Fixed::< 32 >.serialize_into(* key, obuf);
            U32Be.serialize_into(payload_len, obuf);
            Varied (* payload_len).serialize_into(* payload, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<FlatRecord<'i>> for FlatRecordFmt {
        fn prepare(&self, v: &FlatRecord<'i>) -> Result<usize, PreSerializeError> {
            reveal(<FlatRecordFmt as SpecByteLen>::byte_len);
            reveal(<FlatRecord as DeepView>::deep_view);
            reveal(FlatRecordSpec::into_structural);
            let FlatRecord {
                id,
                key,
                payload_len,
                payload,
            } = v;
            let l1 = (U64Be).prepare (id) ?;
            let l2 = (Fixed::< 32 >).prepare (key) ?;
            let l3 = (U32Be).prepare (payload_len) ?;
            let l4 = (Varied (* payload_len)).prepare (payload) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l4).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
