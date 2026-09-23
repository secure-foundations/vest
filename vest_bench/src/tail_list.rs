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
# [doc = "data type for `tail_item`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct TailItem<'i> {
    pub tag: u16,
    pub len: u16,
    pub body: &'i [u8],
}
# [verifier::ext_equal]
pub struct TailItemSpec < T0 = u16, T1 = u16, T2 = Seq < u8 > > {
    pub tag: T0,
    pub len: T1,
    pub body: T2,
}
pub type TailItemInner = (u16, (u16, Seq < u8 >)) ;
impl<'i> DeepView for TailItem<'i> {
    type V = TailItemSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        TailItemSpec {
            tag: self.tag.deep_view(),
            len: self.len.deep_view(),
            body: self.body.deep_view(),
        }
    }
}
impl<'i> TailItem<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().tag == self.tag.deep_view(),
    self.deep_view().len == self.len.deep_view(),
    self.deep_view().body == self.body.deep_view(),
    {
        reveal(< TailItem as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > TailItemSpec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (tag,
        (len,
        body)) = input ;
        Self {
            tag,
            len,
            body
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            tag,
            len,
            body
        }
        = self ;
        (tag,
        (len,
        body))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TailItemSpec::from_structural) ;
        reveal(TailItemSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TailItemSpec::from_structural) ;
        reveal(TailItemSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            tag,
            len,
            body
        }
        => (tag,
        (len,
        body)),
    }
   ,
    {
        reveal(TailItemSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TailItemForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TailItemReverse ;
impl SpecMap for TailItemForward {
    type Input = TailItemInner ;
    type Output = TailItemSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TailItemSpec::from_structural (input)
    }
}
impl SpecMap for TailItemReverse {
    type Input = TailItemSpec ;
    type Output = TailItemInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tail_list`."]
pub type TailList<'i> = Vec < TailItem<'i> > ;
pub type TailListSpec = Seq < TailItemSpec > ;

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `tail_item`."]
# [derive (Clone, Copy)]
pub struct TailItemFmt ;

pub type TailItemFmtSpec = Named < Mapped < Pair < U16Be, Bind < U16Be, spec_fn (u16) -> Varied < u16 > > >, BiMap < TailItemForward, TailItemReverse >> > ;

impl TailItemFmt {
    # [doc = "specification constructor for `tail_item`."] pub open spec fn spec_inner() -> TailItemFmtSpec {
        Named ("tail_item",
        Mapped {
            inner: Pair (U16Be,
            Bind (U16Be,
            | len: u16 | Varied (len))),
            mapper: BiMap (TailItemForward,
            TailItemReverse),
        }
        )
    }
}


# [doc = "named format combinator for `tail_list`."]
# [derive (Clone, Copy)]
pub struct TailListFmt ;

pub type TailListFmtSpec = Named < AndThen < Tail, RepeatTillEnd < TailItemFmt > > > ;

impl TailListFmt {
    # [doc = "specification constructor for `tail_list`."] pub open spec fn spec_inner() -> TailListFmtSpec {
        Named ("tail_list",
        AndThen (Tail,
        RepeatTillEnd (TailItemFmt)))
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for TailItemFmt {
        type PVal = TailItemSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TailItemFmt {
        type Val = TailItemSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TailItemFmt {
        type SValue = TailItemSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TailItemFmt {
        type SVal = TailItemSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TailItemFmt {
        type T = TailItemSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TailListFmt {
        type PVal = TailListSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TailListFmt {
        type Val = TailListSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TailListFmt {
        type SValue = TailListSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TailListFmt {
        type SVal = TailListSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TailListFmt {
        type T = TailListSpec ;
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
        TailItemSpec::lemma_from_into,
        TailItemSpec::lemma_into_from,
    };

    impl SafeParser for TailItemFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TailItemFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TailItemFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TailItemFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TailItemFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TailItemFmt as SpecParser>::spec_parse) ;
            reveal(< TailItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TailItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TailItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TailItemFmt as SpecParser>::spec_parse) ;
            reveal(< TailItemFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TailItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TailItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TailItemFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TailItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TailItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TailItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TailItemFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TailItemFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TailItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TailItemFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TailItemFmt as SpecParser>::spec_parse) ;
            reveal(< TailItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TailItemFmt as Consistency>::consistent) ;
            reveal(< TailItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TailItemSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TailItemSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TailItemFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TailItemFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TailItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TailItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TailItemFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TailItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TailItemFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TailItemFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TailItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TailItemFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TailListFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TailListFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TailListFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TailListFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TailListFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TailListFmt as SpecParser>::spec_parse) ;
            reveal(< TailListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TailListFmt as SpecParser>::spec_parse) ;
            reveal(< TailListFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl GoodSerializer for TailListFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TailListFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TailListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TailListFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TailListFmt as SpecParser>::spec_parse) ;
            reveal(< TailListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TailListFmt as Consistency>::consistent) ;
            reveal(< TailListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TailListFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TailListFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializers for TailListFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TailListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TailListFmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for TailItemFmt {
        type PT = TailItem<'i>;

        fn min_byte_len(&self) -> usize {
            4
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TailItemFmt as SpecParser>::spec_parse);
            reveal(<TailItem as DeepView>::deep_view);
            reveal(TailItemSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, tag) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, len) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, body) = (Varied (len)).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = TailItem {
                tag,
                len,
                body,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TailItem<'i>> for TailItemFmt {
        fn serialize_into(&self, v: &TailItem<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TailItemFmt as SpecSerializer>::spec_serialize);
            reveal(<TailItemFmt as SpecByteLen>::byte_len);
            reveal(<TailItem as DeepView>::deep_view);
            reveal(TailItemSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TailItem {
                tag,
                len,
                body,
            } = v;
            U16Be.serialize_into(tag, obuf);
            U16Be.serialize_into(len, obuf);
            Varied (*len).serialize_into(* body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TailItem<'i>> for TailItemFmt {
        fn prepare(&self, v: &TailItem<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TailItemFmt as SpecByteLen>::byte_len);
            reveal(<TailItem as DeepView>::deep_view);
            reveal(TailItemSpec::into_structural);
            let TailItem {
                tag,
                len,
                body,
            } = v;
            let l1 = (U16Be).prepare (tag) ?;
            let l2 = (U16Be).prepare (len) ?;
            let l3 = (Varied (*len)).prepare (body) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for TailListFmt {
        type PT = TailList<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TailListFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = AndThen (Tail, Star (TailItemFmt)).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TailList<'i>> for TailListFmt {
        fn serialize_into(&self, v: &TailList<'i>, obuf: &mut Output) {
            reveal(<TailListFmt as SpecSerializer>::spec_serialize);
            reveal(<TailListFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            AndThen (Tail, Star (TailItemFmt)).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TailList<'i>> for TailListFmt {
        fn prepare(&self, v: &TailList<'i>) -> Result<usize, PreSerializeError> {
            broadcast use vest_lib::combinators::bytes::spec::tail_and_then_lemmas;
            reveal(<TailListFmt as SpecByteLen>::byte_len);
            (AndThen (Tail, Star (TailItemFmt))).prepare (v)
        }
    }

}
}
