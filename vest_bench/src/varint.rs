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
# [doc = "data type for `varint_item`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct VarintItem<'i> {
    pub len: u64,
    pub data: &'i [u8],
}
# [verifier::ext_equal]
pub struct VarintItemSpec < T0 = u64, T1 = Seq < u8 > > {
    pub len: T0,
    pub data: T1,
}
pub type VarintItemInner = (u64, Seq < u8 >) ;
impl<'i> DeepView for VarintItem<'i> {
    type V = VarintItemSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        VarintItemSpec {
            len: self.len.deep_view(),
            data: self.data.deep_view(),
        }
    }
}
impl<'i> VarintItem<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().len == self.len.deep_view(),
    self.deep_view().data == self.data.deep_view(),
    {
        reveal(< VarintItem as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > VarintItemSpec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    T1)) -> Self {
        let (len,
        data) = input ;
        Self {
            len,
            data
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    T1) {
        let Self {
            len,
            data
        }
        = self ;
        (len,
        data)
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(VarintItemSpec::from_structural) ;
        reveal(VarintItemSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    T1)) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(VarintItemSpec::from_structural) ;
        reveal(VarintItemSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            len,
            data
        }
        => (len,
        data),
    }
   ,
    {
        reveal(VarintItemSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct VarintItemForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct VarintItemReverse ;
impl SpecMap for VarintItemForward {
    type Input = VarintItemInner ;
    type Output = VarintItemSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        VarintItemSpec::from_structural (input)
    }
}
impl SpecMap for VarintItemReverse {
    type Input = VarintItemSpec ;
    type Output = VarintItemInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `varint_list`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct VarintList<'i> {
    pub count: u64,
    pub items: Vec < VarintItem<'i> >,
}
# [verifier::ext_equal]
pub struct VarintListSpec < T0 = u64, T1 = Seq < VarintItemSpec > > {
    pub count: T0,
    pub items: T1,
}
pub type VarintListInner = (u64, Seq < VarintItemSpec >) ;
impl<'i> DeepView for VarintList<'i> {
    type V = VarintListSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        VarintListSpec {
            count: self.count.deep_view(),
            items: self.items.deep_view(),
        }
    }
}
impl<'i> VarintList<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().count == self.count.deep_view(),
    self.deep_view().items == self.items.deep_view(),
    {
        reveal(< VarintList as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > VarintListSpec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    T1)) -> Self {
        let (count,
        items) = input ;
        Self {
            count,
            items
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    T1) {
        let Self {
            count,
            items
        }
        = self ;
        (count,
        items)
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(VarintListSpec::from_structural) ;
        reveal(VarintListSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    T1)) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(VarintListSpec::from_structural) ;
        reveal(VarintListSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            count,
            items
        }
        => (count,
        items),
    }
   ,
    {
        reveal(VarintListSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct VarintListForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct VarintListReverse ;
impl SpecMap for VarintListForward {
    type Input = VarintListInner ;
    type Output = VarintListSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        VarintListSpec::from_structural (input)
    }
}
impl SpecMap for VarintListReverse {
    type Input = VarintListSpec ;
    type Output = VarintListInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `varint_item`."]
# [derive (Clone, Copy)]
pub struct VarintItemFmt ;

pub type VarintItemFmtSpec = Named < Mapped < Bind < VarInt < true >, spec_fn (u64) -> Varied < u64 > >, BiMap < VarintItemForward, VarintItemReverse >> > ;

impl VarintItemFmt {
    # [doc = "specification constructor for `varint_item`."] pub open spec fn spec_inner() -> VarintItemFmtSpec {
        Named ("varint_item",
        Mapped {
            inner: Bind (VarInt::< true >,
            | len: u64 | Varied (len)),
            mapper: BiMap (VarintItemForward,
            VarintItemReverse),
        }
        )
    }
}


# [doc = "named format combinator for `varint_list`."]
# [derive (Clone, Copy)]
pub struct VarintListFmt ;

pub type VarintListFmtSpec = Named < Mapped < Bind < VarInt < true >, spec_fn (u64) -> RepeatN < VarintItemFmt, u64 > >, BiMap < VarintListForward, VarintListReverse >> > ;

impl VarintListFmt {
    # [doc = "specification constructor for `varint_list`."] pub open spec fn spec_inner() -> VarintListFmtSpec {
        Named ("varint_list",
        Mapped {
            inner: Bind (VarInt::< true >,
            | count: u64 | RepeatN (count,
            VarintItemFmt)),
            mapper: BiMap (VarintListForward,
            VarintListReverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for VarintItemFmt {
        type PVal = VarintItemSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for VarintItemFmt {
        type Val = VarintItemSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for VarintItemFmt {
        type SValue = VarintItemSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for VarintItemFmt {
        type SVal = VarintItemSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for VarintItemFmt {
        type T = VarintItemSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for VarintListFmt {
        type PVal = VarintListSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for VarintListFmt {
        type Val = VarintListSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for VarintListFmt {
        type SValue = VarintListSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for VarintListFmt {
        type SVal = VarintListSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for VarintListFmt {
        type T = VarintListSpec ;
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
        VarintItemSpec::lemma_from_into,
        VarintItemSpec::lemma_into_from,
        VarintListSpec::lemma_from_into,
        VarintListSpec::lemma_into_from,
    };

    impl SafeParser for VarintItemFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for VarintItemFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for VarintItemFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecParser>::spec_parse) ;
            reveal(< VarintItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: VarintItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                VarintItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecParser>::spec_parse) ;
            reveal(< VarintItemFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: VarintItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                VarintItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for VarintItemFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< VarintItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for VarintItemFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< VarintItemFmt as SpecSerializer>::spec_serialize) ;
            reveal(< VarintItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for VarintItemFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecParser>::spec_parse) ;
            reveal(< VarintItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< VarintItemFmt as Consistency>::consistent) ;
            reveal(< VarintItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: VarintItemSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                VarintItemSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for VarintItemFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: VarintItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                VarintItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for VarintItemFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< VarintItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< VarintItemFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for VarintItemFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< VarintItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< VarintItemFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for VarintListFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< VarintListFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for VarintListFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< VarintListFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for VarintListFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< VarintListFmt as SpecParser>::spec_parse) ;
            reveal(< VarintListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: VarintListInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                VarintListSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< VarintListFmt as SpecParser>::spec_parse) ;
            reveal(< VarintListFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: VarintListInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                VarintListSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for VarintListFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< VarintListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< VarintListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< VarintListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for VarintListFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< VarintListFmt as SpecSerializer>::spec_serialize) ;
            reveal(< VarintListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for VarintListFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< VarintListFmt as SpecParser>::spec_parse) ;
            reveal(< VarintListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< VarintListFmt as Consistency>::consistent) ;
            reveal(< VarintListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: VarintListSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                VarintListSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for VarintListFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< VarintListFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: VarintListInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                VarintListSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for VarintListFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< VarintListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< VarintListFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for VarintListFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< VarintListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< VarintListFmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for VarintItemFmt {
        type PT = VarintItem<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<VarintItemFmt as SpecParser>::spec_parse);
            reveal(<VarintItem as DeepView>::deep_view);
            reveal(VarintItemSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, len) = (VarInt::< true >).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, data) = (Varied (len)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = VarintItem {
                len,
                data,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, VarintItem<'i>> for VarintItemFmt {
        fn serialize_into(&self, v: &VarintItem<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<VarintItemFmt as SpecSerializer>::spec_serialize);
            reveal(<VarintItemFmt as SpecByteLen>::byte_len);
            reveal(<VarintItem as DeepView>::deep_view);
            reveal(VarintItemSpec::into_structural);
            let ghost old_obuf = obuf@;

            let VarintItem {
                len,
                data,
            } = v;
            VarInt::< true >.serialize_into(len, obuf);
            Varied (*len).serialize_into(* data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<VarintItem<'i>> for VarintItemFmt {
        fn prepare(&self, v: &VarintItem<'i>) -> Result<usize, PreSerializeError> {
            reveal(<VarintItemFmt as SpecByteLen>::byte_len);
            reveal(<VarintItem as DeepView>::deep_view);
            reveal(VarintItemSpec::into_structural);
            let VarintItem {
                len,
                data,
            } = v;
            let l1 = (VarInt::< true >).prepare (len) ?;
            let l2 = (Varied (*len)).prepare (data) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for VarintListFmt {
        type PT = VarintList<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<VarintListFmt as SpecParser>::spec_parse);
            reveal(<VarintList as DeepView>::deep_view);
            reveal(VarintListSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, count) = (VarInt::< true >).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, items) = (RepeatN (count, VarintItemFmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = VarintList {
                count,
                items,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, VarintList<'i>> for VarintListFmt {
        fn serialize_into(&self, v: &VarintList<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<VarintListFmt as SpecSerializer>::spec_serialize);
            reveal(<VarintListFmt as SpecByteLen>::byte_len);
            reveal(<VarintList as DeepView>::deep_view);
            reveal(VarintListSpec::into_structural);
            let ghost old_obuf = obuf@;

            let VarintList {
                count,
                items,
            } = v;
            VarInt::< true >.serialize_into(count, obuf);
            RepeatN (* count, VarintItemFmt).serialize_into(items, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<VarintList<'i>> for VarintListFmt {
        fn prepare(&self, v: &VarintList<'i>) -> Result<usize, PreSerializeError> {
            reveal(<VarintListFmt as SpecByteLen>::byte_len);
            reveal(<VarintList as DeepView>::deep_view);
            reveal(VarintListSpec::into_structural);
            let VarintList {
                count,
                items,
            } = v;
            let l1 = (VarInt::< true >).prepare (count) ?;
            let l2 = (RepeatN (* count, VarintItemFmt)).prepare (items) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
