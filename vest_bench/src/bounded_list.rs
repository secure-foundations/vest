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
# [doc = "data type for `bounded_item`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct BoundedItem<'i> {
    pub tag: u16,
    pub len: u16,
    pub body: &'i [u8],
}
# [verifier::ext_equal]
pub struct BoundedItemSpec < T0 = u16, T1 = u16, T2 = Seq < u8 > > {
    pub tag: T0,
    pub len: T1,
    pub body: T2,
}
pub type BoundedItemInner = (u16, (u16, Seq < u8 >)) ;
impl<'i> DeepView for BoundedItem<'i> {
    type V = BoundedItemSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        BoundedItemSpec {
            tag: self.tag.deep_view(),
            len: self.len.deep_view(),
            body: self.body.deep_view(),
        }
    }
}
impl<'i> BoundedItem<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().tag == self.tag.deep_view(),
    self.deep_view().len == self.len.deep_view(),
    self.deep_view().body == self.body.deep_view(),
    {
        reveal(< BoundedItem as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > BoundedItemSpec < T0, T1, T2 > {
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
        reveal(BoundedItemSpec::from_structural) ;
        reveal(BoundedItemSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(BoundedItemSpec::from_structural) ;
        reveal(BoundedItemSpec::into_structural) ;
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
        reveal(BoundedItemSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BoundedItemForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BoundedItemReverse ;
impl SpecMap for BoundedItemForward {
    type Input = BoundedItemInner ;
    type Output = BoundedItemSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        BoundedItemSpec::from_structural (input)
    }
}
impl SpecMap for BoundedItemReverse {
    type Input = BoundedItemSpec ;
    type Output = BoundedItemInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `bounded_list`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct BoundedList<'i> {
    pub byte_len: u32,
    pub items: Vec < BoundedItem<'i> >,
}
# [verifier::ext_equal]
pub struct BoundedListSpec < T0 = u32, T1 = Seq < BoundedItemSpec > > {
    pub byte_len: T0,
    pub items: T1,
}
pub type BoundedListInner = (u32, Seq < BoundedItemSpec >) ;
impl<'i> DeepView for BoundedList<'i> {
    type V = BoundedListSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        BoundedListSpec {
            byte_len: self.byte_len.deep_view(),
            items: self.items.deep_view(),
        }
    }
}
impl<'i> BoundedList<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().byte_len == self.byte_len.deep_view(),
    self.deep_view().items == self.items.deep_view(),
    {
        reveal(< BoundedList as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > BoundedListSpec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    T1)) -> Self {
        let (byte_len,
        items) = input ;
        Self {
            byte_len,
            items
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    T1) {
        let Self {
            byte_len,
            items
        }
        = self ;
        (byte_len,
        items)
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(BoundedListSpec::from_structural) ;
        reveal(BoundedListSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    T1)) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(BoundedListSpec::from_structural) ;
        reveal(BoundedListSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            byte_len,
            items
        }
        => (byte_len,
        items),
    }
   ,
    {
        reveal(BoundedListSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BoundedListForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BoundedListReverse ;
impl SpecMap for BoundedListForward {
    type Input = BoundedListInner ;
    type Output = BoundedListSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        BoundedListSpec::from_structural (input)
    }
}
impl SpecMap for BoundedListReverse {
    type Input = BoundedListSpec ;
    type Output = BoundedListInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `bounded_item`."]
# [derive (Clone, Copy)]
pub struct BoundedItemFmt ;

pub type BoundedItemFmtSpec = Named < Mapped < Pair < U16Be, Bind < U16Be, spec_fn (u16) -> Varied < u16 > > >, BiMap < BoundedItemForward, BoundedItemReverse >> > ;

impl BoundedItemFmt {
    # [doc = "specification constructor for `bounded_item`."] pub open spec fn spec_inner() -> BoundedItemFmtSpec {
        Named ("bounded_item",
        Mapped {
            inner: Pair (U16Be,
            Bind (U16Be,
            | len: u16 | Varied (len))),
            mapper: BiMap (BoundedItemForward,
            BoundedItemReverse),
        }
        )
    }
}


# [doc = "named format combinator for `bounded_list`."]
# [derive (Clone, Copy)]
pub struct BoundedListFmt ;

pub type BoundedListFmtSpec = Named < Mapped < Bind < U32Be, spec_fn (u32) -> ExactLen < RepeatTillEnd < BoundedItemFmt >, u32 > >, BiMap < BoundedListForward, BoundedListReverse >> > ;

impl BoundedListFmt {
    # [doc = "specification constructor for `bounded_list`."] pub open spec fn spec_inner() -> BoundedListFmtSpec {
        Named ("bounded_list",
        Mapped {
            inner: Bind (U32Be,
            | byte_len: u32 | ExactLen (byte_len,
            RepeatTillEnd (BoundedItemFmt))),
            mapper: BiMap (BoundedListForward,
            BoundedListReverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for BoundedItemFmt {
        type PVal = BoundedItemSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for BoundedItemFmt {
        type Val = BoundedItemSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for BoundedItemFmt {
        type SValue = BoundedItemSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for BoundedItemFmt {
        type SVal = BoundedItemSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for BoundedItemFmt {
        type T = BoundedItemSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for BoundedListFmt {
        type PVal = BoundedListSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for BoundedListFmt {
        type Val = BoundedListSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for BoundedListFmt {
        type SValue = BoundedListSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for BoundedListFmt {
        type SVal = BoundedListSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for BoundedListFmt {
        type T = BoundedListSpec ;
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
        BoundedItemSpec::lemma_from_into,
        BoundedItemSpec::lemma_into_from,
        BoundedListSpec::lemma_from_into,
        BoundedListSpec::lemma_into_from,
    };

    impl SafeParser for BoundedItemFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for BoundedItemFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for BoundedItemFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecParser>::spec_parse) ;
            reveal(< BoundedItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BoundedItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BoundedItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecParser>::spec_parse) ;
            reveal(< BoundedItemFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BoundedItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BoundedItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for BoundedItemFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BoundedItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for BoundedItemFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< BoundedItemFmt as SpecSerializer>::spec_serialize) ;
            reveal(< BoundedItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for BoundedItemFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecParser>::spec_parse) ;
            reveal(< BoundedItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BoundedItemFmt as Consistency>::consistent) ;
            reveal(< BoundedItemFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: BoundedItemSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                BoundedItemSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for BoundedItemFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BoundedItemInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BoundedItemSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for BoundedItemFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< BoundedItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BoundedItemFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for BoundedItemFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< BoundedItemFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BoundedItemFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for BoundedListFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for BoundedListFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for BoundedListFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecParser>::spec_parse) ;
            reveal(< BoundedListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BoundedListInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BoundedListSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecParser>::spec_parse) ;
            reveal(< BoundedListFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BoundedListInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BoundedListSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for BoundedListFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BoundedListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for BoundedListFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< BoundedListFmt as SpecSerializer>::spec_serialize) ;
            reveal(< BoundedListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for BoundedListFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecParser>::spec_parse) ;
            reveal(< BoundedListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BoundedListFmt as Consistency>::consistent) ;
            reveal(< BoundedListFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: BoundedListSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                BoundedListSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for BoundedListFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BoundedListInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BoundedListSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for BoundedListFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< BoundedListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BoundedListFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for BoundedListFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< BoundedListFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BoundedListFmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for BoundedItemFmt {
        type PT = BoundedItem<'i>;

        fn min_byte_len(&self) -> usize {
            4
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<BoundedItemFmt as SpecParser>::spec_parse);
            reveal(<BoundedItem as DeepView>::deep_view);
            reveal(BoundedItemSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, tag) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, len) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, body) = (Varied (len)).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = BoundedItem {
                tag,
                len,
                body,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, BoundedItem<'i>> for BoundedItemFmt {
        fn serialize_into(&self, v: &BoundedItem<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<BoundedItemFmt as SpecSerializer>::spec_serialize);
            reveal(<BoundedItemFmt as SpecByteLen>::byte_len);
            reveal(<BoundedItem as DeepView>::deep_view);
            reveal(BoundedItemSpec::into_structural);
            let ghost old_obuf = obuf@;

            let BoundedItem {
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

    impl<'i> Prepare<BoundedItem<'i>> for BoundedItemFmt {
        fn prepare(&self, v: &BoundedItem<'i>) -> Result<usize, PreSerializeError> {
            reveal(<BoundedItemFmt as SpecByteLen>::byte_len);
            reveal(<BoundedItem as DeepView>::deep_view);
            reveal(BoundedItemSpec::into_structural);
            let BoundedItem {
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



    impl<'i> Parser<&'i [u8]> for BoundedListFmt {
        type PT = BoundedList<'i>;

        fn min_byte_len(&self) -> usize {
            4
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<BoundedListFmt as SpecParser>::spec_parse);
            reveal(<BoundedList as DeepView>::deep_view);
            reveal(BoundedListSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, byte_len) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, items) = (ExactLen (byte_len, Star (BoundedItemFmt))).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = BoundedList {
                byte_len,
                items,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, BoundedList<'i>> for BoundedListFmt {
        fn serialize_into(&self, v: &BoundedList<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<BoundedListFmt as SpecSerializer>::spec_serialize);
            reveal(<BoundedListFmt as SpecByteLen>::byte_len);
            reveal(<BoundedList as DeepView>::deep_view);
            reveal(BoundedListSpec::into_structural);
            let ghost old_obuf = obuf@;

            let BoundedList {
                byte_len,
                items,
            } = v;
            U32Be.serialize_into(byte_len, obuf);
            ExactLen (* byte_len, Star (BoundedItemFmt)).serialize_into(items, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<BoundedList<'i>> for BoundedListFmt {
        fn prepare(&self, v: &BoundedList<'i>) -> Result<usize, PreSerializeError> {
            reveal(<BoundedListFmt as SpecByteLen>::byte_len);
            reveal(<BoundedList as DeepView>::deep_view);
            reveal(BoundedListSpec::into_structural);
            let BoundedList {
                byte_len,
                items,
            } = v;
            let l1 = (U32Be).prepare (byte_len) ?;
            let l2 = (ExactLen (* byte_len, Star (BoundedItemFmt))).prepare (items) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
