#![allow(warnings)]
use vest_lib::combinators::mapped::spec::*;
use vest_lib::combinators::recursive::*;
use vest_lib::combinators::*;
use vest_lib::core::exec::bytes_eq;
use vest_lib::core::exec::input::{InputBuf, InputSlice};
use vest_lib::core::exec::output::OutputBuf;
use vest_lib::core::exec::parser::*;
use vest_lib::core::exec::serializer::*;
use vest_lib::core::exec::ParseError;
use vest_lib::core::{proof::*, spec::*};
use vest_lib::primitives::btcvarint::VarInt;
use vest_lib::primitives::leb128::ULeb128;
use vest_lib::Never;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `opaque_u16`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct OpaqueU16<'i> {
    pub l: u16,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct OpaqueU16Spec<T0 = u16, T1 = Seq<u8>> {
    pub l: T0,
    pub data: T1,
}

pub type OpaqueU16Inner = (u16, Seq<u8>);

impl<'i> DeepView for OpaqueU16<'i> {
    type V = OpaqueU16Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        OpaqueU16Spec { l: self.l.deep_view(), data: self.data.deep_view() }
    }
}

impl<'i> OpaqueU16<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().l == self.l.deep_view(),
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<OpaqueU16 as DeepView>::deep_view);
    }
}

impl<T0, T1> OpaqueU16Spec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (l, data) = input;
        Self { l, data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { l, data } = self;
        (l, data)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(OpaqueU16Spec::from_structural);
        reveal(OpaqueU16Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(OpaqueU16Spec::from_structural);
        reveal(OpaqueU16Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { l, data } => (l, data),
            },
    {
        reveal(OpaqueU16Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct OpaqueU16Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct OpaqueU16Reverse;

impl SpecMap for OpaqueU16Forward {
    type Input = OpaqueU16Inner;

    type Output = OpaqueU16Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        OpaqueU16Spec::from_structural(input)
    }
}

impl SpecMap for OpaqueU16Reverse {
    type Input = OpaqueU16Spec;

    type Output = OpaqueU16Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `responder_id`."]
pub type ResponderId<'i> = OpaqueU16<'i>;

pub type ResponderIdSpec = OpaqueU16Spec;

# [doc = "data type for `responder_id_list`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct ResponderIdList<'i> {
    pub l: u16,
    pub list: Vec<ResponderId<'i>>,
}

# [verifier::ext_equal]
pub struct ResponderIdListSpec<T0 = u16, T1 = Seq<ResponderIdSpec>> {
    pub l: T0,
    pub list: T1,
}

pub type ResponderIdListInner = (u16, Seq<ResponderIdSpec>);

impl<'i> DeepView for ResponderIdList<'i> {
    type V = ResponderIdListSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        ResponderIdListSpec { l: self.l.deep_view(), list: self.list.deep_view() }
    }
}

impl<'i> ResponderIdList<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().l == self.l.deep_view(),
            self.deep_view().list == self.list.deep_view(),
    {
        reveal(<ResponderIdList as DeepView>::deep_view);
    }
}

impl<T0, T1> ResponderIdListSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (l, list) = input;
        Self { l, list }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { l, list } = self;
        (l, list)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ResponderIdListSpec::from_structural);
        reveal(ResponderIdListSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ResponderIdListSpec::from_structural);
        reveal(ResponderIdListSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { l, list } => (l, list),
            },
    {
        reveal(ResponderIdListSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ResponderIdListForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ResponderIdListReverse;

impl SpecMap for ResponderIdListForward {
    type Input = ResponderIdListInner;

    type Output = ResponderIdListSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ResponderIdListSpec::from_structural(input)
    }
}

impl SpecMap for ResponderIdListReverse {
    type Input = ResponderIdListSpec;

    type Output = ResponderIdListInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `repeat_fix`."]
pub type RepeatFix = [u16; 32];

pub type RepeatFixSpec = Seq<u16>;

# [doc = "data type for `repeat_dyn`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct RepeatDyn<'i> {
    pub l: u64,
    pub data: Vec<ResponderIdList<'i>>,
}

# [verifier::ext_equal]
pub struct RepeatDynSpec<T0 = u64, T1 = Seq<ResponderIdListSpec>> {
    pub l: T0,
    pub data: T1,
}

pub type RepeatDynInner = (u64, Seq<ResponderIdListSpec>);

impl<'i> DeepView for RepeatDyn<'i> {
    type V = RepeatDynSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        RepeatDynSpec { l: self.l.deep_view(), data: self.data.deep_view() }
    }
}

impl<'i> RepeatDyn<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().l == self.l.deep_view(),
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<RepeatDyn as DeepView>::deep_view);
    }
}

impl<T0, T1> RepeatDynSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (l, data) = input;
        Self { l, data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { l, data } = self;
        (l, data)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(RepeatDynSpec::from_structural);
        reveal(RepeatDynSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(RepeatDynSpec::from_structural);
        reveal(RepeatDynSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { l, data } => (l, data),
            },
    {
        reveal(RepeatDynSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct RepeatDynForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct RepeatDynReverse;

impl SpecMap for RepeatDynForward {
    type Input = RepeatDynInner;

    type Output = RepeatDynSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        RepeatDynSpec::from_structural(input)
    }
}

impl SpecMap for RepeatDynReverse {
    type Input = RepeatDynSpec;

    type Output = RepeatDynInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `opaque_u16`."]
# [derive (Clone, Copy)]
pub struct OpaqueU16Fmt;

pub type OpaqueU16FmtSpec = Named<
    Mapped<
        Bind<Refined<U16Le, PredFnSpec<u16>>, spec_fn(u16) -> Varied<u16>>,
        BiMap<OpaqueU16Forward, OpaqueU16Reverse>,
    >,
>;

impl OpaqueU16Fmt {
    # [doc = "specification constructor for `opaque_u16`."]
    pub open spec fn spec_inner() -> OpaqueU16FmtSpec {
        Named(
            "opaque_u16",
            Mapped {
                inner: Bind(Refined(U16Le, |x: u16| x >= 1 && x <= 65535), |l: u16| Varied(l)),
                mapper: BiMap(OpaqueU16Forward, OpaqueU16Reverse),
            },
        )
    }
}

# [doc = "named format combinator for `responder_id`."]
# [derive (Clone, Copy)]
pub struct ResponderIdFmt;

pub type ResponderIdFmtSpec = Named<OpaqueU16Fmt>;

impl ResponderIdFmt {
    # [doc = "specification constructor for `responder_id`."]
    pub open spec fn spec_inner() -> ResponderIdFmtSpec {
        Named("responder_id", OpaqueU16Fmt)
    }
}

# [doc = "named format combinator for `responder_id_list`."]
# [derive (Clone, Copy)]
pub struct ResponderIdListFmt;

pub type ResponderIdListFmtSpec = Named<
    Mapped<
        Bind<
            Refined<U16Le, PredFnSpec<u16>>,
            spec_fn(u16) -> ExactLen<RepeatTillEnd<ResponderIdFmt>, u16>,
        >,
        BiMap<ResponderIdListForward, ResponderIdListReverse>,
    >,
>;

impl ResponderIdListFmt {
    # [doc = "specification constructor for `responder_id_list`."]
    pub open spec fn spec_inner() -> ResponderIdListFmtSpec {
        Named(
            "responder_id_list",
            Mapped {
                inner: Bind(
                    Refined(U16Le, |x: u16| x >= 0 && x <= 65535),
                    |l: u16| ExactLen(l, RepeatTillEnd(ResponderIdFmt)),
                ),
                mapper: BiMap(ResponderIdListForward, ResponderIdListReverse),
            },
        )
    }
}

# [doc = "named format combinator for `repeat_fix`."]
# [derive (Clone, Copy)]
pub struct RepeatFixFmt;

pub type RepeatFixFmtSpec = Named<Array<32, U16Le>>;

impl RepeatFixFmt {
    # [doc = "specification constructor for `repeat_fix`."]
    pub open spec fn spec_inner() -> RepeatFixFmtSpec {
        Named("repeat_fix", Array::<32, _>(U16Le))
    }
}

# [doc = "named format combinator for `repeat_dyn`."]
# [derive (Clone, Copy)]
pub struct RepeatDynFmt;

pub type RepeatDynFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> RepeatN<ResponderIdListFmt, u64>>,
        BiMap<RepeatDynForward, RepeatDynReverse>,
    >,
>;

impl RepeatDynFmt {
    # [doc = "specification constructor for `repeat_dyn`."]
    pub open spec fn spec_inner() -> RepeatDynFmtSpec {
        Named(
            "repeat_dyn",
            Mapped {
                inner: Bind(VarInt::<true>, |l: u64| RepeatN(l, ResponderIdListFmt)),
                mapper: BiMap(RepeatDynForward, RepeatDynReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for OpaqueU16Fmt {
        type PVal = OpaqueU16Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for OpaqueU16Fmt {
        type Val = OpaqueU16Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for OpaqueU16Fmt {
        type SValue = OpaqueU16Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OpaqueU16Fmt {
        type SVal = OpaqueU16Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for OpaqueU16Fmt {
        type T = OpaqueU16Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ResponderIdFmt {
        type PVal = ResponderIdSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ResponderIdFmt {
        type Val = ResponderIdSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ResponderIdFmt {
        type SValue = ResponderIdSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ResponderIdFmt {
        type SVal = ResponderIdSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ResponderIdFmt {
        type T = ResponderIdSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ResponderIdListFmt {
        type PVal = ResponderIdListSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ResponderIdListFmt {
        type Val = ResponderIdListSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ResponderIdListFmt {
        type SValue = ResponderIdListSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ResponderIdListFmt {
        type SVal = ResponderIdListSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ResponderIdListFmt {
        type T = ResponderIdListSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for RepeatFixFmt {
        type PVal = RepeatFixSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for RepeatFixFmt {
        type Val = RepeatFixSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for RepeatFixFmt {
        type SValue = RepeatFixSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for RepeatFixFmt {
        type SVal = RepeatFixSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for RepeatFixFmt {
        type T = RepeatFixSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for RepeatDynFmt {
        type PVal = RepeatDynSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for RepeatDynFmt {
        type Val = RepeatDynSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for RepeatDynFmt {
        type SValue = RepeatDynSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for RepeatDynFmt {
        type SVal = RepeatDynSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for RepeatDynFmt {
        type T = RepeatDynSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
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
        OpaqueU16Spec::lemma_from_into,
        OpaqueU16Spec::lemma_into_from,
        ResponderIdListSpec::lemma_from_into,
        ResponderIdListSpec::lemma_into_from,
        RepeatDynSpec::lemma_from_into,
        RepeatDynSpec::lemma_into_from,
    };

    impl SafeParser for OpaqueU16Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for OpaqueU16Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for OpaqueU16Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecParser>::spec_parse);
            reveal(<OpaqueU16Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: OpaqueU16Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OpaqueU16Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecParser>::spec_parse);
            reveal(<OpaqueU16Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: OpaqueU16Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OpaqueU16Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for OpaqueU16Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OpaqueU16Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for OpaqueU16Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<OpaqueU16Fmt as SpecSerializer>::spec_serialize);
            reveal(<OpaqueU16Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for OpaqueU16Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecParser>::spec_parse);
            reveal(<OpaqueU16Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OpaqueU16Fmt as Consistency>::consistent);
            reveal(<OpaqueU16Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: OpaqueU16Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                OpaqueU16Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OpaqueU16Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: OpaqueU16Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OpaqueU16Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for OpaqueU16Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<OpaqueU16Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OpaqueU16Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for OpaqueU16Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<OpaqueU16Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OpaqueU16Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ResponderIdFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ResponderIdFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ResponderIdFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecParser>::spec_parse);
            reveal(<ResponderIdFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecParser>::spec_parse);
            reveal(<ResponderIdFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ResponderIdFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ResponderIdFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ResponderIdFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ResponderIdFmt as SpecSerializer>::spec_serialize);
            reveal(<ResponderIdFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ResponderIdFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecParser>::spec_parse);
            reveal(<ResponderIdFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ResponderIdFmt as Consistency>::consistent);
            reveal(<ResponderIdFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ResponderIdFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ResponderIdFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ResponderIdFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ResponderIdFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ResponderIdFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ResponderIdFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ResponderIdFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ResponderIdListFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ResponderIdListFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ResponderIdListFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecParser>::spec_parse);
            reveal(<ResponderIdListFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: ResponderIdListInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ResponderIdListSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecParser>::spec_parse);
            reveal(<ResponderIdListFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ResponderIdListInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ResponderIdListSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ResponderIdListFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ResponderIdListFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ResponderIdListFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ResponderIdListFmt as SpecSerializer>::spec_serialize);
            reveal(<ResponderIdListFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ResponderIdListFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecParser>::spec_parse);
            reveal(<ResponderIdListFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ResponderIdListFmt as Consistency>::consistent);
            reveal(<ResponderIdListFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: ResponderIdListSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ResponderIdListSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ResponderIdListFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: ResponderIdListInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ResponderIdListSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ResponderIdListFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ResponderIdListFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ResponderIdListFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ResponderIdListFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ResponderIdListFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ResponderIdListFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for RepeatFixFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for RepeatFixFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for RepeatFixFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecParser>::spec_parse);
            reveal(<RepeatFixFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecParser>::spec_parse);
            reveal(<RepeatFixFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for RepeatFixFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<RepeatFixFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for RepeatFixFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<RepeatFixFmt as SpecSerializer>::spec_serialize);
            reveal(<RepeatFixFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for RepeatFixFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecParser>::spec_parse);
            reveal(<RepeatFixFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<RepeatFixFmt as Consistency>::consistent);
            reveal(<RepeatFixFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for RepeatFixFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for RepeatFixFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<RepeatFixFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<RepeatFixFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for RepeatFixFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<RepeatFixFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<RepeatFixFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for RepeatDynFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for RepeatDynFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for RepeatDynFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecParser>::spec_parse);
            reveal(<RepeatDynFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: RepeatDynInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                RepeatDynSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecParser>::spec_parse);
            reveal(<RepeatDynFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: RepeatDynInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                RepeatDynSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for RepeatDynFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<RepeatDynFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for RepeatDynFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<RepeatDynFmt as SpecSerializer>::spec_serialize);
            reveal(<RepeatDynFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for RepeatDynFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecParser>::spec_parse);
            reveal(<RepeatDynFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<RepeatDynFmt as Consistency>::consistent);
            reveal(<RepeatDynFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: RepeatDynSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                RepeatDynSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for RepeatDynFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: RepeatDynInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                RepeatDynSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for RepeatDynFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<RepeatDynFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<RepeatDynFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for RepeatDynFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<RepeatDynFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<RepeatDynFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
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

    impl<'i> Parser<&'i [u8]> for OpaqueU16Fmt {
        type PT = OpaqueU16<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<OpaqueU16Fmt as SpecParser>::spec_parse);
            reveal(<OpaqueU16 as DeepView>::deep_view);
            reveal(OpaqueU16Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, l) = (U16Le).parse(&rest)?;
            if !(l >= 1 && l <= 65535) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, data) = (Varied(l)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = OpaqueU16 { l, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, OpaqueU16<'i>> for OpaqueU16Fmt {
        fn serialize_into(&self, v: &OpaqueU16<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<OpaqueU16Fmt as SpecSerializer>::spec_serialize);
            reveal(<OpaqueU16Fmt as SpecByteLen>::byte_len);
            reveal(<OpaqueU16 as DeepView>::deep_view);
            reveal(OpaqueU16Spec::into_structural);
            let ghost old_obuf = obuf@;

            let OpaqueU16 { l, data } = v;
            U16Le.serialize_into(l, obuf);
            Varied(*l).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<OpaqueU16<'i>> for OpaqueU16Fmt {
        fn prepare(&self, v: &OpaqueU16<'i>) -> Result<usize, PreSerializeError> {
            reveal(<OpaqueU16Fmt as SpecByteLen>::byte_len);
            reveal(<OpaqueU16 as DeepView>::deep_view);
            reveal(OpaqueU16Spec::into_structural);
            let OpaqueU16 { l, data } = v;
            let l1 = {
                if !(*l >= 1 && *l <= 65535) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (U16Le).prepare(l)
                }
            }?;
            let l2 = (Varied(*l)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for ResponderIdFmt {
        type PT = ResponderId<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ResponderIdFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Named("opaque_u16", OpaqueU16Fmt).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ResponderId<'i>> for ResponderIdFmt {
        fn serialize_into(&self, v: &ResponderId<'i>, obuf: &mut Output) {
            reveal(<ResponderIdFmt as SpecSerializer>::spec_serialize);
            reveal(<ResponderIdFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            OpaqueU16Fmt.serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ResponderId<'i>> for ResponderIdFmt {
        fn prepare(&self, v: &ResponderId<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ResponderIdFmt as SpecByteLen>::byte_len);
            Named("opaque_u16", OpaqueU16Fmt).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for ResponderIdListFmt {
        type PT = ResponderIdList<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ResponderIdListFmt as SpecParser>::spec_parse);
            reveal(<ResponderIdList as DeepView>::deep_view);
            reveal(ResponderIdListSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, l) = (U16Le).parse(&rest)?;
            if !(l >= 0 && l <= 65535) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, list) = (ExactLen(l, Star(ResponderIdFmt))).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = ResponderIdList { l, list };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ResponderIdList<'i>> for ResponderIdListFmt {
        fn serialize_into(&self, v: &ResponderIdList<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<ResponderIdListFmt as SpecSerializer>::spec_serialize);
            reveal(<ResponderIdListFmt as SpecByteLen>::byte_len);
            reveal(<ResponderIdList as DeepView>::deep_view);
            reveal(ResponderIdListSpec::into_structural);
            let ghost old_obuf = obuf@;

            let ResponderIdList { l, list } = v;
            U16Le.serialize_into(l, obuf);
            ExactLen(*l, Star(ResponderIdFmt)).serialize_into(list, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ResponderIdList<'i>> for ResponderIdListFmt {
        fn prepare(&self, v: &ResponderIdList<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ResponderIdListFmt as SpecByteLen>::byte_len);
            reveal(<ResponderIdList as DeepView>::deep_view);
            reveal(ResponderIdListSpec::into_structural);
            let ResponderIdList { l, list } = v;
            let l1 = {
                if !(*l >= 0 && *l <= 65535) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (U16Le).prepare(l)
                }
            }?;
            let l2 = (ExactLen(*l, Star(ResponderIdFmt))).prepare(list)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for RepeatFixFmt {
        type PT = RepeatFix;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<RepeatFixFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Array::<32, _>(U16Le).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, RepeatFix> for RepeatFixFmt {
        fn serialize_into(&self, v: &RepeatFix, obuf: &mut Output) {
            reveal(<RepeatFixFmt as SpecSerializer>::spec_serialize);
            reveal(<RepeatFixFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            Array::<32, _>(U16Le).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<RepeatFix> for RepeatFixFmt {
        fn prepare(&self, v: &RepeatFix) -> Result<usize, PreSerializeError> {
            reveal(<RepeatFixFmt as SpecByteLen>::byte_len);
            (Array::<32, _>(U16Le)).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for RepeatDynFmt {
        type PT = RepeatDyn<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<RepeatDynFmt as SpecParser>::spec_parse);
            reveal(<RepeatDyn as DeepView>::deep_view);
            reveal(RepeatDynSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, l) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, data) = (RepeatN(l, ResponderIdListFmt)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = RepeatDyn { l, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, RepeatDyn<'i>> for RepeatDynFmt {
        fn serialize_into(&self, v: &RepeatDyn<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<RepeatDynFmt as SpecSerializer>::spec_serialize);
            reveal(<RepeatDynFmt as SpecByteLen>::byte_len);
            reveal(<RepeatDyn as DeepView>::deep_view);
            reveal(RepeatDynSpec::into_structural);
            let ghost old_obuf = obuf@;

            let RepeatDyn { l, data } = v;
            VarInt::<true>.serialize_into(l, obuf);
            RepeatN(*l, ResponderIdListFmt).serialize_into(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<RepeatDyn<'i>> for RepeatDynFmt {
        fn prepare(&self, v: &RepeatDyn<'i>) -> Result<usize, PreSerializeError> {
            reveal(<RepeatDynFmt as SpecByteLen>::byte_len);
            reveal(<RepeatDyn as DeepView>::deep_view);
            reveal(RepeatDynSpec::into_structural);
            let RepeatDyn { l, data } = v;
            let l1 = (VarInt::<true>).prepare(l)?;
            let l2 = (RepeatN(*l, ResponderIdListFmt)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

}

} // verus!
