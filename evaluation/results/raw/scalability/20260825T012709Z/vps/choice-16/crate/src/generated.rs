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
# [doc = "data type for `choice_width16`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum ChoiceWidth16 {
    Variant0 (u8),
    Variant1 (u8),
    Variant2 (u8),
    Variant3 (u8),
    Variant4 (u8),
    Variant5 (u8),
    Variant6 (u8),
    Variant7 (u8),
    Variant8 (u8),
    Variant9 (u8),
    Variant10 (u8),
    Variant11 (u8),
    Variant12 (u8),
    Variant13 (u8),
    Variant14 (u8),
    Variant15 (u8),
}
# [verifier::ext_equal]
pub enum ChoiceWidth16Spec < T0 = u8, T1 = u8, T2 = u8, T3 = u8, T4 = u8, T5 = u8, T6 = u8, T7 = u8, T8 = u8, T9 = u8, T10 = u8, T11 = u8, T12 = u8, T13 = u8, T14 = u8, T15 = u8 > {
    Variant0 (T0),
    Variant1 (T1),
    Variant2 (T2),
    Variant3 (T3),
    Variant4 (T4),
    Variant5 (T5),
    Variant6 (T6),
    Variant7 (T7),
    Variant8 (T8),
    Variant9 (T9),
    Variant10 (T10),
    Variant11 (T11),
    Variant12 (T12),
    Variant13 (T13),
    Variant14 (T14),
    Variant15 (T15),
}
pub type ChoiceWidth16Inner = Sum < Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > >, Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > > > ;
impl DeepView for ChoiceWidth16 {
    type V = ChoiceWidth16Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            ChoiceWidth16::Variant0 (v) => ChoiceWidth16Spec::Variant0 (v.deep_view()),
            ChoiceWidth16::Variant1 (v) => ChoiceWidth16Spec::Variant1 (v.deep_view()),
            ChoiceWidth16::Variant2 (v) => ChoiceWidth16Spec::Variant2 (v.deep_view()),
            ChoiceWidth16::Variant3 (v) => ChoiceWidth16Spec::Variant3 (v.deep_view()),
            ChoiceWidth16::Variant4 (v) => ChoiceWidth16Spec::Variant4 (v.deep_view()),
            ChoiceWidth16::Variant5 (v) => ChoiceWidth16Spec::Variant5 (v.deep_view()),
            ChoiceWidth16::Variant6 (v) => ChoiceWidth16Spec::Variant6 (v.deep_view()),
            ChoiceWidth16::Variant7 (v) => ChoiceWidth16Spec::Variant7 (v.deep_view()),
            ChoiceWidth16::Variant8 (v) => ChoiceWidth16Spec::Variant8 (v.deep_view()),
            ChoiceWidth16::Variant9 (v) => ChoiceWidth16Spec::Variant9 (v.deep_view()),
            ChoiceWidth16::Variant10 (v) => ChoiceWidth16Spec::Variant10 (v.deep_view()),
            ChoiceWidth16::Variant11 (v) => ChoiceWidth16Spec::Variant11 (v.deep_view()),
            ChoiceWidth16::Variant12 (v) => ChoiceWidth16Spec::Variant12 (v.deep_view()),
            ChoiceWidth16::Variant13 (v) => ChoiceWidth16Spec::Variant13 (v.deep_view()),
            ChoiceWidth16::Variant14 (v) => ChoiceWidth16Spec::Variant14 (v.deep_view()),
            ChoiceWidth16::Variant15 (v) => ChoiceWidth16Spec::Variant15 (v.deep_view()),
        }
    }
}
impl ChoiceWidth16 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        ChoiceWidth16::Variant0 (v) => ChoiceWidth16Spec::Variant0 (v.deep_view()),
        ChoiceWidth16::Variant1 (v) => ChoiceWidth16Spec::Variant1 (v.deep_view()),
        ChoiceWidth16::Variant2 (v) => ChoiceWidth16Spec::Variant2 (v.deep_view()),
        ChoiceWidth16::Variant3 (v) => ChoiceWidth16Spec::Variant3 (v.deep_view()),
        ChoiceWidth16::Variant4 (v) => ChoiceWidth16Spec::Variant4 (v.deep_view()),
        ChoiceWidth16::Variant5 (v) => ChoiceWidth16Spec::Variant5 (v.deep_view()),
        ChoiceWidth16::Variant6 (v) => ChoiceWidth16Spec::Variant6 (v.deep_view()),
        ChoiceWidth16::Variant7 (v) => ChoiceWidth16Spec::Variant7 (v.deep_view()),
        ChoiceWidth16::Variant8 (v) => ChoiceWidth16Spec::Variant8 (v.deep_view()),
        ChoiceWidth16::Variant9 (v) => ChoiceWidth16Spec::Variant9 (v.deep_view()),
        ChoiceWidth16::Variant10 (v) => ChoiceWidth16Spec::Variant10 (v.deep_view()),
        ChoiceWidth16::Variant11 (v) => ChoiceWidth16Spec::Variant11 (v.deep_view()),
        ChoiceWidth16::Variant12 (v) => ChoiceWidth16Spec::Variant12 (v.deep_view()),
        ChoiceWidth16::Variant13 (v) => ChoiceWidth16Spec::Variant13 (v.deep_view()),
        ChoiceWidth16::Variant14 (v) => ChoiceWidth16Spec::Variant14 (v.deep_view()),
        ChoiceWidth16::Variant15 (v) => ChoiceWidth16Spec::Variant15 (v.deep_view()),
    }
   ,
    {
        reveal(< ChoiceWidth16 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 > ChoiceWidth16Spec < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 > {
    # [verifier::opaque] pub open spec fn from_structural (input: Sum < Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > >,
    Sum < Sum < Sum < T8,
    T9 >,
    Sum < T10,
    T11 > >,
    Sum < Sum < T12,
    T13 >,
    Sum < T14,
    T15 > > > >) -> Self {
        match input {
            L (L (L (L (value)))) => Self::Variant0 (value),
            L (L (L (R (value)))) => Self::Variant1 (value),
            L (L (R (L (value)))) => Self::Variant2 (value),
            L (L (R (R (value)))) => Self::Variant3 (value),
            L (R (L (L (value)))) => Self::Variant4 (value),
            L (R (L (R (value)))) => Self::Variant5 (value),
            L (R (R (L (value)))) => Self::Variant6 (value),
            L (R (R (R (value)))) => Self::Variant7 (value),
            R (L (L (L (value)))) => Self::Variant8 (value),
            R (L (L (R (value)))) => Self::Variant9 (value),
            R (L (R (L (value)))) => Self::Variant10 (value),
            R (L (R (R (value)))) => Self::Variant11 (value),
            R (R (L (L (value)))) => Self::Variant12 (value),
            R (R (L (R (value)))) => Self::Variant13 (value),
            R (R (R (L (value)))) => Self::Variant14 (value),
            R (R (R (R (value)))) => Self::Variant15 (value),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> Sum < Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > >,
    Sum < Sum < Sum < T8,
    T9 >,
    Sum < T10,
    T11 > >,
    Sum < Sum < T12,
    T13 >,
    Sum < T14,
    T15 > > > > {
        match self {
            Self::Variant0 (value) => L (L (L (L (value)))),
            Self::Variant1 (value) => L (L (L (R (value)))),
            Self::Variant2 (value) => L (L (R (L (value)))),
            Self::Variant3 (value) => L (L (R (R (value)))),
            Self::Variant4 (value) => L (R (L (L (value)))),
            Self::Variant5 (value) => L (R (L (R (value)))),
            Self::Variant6 (value) => L (R (R (L (value)))),
            Self::Variant7 (value) => L (R (R (R (value)))),
            Self::Variant8 (value) => R (L (L (L (value)))),
            Self::Variant9 (value) => R (L (L (R (value)))),
            Self::Variant10 (value) => R (L (R (L (value)))),
            Self::Variant11 (value) => R (L (R (R (value)))),
            Self::Variant12 (value) => R (R (L (L (value)))),
            Self::Variant13 (value) => R (R (L (R (value)))),
            Self::Variant14 (value) => R (R (R (L (value)))),
            Self::Variant15 (value) => R (R (R (R (value)))),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(ChoiceWidth16Spec::from_structural) ;
        reveal(ChoiceWidth16Spec::into_structural) ;
        match self {
            Self::Variant0 (_) => {
            }
           ,
            Self::Variant1 (_) => {
            }
           ,
            Self::Variant2 (_) => {
            }
           ,
            Self::Variant3 (_) => {
            }
           ,
            Self::Variant4 (_) => {
            }
           ,
            Self::Variant5 (_) => {
            }
           ,
            Self::Variant6 (_) => {
            }
           ,
            Self::Variant7 (_) => {
            }
           ,
            Self::Variant8 (_) => {
            }
           ,
            Self::Variant9 (_) => {
            }
           ,
            Self::Variant10 (_) => {
            }
           ,
            Self::Variant11 (_) => {
            }
           ,
            Self::Variant12 (_) => {
            }
           ,
            Self::Variant13 (_) => {
            }
           ,
            Self::Variant14 (_) => {
            }
           ,
            Self::Variant15 (_) => {
            }
           ,
        }
    }
    pub broadcast proof fn lemma_into_from (input: Sum < Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > >,
    Sum < Sum < Sum < T8,
    T9 >,
    Sum < T10,
    T11 > >,
    Sum < Sum < T12,
    T13 >,
    Sum < T14,
    T15 > > > >) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(ChoiceWidth16Spec::from_structural) ;
        reveal(ChoiceWidth16Spec::into_structural) ;
        match input {
            L (L (L (L (_)))) => {
            }
           ,
            L (L (L (R (_)))) => {
            }
           ,
            L (L (R (L (_)))) => {
            }
           ,
            L (L (R (R (_)))) => {
            }
           ,
            L (R (L (L (_)))) => {
            }
           ,
            L (R (L (R (_)))) => {
            }
           ,
            L (R (R (L (_)))) => {
            }
           ,
            L (R (R (R (_)))) => {
            }
           ,
            R (L (L (L (_)))) => {
            }
           ,
            R (L (L (R (_)))) => {
            }
           ,
            R (L (R (L (_)))) => {
            }
           ,
            R (L (R (R (_)))) => {
            }
           ,
            R (R (L (L (_)))) => {
            }
           ,
            R (R (L (R (_)))) => {
            }
           ,
            R (R (R (L (_)))) => {
            }
           ,
            R (R (R (R (_)))) => {
            }
           ,
        }
    }
    pub proof fn lemma_into_structural_variant (self) ensures Self::into_structural (self) == match self {
        Self::Variant0 (value) => L (L (L (L (value)))),
        Self::Variant1 (value) => L (L (L (R (value)))),
        Self::Variant2 (value) => L (L (R (L (value)))),
        Self::Variant3 (value) => L (L (R (R (value)))),
        Self::Variant4 (value) => L (R (L (L (value)))),
        Self::Variant5 (value) => L (R (L (R (value)))),
        Self::Variant6 (value) => L (R (R (L (value)))),
        Self::Variant7 (value) => L (R (R (R (value)))),
        Self::Variant8 (value) => R (L (L (L (value)))),
        Self::Variant9 (value) => R (L (L (R (value)))),
        Self::Variant10 (value) => R (L (R (L (value)))),
        Self::Variant11 (value) => R (L (R (R (value)))),
        Self::Variant12 (value) => R (R (L (L (value)))),
        Self::Variant13 (value) => R (R (L (R (value)))),
        Self::Variant14 (value) => R (R (R (L (value)))),
        Self::Variant15 (value) => R (R (R (R (value)))),
    }
   ,
    {
        reveal(ChoiceWidth16Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth16Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth16Reverse ;
impl SpecMap for ChoiceWidth16Forward {
    type Input = ChoiceWidth16Inner ;
    type Output = ChoiceWidth16Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        ChoiceWidth16Spec::from_structural (input)
    }
}
impl SpecMap for ChoiceWidth16Reverse {
    type Input = ChoiceWidth16Spec ;
    type Output = ChoiceWidth16Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `choice_width16`."]
# [derive (Clone, Copy)]
pub struct ChoiceWidth16Fmt ;

pub type ChoiceWidth16FmtSpec = Named < Mapped < Choice < Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > >, Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > > >, BiMap < ChoiceWidth16Forward, ChoiceWidth16Reverse >> > ;

impl ChoiceWidth16Fmt {
    # [doc = "specification constructor for `choice_width16`."] pub open spec fn spec_inner() -> ChoiceWidth16FmtSpec {
        Named ("choice_width16",
        Mapped {
            inner: Choice (Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 0),
            Refined (U8,
            | x: u8 | x == 1)),
            Choice (Refined (U8,
            | x: u8 | x == 2),
            Refined (U8,
            | x: u8 | x == 3))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 4),
            Refined (U8,
            | x: u8 | x == 5)),
            Choice (Refined (U8,
            | x: u8 | x == 6),
            Refined (U8,
            | x: u8 | x == 7)))),
            Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 8),
            Refined (U8,
            | x: u8 | x == 9)),
            Choice (Refined (U8,
            | x: u8 | x == 10),
            Refined (U8,
            | x: u8 | x == 11))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 12),
            Refined (U8,
            | x: u8 | x == 13)),
            Choice (Refined (U8,
            | x: u8 | x == 14),
            Refined (U8,
            | x: u8 | x >= 15))))),
            mapper: BiMap (ChoiceWidth16Forward,
            ChoiceWidth16Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ChoiceWidth16Fmt {
        type PVal = ChoiceWidth16Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for ChoiceWidth16Fmt {
        type Val = ChoiceWidth16Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for ChoiceWidth16Fmt {
        type SValue = ChoiceWidth16Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for ChoiceWidth16Fmt {
        type SVal = ChoiceWidth16Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for ChoiceWidth16Fmt {
        type T = ChoiceWidth16Spec ;
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
        ChoiceWidth16Spec::lemma_from_into,
        ChoiceWidth16Spec::lemma_into_from,
    };

    impl SafeParser for ChoiceWidth16Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for ChoiceWidth16Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for ChoiceWidth16Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth16Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for ChoiceWidth16Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for ChoiceWidth16Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth16Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< ChoiceWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for ChoiceWidth16Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth16Fmt as Consistency>::consistent) ;
            reveal(< ChoiceWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: ChoiceWidth16Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                ChoiceWidth16Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for ChoiceWidth16Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for ChoiceWidth16Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth16Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for ChoiceWidth16Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth16Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for ChoiceWidth16Fmt {
        type PT = ChoiceWidth16;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceWidth16Fmt as SpecParser>::spec_parse);
            reveal(<ChoiceWidth16 as DeepView>::deep_view);
            reveal(ChoiceWidth16Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U8).parse (& rest) {
        Ok ((n,
        va)) if va == 0 => {
            Ok ((n,
            ChoiceWidth16::Variant0 (va)))
        }
       ,
        _ => match (U8).parse (& rest) {
            Ok ((n,
            va)) if va == 1 => {
                Ok ((n,
                ChoiceWidth16::Variant1 (va)))
            }
           ,
            _ => match (U8).parse (& rest) {
                Ok ((n,
                va)) if va == 2 => {
                    Ok ((n,
                    ChoiceWidth16::Variant2 (va)))
                }
               ,
                _ => match (U8).parse (& rest) {
                    Ok ((n,
                    va)) if va == 3 => {
                        Ok ((n,
                        ChoiceWidth16::Variant3 (va)))
                    }
                   ,
                    _ => match (U8).parse (& rest) {
                        Ok ((n,
                        va)) if va == 4 => {
                            Ok ((n,
                            ChoiceWidth16::Variant4 (va)))
                        }
                       ,
                        _ => match (U8).parse (& rest) {
                            Ok ((n,
                            va)) if va == 5 => {
                                Ok ((n,
                                ChoiceWidth16::Variant5 (va)))
                            }
                           ,
                            _ => match (U8).parse (& rest) {
                                Ok ((n,
                                va)) if va == 6 => {
                                    Ok ((n,
                                    ChoiceWidth16::Variant6 (va)))
                                }
                               ,
                                _ => match (U8).parse (& rest) {
                                    Ok ((n,
                                    va)) if va == 7 => {
                                        Ok ((n,
                                        ChoiceWidth16::Variant7 (va)))
                                    }
                                   ,
                                    _ => match (U8).parse (& rest) {
                                        Ok ((n,
                                        va)) if va == 8 => {
                                            Ok ((n,
                                            ChoiceWidth16::Variant8 (va)))
                                        }
                                       ,
                                        _ => match (U8).parse (& rest) {
                                            Ok ((n,
                                            va)) if va == 9 => {
                                                Ok ((n,
                                                ChoiceWidth16::Variant9 (va)))
                                            }
                                           ,
                                            _ => match (U8).parse (& rest) {
                                                Ok ((n,
                                                va)) if va == 10 => {
                                                    Ok ((n,
                                                    ChoiceWidth16::Variant10 (va)))
                                                }
                                               ,
                                                _ => match (U8).parse (& rest) {
                                                    Ok ((n,
                                                    va)) if va == 11 => {
                                                        Ok ((n,
                                                        ChoiceWidth16::Variant11 (va)))
                                                    }
                                                   ,
                                                    _ => match (U8).parse (& rest) {
                                                        Ok ((n,
                                                        va)) if va == 12 => {
                                                            Ok ((n,
                                                            ChoiceWidth16::Variant12 (va)))
                                                        }
                                                       ,
                                                        _ => match (U8).parse (& rest) {
                                                            Ok ((n,
                                                            va)) if va == 13 => {
                                                                Ok ((n,
                                                                ChoiceWidth16::Variant13 (va)))
                                                            }
                                                           ,
                                                            _ => match (U8).parse (& rest) {
                                                                Ok ((n,
                                                                va)) if va == 14 => {
                                                                    Ok ((n,
                                                                    ChoiceWidth16::Variant14 (va)))
                                                                }
                                                               ,
                                                                _ => match (U8).parse (& rest) {
                                                                    Ok ((n,
                                                                    va)) if va >= 15 => {
                                                                        Ok ((n,
                                                                        ChoiceWidth16::Variant15 (va)))
                                                                    }
                                                                   ,
                                                                    _ => Err (ParseError::invalid_choice()),
                                                                }
                                                               ,
                                                            }
                                                           ,
                                                        }
                                                       ,
                                                    }
                                                   ,
                                                }
                                               ,
                                            }
                                           ,
                                        }
                                       ,
                                    }
                                   ,
                                }
                               ,
                            }
                           ,
                        }
                       ,
                    }
                   ,
                }
               ,
            }
           ,
        }
       ,
    }
    ?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ChoiceWidth16> for ChoiceWidth16Fmt {
        fn serialize_into(&self, v: &ChoiceWidth16, obuf: &mut Output) {
            reveal(<ChoiceWidth16Fmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceWidth16Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth16 as DeepView>::deep_view);
            reveal(ChoiceWidth16Spec::into_structural);
            let ghost old_obuf = obuf@;

            match v {
                ChoiceWidth16::Variant0 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant1 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant2 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant3 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant4 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant5 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant6 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant7 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant8 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant9 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant10 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant11 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant12 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant13 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant14 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth16::Variant15 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceWidth16> for ChoiceWidth16Fmt {
        fn prepare(&self, v: &ChoiceWidth16) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceWidth16Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth16 as DeepView>::deep_view);
            reveal(ChoiceWidth16Spec::into_structural);
            match v {
                ChoiceWidth16::Variant0 (v) => {
                    if ! (*v == 0) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant1 (v) => {
                    if ! (*v == 1) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant2 (v) => {
                    if ! (*v == 2) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant3 (v) => {
                    if ! (*v == 3) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant4 (v) => {
                    if ! (*v == 4) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant5 (v) => {
                    if ! (*v == 5) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant6 (v) => {
                    if ! (*v == 6) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant7 (v) => {
                    if ! (*v == 7) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant8 (v) => {
                    if ! (*v == 8) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant9 (v) => {
                    if ! (*v == 9) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant10 (v) => {
                    if ! (*v == 10) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant11 (v) => {
                    if ! (*v == 11) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant12 (v) => {
                    if ! (*v == 12) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant13 (v) => {
                    if ! (*v == 13) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant14 (v) => {
                    if ! (*v == 14) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth16::Variant15 (v) => {
                    if ! (*v >= 15) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
            }
        }
    }

}
}
