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
# [doc = "data type for `choice_width2`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum ChoiceWidth2 {
    Variant0 (u8),
    Variant1 (u8),
}
# [verifier::ext_equal]
pub enum ChoiceWidth2Spec < T0 = u8, T1 = u8 > {
    Variant0 (T0),
    Variant1 (T1),
}
pub type ChoiceWidth2Inner = Sum < u8, u8 > ;
impl DeepView for ChoiceWidth2 {
    type V = ChoiceWidth2Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            ChoiceWidth2::Variant0 (v) => ChoiceWidth2Spec::Variant0 (v.deep_view()),
            ChoiceWidth2::Variant1 (v) => ChoiceWidth2Spec::Variant1 (v.deep_view()),
        }
    }
}
impl ChoiceWidth2 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        ChoiceWidth2::Variant0 (v) => ChoiceWidth2Spec::Variant0 (v.deep_view()),
        ChoiceWidth2::Variant1 (v) => ChoiceWidth2Spec::Variant1 (v.deep_view()),
    }
   ,
    {
        reveal(< ChoiceWidth2 as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > ChoiceWidth2Spec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: Sum < T0,
    T1 >) -> Self {
        match input {
            L (value) => Self::Variant0 (value),
            R (value) => Self::Variant1 (value),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> Sum < T0,
    T1 > {
        match self {
            Self::Variant0 (value) => L (value),
            Self::Variant1 (value) => R (value),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(ChoiceWidth2Spec::from_structural) ;
        reveal(ChoiceWidth2Spec::into_structural) ;
        match self {
            Self::Variant0 (_) => {
            }
           ,
            Self::Variant1 (_) => {
            }
           ,
        }
    }
    pub broadcast proof fn lemma_into_from (input: Sum < T0,
    T1 >) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(ChoiceWidth2Spec::from_structural) ;
        reveal(ChoiceWidth2Spec::into_structural) ;
        match input {
            L (_) => {
            }
           ,
            R (_) => {
            }
           ,
        }
    }
    pub proof fn lemma_into_structural_variant (self) ensures Self::into_structural (self) == match self {
        Self::Variant0 (value) => L (value),
        Self::Variant1 (value) => R (value),
    }
   ,
    {
        reveal(ChoiceWidth2Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth2Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth2Reverse ;
impl SpecMap for ChoiceWidth2Forward {
    type Input = ChoiceWidth2Inner ;
    type Output = ChoiceWidth2Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        ChoiceWidth2Spec::from_structural (input)
    }
}
impl SpecMap for ChoiceWidth2Reverse {
    type Input = ChoiceWidth2Spec ;
    type Output = ChoiceWidth2Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `choice_width2`."]
# [derive (Clone, Copy)]
pub struct ChoiceWidth2Fmt ;

pub type ChoiceWidth2FmtSpec = Named < Mapped < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, BiMap < ChoiceWidth2Forward, ChoiceWidth2Reverse >> > ;

impl ChoiceWidth2Fmt {
    # [doc = "specification constructor for `choice_width2`."] pub open spec fn spec_inner() -> ChoiceWidth2FmtSpec {
        Named ("choice_width2",
        Mapped {
            inner: Choice (Refined (U8,
            | x: u8 | x == 0),
            Refined (U8,
            | x: u8 | x >= 1)),
            mapper: BiMap (ChoiceWidth2Forward,
            ChoiceWidth2Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ChoiceWidth2Fmt {
        type PVal = ChoiceWidth2Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for ChoiceWidth2Fmt {
        type Val = ChoiceWidth2Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for ChoiceWidth2Fmt {
        type SValue = ChoiceWidth2Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for ChoiceWidth2Fmt {
        type SVal = ChoiceWidth2Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for ChoiceWidth2Fmt {
        type T = ChoiceWidth2Spec ;
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
        ChoiceWidth2Spec::lemma_from_into,
        ChoiceWidth2Spec::lemma_into_from,
    };

    impl SafeParser for ChoiceWidth2Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for ChoiceWidth2Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for ChoiceWidth2Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth2Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth2Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth2Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for ChoiceWidth2Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for ChoiceWidth2Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth2Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< ChoiceWidth2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for ChoiceWidth2Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth2Fmt as Consistency>::consistent) ;
            reveal(< ChoiceWidth2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: ChoiceWidth2Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                ChoiceWidth2Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for ChoiceWidth2Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth2Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for ChoiceWidth2Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth2Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for ChoiceWidth2Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth2Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for ChoiceWidth2Fmt {
        type PT = ChoiceWidth2;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceWidth2Fmt as SpecParser>::spec_parse);
            reveal(<ChoiceWidth2 as DeepView>::deep_view);
            reveal(ChoiceWidth2Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U8).parse (& rest) {
        Ok ((n,
        va)) if va == 0 => {
            Ok ((n,
            ChoiceWidth2::Variant0 (va)))
        }
       ,
        _ => match (U8).parse (& rest) {
            Ok ((n,
            va)) if va >= 1 => {
                Ok ((n,
                ChoiceWidth2::Variant1 (va)))
            }
           ,
            _ => Err (ParseError::invalid_choice()),
        }
       ,
    }
    ?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ChoiceWidth2> for ChoiceWidth2Fmt {
        fn serialize_into(&self, v: &ChoiceWidth2, obuf: &mut Output) {
            reveal(<ChoiceWidth2Fmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceWidth2Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth2 as DeepView>::deep_view);
            reveal(ChoiceWidth2Spec::into_structural);
            let ghost old_obuf = obuf@;

            match v {
                ChoiceWidth2::Variant0 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth2::Variant1 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceWidth2> for ChoiceWidth2Fmt {
        fn prepare(&self, v: &ChoiceWidth2) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceWidth2Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth2 as DeepView>::deep_view);
            reveal(ChoiceWidth2Spec::into_structural);
            match v {
                ChoiceWidth2::Variant0 (v) => {
                    if ! (*v == 0) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth2::Variant1 (v) => {
                    if ! (*v >= 1) {
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
