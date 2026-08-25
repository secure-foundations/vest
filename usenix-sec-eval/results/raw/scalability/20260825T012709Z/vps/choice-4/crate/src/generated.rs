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
# [doc = "data type for `choice_width4`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum ChoiceWidth4 {
    Variant0 (u8),
    Variant1 (u8),
    Variant2 (u8),
    Variant3 (u8),
}
# [verifier::ext_equal]
pub enum ChoiceWidth4Spec < T0 = u8, T1 = u8, T2 = u8, T3 = u8 > {
    Variant0 (T0),
    Variant1 (T1),
    Variant2 (T2),
    Variant3 (T3),
}
pub type ChoiceWidth4Inner = Sum < Sum < u8, u8 >, Sum < u8, u8 > > ;
impl DeepView for ChoiceWidth4 {
    type V = ChoiceWidth4Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            ChoiceWidth4::Variant0 (v) => ChoiceWidth4Spec::Variant0 (v.deep_view()),
            ChoiceWidth4::Variant1 (v) => ChoiceWidth4Spec::Variant1 (v.deep_view()),
            ChoiceWidth4::Variant2 (v) => ChoiceWidth4Spec::Variant2 (v.deep_view()),
            ChoiceWidth4::Variant3 (v) => ChoiceWidth4Spec::Variant3 (v.deep_view()),
        }
    }
}
impl ChoiceWidth4 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        ChoiceWidth4::Variant0 (v) => ChoiceWidth4Spec::Variant0 (v.deep_view()),
        ChoiceWidth4::Variant1 (v) => ChoiceWidth4Spec::Variant1 (v.deep_view()),
        ChoiceWidth4::Variant2 (v) => ChoiceWidth4Spec::Variant2 (v.deep_view()),
        ChoiceWidth4::Variant3 (v) => ChoiceWidth4Spec::Variant3 (v.deep_view()),
    }
   ,
    {
        reveal(< ChoiceWidth4 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3 > ChoiceWidth4Spec < T0, T1, T2, T3 > {
    # [verifier::opaque] pub open spec fn from_structural (input: Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >) -> Self {
        match input {
            L (L (value)) => Self::Variant0 (value),
            L (R (value)) => Self::Variant1 (value),
            R (L (value)) => Self::Variant2 (value),
            R (R (value)) => Self::Variant3 (value),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > > {
        match self {
            Self::Variant0 (value) => L (L (value)),
            Self::Variant1 (value) => L (R (value)),
            Self::Variant2 (value) => R (L (value)),
            Self::Variant3 (value) => R (R (value)),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(ChoiceWidth4Spec::from_structural) ;
        reveal(ChoiceWidth4Spec::into_structural) ;
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
        }
    }
    pub broadcast proof fn lemma_into_from (input: Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(ChoiceWidth4Spec::from_structural) ;
        reveal(ChoiceWidth4Spec::into_structural) ;
        match input {
            L (L (_)) => {
            }
           ,
            L (R (_)) => {
            }
           ,
            R (L (_)) => {
            }
           ,
            R (R (_)) => {
            }
           ,
        }
    }
    pub proof fn lemma_into_structural_variant (self) ensures Self::into_structural (self) == match self {
        Self::Variant0 (value) => L (L (value)),
        Self::Variant1 (value) => L (R (value)),
        Self::Variant2 (value) => R (L (value)),
        Self::Variant3 (value) => R (R (value)),
    }
   ,
    {
        reveal(ChoiceWidth4Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth4Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth4Reverse ;
impl SpecMap for ChoiceWidth4Forward {
    type Input = ChoiceWidth4Inner ;
    type Output = ChoiceWidth4Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        ChoiceWidth4Spec::from_structural (input)
    }
}
impl SpecMap for ChoiceWidth4Reverse {
    type Input = ChoiceWidth4Spec ;
    type Output = ChoiceWidth4Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `choice_width4`."]
# [derive (Clone, Copy)]
pub struct ChoiceWidth4Fmt ;

pub type ChoiceWidth4FmtSpec = Named < Mapped < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, BiMap < ChoiceWidth4Forward, ChoiceWidth4Reverse >> > ;

impl ChoiceWidth4Fmt {
    # [doc = "specification constructor for `choice_width4`."] pub open spec fn spec_inner() -> ChoiceWidth4FmtSpec {
        Named ("choice_width4",
        Mapped {
            inner: Choice (Choice (Refined (U8,
            | x: u8 | x == 0),
            Refined (U8,
            | x: u8 | x == 1)),
            Choice (Refined (U8,
            | x: u8 | x == 2),
            Refined (U8,
            | x: u8 | x >= 3))),
            mapper: BiMap (ChoiceWidth4Forward,
            ChoiceWidth4Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ChoiceWidth4Fmt {
        type PVal = ChoiceWidth4Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for ChoiceWidth4Fmt {
        type Val = ChoiceWidth4Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for ChoiceWidth4Fmt {
        type SValue = ChoiceWidth4Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for ChoiceWidth4Fmt {
        type SVal = ChoiceWidth4Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for ChoiceWidth4Fmt {
        type T = ChoiceWidth4Spec ;
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
        ChoiceWidth4Spec::lemma_from_into,
        ChoiceWidth4Spec::lemma_into_from,
    };

    impl SafeParser for ChoiceWidth4Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for ChoiceWidth4Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for ChoiceWidth4Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth4Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth4Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth4Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for ChoiceWidth4Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for ChoiceWidth4Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth4Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< ChoiceWidth4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for ChoiceWidth4Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth4Fmt as Consistency>::consistent) ;
            reveal(< ChoiceWidth4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: ChoiceWidth4Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                ChoiceWidth4Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for ChoiceWidth4Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth4Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for ChoiceWidth4Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth4Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for ChoiceWidth4Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth4Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for ChoiceWidth4Fmt {
        type PT = ChoiceWidth4;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceWidth4Fmt as SpecParser>::spec_parse);
            reveal(<ChoiceWidth4 as DeepView>::deep_view);
            reveal(ChoiceWidth4Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U8).parse (& rest) {
        Ok ((n,
        va)) if va == 0 => {
            Ok ((n,
            ChoiceWidth4::Variant0 (va)))
        }
       ,
        _ => match (U8).parse (& rest) {
            Ok ((n,
            va)) if va == 1 => {
                Ok ((n,
                ChoiceWidth4::Variant1 (va)))
            }
           ,
            _ => match (U8).parse (& rest) {
                Ok ((n,
                va)) if va == 2 => {
                    Ok ((n,
                    ChoiceWidth4::Variant2 (va)))
                }
               ,
                _ => match (U8).parse (& rest) {
                    Ok ((n,
                    va)) if va >= 3 => {
                        Ok ((n,
                        ChoiceWidth4::Variant3 (va)))
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
    ?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ChoiceWidth4> for ChoiceWidth4Fmt {
        fn serialize_into(&self, v: &ChoiceWidth4, obuf: &mut Output) {
            reveal(<ChoiceWidth4Fmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceWidth4Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth4 as DeepView>::deep_view);
            reveal(ChoiceWidth4Spec::into_structural);
            let ghost old_obuf = obuf@;

            match v {
                ChoiceWidth4::Variant0 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth4::Variant1 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth4::Variant2 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth4::Variant3 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceWidth4> for ChoiceWidth4Fmt {
        fn prepare(&self, v: &ChoiceWidth4) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceWidth4Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth4 as DeepView>::deep_view);
            reveal(ChoiceWidth4Spec::into_structural);
            match v {
                ChoiceWidth4::Variant0 (v) => {
                    if ! (*v == 0) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth4::Variant1 (v) => {
                    if ! (*v == 1) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth4::Variant2 (v) => {
                    if ! (*v == 2) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth4::Variant3 (v) => {
                    if ! (*v >= 3) {
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
