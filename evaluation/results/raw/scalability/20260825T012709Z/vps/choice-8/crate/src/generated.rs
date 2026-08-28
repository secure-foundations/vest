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
# [doc = "data type for `choice_width8`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum ChoiceWidth8 {
    Variant0 (u8),
    Variant1 (u8),
    Variant2 (u8),
    Variant3 (u8),
    Variant4 (u8),
    Variant5 (u8),
    Variant6 (u8),
    Variant7 (u8),
}
# [verifier::ext_equal]
pub enum ChoiceWidth8Spec < T0 = u8, T1 = u8, T2 = u8, T3 = u8, T4 = u8, T5 = u8, T6 = u8, T7 = u8 > {
    Variant0 (T0),
    Variant1 (T1),
    Variant2 (T2),
    Variant3 (T3),
    Variant4 (T4),
    Variant5 (T5),
    Variant6 (T6),
    Variant7 (T7),
}
pub type ChoiceWidth8Inner = Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > > ;
impl DeepView for ChoiceWidth8 {
    type V = ChoiceWidth8Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            ChoiceWidth8::Variant0 (v) => ChoiceWidth8Spec::Variant0 (v.deep_view()),
            ChoiceWidth8::Variant1 (v) => ChoiceWidth8Spec::Variant1 (v.deep_view()),
            ChoiceWidth8::Variant2 (v) => ChoiceWidth8Spec::Variant2 (v.deep_view()),
            ChoiceWidth8::Variant3 (v) => ChoiceWidth8Spec::Variant3 (v.deep_view()),
            ChoiceWidth8::Variant4 (v) => ChoiceWidth8Spec::Variant4 (v.deep_view()),
            ChoiceWidth8::Variant5 (v) => ChoiceWidth8Spec::Variant5 (v.deep_view()),
            ChoiceWidth8::Variant6 (v) => ChoiceWidth8Spec::Variant6 (v.deep_view()),
            ChoiceWidth8::Variant7 (v) => ChoiceWidth8Spec::Variant7 (v.deep_view()),
        }
    }
}
impl ChoiceWidth8 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        ChoiceWidth8::Variant0 (v) => ChoiceWidth8Spec::Variant0 (v.deep_view()),
        ChoiceWidth8::Variant1 (v) => ChoiceWidth8Spec::Variant1 (v.deep_view()),
        ChoiceWidth8::Variant2 (v) => ChoiceWidth8Spec::Variant2 (v.deep_view()),
        ChoiceWidth8::Variant3 (v) => ChoiceWidth8Spec::Variant3 (v.deep_view()),
        ChoiceWidth8::Variant4 (v) => ChoiceWidth8Spec::Variant4 (v.deep_view()),
        ChoiceWidth8::Variant5 (v) => ChoiceWidth8Spec::Variant5 (v.deep_view()),
        ChoiceWidth8::Variant6 (v) => ChoiceWidth8Spec::Variant6 (v.deep_view()),
        ChoiceWidth8::Variant7 (v) => ChoiceWidth8Spec::Variant7 (v.deep_view()),
    }
   ,
    {
        reveal(< ChoiceWidth8 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7 > ChoiceWidth8Spec < T0, T1, T2, T3, T4, T5, T6, T7 > {
    # [verifier::opaque] pub open spec fn from_structural (input: Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > >) -> Self {
        match input {
            L (L (L (value))) => Self::Variant0 (value),
            L (L (R (value))) => Self::Variant1 (value),
            L (R (L (value))) => Self::Variant2 (value),
            L (R (R (value))) => Self::Variant3 (value),
            R (L (L (value))) => Self::Variant4 (value),
            R (L (R (value))) => Self::Variant5 (value),
            R (R (L (value))) => Self::Variant6 (value),
            R (R (R (value))) => Self::Variant7 (value),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > > {
        match self {
            Self::Variant0 (value) => L (L (L (value))),
            Self::Variant1 (value) => L (L (R (value))),
            Self::Variant2 (value) => L (R (L (value))),
            Self::Variant3 (value) => L (R (R (value))),
            Self::Variant4 (value) => R (L (L (value))),
            Self::Variant5 (value) => R (L (R (value))),
            Self::Variant6 (value) => R (R (L (value))),
            Self::Variant7 (value) => R (R (R (value))),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(ChoiceWidth8Spec::from_structural) ;
        reveal(ChoiceWidth8Spec::into_structural) ;
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
        }
    }
    pub broadcast proof fn lemma_into_from (input: Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > >) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(ChoiceWidth8Spec::from_structural) ;
        reveal(ChoiceWidth8Spec::into_structural) ;
        match input {
            L (L (L (_))) => {
            }
           ,
            L (L (R (_))) => {
            }
           ,
            L (R (L (_))) => {
            }
           ,
            L (R (R (_))) => {
            }
           ,
            R (L (L (_))) => {
            }
           ,
            R (L (R (_))) => {
            }
           ,
            R (R (L (_))) => {
            }
           ,
            R (R (R (_))) => {
            }
           ,
        }
    }
    pub proof fn lemma_into_structural_variant (self) ensures Self::into_structural (self) == match self {
        Self::Variant0 (value) => L (L (L (value))),
        Self::Variant1 (value) => L (L (R (value))),
        Self::Variant2 (value) => L (R (L (value))),
        Self::Variant3 (value) => L (R (R (value))),
        Self::Variant4 (value) => R (L (L (value))),
        Self::Variant5 (value) => R (L (R (value))),
        Self::Variant6 (value) => R (R (L (value))),
        Self::Variant7 (value) => R (R (R (value))),
    }
   ,
    {
        reveal(ChoiceWidth8Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth8Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth8Reverse ;
impl SpecMap for ChoiceWidth8Forward {
    type Input = ChoiceWidth8Inner ;
    type Output = ChoiceWidth8Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        ChoiceWidth8Spec::from_structural (input)
    }
}
impl SpecMap for ChoiceWidth8Reverse {
    type Input = ChoiceWidth8Spec ;
    type Output = ChoiceWidth8Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `choice_width8`."]
# [derive (Clone, Copy)]
pub struct ChoiceWidth8Fmt ;

pub type ChoiceWidth8FmtSpec = Named < Mapped < Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > >, BiMap < ChoiceWidth8Forward, ChoiceWidth8Reverse >> > ;

impl ChoiceWidth8Fmt {
    # [doc = "specification constructor for `choice_width8`."] pub open spec fn spec_inner() -> ChoiceWidth8FmtSpec {
        Named ("choice_width8",
        Mapped {
            inner: Choice (Choice (Choice (Refined (U8,
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
            | x: u8 | x >= 7)))),
            mapper: BiMap (ChoiceWidth8Forward,
            ChoiceWidth8Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ChoiceWidth8Fmt {
        type PVal = ChoiceWidth8Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for ChoiceWidth8Fmt {
        type Val = ChoiceWidth8Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for ChoiceWidth8Fmt {
        type SValue = ChoiceWidth8Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for ChoiceWidth8Fmt {
        type SVal = ChoiceWidth8Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for ChoiceWidth8Fmt {
        type T = ChoiceWidth8Spec ;
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
        ChoiceWidth8Spec::lemma_from_into,
        ChoiceWidth8Spec::lemma_into_from,
    };

    impl SafeParser for ChoiceWidth8Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for ChoiceWidth8Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for ChoiceWidth8Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth8Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth8Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth8Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for ChoiceWidth8Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for ChoiceWidth8Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth8Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< ChoiceWidth8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for ChoiceWidth8Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth8Fmt as Consistency>::consistent) ;
            reveal(< ChoiceWidth8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: ChoiceWidth8Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                ChoiceWidth8Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for ChoiceWidth8Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth8Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for ChoiceWidth8Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth8Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for ChoiceWidth8Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth8Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for ChoiceWidth8Fmt {
        type PT = ChoiceWidth8;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceWidth8Fmt as SpecParser>::spec_parse);
            reveal(<ChoiceWidth8 as DeepView>::deep_view);
            reveal(ChoiceWidth8Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U8).parse (& rest) {
        Ok ((n,
        va)) if va == 0 => {
            Ok ((n,
            ChoiceWidth8::Variant0 (va)))
        }
       ,
        _ => match (U8).parse (& rest) {
            Ok ((n,
            va)) if va == 1 => {
                Ok ((n,
                ChoiceWidth8::Variant1 (va)))
            }
           ,
            _ => match (U8).parse (& rest) {
                Ok ((n,
                va)) if va == 2 => {
                    Ok ((n,
                    ChoiceWidth8::Variant2 (va)))
                }
               ,
                _ => match (U8).parse (& rest) {
                    Ok ((n,
                    va)) if va == 3 => {
                        Ok ((n,
                        ChoiceWidth8::Variant3 (va)))
                    }
                   ,
                    _ => match (U8).parse (& rest) {
                        Ok ((n,
                        va)) if va == 4 => {
                            Ok ((n,
                            ChoiceWidth8::Variant4 (va)))
                        }
                       ,
                        _ => match (U8).parse (& rest) {
                            Ok ((n,
                            va)) if va == 5 => {
                                Ok ((n,
                                ChoiceWidth8::Variant5 (va)))
                            }
                           ,
                            _ => match (U8).parse (& rest) {
                                Ok ((n,
                                va)) if va == 6 => {
                                    Ok ((n,
                                    ChoiceWidth8::Variant6 (va)))
                                }
                               ,
                                _ => match (U8).parse (& rest) {
                                    Ok ((n,
                                    va)) if va >= 7 => {
                                        Ok ((n,
                                        ChoiceWidth8::Variant7 (va)))
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
    ?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ChoiceWidth8> for ChoiceWidth8Fmt {
        fn serialize_into(&self, v: &ChoiceWidth8, obuf: &mut Output) {
            reveal(<ChoiceWidth8Fmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceWidth8Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth8 as DeepView>::deep_view);
            reveal(ChoiceWidth8Spec::into_structural);
            let ghost old_obuf = obuf@;

            match v {
                ChoiceWidth8::Variant0 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth8::Variant1 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth8::Variant2 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth8::Variant3 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth8::Variant4 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth8::Variant5 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth8::Variant6 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth8::Variant7 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceWidth8> for ChoiceWidth8Fmt {
        fn prepare(&self, v: &ChoiceWidth8) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceWidth8Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth8 as DeepView>::deep_view);
            reveal(ChoiceWidth8Spec::into_structural);
            match v {
                ChoiceWidth8::Variant0 (v) => {
                    if ! (*v == 0) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth8::Variant1 (v) => {
                    if ! (*v == 1) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth8::Variant2 (v) => {
                    if ! (*v == 2) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth8::Variant3 (v) => {
                    if ! (*v == 3) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth8::Variant4 (v) => {
                    if ! (*v == 4) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth8::Variant5 (v) => {
                    if ! (*v == 5) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth8::Variant6 (v) => {
                    if ! (*v == 6) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth8::Variant7 (v) => {
                    if ! (*v >= 7) {
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
