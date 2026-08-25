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
# [doc = "data type for `depth0`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth0 {
    pub value: u8,
}
# [verifier::ext_equal]
pub struct Depth0Spec < T0 = u8 > {
    pub value: T0,
}
pub type Depth0Inner = u8 ;
impl DeepView for Depth0 {
    type V = Depth0Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth0Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth0 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth0 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth0Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth0Spec::from_structural) ;
        reveal(Depth0Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth0Spec::from_structural) ;
        reveal(Depth0Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth0Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth0Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth0Reverse ;
impl SpecMap for Depth0Forward {
    type Input = Depth0Inner ;
    type Output = Depth0Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth0Spec::from_structural (input)
    }
}
impl SpecMap for Depth0Reverse {
    type Input = Depth0Spec ;
    type Output = Depth0Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth1 {
    pub value: Depth0,
}
# [verifier::ext_equal]
pub struct Depth1Spec < T0 = Depth0Spec > {
    pub value: T0,
}
pub type Depth1Inner = Depth0Spec ;
impl DeepView for Depth1 {
    type V = Depth1Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth1Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth1 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth1 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth1Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth1Spec::from_structural) ;
        reveal(Depth1Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth1Spec::from_structural) ;
        reveal(Depth1Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth1Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth1Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth1Reverse ;
impl SpecMap for Depth1Forward {
    type Input = Depth1Inner ;
    type Output = Depth1Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth1Spec::from_structural (input)
    }
}
impl SpecMap for Depth1Reverse {
    type Input = Depth1Spec ;
    type Output = Depth1Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `depth0`."]
# [derive (Clone, Copy)]
pub struct Depth0Fmt ;

pub type Depth0FmtSpec = Named < Mapped < U8, BiMap < Depth0Forward, Depth0Reverse >> > ;

impl Depth0Fmt {
    # [doc = "specification constructor for `depth0`."] pub open spec fn spec_inner() -> Depth0FmtSpec {
        Named ("depth0",
        Mapped {
            inner: U8,
            mapper: BiMap (Depth0Forward,
            Depth0Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth1`."]
# [derive (Clone, Copy)]
pub struct Depth1Fmt ;

pub type Depth1FmtSpec = Named < Mapped < Depth0Fmt, BiMap < Depth1Forward, Depth1Reverse >> > ;

impl Depth1Fmt {
    # [doc = "specification constructor for `depth1`."] pub open spec fn spec_inner() -> Depth1FmtSpec {
        Named ("depth1",
        Mapped {
            inner: Depth0Fmt,
            mapper: BiMap (Depth1Forward,
            Depth1Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for Depth0Fmt {
        type PVal = Depth0Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth0Fmt {
        type Val = Depth0Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth0Fmt {
        type SValue = Depth0Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth0Fmt {
        type SVal = Depth0Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth0Fmt {
        type T = Depth0Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth1Fmt {
        type PVal = Depth1Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth1Fmt {
        type Val = Depth1Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth1Fmt {
        type SValue = Depth1Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth1Fmt {
        type SVal = Depth1Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth1Fmt {
        type T = Depth1Spec ;
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
        Depth0Spec::lemma_from_into,
        Depth0Spec::lemma_into_from,
        Depth1Spec::lemma_from_into,
        Depth1Spec::lemma_into_from,
    };

    impl SafeParser for Depth0Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth0Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth0Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth0Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth0Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth0Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth0Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth0Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth0Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth0Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth0Fmt as Consistency>::consistent) ;
            reveal(< Depth0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth0Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth0Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth0Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth0Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth0Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth0Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth0Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth0Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth1Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth1Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth1Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth1Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth1Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth1Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth1Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth1Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth1Fmt as Consistency>::consistent) ;
            reveal(< Depth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth1Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth1Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth1Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth1Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth1Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth1Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth1Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for Depth0Fmt {
        type PT = Depth0;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth0Fmt as SpecParser>::spec_parse);
            reveal(<Depth0 as DeepView>::deep_view);
            reveal(Depth0Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (U8).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth0 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth0> for Depth0Fmt {
        fn serialize_into(&self, v: &Depth0, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;
            reveal(<Depth0Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth0Fmt as SpecByteLen>::byte_len);
            reveal(<Depth0 as DeepView>::deep_view);
            reveal(Depth0Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth0 {
                value,
            } = v;
            U8.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth0> for Depth0Fmt {
        fn prepare(&self, v: &Depth0) -> Result<usize, PreSerializeError> {
            reveal(<Depth0Fmt as SpecByteLen>::byte_len);
            reveal(<Depth0 as DeepView>::deep_view);
            reveal(Depth0Spec::into_structural);
            let Depth0 {
                value,
            } = v;
            let l1 = (U8).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth1Fmt {
        type PT = Depth1;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth1Fmt as SpecParser>::spec_parse);
            reveal(<Depth1 as DeepView>::deep_view);
            reveal(Depth1Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth0", Depth0Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth1 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth1> for Depth1Fmt {
        fn serialize_into(&self, v: &Depth1, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;
            reveal(<Depth1Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth1Fmt as SpecByteLen>::byte_len);
            reveal(<Depth1 as DeepView>::deep_view);
            reveal(Depth1Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth1 {
                value,
            } = v;
            Depth0Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth1> for Depth1Fmt {
        fn prepare(&self, v: &Depth1) -> Result<usize, PreSerializeError> {
            reveal(<Depth1Fmt as SpecByteLen>::byte_len);
            reveal(<Depth1 as DeepView>::deep_view);
            reveal(Depth1Spec::into_structural);
            let Depth1 {
                value,
            } = v;
            let l1 = (Named ("depth0", Depth0Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }

}
}
