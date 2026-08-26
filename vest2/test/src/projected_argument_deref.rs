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
# [doc = "data type for `tag`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum Tag {
    A = 0,
    B = 1,
    Unknown (u8),
}
pub type TagSpec = Tag ;
pub type TagInner = Sum < u8, u8 > ;
impl DeepView for Tag {
    type V = Self ;
    open spec fn deep_view (& self) -> Self::V {
        * self
    }
}
# [cfg (not (verus_keep_ghost))] unsafe impl Structural for Tag {
}

# [doc = "data type for `header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct Header {
    pub t: Tag,
}
pub type HeaderSpec = Header ;
pub type HeaderInner = TagSpec ;
impl DeepView for Header {
    type V = Self ;
    open spec fn deep_view (& self) -> Self::V {
        * self
    }
}

# [doc = "data type for `body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum Body {
    A (u8),
    Default (u16),
}
pub type BodySpec = Body ;
pub type BodyInner = Sum < u8, u16 > ;
impl DeepView for Body {
    type V = Self ;
    open spec fn deep_view (& self) -> Self::V {
        * self
    }
}

# [doc = "data type for `length_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct LengthHeader {
    pub len: u8,
}
pub type LengthHeaderSpec = LengthHeader ;
pub type LengthHeaderInner = u8 ;
impl DeepView for LengthHeader {
    type V = Self ;
    open spec fn deep_view (& self) -> Self::V {
        * self
    }
}

# [doc = "data type for `sized_body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct SizedBody<'i> {
    pub bytes: &'i [u8],
}
# [verifier::ext_equal]
pub struct SizedBodySpec {
    pub bytes: Seq < u8 >,
}
pub type SizedBodyInner = Seq < u8 > ;
impl<'i> DeepView for SizedBody<'i> {
    type V = SizedBodySpec ;
    open spec fn deep_view (& self) -> Self::V {
        SizedBodySpec {
            bytes: self.bytes.deep_view(),
        }
    }
}

# [doc = "data type for `dotted`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct Dotted {
    pub h: Header,
    pub b: Body,
}
pub type DottedSpec = Dotted ;
pub type DottedInner = (HeaderSpec, BodySpec) ;
impl DeepView for Dotted {
    type V = Self ;
    open spec fn deep_view (& self) -> Self::V {
        * self
    }
}

# [doc = "data type for `dotted_length`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct DottedLength<'i> {
    pub h: LengthHeader,
    pub b: SizedBody<'i>,
}
# [verifier::ext_equal]
pub struct DottedLengthSpec {
    pub h: LengthHeaderSpec,
    pub b: SizedBodySpec,
}
pub type DottedLengthInner = (LengthHeaderSpec, SizedBodySpec) ;
impl<'i> DeepView for DottedLength<'i> {
    type V = DottedLengthSpec ;
    open spec fn deep_view (& self) -> Self::V {
        DottedLengthSpec {
            h: self.h.deep_view(),
            b: self.b.deep_view(),
        }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `tag`."]
# [derive (Clone, Copy)]
pub struct TagFmt ;

pub type TagFmtSpec = Named < Mapped < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, FnSpecMapper < TagInner, TagSpec >> > ;

impl TagFmt {
    # [doc = "specification constructor for `tag`."] pub open spec fn spec_inner() -> TagFmtSpec {
        Named ("tag",
        Mapped {
            inner: Choice (Refined (U8,
            | x: u8 | (x == 0) || (x == 1)),
            Refined (U8,
            | x: u8 | (x != 0) && (x != 1))),
            mapper: (| parsed: TagInner | -> TagSpec {
                match parsed {
                    L (x) => match x {
                        0 => TagSpec::A,
                        1 => TagSpec::B,
                        _ => arbitrary(),
                    }
                   ,
                    R (x) => TagSpec::Unknown (x),
                }
            }
           ,
            | value: TagSpec | -> TagInner {
                match value {
                    TagSpec::A => L (0),
                    TagSpec::B => L (1),
                    TagSpec::Unknown (x) => R (x),
                }
            }
            )
        }
        )
    }
}


# [doc = "named format combinator for `header`."]
# [derive (Clone, Copy)]
pub struct HeaderFmt ;

pub type HeaderFmtSpec = Named < Mapped < TagFmt, FnSpecMapper < HeaderInner, HeaderSpec >> > ;

impl HeaderFmt {
    # [doc = "specification constructor for `header`."] pub open spec fn spec_inner() -> HeaderFmtSpec {
        Named ("header",
        Mapped {
            inner: TagFmt,
            mapper: (| parsed: HeaderInner | -> HeaderSpec {
                let t = parsed ;
                HeaderSpec {
                    t
                }
            }
           ,
            | value: HeaderSpec | -> HeaderInner {
                let HeaderSpec {
                    t
                }
                = value ;
                t
            }
            )
        }
        )
    }
}


# [doc = "named format combinator for `body`."]
# [derive (Clone, Copy)]
pub struct BodyFmt {
    t: Tag,
}
impl BodyFmt {
    # [verifier::type_invariant] spec fn wf (& self) -> bool {
        TagFmt.consistent (self.t.deep_view())
    }
    pub closed spec fn t_spec (& self) -> TagSpec {
        self.t.deep_view()
    }
    pub closed spec fn spec (t: Tag) -> Self {
        BodyFmt {
            t
        }
    }
}

pub type BodyFmtSpec = Named < Mapped < Sum < U8, U16Le >, FnSpecMapper < BodyInner, BodySpec >> > ;

impl BodyFmt {
    # [doc = "specification constructor for `body`."] pub open spec fn spec_inner (t: TagSpec) -> BodyFmtSpec {
        Named ("body",
        Mapped {
            inner: match t {
                TagSpec::A => L (U8),
                _ => R (U16Le),
            }
           ,
            mapper: (| parsed: BodyInner | -> BodySpec {
                match parsed {
                    L (v) => BodySpec::A (v),
                    R (v) => BodySpec::Default (v),
                }
            }
           ,
            | value: BodySpec | -> BodyInner {
                match value {
                    BodySpec::A (v) => L (v),
                    BodySpec::Default (v) => R (v),
                }
            }
            )
        }
        )
    }
}


# [doc = "named format combinator for `length_header`."]
# [derive (Clone, Copy)]
pub struct LengthHeaderFmt ;

pub type LengthHeaderFmtSpec = Named < Mapped < U8, FnSpecMapper < LengthHeaderInner, LengthHeaderSpec >> > ;

impl LengthHeaderFmt {
    # [doc = "specification constructor for `length_header`."] pub open spec fn spec_inner() -> LengthHeaderFmtSpec {
        Named ("length_header",
        Mapped {
            inner: U8,
            mapper: (| parsed: LengthHeaderInner | -> LengthHeaderSpec {
                let len = parsed ;
                LengthHeaderSpec {
                    len
                }
            }
           ,
            | value: LengthHeaderSpec | -> LengthHeaderInner {
                let LengthHeaderSpec {
                    len
                }
                = value ;
                len
            }
            )
        }
        )
    }
}


# [doc = "named format combinator for `sized_body`."]
# [derive (Clone, Copy)]
pub struct SizedBodyFmt {
    len: u8,
}
impl SizedBodyFmt {
    # [verifier::type_invariant] spec fn wf (& self) -> bool {
        true
    }
    pub closed spec fn len_spec (& self) -> u8 {
        self.len.deep_view()
    }
    pub closed spec fn spec (len: u8) -> Self {
        SizedBodyFmt {
            len
        }
    }
}

pub type SizedBodyFmtSpec = Named < Mapped < Varied < u8 >, FnSpecMapper < SizedBodyInner, SizedBodySpec >> > ;

impl SizedBodyFmt {
    # [doc = "specification constructor for `sized_body`."] pub open spec fn spec_inner (len: u8) -> SizedBodyFmtSpec {
        Named ("sized_body",
        Mapped {
            inner: Varied (len),
            mapper: (| parsed: SizedBodyInner | -> SizedBodySpec {
                let bytes = parsed ;
                SizedBodySpec {
                    bytes
                }
            }
           ,
            | value: SizedBodySpec | -> SizedBodyInner {
                let SizedBodySpec {
                    bytes
                }
                = value ;
                bytes
            }
            )
        }
        )
    }
}


# [doc = "named format combinator for `dotted`."]
# [derive (Clone, Copy)]
pub struct DottedFmt ;

pub type DottedFmtSpec = Named < Mapped < Bind < HeaderFmt, spec_fn (HeaderSpec) -> BodyFmt >, FnSpecMapper < DottedInner, DottedSpec >> > ;

impl DottedFmt {
    # [doc = "specification constructor for `dotted`."] pub open spec fn spec_inner() -> DottedFmtSpec {
        Named ("dotted",
        Mapped {
            inner: Bind (HeaderFmt,
            | h: HeaderSpec | BodyFmt::spec (h.t)),
            mapper: (| parsed: DottedInner | -> DottedSpec {
                let (h,
                b) = parsed ;
                DottedSpec {
                    h,
                    b
                }
            }
           ,
            | value: DottedSpec | -> DottedInner {
                let DottedSpec {
                    h,
                    b
                }
                = value ;
                (h,
                b)
            }
            )
        }
        )
    }
}


# [doc = "named format combinator for `dotted_length`."]
# [derive (Clone, Copy)]
pub struct DottedLengthFmt ;

pub type DottedLengthFmtSpec = Named < Mapped < Bind < LengthHeaderFmt, spec_fn (LengthHeaderSpec) -> SizedBodyFmt >, FnSpecMapper < DottedLengthInner, DottedLengthSpec >> > ;

impl DottedLengthFmt {
    # [doc = "specification constructor for `dotted_length`."] pub open spec fn spec_inner() -> DottedLengthFmtSpec {
        Named ("dotted_length",
        Mapped {
            inner: Bind (LengthHeaderFmt,
            | h: LengthHeaderSpec | SizedBodyFmt::spec (h.len)),
            mapper: (| parsed: DottedLengthInner | -> DottedLengthSpec {
                let (h,
                b) = parsed ;
                DottedLengthSpec {
                    h,
                    b
                }
            }
           ,
            | value: DottedLengthSpec | -> DottedLengthInner {
                let DottedLengthSpec {
                    h,
                    b
                }
                = value ;
                (h,
                b)
            }
            )
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for TagFmt {
        type PVal = TagSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TagFmt {
        type Val = TagSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TagFmt {
        type SValue = TagSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TagFmt {
        type SVal = TagSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TagFmt {
        type T = TagSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for HeaderFmt {
        type PVal = HeaderSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for HeaderFmt {
        type Val = HeaderSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for HeaderFmt {
        type SValue = HeaderSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for HeaderFmt {
        type SVal = HeaderSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for HeaderFmt {
        type T = HeaderSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for BodyFmt {
        type PVal = BodySpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner (self.t_spec()).spec_parse (ibuf)
        }
    }
    impl Consistency for BodyFmt {
        type Val = BodySpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner (self.t_spec()).consistent (v)
        }
    }
    impl SpecSerializerDps for BodyFmt {
        type SValue = BodySpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner (self.t_spec()).spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for BodyFmt {
        type SVal = BodySpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner (self.t_spec()).spec_serialize (v)
        }
    }
    impl SpecByteLen for BodyFmt {
        type T = BodySpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner (self.t_spec()).byte_len (v)
        }
    }

    impl SpecParser for LengthHeaderFmt {
        type PVal = LengthHeaderSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for LengthHeaderFmt {
        type Val = LengthHeaderSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for LengthHeaderFmt {
        type SValue = LengthHeaderSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for LengthHeaderFmt {
        type SVal = LengthHeaderSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for LengthHeaderFmt {
        type T = LengthHeaderSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for SizedBodyFmt {
        type PVal = SizedBodySpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner (self.len_spec()).spec_parse (ibuf)
        }
    }
    impl Consistency for SizedBodyFmt {
        type Val = SizedBodySpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner (self.len_spec()).consistent (v)
        }
    }
    impl SpecSerializerDps for SizedBodyFmt {
        type SValue = SizedBodySpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner (self.len_spec()).spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for SizedBodyFmt {
        type SVal = SizedBodySpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner (self.len_spec()).spec_serialize (v)
        }
    }
    impl SpecByteLen for SizedBodyFmt {
        type T = SizedBodySpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner (self.len_spec()).byte_len (v)
        }
    }

    impl SpecParser for DottedFmt {
        type PVal = DottedSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for DottedFmt {
        type Val = DottedSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for DottedFmt {
        type SValue = DottedSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for DottedFmt {
        type SVal = DottedSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for DottedFmt {
        type T = DottedSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for DottedLengthFmt {
        type PVal = DottedLengthSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for DottedLengthFmt {
        type Val = DottedLengthSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for DottedLengthFmt {
        type SValue = DottedLengthSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for DottedLengthFmt {
        type SVal = DottedLengthSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for DottedLengthFmt {
        type T = DottedLengthSpec ;
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
    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for TagFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TagFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TagFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TagFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TagFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TagFmt as SpecParser>::spec_parse) ;
            reveal(< TagFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TagFmt as SpecParser>::spec_parse) ;
            reveal(< TagFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TagFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TagFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TagFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TagFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TagFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TagFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TagFmt as SpecParser>::spec_parse) ;
            reveal(< TagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TagFmt as Consistency>::consistent) ;
            reveal(< TagFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TagFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TagFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TagFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TagFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TagFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TagFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for HeaderFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< HeaderFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for HeaderFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< HeaderFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for HeaderFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< HeaderFmt as SpecParser>::spec_parse) ;
            reveal(< HeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< HeaderFmt as SpecParser>::spec_parse) ;
            reveal(< HeaderFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for HeaderFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< HeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< HeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< HeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for HeaderFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< HeaderFmt as SpecSerializer>::spec_serialize) ;
            reveal(< HeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for HeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< HeaderFmt as SpecParser>::spec_parse) ;
            reveal(< HeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< HeaderFmt as Consistency>::consistent) ;
            reveal(< HeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for HeaderFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< HeaderFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for HeaderFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< HeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< HeaderFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for HeaderFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< HeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< HeaderFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for BodyFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< BodyFmt as SpecParser>::spec_parse) ;
            Self::spec_inner (self.t_spec()).lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for BodyFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner (self.t_spec()).productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< BodyFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for BodyFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< BodyFmt as SpecParser>::spec_parse) ;
            reveal(< BodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< BodyFmt as SpecParser>::spec_parse) ;
            reveal(< BodyFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for BodyFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for BodyFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< BodyFmt as SpecSerializer>::spec_serialize) ;
            reveal(< BodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for BodyFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< BodyFmt as SpecParser>::spec_parse) ;
            reveal(< BodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BodyFmt as Consistency>::consistent) ;
            reveal(< BodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for BodyFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< BodyFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for BodyFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< BodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BodyFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for BodyFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< BodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BodyFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner (self.t_spec()) ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for LengthHeaderFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for LengthHeaderFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for LengthHeaderFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecParser>::spec_parse) ;
            reveal(< LengthHeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecParser>::spec_parse) ;
            reveal(< LengthHeaderFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for LengthHeaderFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< LengthHeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for LengthHeaderFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< LengthHeaderFmt as SpecSerializer>::spec_serialize) ;
            reveal(< LengthHeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for LengthHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecParser>::spec_parse) ;
            reveal(< LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< LengthHeaderFmt as Consistency>::consistent) ;
            reveal(< LengthHeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for LengthHeaderFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for LengthHeaderFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< LengthHeaderFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for LengthHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< LengthHeaderFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for SizedBodyFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecParser>::spec_parse) ;
            Self::spec_inner (self.len_spec()).lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for SizedBodyFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner (self.len_spec()).productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for SizedBodyFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecParser>::spec_parse) ;
            reveal(< SizedBodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecParser>::spec_parse) ;
            reveal(< SizedBodyFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for SizedBodyFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< SizedBodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for SizedBodyFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< SizedBodyFmt as SpecSerializer>::spec_serialize) ;
            reveal(< SizedBodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for SizedBodyFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecParser>::spec_parse) ;
            reveal(< SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< SizedBodyFmt as Consistency>::consistent) ;
            reveal(< SizedBodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for SizedBodyFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for SizedBodyFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< SizedBodyFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for SizedBodyFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< SizedBodyFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner (self.len_spec()) ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for DottedFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< DottedFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for DottedFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< DottedFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for DottedFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< DottedFmt as SpecParser>::spec_parse) ;
            reveal(< DottedFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< DottedFmt as SpecParser>::spec_parse) ;
            reveal(< DottedFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for DottedFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< DottedFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< DottedFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DottedFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for DottedFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< DottedFmt as SpecSerializer>::spec_serialize) ;
            reveal(< DottedFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for DottedFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< DottedFmt as SpecParser>::spec_parse) ;
            reveal(< DottedFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DottedFmt as Consistency>::consistent) ;
            reveal(< DottedFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for DottedFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< DottedFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for DottedFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< DottedFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DottedFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for DottedFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< DottedFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DottedFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for DottedLengthFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for DottedLengthFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for DottedLengthFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecParser>::spec_parse) ;
            reveal(< DottedLengthFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecParser>::spec_parse) ;
            reveal(< DottedLengthFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for DottedLengthFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DottedLengthFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for DottedLengthFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< DottedLengthFmt as SpecSerializer>::spec_serialize) ;
            reveal(< DottedLengthFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for DottedLengthFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecParser>::spec_parse) ;
            reveal(< DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DottedLengthFmt as Consistency>::consistent) ;
            reveal(< DottedLengthFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for DottedLengthFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for DottedLengthFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DottedLengthFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for DottedLengthFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DottedLengthFmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for TagFmt {
        type PT = Tag;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TagFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                0 => Tag::A,
                1 => Tag::B,
                x => Tag::Unknown (x),
            };
            assert (self.spec_parse (ibuf @) == Some ((n as int, enum_val.deep_view()))) ;
            Ok((n, enum_val))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Tag> for TagFmt {
        fn serialize_into(&self, v: &Tag, obuf: &mut Output) {
            reveal(<TagFmt as SpecSerializer>::spec_serialize);
            reveal(<TagFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                Tag::A => 0,
                Tag::B => 1,
                Tag::Unknown (x) => x,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Tag> for TagFmt {
        fn prepare(&self, v: &Tag) -> Result<usize, PreSerializeError> {
            reveal(<TagFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                Tag::A => 0,
                Tag::B => 1,
                Tag::Unknown (x) if x != 0 && x != 1 => x, _ => return Err (PreSerializeError::not_compliant (ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }



    impl<'i> Parser<&'i [u8]> for HeaderFmt {
        type PT = Header;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<HeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, t) = (Named ("tag", TagFmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Header {
                t,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Header> for HeaderFmt {
        fn serialize_into(&self, v: &Header, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;
            reveal(<HeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let Header {
                t,
            } = v;
            TagFmt.serialize_into(t, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Header> for HeaderFmt {
        fn prepare(&self, v: &Header) -> Result<usize, PreSerializeError> {
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            let Header {
                t,
            } = v;
            let l1 = (Named ("tag", TagFmt)).prepare (t) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for BodyFmt {
        type PT = Body;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<BodyFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.t {
                Tag::A => {
                    let (n,
                    v) = (U8).parse (& rest) ?;
                    (n,
                    Body::A (v))
                }
                ,
                _ => {
                    let (n,
                    v) = (U16Le).parse (& rest) ?;
                    (n,
                    Body::Default (v))
                }
                ,
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Body> for BodyFmt {
        fn serialize_into(&self, v: &Body, obuf: &mut Output) {
            reveal(<BodyFmt as SpecSerializer>::spec_serialize);
            reveal(<BodyFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.t, v) {
                (Tag::A, Body::A (v)) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                (_, Body::Default (v)) => {
                    (U16Le).serialize_into (v,
                    obuf) ;
                }
                ,
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Body> for BodyFmt {
        fn prepare(&self, v: &Body) -> Result<usize, PreSerializeError> {
            reveal(<BodyFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.t, v) {
                (Tag::A, Body::A (v)) => (U8).prepare (v),
                (Tag::B, Body::Default (v)) => (U16Le).prepare (v),
                (Tag::Unknown (x), Body::Default (v)) if x != 0 && x != 1 => (U16Le).prepare (v),
                 _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }



    impl<'i> Parser<&'i [u8]> for LengthHeaderFmt {
        type PT = LengthHeader;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<LengthHeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, len) = (U8).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = LengthHeader {
                len,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, LengthHeader> for LengthHeaderFmt {
        fn serialize_into(&self, v: &LengthHeader, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;
            reveal(<LengthHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<LengthHeaderFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let LengthHeader {
                len,
            } = v;
            U8.serialize_into(len, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<LengthHeader> for LengthHeaderFmt {
        fn prepare(&self, v: &LengthHeader) -> Result<usize, PreSerializeError> {
            reveal(<LengthHeaderFmt as SpecByteLen>::byte_len);
            let LengthHeader {
                len,
            } = v;
            let l1 = (U8).prepare (len) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for SizedBodyFmt {
        type PT = SizedBody<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<SizedBodyFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, bytes) = (Varied (self.len)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = SizedBody {
                bytes,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, SizedBody<'i>> for SizedBodyFmt {
        fn serialize_into(&self, v: &SizedBody<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;
            reveal(<SizedBodyFmt as SpecSerializer>::spec_serialize);
            reveal(<SizedBodyFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let SizedBody {
                bytes,
            } = v;
            Varied (self.len).serialize_into(* bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<SizedBody<'i>> for SizedBodyFmt {
        fn prepare(&self, v: &SizedBody<'i>) -> Result<usize, PreSerializeError> {
            reveal(<SizedBodyFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let SizedBody {
                bytes,
            } = v;
            let l1 = (Varied (self.len)).prepare (bytes) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for DottedFmt {
        type PT = Dotted;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DottedFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, h) = (Named ("header", HeaderFmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, b) = (Named ("body", BodyFmt {
                t: h.t
            }
            )).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Dotted {
                h,
                b,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Dotted> for DottedFmt {
        fn serialize_into(&self, v: &Dotted, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;
            reveal(<DottedFmt as SpecSerializer>::spec_serialize);
            reveal(<DottedFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let Dotted {
                h,
                b,
            } = v;
            HeaderFmt.serialize_into(h, obuf);
            BodyFmt {
                t: h.t
            }
            .serialize_into(b, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Dotted> for DottedFmt {
        fn prepare(&self, v: &Dotted) -> Result<usize, PreSerializeError> {
            reveal(<DottedFmt as SpecByteLen>::byte_len);
            let Dotted {
                h,
                b,
            } = v;
            let l1 = (Named ("header", HeaderFmt)).prepare (h) ?;
            let l2 = (Named ("body", BodyFmt {
                t: h.t
            }
            )).prepare (b) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for DottedLengthFmt {
        type PT = DottedLength<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DottedLengthFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, h) = (Named ("length_header", LengthHeaderFmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, b) = (Named ("sized_body", SizedBodyFmt {
                len: h.len
            }
            )).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = DottedLength {
                h,
                b,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DottedLength<'i>> for DottedLengthFmt {
        fn serialize_into(&self, v: &DottedLength<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;
            reveal(<DottedLengthFmt as SpecSerializer>::spec_serialize);
            reveal(<DottedLengthFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let DottedLength {
                h,
                b,
            } = v;
            LengthHeaderFmt.serialize_into(h, obuf);
            SizedBodyFmt {
                len: h.len
            }
            .serialize_into(b, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DottedLength<'i>> for DottedLengthFmt {
        fn prepare(&self, v: &DottedLength<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DottedLengthFmt as SpecByteLen>::byte_len);
            let DottedLength {
                h,
                b,
            } = v;
            let l1 = (Named ("length_header", LengthHeaderFmt)).prepare (h) ?;
            let l2 = (Named ("sized_body", SizedBodyFmt {
                len: h.len
            }
            )).prepare (b) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
