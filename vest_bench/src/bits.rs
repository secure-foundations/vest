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
# [doc = "data type for `bits_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct BitsHeader {
    pub version: u8,
    pub ihl: u8,
    pub dscp: u8,
    pub ecn: u8,
}
pub type BitsHeaderSpec = BitsHeader ;
pub type BitsHeaderInner = u16 ;
impl DeepView for BitsHeader {
    type V = Self ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        * self
    }
}
impl BitsHeader {
    pub proof fn lemma_deep_view (& self) ensures self.deep_view() == * self,
    {
        reveal(< BitsHeader as DeepView>::deep_view) ;
    }
}

# [doc = "data type for `bits_packet`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct BitsPacket<'i> {
    pub hdr: BitsHeader,
    pub total_len: u16,
    pub ident: u16,
    pub ttl: u8,
    pub proto: u8,
    pub checksum: u16,
    pub src: &'i [u8],
    pub dst: &'i [u8],
}
# [verifier::ext_equal]
pub struct BitsPacketSpec < T0 = BitsHeaderSpec, T1 = u16, T2 = u16, T3 = u8, T4 = u8, T5 = u16, T6 = Seq < u8 >, T7 = Seq < u8 > > {
    pub hdr: T0,
    pub total_len: T1,
    pub ident: T2,
    pub ttl: T3,
    pub proto: T4,
    pub checksum: T5,
    pub src: T6,
    pub dst: T7,
}
pub type BitsPacketInner = (BitsHeaderSpec, (u16, (u16, (u8, (u8, (u16, (Seq < u8 >, Seq < u8 >))))))) ;
impl<'i> DeepView for BitsPacket<'i> {
    type V = BitsPacketSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        BitsPacketSpec {
            hdr: self.hdr.deep_view(),
            total_len: self.total_len.deep_view(),
            ident: self.ident.deep_view(),
            ttl: self.ttl.deep_view(),
            proto: self.proto.deep_view(),
            checksum: self.checksum.deep_view(),
            src: self.src.deep_view(),
            dst: self.dst.deep_view(),
        }
    }
}
impl<'i> BitsPacket<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().total_len == self.total_len.deep_view(),
    self.deep_view().ident == self.ident.deep_view(),
    self.deep_view().ttl == self.ttl.deep_view(),
    self.deep_view().proto == self.proto.deep_view(),
    self.deep_view().checksum == self.checksum.deep_view(),
    self.deep_view().src == self.src.deep_view(),
    self.deep_view().dst == self.dst.deep_view(),
    {
        reveal(< BitsPacket as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7 > BitsPacketSpec < T0, T1, T2, T3, T4, T5, T6, T7 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    T7)))))))) -> Self {
        let (hdr,
        (total_len,
        (ident,
        (ttl,
        (proto,
        (checksum,
        (src,
        dst))))))) = input ;
        Self {
            hdr,
            total_len,
            ident,
            ttl,
            proto,
            checksum,
            src,
            dst
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    T7))))))) {
        let Self {
            hdr,
            total_len,
            ident,
            ttl,
            proto,
            checksum,
            src,
            dst
        }
        = self ;
        (hdr,
        (total_len,
        (ident,
        (ttl,
        (proto,
        (checksum,
        (src,
        dst)))))))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(BitsPacketSpec::from_structural) ;
        reveal(BitsPacketSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    T7)))))))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(BitsPacketSpec::from_structural) ;
        reveal(BitsPacketSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            total_len,
            ident,
            ttl,
            proto,
            checksum,
            src,
            dst
        }
        => (hdr,
        (total_len,
        (ident,
        (ttl,
        (proto,
        (checksum,
        (src,
        dst))))))),
    }
   ,
    {
        reveal(BitsPacketSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BitsPacketForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BitsPacketReverse ;
impl SpecMap for BitsPacketForward {
    type Input = BitsPacketInner ;
    type Output = BitsPacketSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        BitsPacketSpec::from_structural (input)
    }
}
impl SpecMap for BitsPacketReverse {
    type Input = BitsPacketSpec ;
    type Output = BitsPacketInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `bits_header`."]
# [derive (Clone, Copy)]
pub struct BitsHeaderFmt ;

pub const BITS_HEADER_VERSION_MASK: u16 = 0b0000000000001111u16 ;
pub const BITS_HEADER_VERSION_SHIFT: u16 = 12 ;
pub const BITS_HEADER_VERSION_MAX: u8 = 0b00010000u8 ;
pub const BITS_HEADER_IHL_MASK: u16 = 0b0000000000001111u16 ;
pub const BITS_HEADER_IHL_SHIFT: u16 = 8 ;
pub const BITS_HEADER_IHL_MAX: u8 = 0b00010000u8 ;
pub const BITS_HEADER_DSCP_MASK: u16 = 0b0000000000111111u16 ;
pub const BITS_HEADER_DSCP_SHIFT: u16 = 2 ;
pub const BITS_HEADER_DSCP_MAX: u8 = 0b01000000u8 ;
pub const BITS_HEADER_ECN_MASK: u16 = 0b0000000000000011u16 ;
pub const BITS_HEADER_ECN_SHIFT: u16 = 0 ;
pub const BITS_HEADER_ECN_MAX: u8 = 0b00000100u8 ;
# [verifier::allow_in_spec]
pub fn unpack_bits_header (raw: u16) -> (u8, u8, u8, u8) returns ((((raw >> BITS_HEADER_VERSION_SHIFT) & BITS_HEADER_VERSION_MASK) as u8), (((raw >> BITS_HEADER_IHL_SHIFT) & BITS_HEADER_IHL_MASK) as u8), (((raw >> BITS_HEADER_DSCP_SHIFT) & BITS_HEADER_DSCP_MASK) as u8), ((raw & BITS_HEADER_ECN_MASK) as u8)), {
    ((((raw >> BITS_HEADER_VERSION_SHIFT) & BITS_HEADER_VERSION_MASK) as u8),
    (((raw >> BITS_HEADER_IHL_SHIFT) & BITS_HEADER_IHL_MASK) as u8),
    (((raw >> BITS_HEADER_DSCP_SHIFT) & BITS_HEADER_DSCP_MASK) as u8),
    ((raw & BITS_HEADER_ECN_MASK) as u8))
}
# [verifier::allow_in_spec]
pub fn pack_bits_header (version: u8, ihl: u8, dscp: u8, ecn: u8) -> u16 returns (((version as u16) & BITS_HEADER_VERSION_MASK) << BITS_HEADER_VERSION_SHIFT) | (((ihl as u16) & BITS_HEADER_IHL_MASK) << BITS_HEADER_IHL_SHIFT) | (((dscp as u16) & BITS_HEADER_DSCP_MASK) << BITS_HEADER_DSCP_SHIFT) | (((ecn as u16) & BITS_HEADER_ECN_MASK)), {
    (((version as u16) & BITS_HEADER_VERSION_MASK) << BITS_HEADER_VERSION_SHIFT) | (((ihl as u16) & BITS_HEADER_IHL_MASK) << BITS_HEADER_IHL_SHIFT) | (((dscp as u16) & BITS_HEADER_DSCP_MASK) << BITS_HEADER_DSCP_SHIFT) | (((ecn as u16) & BITS_HEADER_ECN_MASK))
}
# [verifier::allow_in_spec]
pub fn bits_header_bounds (version: u8, ihl: u8, dscp: u8, ecn: u8) -> bool returns (version < BITS_HEADER_VERSION_MAX) && (ihl < BITS_HEADER_IHL_MAX) && (dscp < BITS_HEADER_DSCP_MAX) && (ecn < BITS_HEADER_ECN_MAX), {
    (version < BITS_HEADER_VERSION_MAX) && (ihl < BITS_HEADER_IHL_MAX) && (dscp < BITS_HEADER_DSCP_MAX) && (ecn < BITS_HEADER_ECN_MAX)
}
pub broadcast proof fn lemma_bits_header_unpack_pack (raw: u16) by (bit_vector) ensures # [trigger]
pack_bits_header (unpack_bits_header (raw).0, unpack_bits_header (raw).1, unpack_bits_header (raw).2, unpack_bits_header (raw).3) == raw, {
}
pub broadcast proof fn lemma_bits_header_pack_unpack (version: u8, ihl: u8, dscp: u8, ecn: u8) by (bit_vector) requires # [trigger] bits_header_bounds (version, ihl, dscp, ecn), ensures unpack_bits_header (pack_bits_header (version, ihl, dscp, ecn)).0 == version, unpack_bits_header (pack_bits_header (version, ihl, dscp, ecn)).1 == ihl, unpack_bits_header (pack_bits_header (version, ihl, dscp, ecn)).2 == dscp, unpack_bits_header (pack_bits_header (version, ihl, dscp, ecn)).3 == ecn, {
}
pub broadcast proof fn lemma_bits_header_mapper_wf_in_out (i: u16) by (bit_vector) ensures # [trigger] bits_header_bounds (unpack_bits_header (i).0, unpack_bits_header (i).1, unpack_bits_header (i).2, unpack_bits_header (i).3), {
}

pub type BitsHeaderFmtSpec = Named < Bits < U16Be, (u8, u8, u8, u8), BitsHeaderSpec > > ;

impl BitsHeaderFmt {
    # [doc = "specification constructor for `bits_header`."] pub open spec fn spec_inner() -> BitsHeaderFmtSpec {
        Named ("bits_header",
        Bits {
            repr: U16Be,
            unpack: | packed: u16 | unpack_bits_header (packed),
            pack: | unpacked: (u8,
            u8,
            u8,
            u8) | {
                let (version,
                ihl,
                dscp,
                ecn) = unpacked ;
                pack_bits_header (version,
                ihl,
                dscp,
                ecn)
            }
           ,
            refinement: | unpacked: (u8,
            u8,
            u8,
            u8) | {
                let (version,
                ihl,
                dscp,
                ecn) = unpacked ;
                true
            }
           ,
            ctor: | unpacked: (u8,
            u8,
            u8,
            u8) | {
                let (version,
                ihl,
                dscp,
                ecn) = unpacked ;
                BitsHeaderSpec {
                    version: version,
                    ihl: ihl,
                    dscp: dscp,
                    ecn: ecn
                }
            }
           ,
            dtor: | value: BitsHeaderSpec | {
                let BitsHeaderSpec {
                    version,
                    ihl,
                    dscp,
                    ecn
                }
                = value ;
                (version,
                ihl,
                dscp,
                ecn)
            }
           ,
            consistent: | value: BitsHeaderSpec | {
                let BitsHeaderSpec {
                    version,
                    ihl,
                    dscp,
                    ecn
                }
                = value ;
                bits_header_bounds (version,
                ihl,
                dscp,
                ecn)
            }
           ,
        }
        )
    }
}


# [doc = "named format combinator for `bits_packet`."]
# [derive (Clone, Copy)]
pub struct BitsPacketFmt ;

pub type BitsPacketFmtSpec = Named < Mapped < Pair < BitsHeaderFmt, Pair < U16Be, Pair < U16Be, Pair < U8, Pair < U8, Pair < U16Be, Pair < Fixed < 4 >, Fixed < 4 > > > > > > > >, BiMap < BitsPacketForward, BitsPacketReverse >> > ;

impl BitsPacketFmt {
    # [doc = "specification constructor for `bits_packet`."] pub open spec fn spec_inner() -> BitsPacketFmtSpec {
        Named ("bits_packet",
        Mapped {
            inner: Pair (BitsHeaderFmt,
            Pair (U16Be,
            Pair (U16Be,
            Pair (U8,
            Pair (U8,
            Pair (U16Be,
            Pair (Fixed::< 4 >,
            Fixed::< 4 >))))))),
            mapper: BiMap (BitsPacketForward,
            BitsPacketReverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for BitsHeaderFmt {
        type PVal = BitsHeaderSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for BitsHeaderFmt {
        type Val = BitsHeaderSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for BitsHeaderFmt {
        type SValue = BitsHeaderSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for BitsHeaderFmt {
        type SVal = BitsHeaderSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for BitsHeaderFmt {
        type T = BitsHeaderSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for BitsPacketFmt {
        type PVal = BitsPacketSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for BitsPacketFmt {
        type Val = BitsPacketSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for BitsPacketFmt {
        type SValue = BitsPacketSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for BitsPacketFmt {
        type SVal = BitsPacketSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for BitsPacketFmt {
        type T = BitsPacketSpec ;
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
        BitsPacketSpec::lemma_from_into,
        BitsPacketSpec::lemma_into_from,
    };

    impl SafeParser for BitsHeaderFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for BitsHeaderFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for BitsHeaderFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecParser>::spec_parse) ;
            reveal(< BitsHeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = BitsHeaderFmt::spec_inner() ;
            broadcast use lemma_bits_header_unpack_pack,
            lemma_bits_header_mapper_wf_in_out ;
            assert (fmt.1.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecParser>::spec_parse) ;
            reveal(< BitsHeaderFmt as Consistency>::consistent) ;
            broadcast use lemma_bits_header_unpack_pack,
            lemma_bits_header_mapper_wf_in_out ;
            let fmt = BitsHeaderFmt::spec_inner() ;
            assert (fmt.1.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for BitsHeaderFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BitsHeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for BitsHeaderFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< BitsHeaderFmt as SpecSerializer>::spec_serialize) ;
            reveal(< BitsHeaderFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for BitsHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BitsHeaderFmt as SpecByteLen>::byte_len) ;
            reveal(< BitsHeaderFmt as SpecParser>::spec_parse) ;
            broadcast use lemma_bits_header_pack_unpack ;
            let fmt = BitsHeaderFmt::spec_inner() ;
            assert (fmt.1.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for BitsHeaderFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecParser>::spec_parse) ;
            broadcast use lemma_bits_header_unpack_pack,
            lemma_bits_header_mapper_wf_in_out ;
            let fmt = BitsHeaderFmt::spec_inner() ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for BitsHeaderFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< BitsHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BitsHeaderFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for BitsHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< BitsHeaderFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BitsHeaderFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for BitsPacketFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for BitsPacketFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for BitsPacketFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecParser>::spec_parse) ;
            reveal(< BitsPacketFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BitsPacketInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BitsPacketSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecParser>::spec_parse) ;
            reveal(< BitsPacketFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BitsPacketInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BitsPacketSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for BitsPacketFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BitsPacketFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for BitsPacketFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< BitsPacketFmt as SpecSerializer>::spec_serialize) ;
            reveal(< BitsPacketFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for BitsPacketFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecParser>::spec_parse) ;
            reveal(< BitsPacketFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BitsPacketFmt as Consistency>::consistent) ;
            reveal(< BitsPacketFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: BitsPacketSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                BitsPacketSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for BitsPacketFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: BitsPacketInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                BitsPacketSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for BitsPacketFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< BitsPacketFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BitsPacketFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for BitsPacketFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< BitsPacketFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< BitsPacketFmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for BitsHeaderFmt {
        type PT = BitsHeader;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<BitsHeaderFmt as SpecParser>::spec_parse);
            reveal(<BitsHeader as DeepView>::deep_view);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, raw) = U16Be.parse(ibuf)?;
            let (version, ihl, dscp, ecn) = unpack_bits_header(raw);
            let final_v = BitsHeader {
                version: version,
                ihl: ihl,
                dscp: dscp,
                ecn: ecn,
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
            Ok((n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, BitsHeader> for BitsHeaderFmt {
        fn serialize_into(&self, v: &BitsHeader, obuf: &mut Output) {
            reveal(<BitsHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<BitsHeaderFmt as SpecByteLen>::byte_len);
            reveal(<BitsHeader as DeepView>::deep_view);
            let ghost old_obuf = obuf@;

            let BitsHeader {
                version,
                ihl,
                dscp,
                ecn
            }
            = *v ;
            let packed = pack_bits_header(version, ihl, dscp, ecn);
            U16Be.serialize_into(&packed, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<BitsHeader> for BitsHeaderFmt {
        fn prepare(&self, v: &BitsHeader) -> Result<usize, PreSerializeError> {
            reveal(<BitsHeaderFmt as SpecByteLen>::byte_len);
            reveal(<BitsHeader as DeepView>::deep_view);
            let BitsHeader {
                version,
                ihl,
                dscp,
                ecn
            }
            = *v ;
            if !(bits_header_bounds (version, ihl, dscp, ecn)) {
                return Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed));
            }
            let packed = pack_bits_header(version, ihl, dscp, ecn);
            U16Be.prepare(&packed)
        }
    }



    impl<'i> Parser<&'i [u8]> for BitsPacketFmt {
        type PT = BitsPacket<'i>;

        fn min_byte_len(&self) -> usize {
            18
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<BitsPacketFmt as SpecParser>::spec_parse);
            reveal(<BitsPacket as DeepView>::deep_view);
            reveal(BitsPacketSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (Named ("bits_header", BitsHeaderFmt)).parse (& rest) ?;
            proof {
                hdr.lemma_deep_view();
            }
            let rest = rest.skip(n1);
            let (n2, total_len) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ident) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let (n4, ttl) = (U8).parse (& rest) ?;
            let rest = rest.skip(n4);
            let (n5, proto) = (U8).parse (& rest) ?;
            let rest = rest.skip(n5);
            let (n6, checksum) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n6);
            let (n7, src) = (Fixed::< 4 >).parse (& rest) ?;
            let rest = rest.skip(n7);
            let (n8, dst) = (Fixed::< 4 >).parse (& rest) ?;
            let rest = rest.skip(n8);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8;
            let final_v = BitsPacket {
                hdr,
                total_len,
                ident,
                ttl,
                proto,
                checksum,
                src,
                dst,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, BitsPacket<'i>> for BitsPacketFmt {
        fn serialize_into(&self, v: &BitsPacket<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<BitsPacketFmt as SpecSerializer>::spec_serialize);
            reveal(<BitsPacketFmt as SpecByteLen>::byte_len);
            reveal(<BitsPacket as DeepView>::deep_view);
            reveal(BitsPacketSpec::into_structural);
            let ghost old_obuf = obuf@;

            let BitsPacket {
                hdr,
                total_len,
                ident,
                ttl,
                proto,
                checksum,
                src,
                dst,
            } = v;
            proof {
                hdr.lemma_deep_view();
            }

            BitsHeaderFmt.serialize_into(hdr, obuf);
            U16Be.serialize_into(total_len, obuf);
            U16Be.serialize_into(ident, obuf);
            U8.serialize_into(ttl, obuf);
            U8.serialize_into(proto, obuf);
            U16Be.serialize_into(checksum, obuf);
            Fixed::< 4 >.serialize_into(* src, obuf);
            Fixed::< 4 >.serialize_into(* dst, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<BitsPacket<'i>> for BitsPacketFmt {
        fn prepare(&self, v: &BitsPacket<'i>) -> Result<usize, PreSerializeError> {
            reveal(<BitsPacketFmt as SpecByteLen>::byte_len);
            reveal(<BitsPacket as DeepView>::deep_view);
            reveal(BitsPacketSpec::into_structural);
            let BitsPacket {
                hdr,
                total_len,
                ident,
                ttl,
                proto,
                checksum,
                src,
                dst,
            } = v;
            proof {
                hdr.lemma_deep_view();
            }

            let l1 = (Named ("bits_header", BitsHeaderFmt)).prepare (hdr) ?;
            let l2 = (U16Be).prepare (total_len) ?;
            let l3 = (U16Be).prepare (ident) ?;
            let l4 = (U8).prepare (ttl) ?;
            let l5 = (U8).prepare (proto) ?;
            let l6 = (U16Be).prepare (checksum) ?;
            let l7 = (Fixed::< 4 >).prepare (src) ?;
            let l8 = (Fixed::< 4 >).prepare (dst) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l4).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l5).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l6).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l7).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l8).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
