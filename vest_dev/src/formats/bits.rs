//! Handwritten reference implementations for prospective Vest DSL bit-packed formats.
//!
//! The corresponding DSL shapes are roughly:
//!
//! ```vest
//! !BIG_ENDIAN
//!
//! version_ihl = bits {
//!     version: u4,
//!     ihl: u4,
//! }
//!
//! cross_byte_span = bits {
//!     prefix: u3,
//!     span: u10,
//!     suffix: u3,
//! }
//!
//! payload_kind = enum {
//!     Raw         = 0u3,
//!     Words       = 1u3,
//!     Tiny        = 2u3,
//!     ...
//! }
//!
//! packet_header = bits {
//!     @kind: payload_kind,
//!     @count: u5 | { 1..31 },
//!     @len: u8,
//! }
//!
//! choice_packet = {
//!     @hdr: packet_header,
//!     payload: choose(@hdr.kind) {
//!         Raw        => [u8; @hdr.len],
//!         Words      => [u16; @hdr.count],
//!         Tiny       => u8,
//!         _          => [u8; @hdr.len],
//!     },
//! }
//! ```
//!
use crate::combinators::mapped::spec::*;
use crate::combinators::*;
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::parser::*;
use crate::core::exec::serializer::*;
use crate::core::exec::ParseError;
use crate::core::exec::{DeepEq, SelfView};
use crate::core::spec::*;
use crate::core::{proof::*, spec};
use vstd::prelude::*;
verus! {

// ============================================================
// Data Types
// ============================================================
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[verifier::ext_equal]
pub struct VersionIhl {
    pub version: u8,
    pub ihl: u8,
}

pub type VersionIhlSpec = VersionIhl;

pub type VersionIhlInner = u8;

impl DeepView for VersionIhl {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[verifier::ext_equal]
pub struct CrossByteSpan {
    pub prefix: u8,
    pub span: u16,
    pub suffix: u8,
}

pub type CrossByteSpanSpec = CrossByteSpan;

pub type CrossByteSpanInner = u16;

impl DeepView for CrossByteSpan {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[repr(u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum PayloadKind {
    Raw = 0,
    Words = 1,
    Tiny = 2,
    Unknown(u8),
}

pub type PayloadKindSpec = PayloadKind;

impl DeepView for PayloadKind {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepEq for PayloadKind {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for PayloadKind {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[verifier::ext_equal]
pub struct PacketHeader {
    pub kind: PayloadKind,
    pub count: u8,
    pub len: u8,
}

pub type PacketHeaderSpec = PacketHeader;

pub type PacketHeaderInner = u16;

impl DeepView for PacketHeader {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ChoicePayload<'i> {
    Raw(&'i [u8]),
    Words(Vec<u16>),
    Tiny(u8),
    Default(&'i [u8]),
}

#[verifier::ext_equal]
pub enum ChoicePayloadSpec {
    Raw(Seq<u8>),
    Words(Seq<u16>),
    Tiny(u8),
    Default(Seq<u8>),
}

pub type ChoicePayloadInner = Sum<Seq<u8>, Sum<Seq<u16>, Sum<u8, Seq<u8>>>>;

impl<'i> DeepView for ChoicePayload<'i> {
    type V = ChoicePayloadSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ChoicePayload::Raw(bytes) => ChoicePayloadSpec::Raw(bytes.deep_view()),
            ChoicePayload::Words(words) => ChoicePayloadSpec::Words(words.deep_view()),
            ChoicePayload::Tiny(x) => ChoicePayloadSpec::Tiny(x.deep_view()),
            ChoicePayload::Default(bytes) => ChoicePayloadSpec::Default(bytes.deep_view()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ChoicePacket<'i> {
    pub hdr: PacketHeader,
    pub payload: ChoicePayload<'i>,
}

#[verifier::ext_equal]
pub struct ChoicePacketSpec {
    pub hdr: PacketHeaderSpec,
    pub payload: ChoicePayloadSpec,
}

pub type ChoicePacketInner = (PacketHeaderSpec, ChoicePayloadSpec);

impl<'i> DeepView for ChoicePacket<'i> {
    type V = ChoicePacketSpec;

    open spec fn deep_view(&self) -> Self::V {
        ChoicePacketSpec { hdr: self.hdr.deep_view(), payload: self.payload.deep_view() }
    }
}

// ============================================================
// Bit helpers
// ============================================================
// Version/IHL field (version: u4, ihl: u4)
pub const VERSION_MASK: u8 = 0b00001111u8;

pub const IHL_MASK: u8 = 0b00001111u8;

pub const VERSION_SHIFT: u8 = 4u8;

pub const PREFIX_MASK_U16: u16 = 0b0000000000000111u16;

pub const SPAN_MASK: u16 = 0b0000001111111111u16;

pub const SUFFIX_MASK: u16 = 0b0000000000000111u16;

pub const PREFIX_SHIFT: u16 = 13u16;

pub const SPAN_SHIFT: u16 = 3u16;

pub const KIND_MASK: u16 = 0b0000000000000111u16;

pub const COUNT_MASK: u16 = 0b0000000000011111u16;

pub const LEN_MASK: u16 = 0b0000000011111111u16;

pub const KIND_SHIFT: u16 = 13u16;

pub const COUNT_SHIFT: u16 = 8u16;

pub const VERSION_MAX: u8 = 0b00010000u8;

pub const IHL_MAX: u8 = 0b00010000u8;

pub const PREFIX_MAX: u8 = 0b00001000u8;

pub const SPAN_MAX: u16 = 0b10000000000u16;

pub const SUFFIX_MAX: u8 = 0b00001000u8;

pub const KIND_MAX: u8 = 0b00001000u8;

pub const COUNT_MAX: u8 = 0b00100000u8;

#[verifier::allow_in_spec]
pub fn unpack_version_ihl(raw: u8) -> (u8, u8)
    returns
        (((raw >> VERSION_SHIFT) & VERSION_MASK), (raw & IHL_MASK)),
{
    (((raw >> VERSION_SHIFT) & VERSION_MASK), (raw & IHL_MASK))
}

#[verifier::allow_in_spec]
pub fn pack_version_ihl(version: u8, ihl: u8) -> u8
    returns
        ((version & VERSION_MASK) << VERSION_SHIFT) | (ihl & IHL_MASK),
{
    ((version & VERSION_MASK) << VERSION_SHIFT) | (ihl & IHL_MASK)
}

#[verifier::allow_in_spec]
pub fn version_ihl_bounds(version: u8, ihl: u8) -> bool
    returns
        version < VERSION_MAX && ihl < IHL_MAX,
{
    version < VERSION_MAX && ihl < IHL_MAX
}

pub proof fn lemma_version_ihl_unpack_pack(raw: u8)
    by (bit_vector)
    ensures
        ({
            let (version, ihl) = unpack_version_ihl(raw);
            pack_version_ihl(version, ihl) == raw
        }),
{
}

pub proof fn lemma_version_ihl_value_pack_unpack(version: u8, ihl: u8)
    by (bit_vector)
    requires
        version_ihl_bounds(version, ihl),
    ensures
        ({
            let (version_, ihl_) = unpack_version_ihl(pack_version_ihl(version, ihl));
            version_ == version && ihl_ == ihl
        }),
{
}

pub proof fn lemma_version_ihl_mapper_wf_in_out(i: u8)
    by (bit_vector)
    ensures
        ({
            let (version, ihl) = unpack_version_ihl(i);
            version_ihl_bounds(version, ihl)
        }),
{
}

#[verifier::allow_in_spec]
pub fn unpack_cross_byte_span(raw: u16) -> (u8, u16, u8)
    returns
        (
            (((raw >> PREFIX_SHIFT) & PREFIX_MASK_U16) as u8),
            (((raw >> SPAN_SHIFT) & SPAN_MASK) as u16),
            ((raw & SUFFIX_MASK) as u8),
        ),
{
    (
        (((raw >> PREFIX_SHIFT) & PREFIX_MASK_U16) as u8),
        (((raw >> SPAN_SHIFT) & SPAN_MASK) as u16),
        ((raw & SUFFIX_MASK) as u8),
    )
}

#[verifier::allow_in_spec]
pub fn pack_cross_byte_span(prefix: u8, span: u16, suffix: u8) -> u16
    returns
        ((((prefix as u16) & PREFIX_MASK_U16) << PREFIX_SHIFT) | (((span as u16) & SPAN_MASK)
            << SPAN_SHIFT) | ((suffix as u16) & SUFFIX_MASK)),
{
    (((prefix as u16) & PREFIX_MASK_U16) << PREFIX_SHIFT) | (((span as u16) & SPAN_MASK)
        << SPAN_SHIFT) | ((suffix as u16) & SUFFIX_MASK)
}

#[verifier::allow_in_spec]
pub fn cross_byte_span_bounds(prefix: u8, span: u16, suffix: u8) -> bool
    returns
        prefix < PREFIX_MAX && span < SPAN_MAX && suffix < SUFFIX_MAX,
{
    prefix < PREFIX_MAX && span < SPAN_MAX && suffix < SUFFIX_MAX
}

pub proof fn lemma_cross_byte_span_unpack_pack(raw: u16)
    by (bit_vector)
    ensures
        ({
            let (prefix, span, suffix) = unpack_cross_byte_span(raw);
            pack_cross_byte_span(prefix, span, suffix) == raw
        }),
{
}

pub proof fn lemma_cross_byte_span_pack_unpack(prefix: u8, span: u16, suffix: u8)
    by (bit_vector)
    requires
        cross_byte_span_bounds(prefix, span, suffix),
    ensures
        ({
            let (prefix_, span_, suffix_) = unpack_cross_byte_span(
                pack_cross_byte_span(prefix, span, suffix),
            );
            prefix_ == prefix && span_ == span && suffix_ == suffix
        }),
{
}

pub proof fn lemma_cross_byte_span_mapper_wf_in_out(i: u16)
    by (bit_vector)
    ensures
        ({
            let (prefix, span, suffix) = unpack_cross_byte_span(i);
            cross_byte_span_bounds(prefix, span, suffix)
        }),
{
}

#[verifier::allow_in_spec]
pub fn unpack_packet_header(raw: u16) -> (u8, u8, u8)
    returns
        (
            (((raw >> KIND_SHIFT) & KIND_MASK) as u8),
            (((raw >> COUNT_SHIFT) & COUNT_MASK) as u8),
            ((raw & LEN_MASK) as u8),
        ),
{
    (
        ((raw >> KIND_SHIFT) & KIND_MASK) as u8,
        ((raw >> COUNT_SHIFT) & COUNT_MASK) as u8,
        (raw & LEN_MASK) as u8,
    )
}

#[verifier::allow_in_spec]
pub fn pack_packet_header(kind_bits: u8, count: u8, len: u8) -> u16
    returns
        ((((kind_bits as u16) & KIND_MASK) << KIND_SHIFT) | (((count as u16) & COUNT_MASK)
            << COUNT_SHIFT) | ((len as u16) & LEN_MASK)),
{
    (((kind_bits as u16) & KIND_MASK) << KIND_SHIFT) | (((count as u16) & COUNT_MASK)
        << COUNT_SHIFT) | ((len as u16) & LEN_MASK)
}

#[verifier::allow_in_spec]
pub fn packet_header_bounds(kind_bits: u8, count: u8, _len: u8) -> bool
    returns
        kind_bits < KIND_MAX && count < COUNT_MAX,
{
    kind_bits < KIND_MAX && count < COUNT_MAX
}

pub proof fn lemma_packet_header_unpack_pack(raw: u16)
    by (bit_vector)
    ensures
        ({
            let (kind_bits, count, len) = unpack_packet_header(raw);
            pack_packet_header(kind_bits, count, len) == raw
        }),
{
}

pub proof fn lemma_packet_header_pack_unpack(kind_bits: u8, count: u8, len: u8)
    by (bit_vector)
    requires
        packet_header_bounds(kind_bits, count, len),
    ensures
        ({
            let (kind_bits_, count_, len_) = unpack_packet_header(
                pack_packet_header(kind_bits, count, len),
            );
            kind_bits_ == kind_bits && count_ == count && len_ == len
        }),
{
}

pub proof fn lemma_packet_header_mapper_wf_in_out(i: u16)
    by (bit_vector)
    ensures
        ({
            let (kind_bits, count, len) = unpack_packet_header(i);
            packet_header_bounds(kind_bits, count, len)
        }),
{
}

#[verifier::allow_in_spec]
pub fn payload_kind_wf(kind: PayloadKind) -> bool
    returns
        kind matches PayloadKind::Unknown(x) ==> x != 0 && x != 1 && x != 2,
{
    matches!(kind, PayloadKind::Raw | PayloadKind::Words | PayloadKind::Tiny)
        || matches!(kind, PayloadKind::Unknown(x) if x != 0 && x != 1 && x != 2)
}

#[verifier::allow_in_spec]
pub fn payload_kind_from_bits(bits: u8) -> PayloadKind
    returns
        match bits {
            0 => PayloadKind::Raw,
            1 => PayloadKind::Words,
            2 => PayloadKind::Tiny,
            _ => PayloadKind::Unknown(bits),
        },
{
    match bits {
        0 => PayloadKind::Raw,
        1 => PayloadKind::Words,
        2 => PayloadKind::Tiny,
        _ => PayloadKind::Unknown(bits),
    }
}

#[verifier::allow_in_spec]
pub fn payload_kind_to_bits(kind: PayloadKind) -> u8
    returns
        match kind {
            PayloadKind::Raw => 0,
            PayloadKind::Words => 1,
            PayloadKind::Tiny => 2,
            PayloadKind::Unknown(x) => x,
        },
{
    match kind {
        PayloadKind::Raw => 0,
        PayloadKind::Words => 1,
        PayloadKind::Tiny => 2,
        PayloadKind::Unknown(x) => x,
    }
}

// ============================================================
// Format Specifications
// ============================================================
#[derive(Clone, Copy)]
pub struct VersionIhlFmt;

pub struct VersionIhlMapper;

impl SpecMapper for VersionIhlMapper {
    type In = VersionIhlInner;

    type Out = VersionIhlSpec;

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        version_ihl_bounds(o.version, o.ihl)
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (version, ihl) = unpack_version_ihl(i);
        VersionIhlSpec { version, ihl }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        pack_version_ihl(o.version, o.ihl)
    }
}

impl LossyMapper for VersionIhlMapper {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        lemma_version_ihl_value_pack_unpack(o.version, o.ihl);
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {
    }
}

impl LosslessMapper for VersionIhlMapper {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        lemma_version_ihl_unpack_pack(i);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        lemma_version_ihl_mapper_wf_in_out(i);
    }
}

pub type VersionIhlFmtSpec = Named<Mapped<U8, VersionIhlMapper>>;

impl VersionIhlFmt {
    pub open spec fn spec_inner() -> VersionIhlFmtSpec {
        Named("version_ihl", Mapped { inner: U8, mapper: VersionIhlMapper })
    }
}

#[derive(Clone, Copy)]
pub struct CrossByteSpanFmt;

pub struct CrossByteSpanMapper;

impl SpecMapper for CrossByteSpanMapper {
    type In = CrossByteSpanInner;

    type Out = CrossByteSpanSpec;

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        cross_byte_span_bounds(o.prefix, o.span, o.suffix)
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (prefix, span, suffix) = unpack_cross_byte_span(i);
        CrossByteSpanSpec { prefix, span, suffix }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        pack_cross_byte_span(o.prefix, o.span, o.suffix)
    }
}

impl LossyMapper for CrossByteSpanMapper {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        lemma_cross_byte_span_pack_unpack(o.prefix, o.span, o.suffix);
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {
    }
}

impl LosslessMapper for CrossByteSpanMapper {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        lemma_cross_byte_span_unpack_pack(i);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        lemma_cross_byte_span_mapper_wf_in_out(i);
    }
}

pub type CrossByteSpanFmtSpec = Named<Mapped<U16Be, CrossByteSpanMapper>>;

impl CrossByteSpanFmt {
    pub open spec fn spec_inner() -> CrossByteSpanFmtSpec {
        Named("cross_byte_span", Mapped { inner: U16Be, mapper: CrossByteSpanMapper })
    }
}

#[derive(Clone, Copy)]
pub struct PacketHeaderFmt;

pub struct PacketHeaderMapper1;

impl SpecMapper for PacketHeaderMapper1 {
    type In = PacketHeaderInner;

    type Out = (u8, u8, u8);

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        let (kind_bits, count, len) = o;
        packet_header_bounds(kind_bits, count, len)
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        unpack_packet_header(i)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        let (kind_bits, count, len) = o;
        pack_packet_header(kind_bits, count, len)
    }
}

impl LossyMapper for PacketHeaderMapper1 {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        let (kind_bits, count, len) = o;
        lemma_packet_header_pack_unpack(kind_bits, count, len);
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {
    }
}

impl LosslessMapper for PacketHeaderMapper1 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        lemma_packet_header_unpack_pack(i);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        lemma_packet_header_mapper_wf_in_out(i);
    }
}

pub struct PacketHeaderMapper2;

impl SpecMapper for PacketHeaderMapper2 {
    type In = (u8, u8, u8);

    type Out = PacketHeaderSpec;

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        payload_kind_wf(o.kind)
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (kind_bits, count, len) = i;
        PacketHeaderSpec { kind: payload_kind_from_bits(kind_bits), count, len }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        let PacketHeaderSpec { kind, count, len } = o;
        (payload_kind_to_bits(kind), count, len)
    }
}

impl LossyMapper for PacketHeaderMapper2 {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {
    }
}

impl LosslessMapper for PacketHeaderMapper2 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

pub type PacketHeaderFmtSpec = Named<
    Mapped<
        Refined<Mapped<U16Be, PacketHeaderMapper1>, PredFnSpec<(u8, u8, u8)>>,
        PacketHeaderMapper2,
    >,
>;

impl PacketHeaderFmt {
    pub open spec fn spec_inner() -> PacketHeaderFmtSpec {
        Named(
            "packet_header",
            Mapped {
                inner: Refined(
                    Mapped { inner: U16Be, mapper: PacketHeaderMapper1 },
                    |hdr: (u8, u8, u8)| hdr.1 >= 1u8,
                ),
                mapper: PacketHeaderMapper2,
            },
        )
    }
}

pub type ChoicePayloadFmt = Mapped<
    Choice<Cond<Varied<u8>>, Choice<Cond<RepeatN<U16Be, u8>>, Choice<Cond<U8>, Cond<Varied<u8>>>>>,
    FnSpecMapper<ChoicePayloadInner, ChoicePayloadSpec>,
>;

pub open spec fn choice_packet_body_fmt(hdr: PacketHeaderSpec) -> ChoicePayloadFmt {
    Mapped {
        inner: Choice(
            Cond(hdr.kind == PayloadKind::Raw, Varied(hdr.len)),
            Choice(
                Cond(hdr.kind == PayloadKind::Words, RepeatN(hdr.count, U16Be)),
                Choice(
                    Cond(hdr.kind == PayloadKind::Tiny, U8),
                    Cond(hdr.kind matches PayloadKind::Unknown(_), Varied(hdr.len)),
                ),
            ),
        ),
        mapper: (
            |parsed: ChoicePayloadInner| -> ChoicePayloadSpec
                {
                    match parsed {
                        Sum::Inl(bytes) => ChoicePayloadSpec::Raw(bytes),
                        Sum::Inr(Sum::Inl(words)) => ChoicePayloadSpec::Words(words),
                        Sum::Inr(Sum::Inr(Sum::Inl(x))) => ChoicePayloadSpec::Tiny(x),
                        Sum::Inr(Sum::Inr(Sum::Inr(bytes))) => ChoicePayloadSpec::Default(bytes),
                    }
                },
            |value: ChoicePayloadSpec| -> ChoicePayloadInner
                {
                    match value {
                        ChoicePayloadSpec::Raw(bytes) => Sum::Inl(bytes),
                        ChoicePayloadSpec::Words(words) => Sum::Inr(Sum::Inl(words)),
                        ChoicePayloadSpec::Tiny(x) => Sum::Inr(Sum::Inr(Sum::Inl(x))),
                        ChoicePayloadSpec::Default(bytes) => Sum::Inr(Sum::Inr(Sum::Inr(bytes))),
                    }
                },
        ),
    }
}

#[derive(Clone, Copy)]
pub struct ChoicePacketFmt;

pub type ChoicePacketFmtSpec = Named<
    Mapped<
        Bind<PacketHeaderFmt, spec_fn(PacketHeaderSpec) -> ChoicePayloadFmt>,
        FnSpecMapper<ChoicePacketInner, ChoicePacketSpec>,
    >,
>;

impl ChoicePacketFmt {
    pub open spec fn spec_inner() -> ChoicePacketFmtSpec {
        Named(
            "choice_packet",
            Mapped {
                inner: Bind(PacketHeaderFmt, |hdr: PacketHeaderSpec| choice_packet_body_fmt(hdr)),
                mapper: (
                    |parsed: ChoicePacketInner| -> ChoicePacketSpec
                        {
                            let (hdr, payload) = parsed;
                            ChoicePacketSpec { hdr, payload }
                        },
                    |value: ChoicePacketSpec| -> ChoicePacketInner
                        {
                            let ChoicePacketSpec { hdr, payload } = value;
                            (hdr, payload)
                        },
                ),
            },
        )
    }
}

// ============================================================
// Executable implementations
// ============================================================
impl<'i> Parser<&'i [u8]> for VersionIhlFmt {
    type PT = VersionIhl;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, raw) = U8.parse(ibuf)?;
        let (version, ihl) = unpack_version_ihl(raw);
        let final_v = VersionIhl { version, ihl };
        assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
        Ok((n, final_v))
    }
}

impl Serializer<VersionIhl> for VersionIhlFmt {
    fn serialize(&self, v: &VersionIhl, obuf: &mut Vec<u8>) {
        let packed = pack_version_ihl(v.version, v.ihl);
        U8.serialize(&packed, obuf);
    }
}

impl Prepare<VersionIhl> for VersionIhlFmt {
    fn prepare(&self, v: &VersionIhl) -> Result<usize, PreSerializeError> {
        if !version_ihl_bounds(v.version, v.ihl) {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        let res = U8.prepare(&pack_version_ihl(v.version, v.ihl));
        if res.is_ok() {
            assert(self.consistent(v.deep_view()));
        }
        res
    }
}

impl<'i> Parser<&'i [u8]> for CrossByteSpanFmt {
    type PT = CrossByteSpan;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, raw) = U16Be.parse(ibuf)?;
        let (prefix, span, suffix) = unpack_cross_byte_span(raw);
        let final_v = CrossByteSpan { prefix, span, suffix };
        assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
        Ok((n, final_v))
    }
}

impl Serializer<CrossByteSpan> for CrossByteSpanFmt {
    fn serialize(&self, v: &CrossByteSpan, obuf: &mut Vec<u8>) {
        let packed = pack_cross_byte_span(v.prefix, v.span, v.suffix);
        U16Be.serialize(&packed, obuf);
    }
}

impl Prepare<CrossByteSpan> for CrossByteSpanFmt {
    fn prepare(&self, v: &CrossByteSpan) -> Result<usize, PreSerializeError> {
        if !cross_byte_span_bounds(v.prefix, v.span, v.suffix) {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        let res = U16Be.prepare(&pack_cross_byte_span(v.prefix, v.span, v.suffix));
        if res.is_ok() {
            assert(self.consistent(v.deep_view()));
        }
        res
    }
}

impl<'i> Parser<&'i [u8]> for PacketHeaderFmt {
    type PT = PacketHeader;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, raw) = U16Be.parse(ibuf)?;
        let (kind_bits, count, len) = unpack_packet_header(raw);
        if !(count >= 1u8) {
            return Err(ParseError::predicate_failed());
        }
        let final_v = PacketHeader { kind: payload_kind_from_bits(kind_bits), count, len };
        assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
        Ok((n, final_v))
    }
}

impl Serializer<PacketHeader> for PacketHeaderFmt {
    fn serialize(&self, v: &PacketHeader, obuf: &mut Vec<u8>) {
        let packed = pack_packet_header(payload_kind_to_bits(v.kind), v.count, v.len);
        U16Be.serialize(&packed, obuf);
    }
}

impl Prepare<PacketHeader> for PacketHeaderFmt {
    fn prepare(&self, v: &PacketHeader) -> Result<usize, PreSerializeError> {
        if !packet_header_bounds(payload_kind_to_bits(v.kind), v.count, v.len) {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        if !payload_kind_wf(v.kind) {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        if !(v.count >= 1u8) {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        let res = U16Be.prepare(&pack_packet_header(payload_kind_to_bits(v.kind), v.count, v.len));
        if res.is_ok() {
            assert(self.consistent(v.deep_view()));
        }
        res
    }
}

impl<'i> Parser<&'i [u8]> for ChoicePacketFmt {
    type PT = ChoicePacket<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let rest = *ibuf;
        let (n1, hdr) = PacketHeaderFmt.parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, payload) = match hdr.kind {
            PayloadKind::Raw => {
                let (n, bytes) = Varied(hdr.len).parse(&rest)?;
                (n, ChoicePayload::Raw(bytes))
            },
            PayloadKind::Words => {
                let (n, words) = RepeatN(hdr.count, U16Be).parse(&rest)?;
                (n, ChoicePayload::Words(words))
            },
            PayloadKind::Tiny => {
                let (n, x) = U8.parse(&rest)?;
                (n, ChoicePayload::Tiny(x))
            },
            PayloadKind::Unknown(_) => {
                let (n, bytes) = Varied(hdr.len).parse(&rest)?;
                (n, ChoicePayload::Default(bytes))
            },
        };
        let _ibuf_len = (*ibuf).len();
        assert(n1 <= ibuf@.len());
        assert(n2 <= ibuf@.len() - n1);
        let total_n = n1 + n2;
        let final_v = ChoicePacket { hdr, payload };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Serializer<ChoicePacket<'i>> for ChoicePacketFmt {
    fn serialize(&self, v: &ChoicePacket<'i>, obuf: &mut Vec<u8>) {
        let ChoicePacket { hdr, payload } = v;
        PacketHeaderFmt.serialize(hdr, obuf);
        match payload {
            ChoicePayload::Raw(bytes) => Varied(hdr.len).serialize(bytes, obuf),
            ChoicePayload::Words(words) => RepeatN(hdr.count, U16Be).serialize(
                words.as_slice(),
                obuf,
            ),
            ChoicePayload::Tiny(x) => U8.serialize(x, obuf),
            ChoicePayload::Default(bytes) => Varied(hdr.len).serialize(bytes, obuf),
        }
    }
}

impl<'i> Prepare<ChoicePacket<'i>> for ChoicePacketFmt {
    fn prepare(&self, v: &ChoicePacket<'i>) -> Result<usize, PreSerializeError> {
        let ChoicePacket { hdr, payload } = v;
        let l1 = PacketHeaderFmt.prepare(hdr)?;
        let l2 = match payload {
            ChoicePayload::Raw(bytes) => {
                if !matches!(hdr.kind, PayloadKind::Raw) {
                    return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidChoice));
                }
                Varied(hdr.len).prepare(bytes)?
            },
            ChoicePayload::Words(words) => {
                if !matches!(hdr.kind, PayloadKind::Words) {
                    return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidChoice));
                }
                RepeatN(hdr.count, U16Be).prepare(words.as_slice())?
            },
            ChoicePayload::Tiny(x) => {
                if !matches!(hdr.kind, PayloadKind::Tiny) {
                    return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidChoice));
                }
                U8.prepare(x)?
            },
            ChoicePayload::Default(bytes) => {
                if !matches!(hdr.kind, PayloadKind::Unknown(_)) {
                    return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidChoice));
                }
                Varied(hdr.len).prepare(bytes)?
            },
        };
        let res = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge);
        if res.is_ok() {
            assert(self.consistent(v.deep_view()));
        }
        res
    }
}

} // verus!
// ============================================================
// Runtime tests
// ============================================================
#[test]
fn exec_version_ihl_roundtrip() {
    let fmt = VersionIhlFmt;
    let input = [0x45u8];
    let (n, parsed) = fmt.parse(&&input[..]).unwrap();
    assert_eq!(n, 1);
    assert_eq!(parsed, VersionIhl { version: 4, ihl: 5 });

    let mut out = Vec::new();
    fmt.serialize(&parsed, &mut out);
    assert_eq!(out, input);
    assert_eq!(fmt.prepare(&parsed).unwrap(), input.len());
}

#[test]
fn exec_cross_byte_span_roundtrip() {
    let fmt = CrossByteSpanFmt;
    let value = CrossByteSpan {
        prefix: 5,
        span: 511,
        suffix: 3,
    };
    let mut out = Vec::new();
    fmt.serialize(&value, &mut out);
    let (n, parsed) = fmt.parse(&&out[..]).unwrap();
    assert_eq!(n, 2);
    assert_eq!(parsed, value);
    assert_eq!(fmt.prepare(&value).unwrap(), 2);
}

#[test]
fn exec_choice_packet_roundtrip() {
    let fmt = ChoicePacketFmt;
    let raw = ChoicePacket {
        hdr: PacketHeader {
            kind: PayloadKind::Raw,
            count: 1,
            len: 3,
        },
        payload: ChoicePayload::Raw(&[0x10u8, 0x20u8, 0x30u8]),
    };
    let mut out = Vec::new();
    fmt.serialize(&raw, &mut out);
    let (n, parsed) = fmt.parse(&&out[..]).unwrap();
    assert_eq!(n, out.len());
    assert_eq!(parsed, raw);
    assert_eq!(fmt.prepare(&raw).unwrap(), out.len());
}

#[cfg(feature = "std")]
#[derive(Clone)]
pub enum ChoicePayloadOwned {
    Raw(Vec<u8>),
    Words(Vec<u16>),
    Tiny(u8),
    Default(Vec<u8>),
}

#[cfg(feature = "std")]
#[derive(Clone)]
pub struct ChoicePacketOwned {
    pub hdr: PacketHeader,
    pub payload: ChoicePayloadOwned,
}

#[cfg(feature = "std")]
impl ChoicePacketOwned {
    pub fn as_borrowed(&self) -> ChoicePacket<'_> {
        let payload = match &self.payload {
            ChoicePayloadOwned::Raw(bytes) => ChoicePayload::Raw(bytes.as_slice()),
            ChoicePayloadOwned::Words(words) => ChoicePayload::Words(words.clone()),
            ChoicePayloadOwned::Tiny(x) => ChoicePayload::Tiny(*x),
            ChoicePayloadOwned::Default(bytes) => ChoicePayload::Default(bytes.as_slice()),
        };
        ChoicePacket {
            hdr: self.hdr,
            payload,
        }
    }
}

#[cfg(feature = "std")]
pub fn benchmark_choice_packets() -> Vec<ChoicePacketOwned> {
    let mut out = Vec::new();
    for i in 1..=64u8 {
        out.push(ChoicePacketOwned {
            hdr: PacketHeader {
                kind: PayloadKind::Raw,
                count: 1,
                len: i % 8 + 1,
            },
            payload: ChoicePayloadOwned::Raw(vec![i; (i % 8 + 1) as usize]),
        });
        let count = (i % 5) + 1;
        out.push(ChoicePacketOwned {
            hdr: PacketHeader {
                kind: PayloadKind::Words,
                count,
                len: 0,
            },
            payload: ChoicePayloadOwned::Words(
                (0..count as usize)
                    .map(|j| ((i as u16) << 8) | (j as u16))
                    .collect(),
            ),
        });
        out.push(ChoicePacketOwned {
            hdr: PacketHeader {
                kind: PayloadKind::Tiny,
                count: 1,
                len: 0,
            },
            payload: ChoicePayloadOwned::Tiny(i),
        });
        let dlen = (i % 6) + 1;
        out.push(ChoicePacketOwned {
            hdr: PacketHeader {
                kind: PayloadKind::Unknown(7),
                count: 1,
                len: dlen,
            },
            payload: ChoicePayloadOwned::Default(vec![0xA0u8.wrapping_add(i); dlen as usize]),
        });
    }
    out
}

#[cfg(feature = "std")]
pub fn handrolled_parse_packet_header(ibuf: &[u8]) -> Option<(usize, PacketHeader)> {
    if ibuf.len() < 2 {
        return None;
    }
    let raw = u16::from_be_bytes([ibuf[0], ibuf[1]]);
    let (kind_bits, count, len) = unpack_packet_header(raw);
    let hdr = PacketHeader {
        kind: payload_kind_from_bits(kind_bits),
        count,
        len,
    };
    if hdr.count < 1 {
        return None;
    }
    Some((2, hdr))
}

#[cfg(feature = "std")]
pub fn handrolled_serialize_packet_header(v: &PacketHeader, obuf: &mut Vec<u8>) -> bool {
    if v.count < 1 || v.count >= 32 || !payload_kind_wf(v.kind) {
        return false;
    }
    let raw = pack_packet_header(payload_kind_to_bits(v.kind), v.count, v.len);
    obuf.extend_from_slice(&raw.to_be_bytes());
    true
}

#[cfg(feature = "std")]
pub fn handrolled_parse_choice_packet<'i>(ibuf: &'i [u8]) -> Option<(usize, ChoicePacket<'i>)> {
    let (n1, hdr) = handrolled_parse_packet_header(ibuf)?;
    let rest = &ibuf[n1..];
    match hdr.kind {
        PayloadKind::Raw => {
            let len = hdr.len as usize;
            if rest.len() < len {
                return None;
            }
            Some((
                n1 + len,
                ChoicePacket {
                    hdr,
                    payload: ChoicePayload::Raw(&rest[..len]),
                },
            ))
        }
        PayloadKind::Words => {
            let count = hdr.count as usize;
            if rest.len() < count * 2 {
                return None;
            }
            let mut words = Vec::with_capacity(count);
            for idx in 0..count {
                let off = idx * 2;
                words.push(u16::from_be_bytes([rest[off], rest[off + 1]]));
            }
            Some((
                n1 + count * 2,
                ChoicePacket {
                    hdr,
                    payload: ChoicePayload::Words(words),
                },
            ))
        }
        PayloadKind::Tiny => {
            if rest.is_empty() {
                return None;
            }
            Some((
                n1 + 1,
                ChoicePacket {
                    hdr,
                    payload: ChoicePayload::Tiny(rest[0]),
                },
            ))
        }
        PayloadKind::Unknown(_) => {
            let len = hdr.len as usize;
            if rest.len() < len {
                return None;
            }
            Some((
                n1 + len,
                ChoicePacket {
                    hdr,
                    payload: ChoicePayload::Default(&rest[..len]),
                },
            ))
        }
    }
}

#[cfg(feature = "std")]
pub fn handrolled_serialize_choice_packet(v: &ChoicePacket<'_>, obuf: &mut Vec<u8>) -> bool {
    if !handrolled_serialize_packet_header(&v.hdr, obuf) {
        return false;
    }
    match &v.payload {
        ChoicePayload::Raw(bytes) | ChoicePayload::Default(bytes) => {
            if bytes.len() != v.hdr.len as usize {
                return false;
            }
            obuf.extend_from_slice(bytes);
        }
        ChoicePayload::Words(words) => {
            if words.len() != v.hdr.count as usize {
                return false;
            }
            for word in words {
                obuf.extend_from_slice(&word.to_be_bytes());
            }
        }
        ChoicePayload::Tiny(x) => obuf.push(*x),
    }
    true
}

macro_rules! impl_named_spec_traits {
    ($fmt:ident, $spec:ty) => {
        verus! {
            impl SpecParser for $fmt {
                type PVal = $spec;

                open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
                    $fmt::spec_inner().spec_parse(ibuf)
                }
            }

            impl Consistency for $fmt {
                type Val = $spec;

                open spec fn consistent(&self, v: Self::Val) -> bool {
                    $fmt::spec_inner().consistent(v)
                }
            }

            impl SpecSerializerDps for $fmt {
                type SValue = $spec;

                open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
                    $fmt::spec_inner().spec_serialize_dps(v, obuf)
                }
            }

            impl SpecSerializer for $fmt {
                type SVal = $spec;

                open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
                    $fmt::spec_inner().spec_serialize(v)
                }
            }

            impl SpecByteLen for $fmt {
                type T = $spec;

                open spec fn byte_len(&self, v: Self::T) -> nat {
                    $fmt::spec_inner().byte_len(v)
                }
            }

            impl SafeParser for $fmt {
                proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
                    reveal(<$fmt as SpecParser>::spec_parse);
                    $fmt::spec_inner().lemma_parse_safe(ibuf);
                }
            }

            impl SoundParser for $fmt {
                proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
                    reveal(<$fmt as SpecParser>::spec_parse);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                    $fmt::spec_inner().lemma_parse_sound_consumption(ibuf);
                }

                proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                    reveal(<$fmt as SpecParser>::spec_parse);
                    reveal(<$fmt as Consistency>::consistent);
                    $fmt::spec_inner().lemma_parse_sound_value(ibuf);
                }
            }

            impl NonTailFmt for $fmt {
                proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
                    reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                    $fmt::spec_inner().lemma_serialize_dps_prepend(v, obuf);
                }

                proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
                    reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                    $fmt::spec_inner().lemma_serialize_dps_len(v, obuf);
                }
            }

            impl GoodSerializer for $fmt {
                proof fn lemma_serialize_len(&self, v: Self::SVal) {
                    reveal(<$fmt as SpecSerializer>::spec_serialize);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                    $fmt::spec_inner().lemma_serialize_len(v);
                }
            }
        }
    };
}

impl_named_spec_traits!(VersionIhlFmt, VersionIhlSpec);
impl_named_spec_traits!(CrossByteSpanFmt, CrossByteSpanSpec);
impl_named_spec_traits!(PacketHeaderFmt, PacketHeaderSpec);
impl_named_spec_traits!(ChoicePacketFmt, ChoicePacketSpec);
