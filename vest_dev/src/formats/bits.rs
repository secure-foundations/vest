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
//! bytes_packet = {
//!     @hdr: packet_header,
//!     body: [u8; @hdr.len],
//! }
//!
//! words_packet = {
//!     @hdr: packet_header,
//!     words: [u16; @hdr.count],
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
//! This module is intentionally written in the style of generated `vest2/test/src/*.rs` code:
//! explicit spec combinators, proof lemmas, and manual exec `Parser` / `Serializer` / `Prepare`
//! implementations over ordinary Rust carrier types.

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
    proof fn self_view(&self) {}

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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct BytesPacket<'i> {
    pub hdr: PacketHeader,
    pub body: &'i [u8],
}

#[verifier::ext_equal]
pub struct BytesPacketSpec {
    pub hdr: PacketHeaderSpec,
    pub body: Seq<u8>,
}

pub type BytesPacketInner = (PacketHeaderSpec, Seq<u8>);

impl<'i> DeepView for BytesPacket<'i> {
    type V = BytesPacketSpec;

    open spec fn deep_view(&self) -> Self::V {
        BytesPacketSpec { hdr: self.hdr.deep_view(), body: self.body.deep_view() }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct WordsPacket {
    pub hdr: PacketHeader,
    pub words: Vec<u16>,
}

#[verifier::ext_equal]
pub struct WordsPacketSpec {
    pub hdr: PacketHeaderSpec,
    pub words: Seq<u16>,
}

pub type WordsPacketInner = (PacketHeaderSpec, Seq<u16>);

impl DeepView for WordsPacket {
    type V = WordsPacketSpec;

    open spec fn deep_view(&self) -> Self::V {
        WordsPacketSpec { hdr: self.hdr.deep_view(), words: self.words.deep_view() }
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
pub const VERSION_MASK: u8 = 0b00001111u8;  // 4 bits for version
pub const IHL_MASK: u8 = 0b00001111u8;  // 4 bits for IHL
pub const VERSION_SHIFT: u8 = 4u8;

pub const PREFIX_MASK_U16: u16 = 0b0000000000000111u16;  // 3 bits for prefix
pub const SPAN_MASK: u16 = 0b0000001111111111u16;  // 10 bits for span
pub const SUFFIX_MASK: u16 = 0b0000000000000111u16;  // 3 bits for suffix
pub const PREFIX_SHIFT: u16 = 13u16;
pub const SPAN_SHIFT: u16 = 3u16;

pub const KIND_MASK: u16 = 0b0000000000000111u16;  // 3 bits for kind
pub const COUNT_MASK: u16 = 0b0000000000011111u16;  // 5 bits for count
pub const LEN_MASK: u16 = 0b0000000011111111u16;  // 8 bits for length
pub const KIND_SHIFT: u16 = 13u16;
pub const COUNT_SHIFT: u16 = 8u16;

pub const VERSION_MAX: u8 = 0b00010000u8;  // 2^4
pub const IHL_MAX: u8 = 0b00010000u8;  // 2^4
pub const PREFIX_MAX: u8 = 0b00001000u8;  // 2^3
pub const SPAN_MAX: u16 = 0b10000000000u16;  // 2^10
pub const SUFFIX_MAX: u8 = 0b00001000u8;  // 2^3
pub const KIND_MAX: u8 = 0b00001000u8;  // 2^3
pub const COUNT_MAX: u8 = 0b00100000u8;  // 2^5

pub open spec fn payload_kind_wf(kind: PayloadKindSpec) -> bool {
    match kind {
        PayloadKind::Raw | PayloadKind::Words | PayloadKind::Tiny => true,
        PayloadKind::Unknown(x) => x < 8 && x != 0 && x != 1 && x != 2,
    }
}

pub fn payload_kind_wf_exec(kind: PayloadKind) -> (res: bool)
    ensures
        res == payload_kind_wf(kind),
{
    match kind {
        PayloadKind::Raw | PayloadKind::Words | PayloadKind::Tiny => true,
        PayloadKind::Unknown(x) => x < 8 && x != 0 && x != 1 && x != 2,
    }
}

pub open spec fn payload_kind_from_bits(bits: u8) -> PayloadKindSpec {
    match bits {
        0 => PayloadKind::Raw,
        1 => PayloadKind::Words,
        2 => PayloadKind::Tiny,
        _ => PayloadKind::Unknown(bits),
    }
}

pub open spec fn payload_kind_to_bits(kind: PayloadKindSpec) -> u8 {
    match kind {
        PayloadKind::Raw => 0,
        PayloadKind::Words => 1,
        PayloadKind::Tiny => 2,
        PayloadKind::Unknown(x) => x,
    }
}

pub proof fn lemma_payload_kind_roundtrip(bits: u8)
    ensures
        payload_kind_to_bits(payload_kind_from_bits(bits)) == bits,
{
}

pub proof fn lemma_payload_kind_value_roundtrip(kind: PayloadKindSpec)
    requires
        payload_kind_wf(kind),
    ensures
        payload_kind_from_bits(payload_kind_to_bits(kind)) == kind,
{
}

pub open spec fn version_ihl_from_raw(raw: u8) -> VersionIhlSpec {
    VersionIhlSpec { version: ((raw >> VERSION_SHIFT) & VERSION_MASK), ihl: (raw & IHL_MASK) }
}

pub open spec fn version_ihl_to_raw_inner(version: u8, ihl: u8) -> u8 {
    ((version & VERSION_MASK) << VERSION_SHIFT) | (ihl & IHL_MASK)
}

pub open spec fn version_ihl_to_raw(v: VersionIhlSpec) -> u8 {
    version_ihl_to_raw_inner(v.version, v.ihl)
}

pub open spec fn version_ihl_wf(v: VersionIhlSpec) -> bool {
    v.version < VERSION_MAX && v.ihl < IHL_MAX
}

pub fn version_ihl_wf_exec(v: &VersionIhl) -> (res: bool)
    ensures
        res == version_ihl_wf(v.deep_view()),
{
    v.version < VERSION_MAX && v.ihl < IHL_MAX
}

pub proof fn lemma_version_ihl_bits_roundtrip(raw: u8) by (bit_vector)
    ensures
        version_ihl_to_raw(version_ihl_from_raw(raw)) == raw,
{
}

pub proof fn lemma_version_ihl_value_roundtrip_inner(version: u8, ihl: u8) by (bit_vector)
    requires
        version_ihl_wf(VersionIhlSpec { version, ihl }),
    ensures
        version_ihl_from_raw(version_ihl_to_raw_inner(version, ihl)).version == version,
        version_ihl_from_raw(version_ihl_to_raw_inner(version, ihl)).ihl == ihl,
{
}

pub proof fn lemma_version_ihl_value_roundtrip(v: VersionIhlSpec)
    requires
        version_ihl_wf(v),
    ensures
        version_ihl_from_raw(version_ihl_to_raw(v)) == v,
{
    lemma_version_ihl_value_roundtrip_inner(v.version, v.ihl);
}

pub open spec fn cross_byte_span_from_raw(raw: u16) -> CrossByteSpanSpec {
    CrossByteSpanSpec {
        prefix: (((raw >> PREFIX_SHIFT) & PREFIX_MASK_U16) as u8),
        span: (((raw >> SPAN_SHIFT) & SPAN_MASK) as u16),
        suffix: ((raw & SUFFIX_MASK) as u8),
    }
}

pub open spec fn cross_byte_span_to_raw_inner(prefix: u8, span: u16, suffix: u8) -> u16 {
    (((prefix as u16) & PREFIX_MASK_U16) << PREFIX_SHIFT)
        | (((span as u16) & SPAN_MASK) << SPAN_SHIFT)
        | ((suffix as u16) & SUFFIX_MASK)
}

pub open spec fn cross_byte_span_to_raw(v: CrossByteSpanSpec) -> u16 {
    cross_byte_span_to_raw_inner(v.prefix, v.span, v.suffix)
}

pub open spec fn cross_byte_span_wf(v: CrossByteSpanSpec) -> bool {
    v.prefix < PREFIX_MAX && v.span < SPAN_MAX && v.suffix < SUFFIX_MAX
}

pub fn cross_byte_span_wf_exec(v: &CrossByteSpan) -> (res: bool)
    ensures
        res == cross_byte_span_wf(v.deep_view()),
{
    v.prefix < PREFIX_MAX && v.span < SPAN_MAX && v.suffix < SUFFIX_MAX
}

pub proof fn lemma_cross_byte_span_bits_roundtrip(raw: u16) by (bit_vector)
    ensures
        cross_byte_span_to_raw(cross_byte_span_from_raw(raw)) == raw,
{
}

pub proof fn lemma_cross_byte_span_value_roundtrip_inner(prefix: u8, span: u16, suffix: u8) by (bit_vector)
    requires
        cross_byte_span_wf(CrossByteSpanSpec { prefix, span, suffix }),
    ensures
        cross_byte_span_from_raw(cross_byte_span_to_raw_inner(prefix, span, suffix)).prefix == prefix,
        cross_byte_span_from_raw(cross_byte_span_to_raw_inner(prefix, span, suffix)).span == span,
        cross_byte_span_from_raw(cross_byte_span_to_raw_inner(prefix, span, suffix)).suffix == suffix,
{
}

pub proof fn lemma_cross_byte_span_value_roundtrip(v: CrossByteSpanSpec)
    requires
        cross_byte_span_wf(v),
    ensures
        cross_byte_span_from_raw(cross_byte_span_to_raw(v)) == v,
{
    lemma_cross_byte_span_value_roundtrip_inner(v.prefix, v.span, v.suffix);
}


pub open spec fn packet_header_from_raw(raw: u16) -> PacketHeaderSpec {
    PacketHeaderSpec {
        kind: payload_kind_from_bits(((raw >> KIND_SHIFT) & KIND_MASK) as u8),
        count: (((raw >> COUNT_SHIFT) & COUNT_MASK) as u8),
        len: ((raw & LEN_MASK) as u8),
    }
}

pub open spec fn packet_header_to_raw_inner(kind: PayloadKindSpec, count: u8, len: u8) -> u16 {
    (((payload_kind_to_bits(kind) as u16) & KIND_MASK) << KIND_SHIFT)
        | (((count as u16) & COUNT_MASK) << COUNT_SHIFT)
        | ((len as u16) & LEN_MASK)
}

pub open spec fn packet_header_to_raw(v: PacketHeaderSpec) -> u16 {
    packet_header_to_raw_inner(v.kind, v.count, v.len)
}

pub open spec fn packet_header_wf(v: PacketHeaderSpec) -> bool {
    &&& payload_kind_wf(v.kind)
    &&& v.count < COUNT_MAX
}

pub open spec fn packet_header_refined(v: PacketHeaderSpec) -> bool {
    &&& packet_header_wf(v)
    &&& v.count >= 1u8
}

pub fn packet_header_refined_exec(v: &PacketHeader) -> (res: bool)
    ensures
        res == packet_header_refined(v.deep_view()),
{
    payload_kind_wf_exec(v.kind) && v.count < COUNT_MAX && v.count >= 1u8
}

pub proof fn lemma_packet_header_bits_roundtrip(raw: u16)
    ensures
        packet_header_to_raw(packet_header_from_raw(raw)) == raw,
{
    let kind_bits = ((raw >> KIND_SHIFT) & KIND_MASK) as u8;
    lemma_payload_kind_roundtrip(kind_bits);
    let pk_bits = payload_kind_to_bits(payload_kind_from_bits(kind_bits));
    assert(pk_bits == kind_bits);
    assert(
        ((((pk_bits as u16) & KIND_MASK) << KIND_SHIFT)
            | (((((raw >> COUNT_SHIFT) & COUNT_MASK) as u8 as u16) & COUNT_MASK) << COUNT_SHIFT)
            | ((((raw & LEN_MASK) as u8 as u16) & LEN_MASK))) == raw
    ) by (bit_vector)
        requires pk_bits == (((raw >> KIND_SHIFT) & KIND_MASK) as u8);
}

pub proof fn lemma_packet_header_value_roundtrip(v: PacketHeaderSpec)
    requires
        packet_header_wf(v),
    ensures
        packet_header_from_raw(packet_header_to_raw(v)) == v,
{
    lemma_payload_kind_value_roundtrip(v.kind);
    let count = v.count;
    assert(count < COUNT_MAX);
    let kind_bits = payload_kind_to_bits(v.kind);
    assert(payload_kind_to_bits(v.kind) < KIND_MAX) by {
        let k = v.kind;
        match k {
            PayloadKind::Raw => assert(payload_kind_to_bits(k) == 0u8),
            PayloadKind::Words => assert(payload_kind_to_bits(k) == 1u8),
            PayloadKind::Tiny => assert(payload_kind_to_bits(k) == 2u8),
            PayloadKind::Unknown(x) => assert(payload_kind_to_bits(k) == x && x < KIND_MAX),
        }
    };
    assert(kind_bits < KIND_MAX);
    let raw = packet_header_to_raw(v);
    assert(raw == (((kind_bits as u16) & KIND_MASK) << KIND_SHIFT)
        | (((count as u16) & COUNT_MASK) << COUNT_SHIFT)
        | ((v.len as u16) & LEN_MASK));
    let v_len = v.len;
    let v2 = packet_header_from_raw(raw);
    let v2_count = v2.count;
    let v2_len = v2.len;
    assert(v2.count == ((raw >> COUNT_SHIFT) & COUNT_MASK) as u8);
    assert(v2.len == (raw & LEN_MASK) as u8);
    let kb: u16 = kind_bits as u16;
    assert(kb < KIND_MAX as u16) by (bit_vector) requires kind_bits < KIND_MAX, kb == kind_bits as u16;
    let raw_kind_bits = ((raw >> KIND_SHIFT) & KIND_MASK) as u8;
    assert(v2.kind == payload_kind_from_bits(raw_kind_bits));
    assert((raw >> KIND_SHIFT) & KIND_MASK == kb) by (bit_vector)
        requires kb < KIND_MAX as u16,
                 raw == ((kb & KIND_MASK) << KIND_SHIFT)
                     | (((count as u16) & COUNT_MASK) << COUNT_SHIFT)
                     | ((v_len as u16) & LEN_MASK);
    assert(kb as u8 == kind_bits);
    assert(raw_kind_bits == kind_bits);
    assert(v2.kind == v.kind) by {
        assert(payload_kind_from_bits(kind_bits) == v.kind);
    };
    assert(v2_count == count) by (bit_vector)
        requires count < COUNT_MAX,
                 raw == (((kind_bits as u16) & KIND_MASK) << KIND_SHIFT)
                     | (((count as u16) & COUNT_MASK) << COUNT_SHIFT)
                     | ((v_len as u16) & LEN_MASK),
                 v2_count == ((raw >> COUNT_SHIFT) & COUNT_MASK) as u8;
    assert(v2_len == v_len) by (bit_vector)
        requires raw == (((kind_bits as u16) & KIND_MASK) << KIND_SHIFT)
                     | (((count as u16) & COUNT_MASK) << COUNT_SHIFT)
                     | ((v_len as u16) & LEN_MASK),
                 v2_len == (raw & LEN_MASK) as u8;
}

#[inline(always)]
pub fn version_ihl_from_raw_exec(raw: u8) -> (out: VersionIhl)
    ensures
        out.deep_view() == version_ihl_from_raw(raw),
{
    VersionIhl { version: (raw >> VERSION_SHIFT) & VERSION_MASK, ihl: raw & IHL_MASK }
}

#[inline(always)]
pub fn version_ihl_to_raw_exec(v: &VersionIhl) -> (raw: u8)
    ensures
        raw == version_ihl_to_raw(v.deep_view()),
{
    ((v.version & VERSION_MASK) << VERSION_SHIFT) | (v.ihl & IHL_MASK)
}

#[inline(always)]
pub fn cross_byte_span_from_raw_exec(raw: u16) -> (out: CrossByteSpan)
    ensures
        out.deep_view() == cross_byte_span_from_raw(raw),
{
    CrossByteSpan {
        prefix: ((raw >> PREFIX_SHIFT) & PREFIX_MASK_U16) as u8,
        span: ((raw >> SPAN_SHIFT) & SPAN_MASK) as u16,
        suffix: (raw & SUFFIX_MASK) as u8,
    }
}

#[inline(always)]
pub fn cross_byte_span_to_raw_exec(v: &CrossByteSpan) -> (raw: u16)
    ensures
        raw == cross_byte_span_to_raw(v.deep_view()),
{
    (((v.prefix as u16) & PREFIX_MASK_U16) << PREFIX_SHIFT)
        | (((v.span as u16) & SPAN_MASK) << SPAN_SHIFT)
        | ((v.suffix as u16) & SUFFIX_MASK)
}

#[inline(always)]
pub fn packet_header_from_raw_exec(raw: u16) -> (out: PacketHeader)
    ensures
        out.deep_view() == packet_header_from_raw(raw),
{
    let kind_bits = ((raw >> KIND_SHIFT) & KIND_MASK) as u8;
    let kind = match kind_bits {
        0 => PayloadKind::Raw,
        1 => PayloadKind::Words,
        2 => PayloadKind::Tiny,
        other => PayloadKind::Unknown(other),
    };
    PacketHeader { kind, count: ((raw >> COUNT_SHIFT) & COUNT_MASK) as u8, len: (raw & LEN_MASK) as u8 }
}

#[inline(always)]
pub fn packet_header_to_raw_exec(v: &PacketHeader) -> (raw: u16)
    ensures
        raw == packet_header_to_raw(v.deep_view()),
{
    let kind_bits: u8 = match v.kind {
        PayloadKind::Raw => 0,
        PayloadKind::Words => 1,
        PayloadKind::Tiny => 2,
        PayloadKind::Unknown(x) => x,
    };
    (((kind_bits as u16) & KIND_MASK) << KIND_SHIFT)
        | (((v.count as u16) & COUNT_MASK) << COUNT_SHIFT)
        | ((v.len as u16) & LEN_MASK)
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
        version_ihl_wf(o)
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        version_ihl_from_raw(i)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        version_ihl_to_raw(o)
    }
}

impl LossyMapper for VersionIhlMapper {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        lemma_version_ihl_value_roundtrip(o);
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {}
}

impl LosslessMapper for VersionIhlMapper {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        lemma_version_ihl_bits_roundtrip(i);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        assert(((i >> VERSION_SHIFT) & VERSION_MASK) < VERSION_MAX) by (bit_vector);
        assert((i & IHL_MASK) < IHL_MAX) by (bit_vector);
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
        cross_byte_span_wf(o)
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        cross_byte_span_from_raw(i)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        cross_byte_span_to_raw(o)
    }
}

impl LossyMapper for CrossByteSpanMapper {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        lemma_cross_byte_span_value_roundtrip(o);
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {}
}

impl LosslessMapper for CrossByteSpanMapper {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        lemma_cross_byte_span_bits_roundtrip(i);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        assert(((i >> PREFIX_SHIFT) & PREFIX_MASK_U16) < PREFIX_MAX as u16) by (bit_vector);
        assert(((i >> SPAN_SHIFT) & SPAN_MASK) < SPAN_MAX) by (bit_vector);
        assert((i & SUFFIX_MASK) < SUFFIX_MAX as u16) by (bit_vector);
        assert((((i >> PREFIX_SHIFT) & PREFIX_MASK_U16) as u8) < PREFIX_MAX) by (bit_vector);
        assert(((i & SUFFIX_MASK) as u8) < SUFFIX_MAX) by (bit_vector);
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

pub struct PacketHeaderMapper;

impl SpecMapper for PacketHeaderMapper {
    type In = PacketHeaderInner;
    type Out = PacketHeaderSpec;

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        packet_header_wf(o)
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        packet_header_from_raw(i)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        packet_header_to_raw(o)
    }
}

impl LossyMapper for PacketHeaderMapper {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        lemma_packet_header_value_roundtrip(o);
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        assert(packet_header_wf(o));
    }
}

impl LosslessMapper for PacketHeaderMapper {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        lemma_packet_header_bits_roundtrip(i);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        assert((((i >> KIND_SHIFT) & KIND_MASK) as u8) < KIND_MAX) by (bit_vector);
        assert((((i >> COUNT_SHIFT) & COUNT_MASK) as u8) < COUNT_MAX) by (bit_vector);
    }
}

pub type PacketHeaderRawFmt = Mapped<U16Be, PacketHeaderMapper>;
pub type PacketHeaderFmtSpec = Named<Refined<PacketHeaderRawFmt, PredFnSpec<PacketHeaderSpec>>>;

impl PacketHeaderFmt {
    pub open spec fn spec_inner() -> PacketHeaderFmtSpec {
        Named(
            "packet_header",
            Refined(
                Mapped { inner: U16Be, mapper: PacketHeaderMapper },
                |hdr: PacketHeaderSpec| packet_header_refined(hdr),
            ),
        )
    }
}

#[derive(Clone, Copy)]
pub struct BytesPacketFmt;

pub type BytesPacketFmtSpec = Named<Mapped<
    Bind<PacketHeaderFmt, spec_fn(PacketHeaderSpec) -> Varied<u8>>,
    FnSpecMapper<BytesPacketInner, BytesPacketSpec>,
>>;

impl BytesPacketFmt {
    pub open spec fn spec_inner() -> BytesPacketFmtSpec {
        Named(
            "bytes_packet",
            Mapped {
                inner: Bind(PacketHeaderFmt, |hdr: PacketHeaderSpec| Varied(hdr.len)),
                mapper: (
                    |parsed: BytesPacketInner| -> BytesPacketSpec {
                        let (hdr, body) = parsed;
                        BytesPacketSpec { hdr, body }
                    },
                    |value: BytesPacketSpec| -> BytesPacketInner {
                        let BytesPacketSpec { hdr, body } = value;
                        (hdr, body)
                    },
                ),
            },
        )
    }
}

#[derive(Clone, Copy)]
pub struct WordsPacketFmt;

pub type WordsPacketFmtSpec = Named<Mapped<
    Bind<PacketHeaderFmt, spec_fn(PacketHeaderSpec) -> RepeatN<U16Be, u8>>,
    FnSpecMapper<WordsPacketInner, WordsPacketSpec>,
>>;

impl WordsPacketFmt {
    pub open spec fn spec_inner() -> WordsPacketFmtSpec {
        Named(
            "words_packet",
            Mapped {
                inner: Bind(PacketHeaderFmt, |hdr: PacketHeaderSpec| RepeatN(hdr.count, U16Be)),
                mapper: (
                    |parsed: WordsPacketInner| -> WordsPacketSpec {
                        let (hdr, words) = parsed;
                        WordsPacketSpec { hdr, words }
                    },
                    |value: WordsPacketSpec| -> WordsPacketInner {
                        let WordsPacketSpec { hdr, words } = value;
                        (hdr, words)
                    },
                ),
            },
        )
    }
}

pub type ChoicePayloadFmt = Mapped<
    Choice<
        Cond<Varied<u8>>,
        Choice<Cond<RepeatN<U16Be, u8>>, Choice<Cond<U8>, Cond<Varied<u8>>>>,
    >,
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
            |parsed: ChoicePayloadInner| -> ChoicePayloadSpec {
                match parsed {
                    Sum::Inl(bytes) => ChoicePayloadSpec::Raw(bytes),
                    Sum::Inr(Sum::Inl(words)) => ChoicePayloadSpec::Words(words),
                    Sum::Inr(Sum::Inr(Sum::Inl(x))) => ChoicePayloadSpec::Tiny(x),
                    Sum::Inr(Sum::Inr(Sum::Inr(bytes))) => ChoicePayloadSpec::Default(bytes),
                }
            },
            |value: ChoicePayloadSpec| -> ChoicePayloadInner {
                match value {
                    ChoicePayloadSpec::Raw(bytes) => Sum::Inl(bytes),
                    ChoicePayloadSpec::Words(words) => Sum::Inr(Sum::Inl(words)),
                    ChoicePayloadSpec::Tiny(x) => Sum::Inr(Sum::Inr(Sum::Inl(x))),
                    ChoicePayloadSpec::Default(bytes) => Sum::Inr(Sum::Inr(Sum::Inr(bytes))),
                }
            },
        )
    }
}

#[derive(Clone, Copy)]
pub struct ChoicePacketFmt;

pub type ChoicePacketFmtSpec = Named<Mapped<
    Bind<PacketHeaderFmt, spec_fn(PacketHeaderSpec) -> ChoicePayloadFmt>,
    FnSpecMapper<ChoicePacketInner, ChoicePacketSpec>
>>;

impl ChoicePacketFmt {
    pub open spec fn spec_inner() -> ChoicePacketFmtSpec {
        Named(
            "choice_packet",
            Mapped {
                inner: Bind(PacketHeaderFmt, |hdr: PacketHeaderSpec| choice_packet_body_fmt(hdr)),
                mapper: (
                    |parsed: ChoicePacketInner| -> ChoicePacketSpec {
                        let (hdr, payload) = parsed;
                        ChoicePacketSpec { hdr, payload }
                    },
                    |value: ChoicePacketSpec| -> ChoicePacketInner {
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
        let final_v = version_ihl_from_raw_exec(raw);
        assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
        Ok((n, final_v))
    }
}

impl Serializer<VersionIhl> for VersionIhlFmt {
    fn serialize(&self, v: &VersionIhl, obuf: &mut Vec<u8>) {
        let raw = version_ihl_to_raw_exec(v);
        U8.serialize(&raw, obuf);
    }
}

impl Prepare<VersionIhl> for VersionIhlFmt {
    fn prepare(&self, v: &VersionIhl) -> Result<usize, PreSerializeError> {
        if !version_ihl_wf_exec(v) {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        let res = U8.prepare(&version_ihl_to_raw_exec(v));
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
        let final_v = cross_byte_span_from_raw_exec(raw);
        assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
        Ok((n, final_v))
    }
}

impl Serializer<CrossByteSpan> for CrossByteSpanFmt {
    fn serialize(&self, v: &CrossByteSpan, obuf: &mut Vec<u8>) {
        let raw = cross_byte_span_to_raw_exec(v);
        U16Be.serialize(&raw, obuf);
    }
}

impl Prepare<CrossByteSpan> for CrossByteSpanFmt {
    fn prepare(&self, v: &CrossByteSpan) -> Result<usize, PreSerializeError> {
        if !cross_byte_span_wf_exec(v) {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        let res = U16Be.prepare(&cross_byte_span_to_raw_exec(v));
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
        let final_v = packet_header_from_raw_exec(raw);
        if !packet_header_refined_exec(&final_v) {
            return Err(ParseError::predicate_failed());
        }
        assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
        Ok((n, final_v))
    }
}

impl Serializer<PacketHeader> for PacketHeaderFmt {
    fn serialize(&self, v: &PacketHeader, obuf: &mut Vec<u8>) {
        let raw = packet_header_to_raw_exec(v);
        U16Be.serialize(&raw, obuf);
    }
}

impl Prepare<PacketHeader> for PacketHeaderFmt {
    fn prepare(&self, v: &PacketHeader) -> Result<usize, PreSerializeError> {
        if !packet_header_refined_exec(v) {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        let res = U16Be.prepare(&packet_header_to_raw_exec(v));
        if res.is_ok() {
            assert(self.consistent(v.deep_view()));
        }
        res
    }
}

impl<'i> Parser<&'i [u8]> for BytesPacketFmt {
    type PT = BytesPacket<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let rest = *ibuf;
        let (n1, hdr) = PacketHeaderFmt.parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, body) = Varied(hdr.len).parse(&rest)?;
        let total_n = n1 + n2;
        let final_v = BytesPacket { hdr, body };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Serializer<BytesPacket<'i>> for BytesPacketFmt {
    fn serialize(&self, v: &BytesPacket<'i>, obuf: &mut Vec<u8>) {
        let BytesPacket { hdr, body } = v;
        PacketHeaderFmt.serialize(hdr, obuf);
        Varied(hdr.len).serialize(body, obuf);
    }
}

impl<'i> Prepare<BytesPacket<'i>> for BytesPacketFmt {
    fn prepare(&self, v: &BytesPacket<'i>) -> Result<usize, PreSerializeError> {
        let BytesPacket { hdr, body } = v;
        let l1 = PacketHeaderFmt.prepare(hdr)?;
        let l2 = Varied(hdr.len).prepare(body)?;
        l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)
    }
}

impl<'i> Parser<&'i [u8]> for WordsPacketFmt {
    type PT = WordsPacket;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let rest = *ibuf;
        let (n1, hdr) = PacketHeaderFmt.parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, words) = RepeatN(hdr.count, U16Be).parse(&rest)?;
        let _ibuf_len = (*ibuf).len();
        assert(n1 <= ibuf@.len());
        assert(n2 <= ibuf@.len() - n1);
        let total_n = n1 + n2;
        let final_v = WordsPacket { hdr, words };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl Serializer<WordsPacket> for WordsPacketFmt {
    fn serialize(&self, v: &WordsPacket, obuf: &mut Vec<u8>) {
        let WordsPacket { hdr, words } = v;
        PacketHeaderFmt.serialize(hdr, obuf);
        RepeatN(hdr.count, U16Be).serialize(words.as_slice(), obuf);
    }
}

impl Prepare<WordsPacket> for WordsPacketFmt {
    fn prepare(&self, v: &WordsPacket) -> Result<usize, PreSerializeError> {
        let WordsPacket { hdr, words } = v;
        let l1 = PacketHeaderFmt.prepare(hdr)?;
        let l2 = RepeatN(hdr.count, U16Be).prepare(words.as_slice())?;
        l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)
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
            ChoicePayload::Words(words) => RepeatN(hdr.count, U16Be).serialize(words.as_slice(), obuf),
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
    let hdr = packet_header_from_raw_exec(raw);
    if hdr.count < 1 {
        return None;
    }
    Some((2, hdr))
}

#[cfg(feature = "std")]
pub fn handrolled_serialize_packet_header(v: &PacketHeader, obuf: &mut Vec<u8>) -> bool {
    if v.count < 1 || v.count >= 32 || !payload_kind_wf_exec(v.kind) {
        return false;
    }
    let raw = packet_header_to_raw_exec(v);
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
impl_named_spec_traits!(BytesPacketFmt, BytesPacketSpec);
impl_named_spec_traits!(WordsPacketFmt, WordsPacketSpec);
impl_named_spec_traits!(ChoicePacketFmt, ChoicePacketSpec);
