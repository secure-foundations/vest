#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::*;
use vest_lib2::core::exec::input::{InputBuf, InputSlice};
use vest_lib2::core::exec::parser::*;
use vest_lib2::core::exec::serializer::*;
use vest_lib2::core::exec::ParseError;
use vest_lib2::core::exec::{DeepEq, SelfView};
use vest_lib2::core::{proof::*, spec::*};
use vest_lib2::macros::impl_self_view_for;
use vest_lib2::primitives::btcvarint::VarInt;
use vest_lib2::primitives::leb128::ULeb128;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `closed_payload_kind`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum ClosedPayloadKind {
    Raw = 0,
    Words = 1,
    Tiny = 2,
}

pub type ClosedPayloadKindSpec = ClosedPayloadKind;

pub type ClosedPayloadKindInner = u8;

impl DeepView for ClosedPayloadKind {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepEq for ClosedPayloadKind {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for ClosedPayloadKind {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `closed_packet_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct ClosedPacketHeader {
    pub kind: ClosedPayloadKind,
    pub count: u8,
    pub len: u8,
}

pub type ClosedPacketHeaderSpec = ClosedPacketHeader;

pub type ClosedPacketHeaderInner = u16;

impl DeepView for ClosedPacketHeader {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `closed_choice_packet_payload`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub enum ClosedChoicePacketPayload<'i> {
    Raw(&'i [u8]),
    Words(Vec<u16>),
    Tiny(u8),
}

# [verifier::ext_equal]
pub enum ClosedChoicePacketPayloadSpec {
    Raw(Seq<u8>),
    Words(Seq<u16>),
    Tiny(u8),
}

pub type ClosedChoicePacketPayloadInner = Sum<Seq<u8>, Sum<Seq<u16>, u8>>;

impl<'i> DeepView for ClosedChoicePacketPayload<'i> {
    type V = ClosedChoicePacketPayloadSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ClosedChoicePacketPayload::Raw(v) => ClosedChoicePacketPayloadSpec::Raw(v.deep_view()),
            ClosedChoicePacketPayload::Words(v) => ClosedChoicePacketPayloadSpec::Words(
                v.deep_view(),
            ),
            ClosedChoicePacketPayload::Tiny(v) => ClosedChoicePacketPayloadSpec::Tiny(
                v.deep_view(),
            ),
        }
    }
}

# [doc = "data type for `closed_choice_packet`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct ClosedChoicePacket<'i> {
    pub hdr: ClosedPacketHeader,
    pub payload: ClosedChoicePacketPayload<'i>,
}

# [verifier::ext_equal]
pub struct ClosedChoicePacketSpec {
    pub hdr: ClosedPacketHeaderSpec,
    pub payload: ClosedChoicePacketPayloadSpec,
}

pub type ClosedChoicePacketInner = (ClosedPacketHeaderSpec, ClosedChoicePacketPayloadSpec);

impl<'i> DeepView for ClosedChoicePacket<'i> {
    type V = ClosedChoicePacketSpec;

    open spec fn deep_view(&self) -> Self::V {
        ClosedChoicePacketSpec { hdr: self.hdr.deep_view(), payload: self.payload.deep_view() }
    }
}

# [doc = "data type for `payload_kind`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum PayloadKind {
    Raw = 0,
    Words = 1,
    Tiny = 2,
    Unknown(u8),
}

pub type PayloadKindSpec = PayloadKind;

pub type PayloadKindInner = Sum<u8, u8>;

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

# [doc = "data type for `packet_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
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

# [doc = "data type for `choice_packet_payload`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub enum ChoicePacketPayload<'i> {
    Raw(&'i [u8]),
    Words(Vec<u16>),
    Tiny(u8),
    Default(&'i [u8]),
}

# [verifier::ext_equal]
pub enum ChoicePacketPayloadSpec {
    Raw(Seq<u8>),
    Words(Seq<u16>),
    Tiny(u8),
    Default(Seq<u8>),
}

pub type ChoicePacketPayloadInner = Sum<Seq<u8>, Sum<Seq<u16>, Sum<u8, Seq<u8>>>>;

impl<'i> DeepView for ChoicePacketPayload<'i> {
    type V = ChoicePacketPayloadSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ChoicePacketPayload::Raw(v) => ChoicePacketPayloadSpec::Raw(v.deep_view()),
            ChoicePacketPayload::Words(v) => ChoicePacketPayloadSpec::Words(v.deep_view()),
            ChoicePacketPayload::Tiny(v) => ChoicePacketPayloadSpec::Tiny(v.deep_view()),
            ChoicePacketPayload::Default(v) => ChoicePacketPayloadSpec::Default(v.deep_view()),
        }
    }
}

# [doc = "data type for `version_ihl`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
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

# [doc = "data type for `choice_packet`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct ChoicePacket<'i> {
    pub hdr: PacketHeader,
    pub payload: ChoicePacketPayload<'i>,
}

# [verifier::ext_equal]
pub struct ChoicePacketSpec {
    pub hdr: PacketHeaderSpec,
    pub payload: ChoicePacketPayloadSpec,
}

pub type ChoicePacketInner = (PacketHeaderSpec, ChoicePacketPayloadSpec);

impl<'i> DeepView for ChoicePacket<'i> {
    type V = ChoicePacketSpec;

    open spec fn deep_view(&self) -> Self::V {
        ChoicePacketSpec { hdr: self.hdr.deep_view(), payload: self.payload.deep_view() }
    }
}

# [doc = "data type for `cross_byte_span`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
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

// ============================================================
// Format Specifications
// ============================================================
# [verifier::allow_in_spec]
pub fn closed_payload_kind_from_bits(bits: u8) -> ClosedPayloadKind
    returns
        match bits {
            0 => ClosedPayloadKind::Raw,
            1 => ClosedPayloadKind::Words,
            2 => ClosedPayloadKind::Tiny,
            _ => ClosedPayloadKind::Tiny,
        },
{
    match bits {
        0 => ClosedPayloadKind::Raw,
        1 => ClosedPayloadKind::Words,
        2 => ClosedPayloadKind::Tiny,
        _ => ClosedPayloadKind::Tiny,
    }
}

# [verifier::allow_in_spec]
pub fn closed_payload_kind_to_bits(kind: ClosedPayloadKind) -> u8
    returns
        match kind {
            ClosedPayloadKind::Raw => (0 as u8),
            ClosedPayloadKind::Words => (1 as u8),
            ClosedPayloadKind::Tiny => (2 as u8),
        },
{
    match kind {
        ClosedPayloadKind::Raw => (0 as u8),
        ClosedPayloadKind::Words => (1 as u8),
        ClosedPayloadKind::Tiny => (2 as u8),
    }
}

# [doc = "named format combinator for `closed_packet_header`."]
# [derive (Clone, Copy)]
pub struct ClosedPacketHeaderFmt;

pub const CLOSED_PACKET_HEADER_KIND_MASK: u16 = 0b0000000000000111u16;

pub const CLOSED_PACKET_HEADER_KIND_SHIFT: u16 = 13;

pub const CLOSED_PACKET_HEADER_KIND_MAX: u8 = 0b00001000u8;

pub const CLOSED_PACKET_HEADER_COUNT_MASK: u16 = 0b0000000000011111u16;

pub const CLOSED_PACKET_HEADER_COUNT_SHIFT: u16 = 8;

pub const CLOSED_PACKET_HEADER_COUNT_MAX: u8 = 0b00100000u8;

pub const CLOSED_PACKET_HEADER_LEN_MASK: u16 = 0b0000000011111111u16;

pub const CLOSED_PACKET_HEADER_LEN_SHIFT: u16 = 0;

# [verifier::allow_in_spec]
pub fn unpack_closed_packet_header(raw: u16) -> (u8, u8, u8)
    returns
        (
            (((raw >> CLOSED_PACKET_HEADER_KIND_SHIFT) & CLOSED_PACKET_HEADER_KIND_MASK) as u8),
            (((raw >> CLOSED_PACKET_HEADER_COUNT_SHIFT) & CLOSED_PACKET_HEADER_COUNT_MASK) as u8),
            ((raw & CLOSED_PACKET_HEADER_LEN_MASK) as u8),
        ),
{
    (
        (((raw >> CLOSED_PACKET_HEADER_KIND_SHIFT) & CLOSED_PACKET_HEADER_KIND_MASK) as u8),
        (((raw >> CLOSED_PACKET_HEADER_COUNT_SHIFT) & CLOSED_PACKET_HEADER_COUNT_MASK) as u8),
        ((raw & CLOSED_PACKET_HEADER_LEN_MASK) as u8),
    )
}

# [verifier::allow_in_spec]
pub fn pack_closed_packet_header(kind: u8, count: u8, len: u8) -> u16
    returns
        (((kind as u16) & CLOSED_PACKET_HEADER_KIND_MASK) << CLOSED_PACKET_HEADER_KIND_SHIFT) | (((
        count as u16) & CLOSED_PACKET_HEADER_COUNT_MASK) << CLOSED_PACKET_HEADER_COUNT_SHIFT) | (((
        len as u16) & CLOSED_PACKET_HEADER_LEN_MASK)),
{
    (((kind as u16) & CLOSED_PACKET_HEADER_KIND_MASK) << CLOSED_PACKET_HEADER_KIND_SHIFT) | (((
    count as u16) & CLOSED_PACKET_HEADER_COUNT_MASK) << CLOSED_PACKET_HEADER_COUNT_SHIFT) | (((
    len as u16) & CLOSED_PACKET_HEADER_LEN_MASK))
}

# [verifier::allow_in_spec]
pub fn closed_packet_header_bounds(kind: u8, count: u8, len: u8) -> bool
    returns
        (kind < CLOSED_PACKET_HEADER_KIND_MAX) && (count < CLOSED_PACKET_HEADER_COUNT_MAX),
{
    (kind < CLOSED_PACKET_HEADER_KIND_MAX) && (count < CLOSED_PACKET_HEADER_COUNT_MAX)
}

pub broadcast proof fn lemma_closed_packet_header_unpack_pack(raw: u16)
    by (bit_vector)
    ensures
        # [trigger] pack_closed_packet_header(
            unpack_closed_packet_header(raw).0,
            unpack_closed_packet_header(raw).1,
            unpack_closed_packet_header(raw).2,
        ) == raw,
{
}

pub broadcast proof fn lemma_closed_packet_header_pack_unpack(kind: u8, count: u8, len: u8)
    by (bit_vector)
    requires
        # [trigger] closed_packet_header_bounds(kind, count, len),
    ensures
        unpack_closed_packet_header(pack_closed_packet_header(kind, count, len)).0 == kind,
        unpack_closed_packet_header(pack_closed_packet_header(kind, count, len)).1 == count,
        unpack_closed_packet_header(pack_closed_packet_header(kind, count, len)).2 == len,
{
}

pub broadcast proof fn lemma_closed_packet_header_mapper_wf_in_out(i: u16)
    by (bit_vector)
    ensures
        # [trigger] closed_packet_header_bounds(
            unpack_closed_packet_header(i).0,
            unpack_closed_packet_header(i).1,
            unpack_closed_packet_header(i).2,
        ),
{
}

pub type ClosedPacketHeaderFmtSpec = Named<Bits<U16Be, (u8, u8, u8), ClosedPacketHeaderSpec>>;

impl ClosedPacketHeaderFmt {
    # [doc = "specification constructor for `closed_packet_header`."]
    pub open spec fn spec_inner() -> ClosedPacketHeaderFmtSpec {
        Named(
            "closed_packet_header",
            Bits {
                repr: U16Be,
                unpack: |packed: u16| unpack_closed_packet_header(packed),
                pack: |unpacked: (u8, u8, u8)|
                    {
                        let (kind, count, len) = unpacked;
                        pack_closed_packet_header(kind, count, len)
                    },
                refinement: |unpacked: (u8, u8, u8)|
                    {
                        let (kind, count, len) = unpacked;
                        ((kind == 0 || kind == 1 || kind == 2)) && (count >= 1 && count <= 31)
                    },
                ctor: |unpacked: (u8, u8, u8)|
                    {
                        let (kind, count, len) = unpacked;
                        ClosedPacketHeaderSpec {
                            kind: closed_payload_kind_from_bits(kind),
                            count: count,
                            len: len,
                        }
                    },
                dtor: |value: ClosedPacketHeaderSpec|
                    {
                        let ClosedPacketHeaderSpec { kind, count, len } = value;
                        let kind = closed_payload_kind_to_bits(kind);
                        (kind, count, len)
                    },
                consistent: |value: ClosedPacketHeaderSpec|
                    {
                        let ClosedPacketHeaderSpec { kind, count, len } = value;
                        closed_packet_header_bounds(closed_payload_kind_to_bits(kind), count, len)
                    },
            },
        )
    }
}

# [doc = "named format combinator for `closed_choice_packet_payload`."]
# [derive (Clone, Copy)]
pub struct ClosedChoicePacketPayloadFmt {
    hdr: ClosedPacketHeader,
}

impl ClosedChoicePacketPayloadFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        ClosedPacketHeaderFmt.consistent(self.hdr.deep_view())
    }

    pub closed spec fn hdr_spec(&self) -> ClosedPacketHeaderSpec {
        self.hdr.deep_view()
    }

    pub closed spec fn spec(hdr: ClosedPacketHeader) -> Self {
        ClosedChoicePacketPayloadFmt { hdr }
    }
}

pub type ClosedChoicePacketPayloadFmtSpec = Named<
    Mapped<
        Sum<Varied<u8>, Sum<RepeatN<U16Be, u8>, U8>>,
        FnSpecMapper<ClosedChoicePacketPayloadInner, ClosedChoicePacketPayloadSpec>,
    >,
>;

impl ClosedChoicePacketPayloadFmt {
    # [doc = "specification constructor for `closed_choice_packet_payload`."]
    pub open spec fn spec_inner(hdr: ClosedPacketHeaderSpec) -> ClosedChoicePacketPayloadFmtSpec {
        Named(
            "closed_choice_packet_payload",
            Mapped {
                inner: match hdr.kind {
                    ClosedPayloadKindSpec::Raw => L(Varied(hdr.len)),
                    ClosedPayloadKindSpec::Words => R(L(RepeatN(hdr.count, U16Be))),
                    ClosedPayloadKindSpec::Tiny => R(R(U8)),
                },
                mapper: (
                    |parsed: ClosedChoicePacketPayloadInner| -> ClosedChoicePacketPayloadSpec
                        {
                            match parsed {
                                L(v) => ClosedChoicePacketPayloadSpec::Raw(v),
                                R(L(v)) => ClosedChoicePacketPayloadSpec::Words(v),
                                R(R(v)) => ClosedChoicePacketPayloadSpec::Tiny(v),
                            }
                        },
                    |value: ClosedChoicePacketPayloadSpec| -> ClosedChoicePacketPayloadInner
                        {
                            match value {
                                ClosedChoicePacketPayloadSpec::Raw(v) => L(v),
                                ClosedChoicePacketPayloadSpec::Words(v) => R(L(v)),
                                ClosedChoicePacketPayloadSpec::Tiny(v) => R(R(v)),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `closed_choice_packet`."]
# [derive (Clone, Copy)]
pub struct ClosedChoicePacketFmt;

pub type ClosedChoicePacketFmtSpec = Named<
    Mapped<
        Bind<
            ClosedPacketHeaderFmt,
            spec_fn(ClosedPacketHeaderSpec) -> ClosedChoicePacketPayloadFmt,
        >,
        FnSpecMapper<ClosedChoicePacketInner, ClosedChoicePacketSpec>,
    >,
>;

impl ClosedChoicePacketFmt {
    # [doc = "specification constructor for `closed_choice_packet`."]
    pub open spec fn spec_inner() -> ClosedChoicePacketFmtSpec {
        Named(
            "closed_choice_packet",
            Mapped {
                inner: Bind(
                    ClosedPacketHeaderFmt,
                    |hdr: ClosedPacketHeaderSpec| ClosedChoicePacketPayloadFmt::spec(hdr),
                ),
                mapper: (
                    |parsed: ClosedChoicePacketInner| -> ClosedChoicePacketSpec
                        {
                            let (hdr, payload) = parsed;
                            ClosedChoicePacketSpec { hdr, payload }
                        },
                    |value: ClosedChoicePacketSpec| -> ClosedChoicePacketInner
                        {
                            let ClosedChoicePacketSpec { hdr, payload } = value;
                            (hdr, payload)
                        },
                ),
            },
        )
    }
}

# [verifier::allow_in_spec]
pub fn payload_kind_wf(kind: PayloadKind) -> bool
    returns
        match kind {
            PayloadKind::Raw => true,
            PayloadKind::Words => true,
            PayloadKind::Tiny => true,
            PayloadKind::Unknown(x) => x != 0 && x != 1 && x != 2,
        },
{
    match kind {
        PayloadKind::Raw => true,
        PayloadKind::Words => true,
        PayloadKind::Tiny => true,
        PayloadKind::Unknown(x) => x != 0 && x != 1 && x != 2,
    }
}

# [verifier::allow_in_spec]
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

# [verifier::allow_in_spec]
pub fn payload_kind_to_bits(kind: PayloadKind) -> u8
    returns
        match kind {
            PayloadKind::Raw => (0 as u8),
            PayloadKind::Words => (1 as u8),
            PayloadKind::Tiny => (2 as u8),
            PayloadKind::Unknown(x) => x,
        },
{
    match kind {
        PayloadKind::Raw => (0 as u8),
        PayloadKind::Words => (1 as u8),
        PayloadKind::Tiny => (2 as u8),
        PayloadKind::Unknown(x) => x,
    }
}

# [doc = "named format combinator for `packet_header`."]
# [derive (Clone, Copy)]
pub struct PacketHeaderFmt;

pub const PACKET_HEADER_KIND_MASK: u16 = 0b0000000000000111u16;

pub const PACKET_HEADER_KIND_SHIFT: u16 = 13;

pub const PACKET_HEADER_KIND_MAX: u8 = 0b00001000u8;

pub const PACKET_HEADER_COUNT_MASK: u16 = 0b0000000000011111u16;

pub const PACKET_HEADER_COUNT_SHIFT: u16 = 8;

pub const PACKET_HEADER_COUNT_MAX: u8 = 0b00100000u8;

pub const PACKET_HEADER_LEN_MASK: u16 = 0b0000000011111111u16;

pub const PACKET_HEADER_LEN_SHIFT: u16 = 0;

# [verifier::allow_in_spec]
pub fn unpack_packet_header(raw: u16) -> (u8, u8, u8)
    returns
        (
            (((raw >> PACKET_HEADER_KIND_SHIFT) & PACKET_HEADER_KIND_MASK) as u8),
            (((raw >> PACKET_HEADER_COUNT_SHIFT) & PACKET_HEADER_COUNT_MASK) as u8),
            ((raw & PACKET_HEADER_LEN_MASK) as u8),
        ),
{
    (
        (((raw >> PACKET_HEADER_KIND_SHIFT) & PACKET_HEADER_KIND_MASK) as u8),
        (((raw >> PACKET_HEADER_COUNT_SHIFT) & PACKET_HEADER_COUNT_MASK) as u8),
        ((raw & PACKET_HEADER_LEN_MASK) as u8),
    )
}

# [verifier::allow_in_spec]
pub fn pack_packet_header(kind: u8, count: u8, len: u8) -> u16
    returns
        (((kind as u16) & PACKET_HEADER_KIND_MASK) << PACKET_HEADER_KIND_SHIFT) | (((count as u16)
            & PACKET_HEADER_COUNT_MASK) << PACKET_HEADER_COUNT_SHIFT) | (((len as u16)
            & PACKET_HEADER_LEN_MASK)),
{
    (((kind as u16) & PACKET_HEADER_KIND_MASK) << PACKET_HEADER_KIND_SHIFT) | (((count as u16)
        & PACKET_HEADER_COUNT_MASK) << PACKET_HEADER_COUNT_SHIFT) | (((len as u16)
        & PACKET_HEADER_LEN_MASK))
}

# [verifier::allow_in_spec]
pub fn packet_header_bounds(kind: u8, count: u8, len: u8) -> bool
    returns
        (kind < PACKET_HEADER_KIND_MAX) && (count < PACKET_HEADER_COUNT_MAX),
{
    (kind < PACKET_HEADER_KIND_MAX) && (count < PACKET_HEADER_COUNT_MAX)
}

pub broadcast proof fn lemma_packet_header_unpack_pack(raw: u16)
    by (bit_vector)
    ensures
        # [trigger] pack_packet_header(
            unpack_packet_header(raw).0,
            unpack_packet_header(raw).1,
            unpack_packet_header(raw).2,
        ) == raw,
{
}

pub broadcast proof fn lemma_packet_header_pack_unpack(kind: u8, count: u8, len: u8)
    by (bit_vector)
    requires
        # [trigger] packet_header_bounds(kind, count, len),
    ensures
        unpack_packet_header(pack_packet_header(kind, count, len)).0 == kind,
        unpack_packet_header(pack_packet_header(kind, count, len)).1 == count,
        unpack_packet_header(pack_packet_header(kind, count, len)).2 == len,
{
}

pub broadcast proof fn lemma_packet_header_mapper_wf_in_out(i: u16)
    by (bit_vector)
    ensures
        # [trigger] packet_header_bounds(
            unpack_packet_header(i).0,
            unpack_packet_header(i).1,
            unpack_packet_header(i).2,
        ),
{
}

pub type PacketHeaderFmtSpec = Named<Bits<U16Be, (u8, u8, u8), PacketHeaderSpec>>;

impl PacketHeaderFmt {
    # [doc = "specification constructor for `packet_header`."]
    pub open spec fn spec_inner() -> PacketHeaderFmtSpec {
        Named(
            "packet_header",
            Bits {
                repr: U16Be,
                unpack: |packed: u16| unpack_packet_header(packed),
                pack: |unpacked: (u8, u8, u8)|
                    {
                        let (kind, count, len) = unpacked;
                        pack_packet_header(kind, count, len)
                    },
                refinement: |unpacked: (u8, u8, u8)|
                    {
                        let (kind, count, len) = unpacked;
                        count >= 1 && count <= 31
                    },
                ctor: |unpacked: (u8, u8, u8)|
                    {
                        let (kind, count, len) = unpacked;
                        PacketHeaderSpec {
                            kind: payload_kind_from_bits(kind),
                            count: count,
                            len: len,
                        }
                    },
                dtor: |value: PacketHeaderSpec|
                    {
                        let PacketHeaderSpec { kind, count, len } = value;
                        let kind = payload_kind_to_bits(kind);
                        (kind, count, len)
                    },
                consistent: |value: PacketHeaderSpec|
                    {
                        let PacketHeaderSpec { kind, count, len } = value;
                        (payload_kind_wf(kind)) && (packet_header_bounds(
                            payload_kind_to_bits(kind),
                            count,
                            len,
                        ))
                    },
            },
        )
    }
}

# [doc = "named format combinator for `choice_packet_payload`."]
# [derive (Clone, Copy)]
pub struct ChoicePacketPayloadFmt {
    hdr: PacketHeader,
}

impl ChoicePacketPayloadFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        PacketHeaderFmt.consistent(self.hdr.deep_view())
    }

    pub closed spec fn hdr_spec(&self) -> PacketHeaderSpec {
        self.hdr.deep_view()
    }

    pub closed spec fn spec(hdr: PacketHeader) -> Self {
        ChoicePacketPayloadFmt { hdr }
    }
}

pub type ChoicePacketPayloadFmtSpec = Named<
    Mapped<
        Sum<Varied<u8>, Sum<RepeatN<U16Be, u8>, Sum<U8, Varied<u8>>>>,
        FnSpecMapper<ChoicePacketPayloadInner, ChoicePacketPayloadSpec>,
    >,
>;

impl ChoicePacketPayloadFmt {
    # [doc = "specification constructor for `choice_packet_payload`."]
    pub open spec fn spec_inner(hdr: PacketHeaderSpec) -> ChoicePacketPayloadFmtSpec {
        Named(
            "choice_packet_payload",
            Mapped {
                inner: match hdr.kind {
                    PayloadKindSpec::Raw => L(Varied(hdr.len)),
                    PayloadKindSpec::Words => R(L(RepeatN(hdr.count, U16Be))),
                    PayloadKindSpec::Tiny => R(R(L(U8))),
                    _ => R(R(R(Varied(hdr.len)))),
                },
                mapper: (
                    |parsed: ChoicePacketPayloadInner| -> ChoicePacketPayloadSpec
                        {
                            match parsed {
                                L(v) => ChoicePacketPayloadSpec::Raw(v),
                                R(L(v)) => ChoicePacketPayloadSpec::Words(v),
                                R(R(L(v))) => ChoicePacketPayloadSpec::Tiny(v),
                                R(R(R(v))) => ChoicePacketPayloadSpec::Default(v),
                            }
                        },
                    |value: ChoicePacketPayloadSpec| -> ChoicePacketPayloadInner
                        {
                            match value {
                                ChoicePacketPayloadSpec::Raw(v) => L(v),
                                ChoicePacketPayloadSpec::Words(v) => R(L(v)),
                                ChoicePacketPayloadSpec::Tiny(v) => R(R(L(v))),
                                ChoicePacketPayloadSpec::Default(v) => R(R(R(v))),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `version_ihl`."]
# [derive (Clone, Copy)]
pub struct VersionIhlFmt;

pub const VERSION_IHL_VERSION_MASK: u8 = 0b00001111u8;

pub const VERSION_IHL_VERSION_SHIFT: u8 = 4;

pub const VERSION_IHL_VERSION_MAX: u8 = 0b00010000u8;

pub const VERSION_IHL_IHL_MASK: u8 = 0b00001111u8;

pub const VERSION_IHL_IHL_SHIFT: u8 = 0;

pub const VERSION_IHL_IHL_MAX: u8 = 0b00010000u8;

# [verifier::allow_in_spec]
pub fn unpack_version_ihl(raw: u8) -> (u8, u8)
    returns
        (
            (((raw >> VERSION_IHL_VERSION_SHIFT) & VERSION_IHL_VERSION_MASK) as u8),
            ((raw & VERSION_IHL_IHL_MASK) as u8),
        ),
{
    (
        (((raw >> VERSION_IHL_VERSION_SHIFT) & VERSION_IHL_VERSION_MASK) as u8),
        ((raw & VERSION_IHL_IHL_MASK) as u8),
    )
}

# [verifier::allow_in_spec]
pub fn pack_version_ihl(version: u8, ihl: u8) -> u8
    returns
        (((version as u8) & VERSION_IHL_VERSION_MASK) << VERSION_IHL_VERSION_SHIFT) | (((ihl as u8)
            & VERSION_IHL_IHL_MASK)),
{
    (((version as u8) & VERSION_IHL_VERSION_MASK) << VERSION_IHL_VERSION_SHIFT) | (((ihl as u8)
        & VERSION_IHL_IHL_MASK))
}

# [verifier::allow_in_spec]
pub fn version_ihl_bounds(version: u8, ihl: u8) -> bool
    returns
        (version < VERSION_IHL_VERSION_MAX) && (ihl < VERSION_IHL_IHL_MAX),
{
    (version < VERSION_IHL_VERSION_MAX) && (ihl < VERSION_IHL_IHL_MAX)
}

pub broadcast proof fn lemma_version_ihl_unpack_pack(raw: u8)
    by (bit_vector)
    ensures
        # [trigger] pack_version_ihl(unpack_version_ihl(raw).0, unpack_version_ihl(raw).1) == raw,
{
}

pub broadcast proof fn lemma_version_ihl_pack_unpack(version: u8, ihl: u8)
    by (bit_vector)
    requires
        # [trigger] version_ihl_bounds(version, ihl),
    ensures
        unpack_version_ihl(pack_version_ihl(version, ihl)).0 == version,
        unpack_version_ihl(pack_version_ihl(version, ihl)).1 == ihl,
{
}

pub broadcast proof fn lemma_version_ihl_mapper_wf_in_out(i: u8)
    by (bit_vector)
    ensures
        # [trigger] version_ihl_bounds(unpack_version_ihl(i).0, unpack_version_ihl(i).1),
{
}

pub type VersionIhlFmtSpec = Named<Bits<U8, (u8, u8), VersionIhlSpec>>;

impl VersionIhlFmt {
    # [doc = "specification constructor for `version_ihl`."]
    pub open spec fn spec_inner() -> VersionIhlFmtSpec {
        Named(
            "version_ihl",
            Bits {
                repr: U8,
                unpack: |packed: u8| unpack_version_ihl(packed),
                pack: |unpacked: (u8, u8)|
                    {
                        let (version, ihl) = unpacked;
                        pack_version_ihl(version, ihl)
                    },
                refinement: |unpacked: (u8, u8)|
                    {
                        let (version, ihl) = unpacked;
                        true
                    },
                ctor: |unpacked: (u8, u8)|
                    {
                        let (version, ihl) = unpacked;
                        VersionIhlSpec { version: version, ihl: ihl }
                    },
                dtor: |value: VersionIhlSpec|
                    {
                        let VersionIhlSpec { version, ihl } = value;
                        (version, ihl)
                    },
                consistent: |value: VersionIhlSpec|
                    {
                        let VersionIhlSpec { version, ihl } = value;
                        version_ihl_bounds(version, ihl)
                    },
            },
        )
    }
}

# [doc = "named format combinator for `choice_packet`."]
# [derive (Clone, Copy)]
pub struct ChoicePacketFmt;

pub type ChoicePacketFmtSpec = Named<
    Mapped<
        Bind<PacketHeaderFmt, spec_fn(PacketHeaderSpec) -> ChoicePacketPayloadFmt>,
        FnSpecMapper<ChoicePacketInner, ChoicePacketSpec>,
    >,
>;

impl ChoicePacketFmt {
    # [doc = "specification constructor for `choice_packet`."]
    pub open spec fn spec_inner() -> ChoicePacketFmtSpec {
        Named(
            "choice_packet",
            Mapped {
                inner: Bind(
                    PacketHeaderFmt,
                    |hdr: PacketHeaderSpec| ChoicePacketPayloadFmt::spec(hdr),
                ),
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

# [doc = "named format combinator for `cross_byte_span`."]
# [derive (Clone, Copy)]
pub struct CrossByteSpanFmt;

pub const CROSS_BYTE_SPAN_PREFIX_MASK: u16 = 0b0000000000000111u16;

pub const CROSS_BYTE_SPAN_PREFIX_SHIFT: u16 = 13;

pub const CROSS_BYTE_SPAN_PREFIX_MAX: u8 = 0b00001000u8;

pub const CROSS_BYTE_SPAN_SPAN_MASK: u16 = 0b0000001111111111u16;

pub const CROSS_BYTE_SPAN_SPAN_SHIFT: u16 = 3;

pub const CROSS_BYTE_SPAN_SPAN_MAX: u16 = 0b0000010000000000u16;

pub const CROSS_BYTE_SPAN_SUFFIX_MASK: u16 = 0b0000000000000111u16;

pub const CROSS_BYTE_SPAN_SUFFIX_SHIFT: u16 = 0;

pub const CROSS_BYTE_SPAN_SUFFIX_MAX: u8 = 0b00001000u8;

# [verifier::allow_in_spec]
pub fn unpack_cross_byte_span(raw: u16) -> (u8, u16, u8)
    returns
        (
            (((raw >> CROSS_BYTE_SPAN_PREFIX_SHIFT) & CROSS_BYTE_SPAN_PREFIX_MASK) as u8),
            (((raw >> CROSS_BYTE_SPAN_SPAN_SHIFT) & CROSS_BYTE_SPAN_SPAN_MASK) as u16),
            ((raw & CROSS_BYTE_SPAN_SUFFIX_MASK) as u8),
        ),
{
    (
        (((raw >> CROSS_BYTE_SPAN_PREFIX_SHIFT) & CROSS_BYTE_SPAN_PREFIX_MASK) as u8),
        (((raw >> CROSS_BYTE_SPAN_SPAN_SHIFT) & CROSS_BYTE_SPAN_SPAN_MASK) as u16),
        ((raw & CROSS_BYTE_SPAN_SUFFIX_MASK) as u8),
    )
}

# [verifier::allow_in_spec]
pub fn pack_cross_byte_span(prefix: u8, span: u16, suffix: u8) -> u16
    returns
        (((prefix as u16) & CROSS_BYTE_SPAN_PREFIX_MASK) << CROSS_BYTE_SPAN_PREFIX_SHIFT) | (((
        span as u16) & CROSS_BYTE_SPAN_SPAN_MASK) << CROSS_BYTE_SPAN_SPAN_SHIFT) | (((suffix as u16)
            & CROSS_BYTE_SPAN_SUFFIX_MASK)),
{
    (((prefix as u16) & CROSS_BYTE_SPAN_PREFIX_MASK) << CROSS_BYTE_SPAN_PREFIX_SHIFT) | (((
    span as u16) & CROSS_BYTE_SPAN_SPAN_MASK) << CROSS_BYTE_SPAN_SPAN_SHIFT) | (((suffix as u16)
        & CROSS_BYTE_SPAN_SUFFIX_MASK))
}

# [verifier::allow_in_spec]
pub fn cross_byte_span_bounds(prefix: u8, span: u16, suffix: u8) -> bool
    returns
        (prefix < CROSS_BYTE_SPAN_PREFIX_MAX) && (span < CROSS_BYTE_SPAN_SPAN_MAX) && (suffix
            < CROSS_BYTE_SPAN_SUFFIX_MAX),
{
    (prefix < CROSS_BYTE_SPAN_PREFIX_MAX) && (span < CROSS_BYTE_SPAN_SPAN_MAX) && (suffix
        < CROSS_BYTE_SPAN_SUFFIX_MAX)
}

pub broadcast proof fn lemma_cross_byte_span_unpack_pack(raw: u16)
    by (bit_vector)
    ensures
        # [trigger] pack_cross_byte_span(
            unpack_cross_byte_span(raw).0,
            unpack_cross_byte_span(raw).1,
            unpack_cross_byte_span(raw).2,
        ) == raw,
{
}

pub broadcast proof fn lemma_cross_byte_span_pack_unpack(prefix: u8, span: u16, suffix: u8)
    by (bit_vector)
    requires
        # [trigger] cross_byte_span_bounds(prefix, span, suffix),
    ensures
        unpack_cross_byte_span(pack_cross_byte_span(prefix, span, suffix)).0 == prefix,
        unpack_cross_byte_span(pack_cross_byte_span(prefix, span, suffix)).1 == span,
        unpack_cross_byte_span(pack_cross_byte_span(prefix, span, suffix)).2 == suffix,
{
}

pub broadcast proof fn lemma_cross_byte_span_mapper_wf_in_out(i: u16)
    by (bit_vector)
    ensures
        # [trigger] cross_byte_span_bounds(
            unpack_cross_byte_span(i).0,
            unpack_cross_byte_span(i).1,
            unpack_cross_byte_span(i).2,
        ),
{
}

pub type CrossByteSpanFmtSpec = Named<Bits<U16Be, (u8, u16, u8), CrossByteSpanSpec>>;

impl CrossByteSpanFmt {
    # [doc = "specification constructor for `cross_byte_span`."]
    pub open spec fn spec_inner() -> CrossByteSpanFmtSpec {
        Named(
            "cross_byte_span",
            Bits {
                repr: U16Be,
                unpack: |packed: u16| unpack_cross_byte_span(packed),
                pack: |unpacked: (u8, u16, u8)|
                    {
                        let (prefix, span, suffix) = unpacked;
                        pack_cross_byte_span(prefix, span, suffix)
                    },
                refinement: |unpacked: (u8, u16, u8)|
                    {
                        let (prefix, span, suffix) = unpacked;
                        true
                    },
                ctor: |unpacked: (u8, u16, u8)|
                    {
                        let (prefix, span, suffix) = unpacked;
                        CrossByteSpanSpec { prefix: prefix, span: span, suffix: suffix }
                    },
                dtor: |value: CrossByteSpanSpec|
                    {
                        let CrossByteSpanSpec { prefix, span, suffix } = value;
                        (prefix, span, suffix)
                    },
                consistent: |value: CrossByteSpanSpec|
                    {
                        let CrossByteSpanSpec { prefix, span, suffix } = value;
                        cross_byte_span_bounds(prefix, span, suffix)
                    },
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ClosedPacketHeaderFmt {
        type PVal = ClosedPacketHeaderSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ClosedPacketHeaderFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ClosedPacketHeaderFmt {
        type Val = ClosedPacketHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ClosedPacketHeaderFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ClosedPacketHeaderFmt {
        type SValue = ClosedPacketHeaderSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ClosedPacketHeaderFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ClosedPacketHeaderFmt {
        type SVal = ClosedPacketHeaderSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ClosedPacketHeaderFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ClosedPacketHeaderFmt {
        type T = ClosedPacketHeaderSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            ClosedPacketHeaderFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ClosedChoicePacketPayloadFmt {
        type PVal = ClosedChoicePacketPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for ClosedChoicePacketPayloadFmt {
        type Val = ClosedChoicePacketPayloadSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for ClosedChoicePacketPayloadFmt {
        type SValue = ClosedChoicePacketPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ClosedChoicePacketPayloadFmt {
        type SVal = ClosedChoicePacketPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ClosedChoicePacketPayloadFmt {
        type T = ClosedChoicePacketPayloadSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).byte_len(v)
        }
    }

    impl SpecParser for ClosedChoicePacketFmt {
        type PVal = ClosedChoicePacketSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ClosedChoicePacketFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ClosedChoicePacketFmt {
        type Val = ClosedChoicePacketSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ClosedChoicePacketFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ClosedChoicePacketFmt {
        type SValue = ClosedChoicePacketSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ClosedChoicePacketFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ClosedChoicePacketFmt {
        type SVal = ClosedChoicePacketSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ClosedChoicePacketFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ClosedChoicePacketFmt {
        type T = ClosedChoicePacketSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ClosedChoicePacketFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for PacketHeaderFmt {
        type PVal = PacketHeaderSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            PacketHeaderFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for PacketHeaderFmt {
        type Val = PacketHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            PacketHeaderFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for PacketHeaderFmt {
        type SValue = PacketHeaderSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            PacketHeaderFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for PacketHeaderFmt {
        type SVal = PacketHeaderSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            PacketHeaderFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for PacketHeaderFmt {
        type T = PacketHeaderSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            PacketHeaderFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ChoicePacketPayloadFmt {
        type PVal = ChoicePacketPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for ChoicePacketPayloadFmt {
        type Val = ChoicePacketPayloadSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for ChoicePacketPayloadFmt {
        type SValue = ChoicePacketPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ChoicePacketPayloadFmt {
        type SVal = ChoicePacketPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ChoicePacketPayloadFmt {
        type T = ChoicePacketPayloadSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).byte_len(v)
        }
    }

    impl SpecParser for VersionIhlFmt {
        type PVal = VersionIhlSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            VersionIhlFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for VersionIhlFmt {
        type Val = VersionIhlSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            VersionIhlFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for VersionIhlFmt {
        type SValue = VersionIhlSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            VersionIhlFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for VersionIhlFmt {
        type SVal = VersionIhlSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            VersionIhlFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for VersionIhlFmt {
        type T = VersionIhlSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            VersionIhlFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ChoicePacketFmt {
        type PVal = ChoicePacketSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ChoicePacketFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ChoicePacketFmt {
        type Val = ChoicePacketSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ChoicePacketFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ChoicePacketFmt {
        type SValue = ChoicePacketSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ChoicePacketFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ChoicePacketFmt {
        type SVal = ChoicePacketSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ChoicePacketFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ChoicePacketFmt {
        type T = ChoicePacketSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ChoicePacketFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CrossByteSpanFmt {
        type PVal = CrossByteSpanSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            CrossByteSpanFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for CrossByteSpanFmt {
        type Val = CrossByteSpanSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            CrossByteSpanFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for CrossByteSpanFmt {
        type SValue = CrossByteSpanSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            CrossByteSpanFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CrossByteSpanFmt {
        type SVal = CrossByteSpanSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            CrossByteSpanFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for CrossByteSpanFmt {
        type T = CrossByteSpanSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            CrossByteSpanFmt::spec_inner().byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for ClosedPacketHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecParser>::spec_parse);
            ClosedPacketHeaderFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ClosedPacketHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            ClosedPacketHeaderFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecParser>::spec_parse);
            let fmt = ClosedPacketHeaderFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ClosedPacketHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecParser>::spec_parse);
            reveal(<ClosedPacketHeaderFmt as SpecByteLen>::byte_len);
            let fmt = ClosedPacketHeaderFmt::spec_inner();
            broadcast use
                lemma_closed_packet_header_unpack_pack,
                lemma_closed_packet_header_mapper_wf_in_out,
            ;

            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecParser>::spec_parse);
            reveal(<ClosedPacketHeaderFmt as Consistency>::consistent);
            broadcast use
                lemma_closed_packet_header_unpack_pack,
                lemma_closed_packet_header_mapper_wf_in_out,
            ;

            let fmt = ClosedPacketHeaderFmt::spec_inner();
            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ClosedPacketHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ClosedPacketHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedPacketHeaderFmt as SpecByteLen>::byte_len);
            let fmt = ClosedPacketHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ClosedPacketHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ClosedPacketHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<ClosedPacketHeaderFmt as SpecByteLen>::byte_len);
            let fmt = ClosedPacketHeaderFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ClosedPacketHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedPacketHeaderFmt as SpecByteLen>::byte_len);
            reveal(<ClosedPacketHeaderFmt as SpecParser>::spec_parse);
            broadcast use lemma_closed_packet_header_pack_unpack;

            let fmt = ClosedPacketHeaderFmt::spec_inner();
            assert(fmt.1.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ClosedPacketHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecParser>::spec_parse);
            broadcast use
                lemma_closed_packet_header_unpack_pack,
                lemma_closed_packet_header_mapper_wf_in_out,
            ;

            let fmt = ClosedPacketHeaderFmt::spec_inner();
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ClosedPacketHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedPacketHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = ClosedPacketHeaderFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ClosedPacketHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ClosedPacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedPacketHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = ClosedPacketHeaderFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ClosedChoicePacketPayloadFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecParser>::spec_parse);
            ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ClosedChoicePacketPayloadFmt {
        open spec fn productive_inv(&self) -> bool {
            ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecParser>::spec_parse);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ClosedChoicePacketPayloadFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecParser>::spec_parse);
            reveal(<ClosedChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecParser>::spec_parse);
            reveal(<ClosedChoicePacketPayloadFmt as Consistency>::consistent);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ClosedChoicePacketPayloadFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ClosedChoicePacketPayloadFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<ClosedChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ClosedChoicePacketPayloadFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecParser>::spec_parse);
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedChoicePacketPayloadFmt as Consistency>::consistent);
            reveal(<ClosedChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ClosedChoicePacketPayloadFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecParser>::spec_parse);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ClosedChoicePacketPayloadFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ClosedChoicePacketPayloadFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = ClosedChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ClosedChoicePacketFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecParser>::spec_parse);
            ClosedChoicePacketFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ClosedChoicePacketFmt {
        open spec fn productive_inv(&self) -> bool {
            ClosedChoicePacketFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecParser>::spec_parse);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ClosedChoicePacketFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecParser>::spec_parse);
            reveal(<ClosedChoicePacketFmt as SpecByteLen>::byte_len);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecParser>::spec_parse);
            reveal(<ClosedChoicePacketFmt as Consistency>::consistent);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ClosedChoicePacketFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedChoicePacketFmt as SpecByteLen>::byte_len);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ClosedChoicePacketFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ClosedChoicePacketFmt as SpecSerializer>::spec_serialize);
            reveal(<ClosedChoicePacketFmt as SpecByteLen>::byte_len);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ClosedChoicePacketFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecParser>::spec_parse);
            reveal(<ClosedChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedChoicePacketFmt as Consistency>::consistent);
            reveal(<ClosedChoicePacketFmt as SpecByteLen>::byte_len);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ClosedChoicePacketFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecParser>::spec_parse);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ClosedChoicePacketFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedChoicePacketFmt as SpecSerializer>::spec_serialize);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ClosedChoicePacketFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ClosedChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ClosedChoicePacketFmt as SpecSerializer>::spec_serialize);
            let fmt = ClosedChoicePacketFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for PacketHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecParser>::spec_parse);
            PacketHeaderFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for PacketHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            PacketHeaderFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecParser>::spec_parse);
            let fmt = PacketHeaderFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for PacketHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecParser>::spec_parse);
            reveal(<PacketHeaderFmt as SpecByteLen>::byte_len);
            let fmt = PacketHeaderFmt::spec_inner();
            broadcast use lemma_packet_header_unpack_pack, lemma_packet_header_mapper_wf_in_out;

            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecParser>::spec_parse);
            reveal(<PacketHeaderFmt as Consistency>::consistent);
            broadcast use lemma_packet_header_unpack_pack, lemma_packet_header_mapper_wf_in_out;

            let fmt = PacketHeaderFmt::spec_inner();
            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for PacketHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = PacketHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PacketHeaderFmt as SpecByteLen>::byte_len);
            let fmt = PacketHeaderFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for PacketHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<PacketHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<PacketHeaderFmt as SpecByteLen>::byte_len);
            let fmt = PacketHeaderFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for PacketHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PacketHeaderFmt as SpecByteLen>::byte_len);
            reveal(<PacketHeaderFmt as SpecParser>::spec_parse);
            broadcast use lemma_packet_header_pack_unpack;

            let fmt = PacketHeaderFmt::spec_inner();
            assert(fmt.1.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for PacketHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecParser>::spec_parse);
            broadcast use lemma_packet_header_unpack_pack, lemma_packet_header_mapper_wf_in_out;

            let fmt = PacketHeaderFmt::spec_inner();
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for PacketHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<PacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PacketHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = PacketHeaderFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for PacketHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<PacketHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PacketHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = PacketHeaderFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ChoicePacketPayloadFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecParser>::spec_parse);
            ChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ChoicePacketPayloadFmt {
        open spec fn productive_inv(&self) -> bool {
            ChoicePacketPayloadFmt::spec_inner(self.hdr_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecParser>::spec_parse);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ChoicePacketPayloadFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecParser>::spec_parse);
            reveal(<ChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecParser>::spec_parse);
            reveal(<ChoicePacketPayloadFmt as Consistency>::consistent);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ChoicePacketPayloadFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ChoicePacketPayloadFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ChoicePacketPayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ChoicePacketPayloadFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecParser>::spec_parse);
            reveal(<ChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoicePacketPayloadFmt as Consistency>::consistent);
            reveal(<ChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ChoicePacketPayloadFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecParser>::spec_parse);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ChoicePacketPayloadFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoicePacketPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ChoicePacketPayloadFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ChoicePacketPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoicePacketPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = ChoicePacketPayloadFmt::spec_inner(self.hdr_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for VersionIhlFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecParser>::spec_parse);
            VersionIhlFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for VersionIhlFmt {
        open spec fn productive_inv(&self) -> bool {
            VersionIhlFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecParser>::spec_parse);
            let fmt = VersionIhlFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for VersionIhlFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecParser>::spec_parse);
            reveal(<VersionIhlFmt as SpecByteLen>::byte_len);
            let fmt = VersionIhlFmt::spec_inner();
            broadcast use lemma_version_ihl_unpack_pack, lemma_version_ihl_mapper_wf_in_out;

            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecParser>::spec_parse);
            reveal(<VersionIhlFmt as Consistency>::consistent);
            broadcast use lemma_version_ihl_unpack_pack, lemma_version_ihl_mapper_wf_in_out;

            let fmt = VersionIhlFmt::spec_inner();
            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for VersionIhlFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = VersionIhlFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<VersionIhlFmt as SpecByteLen>::byte_len);
            let fmt = VersionIhlFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for VersionIhlFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<VersionIhlFmt as SpecSerializer>::spec_serialize);
            reveal(<VersionIhlFmt as SpecByteLen>::byte_len);
            let fmt = VersionIhlFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for VersionIhlFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<VersionIhlFmt as SpecByteLen>::byte_len);
            reveal(<VersionIhlFmt as SpecParser>::spec_parse);
            broadcast use lemma_version_ihl_pack_unpack;

            let fmt = VersionIhlFmt::spec_inner();
            assert(fmt.1.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for VersionIhlFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecParser>::spec_parse);
            broadcast use lemma_version_ihl_unpack_pack, lemma_version_ihl_mapper_wf_in_out;

            let fmt = VersionIhlFmt::spec_inner();
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for VersionIhlFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<VersionIhlFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<VersionIhlFmt as SpecSerializer>::spec_serialize);
            let fmt = VersionIhlFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for VersionIhlFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<VersionIhlFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<VersionIhlFmt as SpecSerializer>::spec_serialize);
            let fmt = VersionIhlFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ChoicePacketFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecParser>::spec_parse);
            ChoicePacketFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ChoicePacketFmt {
        open spec fn productive_inv(&self) -> bool {
            ChoicePacketFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecParser>::spec_parse);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ChoicePacketFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecParser>::spec_parse);
            reveal(<ChoicePacketFmt as SpecByteLen>::byte_len);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecParser>::spec_parse);
            reveal(<ChoicePacketFmt as Consistency>::consistent);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ChoicePacketFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoicePacketFmt as SpecByteLen>::byte_len);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ChoicePacketFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ChoicePacketFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoicePacketFmt as SpecByteLen>::byte_len);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ChoicePacketFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecParser>::spec_parse);
            reveal(<ChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoicePacketFmt as Consistency>::consistent);
            reveal(<ChoicePacketFmt as SpecByteLen>::byte_len);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ChoicePacketFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecParser>::spec_parse);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ChoicePacketFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoicePacketFmt as SpecSerializer>::spec_serialize);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ChoicePacketFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ChoicePacketFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoicePacketFmt as SpecSerializer>::spec_serialize);
            let fmt = ChoicePacketFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CrossByteSpanFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecParser>::spec_parse);
            CrossByteSpanFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CrossByteSpanFmt {
        open spec fn productive_inv(&self) -> bool {
            CrossByteSpanFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecParser>::spec_parse);
            let fmt = CrossByteSpanFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CrossByteSpanFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecParser>::spec_parse);
            reveal(<CrossByteSpanFmt as SpecByteLen>::byte_len);
            let fmt = CrossByteSpanFmt::spec_inner();
            broadcast use lemma_cross_byte_span_unpack_pack, lemma_cross_byte_span_mapper_wf_in_out;

            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecParser>::spec_parse);
            reveal(<CrossByteSpanFmt as Consistency>::consistent);
            broadcast use lemma_cross_byte_span_unpack_pack, lemma_cross_byte_span_mapper_wf_in_out;

            let fmt = CrossByteSpanFmt::spec_inner();
            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CrossByteSpanFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = CrossByteSpanFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CrossByteSpanFmt as SpecByteLen>::byte_len);
            let fmt = CrossByteSpanFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CrossByteSpanFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CrossByteSpanFmt as SpecSerializer>::spec_serialize);
            reveal(<CrossByteSpanFmt as SpecByteLen>::byte_len);
            let fmt = CrossByteSpanFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CrossByteSpanFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CrossByteSpanFmt as SpecByteLen>::byte_len);
            reveal(<CrossByteSpanFmt as SpecParser>::spec_parse);
            broadcast use lemma_cross_byte_span_pack_unpack;

            let fmt = CrossByteSpanFmt::spec_inner();
            assert(fmt.1.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CrossByteSpanFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecParser>::spec_parse);
            broadcast use lemma_cross_byte_span_unpack_pack, lemma_cross_byte_span_mapper_wf_in_out;

            let fmt = CrossByteSpanFmt::spec_inner();
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CrossByteSpanFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CrossByteSpanFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CrossByteSpanFmt as SpecSerializer>::spec_serialize);
            let fmt = CrossByteSpanFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CrossByteSpanFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CrossByteSpanFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CrossByteSpanFmt as SpecSerializer>::spec_serialize);
            let fmt = CrossByteSpanFmt::spec_inner();
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

    impl<'i> Parser<&'i [u8]> for ClosedPacketHeaderFmt {
        type PT = ClosedPacketHeader;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ClosedPacketHeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, raw) = U16Be.parse(ibuf)?;
            let (kind, count, len) = unpack_closed_packet_header(raw);
            if !(kind == 0 || kind == 1 || kind == 2) {
                return Err(ParseError::predicate_failed());
            }
            if !(count >= 1 && count <= 31) {
                return Err(ParseError::predicate_failed());
            }
            let final_v = ClosedPacketHeader {
                kind: closed_payload_kind_from_bits(kind),
                count: count,
                len: len,
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
            Ok((n, final_v))
        }
    }

    impl<'i> Serializer<ClosedPacketHeader> for ClosedPacketHeaderFmt {
        fn serialize(&self, v: &ClosedPacketHeader, obuf: &mut Vec<u8>) {
            reveal(<ClosedPacketHeaderFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let ClosedPacketHeader { kind, count, len } = *v;
            let packed = pack_closed_packet_header(closed_payload_kind_to_bits(kind), count, len);
            U16Be.serialize(&packed, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ClosedPacketHeader> for ClosedPacketHeaderFmt {
        fn prepare(&self, v: &ClosedPacketHeader) -> Result<usize, PreSerializeError> {
            reveal(<ClosedPacketHeaderFmt as SpecByteLen>::byte_len);
            let ClosedPacketHeader { kind, count, len } = *v;
            if !(closed_packet_header_bounds(closed_payload_kind_to_bits(kind), count, len)) {
                return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
            }
            if !(closed_payload_kind_to_bits(kind) == 0 || closed_payload_kind_to_bits(kind) == 1
                || closed_payload_kind_to_bits(kind) == 2) {
                return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
            }
            if !(count >= 1 && count <= 31) {
                return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
            }
            let packed = pack_closed_packet_header(closed_payload_kind_to_bits(kind), count, len);
            U16Be.prepare(&packed)
        }
    }

    impl<'i> Parser<&'i [u8]> for ClosedChoicePacketPayloadFmt {
        type PT = ClosedChoicePacketPayload<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ClosedChoicePacketPayloadFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.hdr.kind {
                ClosedPayloadKind::Raw => {
                    let (n, v) = (Varied(self.hdr.len)).parse(&rest)?;
                    (n, ClosedChoicePacketPayload::Raw(v))
                },
                ClosedPayloadKind::Words => {
                    let (n, v) = (RepeatN(self.hdr.count, U16Be)).parse(&rest)?;
                    (n, ClosedChoicePacketPayload::Words(v))
                },
                ClosedPayloadKind::Tiny => {
                    let (n, v) = (U8).parse(&rest)?;
                    (n, ClosedChoicePacketPayload::Tiny(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<ClosedChoicePacketPayload<'i>> for ClosedChoicePacketPayloadFmt {
        fn serialize(&self, v: &ClosedChoicePacketPayload<'i>, obuf: &mut Vec<u8>) {
            reveal(<ClosedChoicePacketPayloadFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.hdr.kind, v) {
                (ClosedPayloadKind::Raw, ClosedChoicePacketPayload::Raw(v)) => {
                    (Varied(self.hdr.len)).serialize(v, obuf);
                },
                (ClosedPayloadKind::Words, ClosedChoicePacketPayload::Words(v)) => {
                    (RepeatN(self.hdr.count, U16Be)).serialize(v, obuf);
                },
                (ClosedPayloadKind::Tiny, ClosedChoicePacketPayload::Tiny(v)) => {
                    (U8).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ClosedChoicePacketPayload<'i>> for ClosedChoicePacketPayloadFmt {
        fn prepare(&self, v: &ClosedChoicePacketPayload<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ClosedChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.hdr.kind, v) {
                (ClosedPayloadKind::Raw, ClosedChoicePacketPayload::Raw(v)) => (Varied(
                    self.hdr.len,
                )).prepare(v),
                (ClosedPayloadKind::Words, ClosedChoicePacketPayload::Words(v)) => (RepeatN(
                    self.hdr.count,
                    U16Be,
                )).prepare(v),
                (ClosedPayloadKind::Tiny, ClosedChoicePacketPayload::Tiny(v)) => (U8).prepare(v),
                _ => Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for ClosedChoicePacketFmt {
        type PT = ClosedChoicePacket<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ClosedChoicePacketFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = ClosedPacketHeaderFmt.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, payload) = ClosedChoicePacketPayloadFmt { hdr: hdr }.parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = ClosedChoicePacket { hdr, payload };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<ClosedChoicePacket<'i>> for ClosedChoicePacketFmt {
        fn serialize(&self, v: &ClosedChoicePacket<'i>, obuf: &mut Vec<u8>) {
            reveal(<ClosedChoicePacketFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let ClosedChoicePacket { hdr, payload } = v;
            ClosedPacketHeaderFmt.serialize(hdr, obuf);
            ClosedChoicePacketPayloadFmt { hdr: *hdr }.serialize(payload, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ClosedChoicePacket<'i>> for ClosedChoicePacketFmt {
        fn prepare(&self, v: &ClosedChoicePacket<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ClosedChoicePacketFmt as SpecByteLen>::byte_len);
            let ClosedChoicePacket { hdr, payload } = v;
            let l1 = (ClosedPacketHeaderFmt).prepare(hdr)?;
            let l2 = (ClosedChoicePacketPayloadFmt { hdr: *hdr }).prepare(payload)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for PacketHeaderFmt {
        type PT = PacketHeader;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<PacketHeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, raw) = U16Be.parse(ibuf)?;
            let (kind, count, len) = unpack_packet_header(raw);
            if !(count >= 1 && count <= 31) {
                return Err(ParseError::predicate_failed());
            }
            let final_v = PacketHeader {
                kind: payload_kind_from_bits(kind),
                count: count,
                len: len,
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
            Ok((n, final_v))
        }
    }

    impl<'i> Serializer<PacketHeader> for PacketHeaderFmt {
        fn serialize(&self, v: &PacketHeader, obuf: &mut Vec<u8>) {
            reveal(<PacketHeaderFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let PacketHeader { kind, count, len } = *v;
            let packed = pack_packet_header(payload_kind_to_bits(kind), count, len);
            U16Be.serialize(&packed, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<PacketHeader> for PacketHeaderFmt {
        fn prepare(&self, v: &PacketHeader) -> Result<usize, PreSerializeError> {
            reveal(<PacketHeaderFmt as SpecByteLen>::byte_len);
            let PacketHeader { kind, count, len } = *v;
            if !(packet_header_bounds(payload_kind_to_bits(kind), count, len)) {
                return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
            }
            if !(payload_kind_wf(kind)) {
                return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
            }
            if !(count >= 1 && count <= 31) {
                return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
            }
            let packed = pack_packet_header(payload_kind_to_bits(kind), count, len);
            U16Be.prepare(&packed)
        }
    }

    impl<'i> Parser<&'i [u8]> for ChoicePacketPayloadFmt {
        type PT = ChoicePacketPayload<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoicePacketPayloadFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.hdr.kind {
                PayloadKind::Raw => {
                    let (n, v) = (Varied(self.hdr.len)).parse(&rest)?;
                    (n, ChoicePacketPayload::Raw(v))
                },
                PayloadKind::Words => {
                    let (n, v) = (RepeatN(self.hdr.count, U16Be)).parse(&rest)?;
                    (n, ChoicePacketPayload::Words(v))
                },
                PayloadKind::Tiny => {
                    let (n, v) = (U8).parse(&rest)?;
                    (n, ChoicePacketPayload::Tiny(v))
                },
                _ => {
                    let (n, v) = (Varied(self.hdr.len)).parse(&rest)?;
                    (n, ChoicePacketPayload::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<ChoicePacketPayload<'i>> for ChoicePacketPayloadFmt {
        fn serialize(&self, v: &ChoicePacketPayload<'i>, obuf: &mut Vec<u8>) {
            reveal(<ChoicePacketPayloadFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.hdr.kind, v) {
                (PayloadKind::Raw, ChoicePacketPayload::Raw(v)) => {
                    (Varied(self.hdr.len)).serialize(v, obuf);
                },
                (PayloadKind::Words, ChoicePacketPayload::Words(v)) => {
                    (RepeatN(self.hdr.count, U16Be)).serialize(v, obuf);
                },
                (PayloadKind::Tiny, ChoicePacketPayload::Tiny(v)) => {
                    (U8).serialize(v, obuf);
                },
                (_, ChoicePacketPayload::Default(v)) => {
                    (Varied(self.hdr.len)).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoicePacketPayload<'i>> for ChoicePacketPayloadFmt {
        fn prepare(&self, v: &ChoicePacketPayload<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ChoicePacketPayloadFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.hdr.kind, v) {
                (PayloadKind::Raw, ChoicePacketPayload::Raw(v)) => (Varied(self.hdr.len)).prepare(
                    v,
                ),
                (PayloadKind::Words, ChoicePacketPayload::Words(v)) => (RepeatN(
                    self.hdr.count,
                    U16Be,
                )).prepare(v),
                (PayloadKind::Tiny, ChoicePacketPayload::Tiny(v)) => (U8).prepare(v),
                (PayloadKind::Unknown(x), ChoicePacketPayload::Default(v)) if x != 0 && x != 1 && x
                    != 2 => (Varied(self.hdr.len)).prepare(v),
                _ => Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for VersionIhlFmt {
        type PT = VersionIhl;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<VersionIhlFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, raw) = U8.parse(ibuf)?;
            let (version, ihl) = unpack_version_ihl(raw);
            let final_v = VersionIhl { version: version, ihl: ihl };
            assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
            Ok((n, final_v))
        }
    }

    impl<'i> Serializer<VersionIhl> for VersionIhlFmt {
        fn serialize(&self, v: &VersionIhl, obuf: &mut Vec<u8>) {
            reveal(<VersionIhlFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let VersionIhl { version, ihl } = *v;
            let packed = pack_version_ihl(version, ihl);
            U8.serialize(&packed, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<VersionIhl> for VersionIhlFmt {
        fn prepare(&self, v: &VersionIhl) -> Result<usize, PreSerializeError> {
            reveal(<VersionIhlFmt as SpecByteLen>::byte_len);
            let VersionIhl { version, ihl } = *v;
            if !(version_ihl_bounds(version, ihl)) {
                return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
            }
            let packed = pack_version_ihl(version, ihl);
            U8.prepare(&packed)
        }
    }

    impl<'i> Parser<&'i [u8]> for ChoicePacketFmt {
        type PT = ChoicePacket<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ChoicePacketFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = PacketHeaderFmt.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, payload) = ChoicePacketPayloadFmt { hdr: hdr }.parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = ChoicePacket { hdr, payload };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<ChoicePacket<'i>> for ChoicePacketFmt {
        fn serialize(&self, v: &ChoicePacket<'i>, obuf: &mut Vec<u8>) {
            reveal(<ChoicePacketFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let ChoicePacket { hdr, payload } = v;
            PacketHeaderFmt.serialize(hdr, obuf);
            ChoicePacketPayloadFmt { hdr: *hdr }.serialize(payload, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoicePacket<'i>> for ChoicePacketFmt {
        fn prepare(&self, v: &ChoicePacket<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ChoicePacketFmt as SpecByteLen>::byte_len);
            let ChoicePacket { hdr, payload } = v;
            let l1 = (PacketHeaderFmt).prepare(hdr)?;
            let l2 = (ChoicePacketPayloadFmt { hdr: *hdr }).prepare(payload)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CrossByteSpanFmt {
        type PT = CrossByteSpan;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<CrossByteSpanFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, raw) = U16Be.parse(ibuf)?;
            let (prefix, span, suffix) = unpack_cross_byte_span(raw);
            let final_v = CrossByteSpan { prefix: prefix, span: span, suffix: suffix };
            assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
            Ok((n, final_v))
        }
    }

    impl<'i> Serializer<CrossByteSpan> for CrossByteSpanFmt {
        fn serialize(&self, v: &CrossByteSpan, obuf: &mut Vec<u8>) {
            reveal(<CrossByteSpanFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let CrossByteSpan { prefix, span, suffix } = *v;
            let packed = pack_cross_byte_span(prefix, span, suffix);
            U16Be.serialize(&packed, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CrossByteSpan> for CrossByteSpanFmt {
        fn prepare(&self, v: &CrossByteSpan) -> Result<usize, PreSerializeError> {
            reveal(<CrossByteSpanFmt as SpecByteLen>::byte_len);
            let CrossByteSpan { prefix, span, suffix } = *v;
            if !(cross_byte_span_bounds(prefix, span, suffix)) {
                return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
            }
            let packed = pack_cross_byte_span(prefix, span, suffix);
            U16Be.prepare(&packed)
        }
    }

}

} // verus!
