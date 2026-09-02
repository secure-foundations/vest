//! CBOR initial-byte and argument formats.
use crate::combinators::{
    mapped::spec::{LosslessMapper, LossyMapper, SpecMap, SpecMapper},
    Bind, Bits, Const, Empty, Mapped, Refined, Sum, U16Be, U32Be, U64Be, Void, U8,
};
use crate::core::exec::{
    input::{InputBuf, InputSlice},
    output::OutputBuf,
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::{proof::*, spec::*};
use crate::Never;
use vstd::assert_seqs_equal;
use vstd::prelude::*;

use super::CborFloat;
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

pub const ADDITIONAL_INFO_MASK: u8 = 0x1fu8;

/// The two bit fields in a CBOR initial byte (RFC 8949 section 3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub struct CborInitial {
    /// Three-bit major-type code.
    pub major: u8,
    /// Five-bit additional-information value.
    pub additional: u8,
}

impl DeepView for CborInitial {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[verifier::allow_in_spec]
pub fn unpack_initial(raw: u8) -> (fields: (u8, u8))
    returns
        ((raw >> 5, raw & ADDITIONAL_INFO_MASK)),
{
    (raw >> 5, raw & ADDITIONAL_INFO_MASK)
}

#[verifier::allow_in_spec]
pub fn pack_initial(major: u8, additional: u8) -> (raw: u8)
    returns
        ((major << 5) | additional),
{
    (major << 5) | additional
}

#[verifier::allow_in_spec]
pub fn initial_fields_in_bounds(major: u8, additional: u8) -> (valid: bool)
    returns
        (major < 8u8 && additional < 32u8),
{
    major < 8u8 && additional < 32u8
}

pub broadcast proof fn lemma_initial_unpack_pack(raw: u8)
    by (bit_vector)
    ensures
        #[trigger] pack_initial(unpack_initial(raw).0, unpack_initial(raw).1) == raw,
{
}

pub broadcast proof fn lemma_initial_pack_unpack(major: u8, additional: u8)
    by (bit_vector)
    requires
        #[trigger] initial_fields_in_bounds(major, additional),
    ensures
        unpack_initial(pack_initial(major, additional)).0 == major,
        unpack_initial(pack_initial(major, additional)).1 == additional,
{
}

pub broadcast proof fn lemma_initial_unpack_in_bounds(raw: u8)
    by (bit_vector)
    ensures
        #[trigger] initial_fields_in_bounds(unpack_initial(raw).0, unpack_initial(raw).1),
{
}

type CborInitialInnerFmt = Bits<U8, (u8, u8), CborInitial>;

pub open spec fn cbor_initial_fmt() -> CborInitialInnerFmt {
    Bits {
        repr: U8,
        unpack: |raw: u8| unpack_initial(raw),
        pack: |fields: (u8, u8)| pack_initial(fields.0, fields.1),
        refinement: |_fields: (u8, u8)| true,
        ctor: |fields: (u8, u8)| CborInitial { major: fields.0, additional: fields.1 },
        dtor: |initial: CborInitial| (initial.major, initial.additional),
        consistent: |initial: CborInitial|
            { initial_fields_in_bounds(initial.major, initial.additional) },
    }
}

/// The fixed-width initial-byte bit-field format.
#[derive(Debug, Clone, Copy)]
pub struct CborInitialFmt;

impl<'i> Parser<&'i [u8]> for CborInitialFmt {
    type PT = CborInitial;

    fn parse(&self, input: &&'i [u8]) -> PResult<Self::PT> {
        let (n, raw) = U8.parse(input)?;
        let (major, additional) = unpack_initial(raw);
        Ok((n, CborInitial { major, additional }))
    }
}

impl<Output: OutputBuf> Serializer<Output, CborInitial> for CborInitialFmt {
    fn serialize_into(&self, value: &CborInitial, out: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        let ghost old_out = out@;
        let r = pack_initial(value.major, value.additional);
        U8.serialize_into(&r, out);
        assert(out@ == old_out + self.spec_serialize(value.deep_view()));
    }
}

impl Prepare<CborInitial> for CborInitialFmt {
    fn prepare(&self, value: &CborInitial) -> Result<usize, PreSerializeError> {
        if !initial_fields_in_bounds(value.major, value.additional) {
            Err(PreSerializeError::custom("CBOR initial-byte field is out of range"))
        } else {
            let r = pack_initial(value.major, value.additional);
            U8.prepare(&r)
        }
    }
}

impl ByteLen<CborInitial> for CborInitialFmt {
    fn length(&self, value: &CborInitial) -> usize {
        let r = pack_initial(value.major, value.additional);
        U8.length(&r)
    }
}

/// The eight CBOR major types from RFC 8949 section 3.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum MajorType {
    Unsigned,
    Negative,
    Bytes,
    Text,
    Array,
    Map,
    Tag,
    Simple,
}

impl DeepView for MajorType {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

/// Semantic payload carried by a decoded CBOR head.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum CborHeadValue {
    Argument(u64),
    Indefinite,
    Simple(u8),
    Float(CborFloat),
    Break,
}

impl DeepView for CborHeadValue {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

/// A normalized CBOR initial byte and its optional argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub struct CborHead {
    pub major: MajorType,
    pub value: CborHeadValue,
}

impl DeepView for CborHead {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[verifier::allow_in_spec]
pub fn major_from_code(code: u8) -> MajorType
    returns
        (match code {
            0 => MajorType::Unsigned,
            1 => MajorType::Negative,
            2 => MajorType::Bytes,
            3 => MajorType::Text,
            4 => MajorType::Array,
            5 => MajorType::Map,
            6 => MajorType::Tag,
            _ => MajorType::Simple,
        }),
{
    match code {
        0 => MajorType::Unsigned,
        1 => MajorType::Negative,
        2 => MajorType::Bytes,
        3 => MajorType::Text,
        4 => MajorType::Array,
        5 => MajorType::Map,
        6 => MajorType::Tag,
        _ => MajorType::Simple,
    }
}

#[verifier::allow_in_spec]
pub fn major_code(major: MajorType) -> u8
    returns
        (match major {
            MajorType::Unsigned => 0u8,
            MajorType::Negative => 1u8,
            MajorType::Bytes => 2u8,
            MajorType::Text => 3u8,
            MajorType::Array => 4u8,
            MajorType::Map => 5u8,
            MajorType::Tag => 6u8,
            MajorType::Simple => 7u8,
        }),
{
    match major {
        MajorType::Unsigned => 0u8,
        MajorType::Negative => 1u8,
        MajorType::Bytes => 2u8,
        MajorType::Text => 3u8,
        MajorType::Array => 4u8,
        MajorType::Map => 5u8,
        MajorType::Tag => 6u8,
        MajorType::Simple => 7u8,
    }
}

#[verifier::allow_in_spec]
pub fn valid_simple(value: u8) -> bool
    returns
        (value <= 23u8 || value >= 32u8),
{
    value <= 23u8 || value >= 32u8
}

#[verifier::allow_in_spec]
pub fn valid_head<const DET: bool>(head: CborHead) -> bool
    returns
        (match head.value {
            CborHeadValue::Argument(_) => head.major != MajorType::Simple,
            CborHeadValue::Indefinite => !DET && {
                head.major == MajorType::Bytes || head.major == MajorType::Text || head.major
                    == MajorType::Array || head.major == MajorType::Map
            },
            CborHeadValue::Simple(value) => head.major == MajorType::Simple && valid_simple(value),
            CborHeadValue::Float(_) => head.major == MajorType::Simple,
            CborHeadValue::Break => head.major == MajorType::Simple,
        }),
{
    match head.value {
        CborHeadValue::Argument(_) => head.major != MajorType::Simple,
        CborHeadValue::Indefinite => !DET && {
            head.major == MajorType::Bytes || head.major == MajorType::Text || head.major
                == MajorType::Array || head.major == MajorType::Map
        },
        CborHeadValue::Simple(value) => head.major == MajorType::Simple && valid_simple(value),
        CborHeadValue::Float(_) => head.major == MajorType::Simple,
        CborHeadValue::Break => head.major == MajorType::Simple,
    }
}

#[verifier::allow_in_spec]
pub fn minimal_u8_argument(value: u8) -> bool
    returns
        (value >= 24u8),
{
    value >= 24u8
}

#[verifier::allow_in_spec]
pub fn minimal_u16_argument(value: u16) -> bool
    returns
        (value > u8::MAX as u16),
{
    value > u8::MAX as u16
}

#[verifier::allow_in_spec]
pub fn minimal_u32_argument(value: u32) -> bool
    returns
        (value > u16::MAX as u32),
{
    value > u16::MAX as u32
}

#[verifier::allow_in_spec]
pub fn minimal_u64_argument(value: u64) -> bool
    returns
        (value > u32::MAX as u64),
{
    value > u32::MAX as u64
}

type HeadWireValue = Sum<(), Sum<u8, Sum<u16, Sum<u32, Sum<u64, Sum<(), Never>>>>>>;

type HeadBranchesFmt = Sum<Empty, Sum<U8, Sum<U16Be, Sum<U32Be, Sum<U64Be, Sum<Empty, Void>>>>>>;

type HeadWireFmt<const DET: bool> = Bind<CborInitialFmt, spec_fn(CborInitial) -> HeadBranchesFmt>;

type RefinedHeadWireFmt<const DET: bool> = Refined<
    HeadWireFmt<DET>,
    PredFnSpec<(CborInitial, HeadWireValue)>,
>;

type HeadMappedFmt<const DET: bool> = Mapped<RefinedHeadWireFmt<DET>, HeadMapper<DET>>;

pub open spec fn head_wire<const DET: bool>() -> HeadWireFmt<DET> {
    Bind(
        CborInitialFmt,
        |initial: CborInitial|
            {
                let major = major_from_code(initial.major);
                match initial.additional {
                    ai if ai <= 23u8 => L(Empty),
                    24u8 => R(L(U8)),
                    25u8 => R(R(L(U16Be))),
                    26u8 => R(R(R(L(U32Be)))),
                    27u8 => R(R(R(R(L(U64Be))))),
                    31u8 if major == MajorType::Bytes || major == MajorType::Text || major
                        == MajorType::Array || major == MajorType::Map || major
                        == MajorType::Simple => R(R(R(R(R(L(Empty)))))),
                    _ => R(R(R(R(R(R(Void("Reserved or invalid CBOR additional information"))))))),
                }
            },
    )
}

pub open spec fn valid_head_wire<const DET: bool>(wire: (CborInitial, HeadWireValue)) -> bool {
    let major = major_from_code(wire.0.major);
    match wire.1 {
        L(()) => true,
        R(L(value)) => {
            if major == MajorType::Simple {
                value >= 32u8
            } else {
                DET ==> minimal_u8_argument(value)
            }
        },
        R(R(L(value))) => major == MajorType::Simple || (DET ==> minimal_u16_argument(value)),
        R(R(R(L(value)))) => major == MajorType::Simple || (DET ==> minimal_u32_argument(value)),
        R(R(R(R(L(value))))) => major == MajorType::Simple || (DET ==> minimal_u64_argument(value)),
        R(R(R(R(R(L(())))))) => major == MajorType::Simple || !DET,
        _ => false,
    }
}

pub open spec fn decode_head_wire(wire: (CborInitial, HeadWireValue)) -> CborHead {
    let (initial, rest) = wire;
    let major = major_from_code(initial.major);
    let ai = initial.additional;
    let value = match rest {
        L(()) => {
            if major == MajorType::Simple {
                CborHeadValue::Simple(ai)
            } else {
                CborHeadValue::Argument(ai as u64)
            }
        },
        R(L(value)) => {
            if major == MajorType::Simple {
                CborHeadValue::Simple(value)
            } else {
                CborHeadValue::Argument(value as u64)
            }
        },
        R(R(L(value))) => {
            if major == MajorType::Simple {
                CborHeadValue::Float(CborFloat::F16(value))
            } else {
                CborHeadValue::Argument(value as u64)
            }
        },
        R(R(R(L(value)))) => {
            if major == MajorType::Simple {
                CborHeadValue::Float(CborFloat::F32(value))
            } else {
                CborHeadValue::Argument(value as u64)
            }
        },
        R(R(R(R(L(value))))) => {
            if major == MajorType::Simple {
                CborHeadValue::Float(CborFloat::F64(value))
            } else {
                CborHeadValue::Argument(value)
            }
        },
        R(R(R(R(R(L(())))))) => {
            if major == MajorType::Simple {
                CborHeadValue::Break
            } else {
                CborHeadValue::Indefinite
            }
        },
        _ => arbitrary(),
    };
    CborHead { major, value }
}

pub open spec fn encode_head_wire(head: CborHead) -> (CborInitial, HeadWireValue) {
    let major = major_code(head.major);
    match head.value {
        CborHeadValue::Argument(value) => {
            if value <= 23u64 {
                (CborInitial { major, additional: value as u8 }, L(()))
            } else if value <= u8::MAX as u64 {
                (CborInitial { major, additional: 24u8 }, R(L(value as u8)))
            } else if value <= u16::MAX as u64 {
                (CborInitial { major, additional: 25u8 }, R(R(L(value as u16))))
            } else if value <= u32::MAX as u64 {
                (CborInitial { major, additional: 26u8 }, R(R(R(L(value as u32)))))
            } else {
                (CborInitial { major, additional: 27u8 }, R(R(R(R(L(value))))))
            }
        },
        CborHeadValue::Indefinite => (
            CborInitial { major, additional: 31u8 },
            R(R(R(R(R(L(())))))),
        ),
        CborHeadValue::Simple(value) => {
            if value <= 23u8 {
                (CborInitial { major, additional: value }, L(()))
            } else {
                (CborInitial { major, additional: 24u8 }, R(L(value)))
            }
        },
        CborHeadValue::Float(CborFloat::F16(value)) => {
            (CborInitial { major, additional: 25u8 }, R(R(L(value))))
        },
        CborHeadValue::Float(CborFloat::F32(value)) => {
            (CborInitial { major, additional: 26u8 }, R(R(R(L(value)))))
        },
        CborHeadValue::Float(CborFloat::F64(value)) => {
            (CborInitial { major, additional: 27u8 }, R(R(R(R(L(value))))))
        },
        CborHeadValue::Break => (CborInitial { major, additional: 31u8 }, R(R(R(R(R(L(()))))))),
    }
}

#[derive(Clone, Copy)]
pub struct HeadMapper<const DET: bool>;

impl<const DET: bool> SpecMapper for HeadMapper<DET> {
    type In = (CborInitial, HeadWireValue);

    type Out = CborHead;

    open spec fn spec_map(&self, wire: Self::In) -> Self::Out {
        decode_head_wire(wire)
    }

    open spec fn spec_map_rev(&self, head: Self::Out) -> Self::In {
        encode_head_wire(head)
    }

    open spec fn wf_in(&self, wire: Self::In) -> bool {
        &&& head_wire::<DET>().consistent(wire)
        &&& valid_head_wire::<DET>(wire)
    }

    open spec fn wf_out(&self, head: Self::Out) -> bool {
        valid_head::<DET>(head)
    }
}

impl<const DET: bool> LossyMapper for HeadMapper<DET> {
    proof fn lemma_sound_mapper(&self, head: Self::Out) {
        match head.value {
            CborHeadValue::Argument(value) => {
                if value <= 23u64 {
                    assert((value as u8) as u64 == value) by (bit_vector)
                        requires
                            value <= 23u64,
                    ;
                } else if value <= u8::MAX as u64 {
                    assert((value as u8) as u64 == value) by (bit_vector)
                        requires
                            value <= u8::MAX as u64,
                    ;
                } else if value <= u16::MAX as u64 {
                    assert((value as u16) as u64 == value) by (bit_vector)
                        requires
                            value <= u16::MAX as u64,
                    ;
                } else if value <= u32::MAX as u64 {
                    assert((value as u32) as u64 == value) by (bit_vector)
                        requires
                            value <= u32::MAX as u64,
                    ;
                }
            },
            _ => {},
        }
    }

    proof fn lemma_mapper_wf_out_in(&self, head: Self::Out) {
    }
}

impl LosslessMapper for HeadMapper<true> {
    proof fn lemma_lossless_mapper(&self, wire: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, wire: Self::In) {
    }
}

pub open spec fn cbor_head_fmt<const DET: bool>() -> HeadMappedFmt<DET> {
    Mapped {
        inner: Refined(
            head_wire::<DET>(),
            |wire: (CborInitial, HeadWireValue)| valid_head_wire::<DET>(wire),
        ),
        mapper: HeadMapper::<DET>,
    }
}

/// One normalized CBOR head.
///
/// `DET = true` rejects nonminimal integer, length, and tag arguments and
/// rejects indefinite-length heads. Floating-point payload widths remain an
/// explicit part of [`CborFloat`] and are not shortened here.
#[derive(Debug, Clone, Copy)]
pub struct CborHeadFmt<const DET: bool>;

pub type BreakFmt = Const<U8, u8>;

/// The CBOR break stop code (`0xff`).
pub const BREAK: BreakFmt = Const(U8, 0xffu8);

impl<'i, const DET: bool> Parser<&'i [u8]> for CborHeadFmt<DET> {
    type PT = CborHead;

    fn parse(&self, input: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let (n1, initial) = CborInitialFmt.parse(input)?;
        let major = major_from_code(initial.major);
        let ai = initial.additional;
        let rest = input.skip(n1);

        match ai {
            0..=23 => {
                let value = if major == MajorType::Simple {
                    CborHeadValue::Simple(ai)
                } else {
                    CborHeadValue::Argument(ai as u64)
                };
                Ok((1, CborHead { major, value }))
            },
            24 => {
                let (_, value) = U8.parse(&rest)?;
                if major == MajorType::Simple {
                    if value < 32 {
                        Err(ParseError::invalid_tag())
                    } else {
                        Ok((2, CborHead { major, value: CborHeadValue::Simple(value) }))
                    }
                } else if DET && !minimal_u8_argument(value) {
                    Err(ParseError::non_canonical())
                } else {
                    Ok((2, CborHead { major, value: CborHeadValue::Argument(value as u64) }))
                }
            },
            25 => {
                let (_, value) = U16Be.parse(&rest)?;
                if major == MajorType::Simple {
                    Ok((3, CborHead { major, value: CborHeadValue::Float(CborFloat::F16(value)) }))
                } else if DET && !minimal_u16_argument(value) {
                    Err(ParseError::non_canonical())
                } else {
                    Ok((3, CborHead { major, value: CborHeadValue::Argument(value as u64) }))
                }
            },
            26 => {
                let (_, value) = U32Be.parse(&rest)?;
                if major == MajorType::Simple {
                    Ok((5, CborHead { major, value: CborHeadValue::Float(CborFloat::F32(value)) }))
                } else if DET && !minimal_u32_argument(value) {
                    Err(ParseError::non_canonical())
                } else {
                    Ok((5, CborHead { major, value: CborHeadValue::Argument(value as u64) }))
                }
            },
            27 => {
                let (_, value) = U64Be.parse(&rest)?;
                if major == MajorType::Simple {
                    Ok((9, CborHead { major, value: CborHeadValue::Float(CborFloat::F64(value)) }))
                } else if DET && !minimal_u64_argument(value) {
                    Err(ParseError::non_canonical())
                } else {
                    Ok((9, CborHead { major, value: CborHeadValue::Argument(value) }))
                }
            },
            31 => {
                if !DET && (major == MajorType::Bytes || major == MajorType::Text || major
                    == MajorType::Array || major == MajorType::Map) {
                    Ok((1, CborHead { major, value: CborHeadValue::Indefinite }))
                } else if major == MajorType::Simple {
                    Ok((1, CborHead { major, value: CborHeadValue::Break }))
                } else {
                    Err(ParseError::invalid_tag())
                }
            },
            _ => Err(ParseError::invalid_tag()),
        }
    }
}

impl<Output: OutputBuf, const DET: bool> Serializer<Output, CborHead> for CborHeadFmt<DET> {
    fn serialize_into(&self, head: &CborHead, out: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        let ghost old_out = out@;
        let major = major_code(head.major);
        match head.value {
            CborHeadValue::Argument(value) => {
                if value <= 23 {
                    CborInitialFmt.serialize_into(
                        &CborInitial { major, additional: value as u8 },
                        out,
                    );
                } else if value <= u8::MAX as u64 {
                    CborInitialFmt.serialize_into(&CborInitial { major, additional: 24 }, out);
                    U8.serialize_into(&(value as u8), out);
                } else if value <= u16::MAX as u64 {
                    CborInitialFmt.serialize_into(&CborInitial { major, additional: 25 }, out);
                    U16Be.serialize_into(&(value as u16), out);
                } else if value <= u32::MAX as u64 {
                    CborInitialFmt.serialize_into(&CborInitial { major, additional: 26 }, out);
                    U32Be.serialize_into(&(value as u32), out);
                } else {
                    CborInitialFmt.serialize_into(&CborInitial { major, additional: 27 }, out);
                    U64Be.serialize_into(&value, out);
                }
            },
            CborHeadValue::Indefinite => {
                CborInitialFmt.serialize_into(&CborInitial { major, additional: 31 }, out);
            },
            CborHeadValue::Simple(value) => {
                if value <= 23 {
                    CborInitialFmt.serialize_into(&CborInitial { major, additional: value }, out);
                } else {
                    CborInitialFmt.serialize_into(&CborInitial { major, additional: 24 }, out);
                    U8.serialize_into(&value, out);
                }
            },
            CborHeadValue::Float(CborFloat::F16(value)) => {
                CborInitialFmt.serialize_into(&CborInitial { major, additional: 25 }, out);
                U16Be.serialize_into(&value, out);
            },
            CborHeadValue::Float(CborFloat::F32(value)) => {
                CborInitialFmt.serialize_into(&CborInitial { major, additional: 26 }, out);
                U32Be.serialize_into(&value, out);
            },
            CborHeadValue::Float(CborFloat::F64(value)) => {
                CborInitialFmt.serialize_into(&CborInitial { major, additional: 27 }, out);
                U64Be.serialize_into(&value, out);
            },
            CborHeadValue::Break => {
                CborInitialFmt.serialize_into(
                    &CborInitial { major: major_code(MajorType::Simple), additional: 31 },
                    out,
                );
            },
        }

        assert(out@ =~= old_out + self.spec_serialize(head.deep_view()));
    }
}

pub fn head_len<const DET: bool>(head: &CborHead) -> (len: usize)
    ensures
        len == CborHeadFmt::<DET>.byte_len(head.deep_view()),
{
    let len = match head.value {
        CborHeadValue::Argument(value) => {
            if value <= 23 {
                1
            } else if value <= u8::MAX as u64 {
                2
            } else if value <= u16::MAX as u64 {
                3
            } else if value <= u32::MAX as u64 {
                5
            } else {
                9
            }
        },
        CborHeadValue::Indefinite => 1,
        CborHeadValue::Simple(value) => if value <= 23 {
            1
        } else {
            2
        },
        CborHeadValue::Float(CborFloat::F16(_)) => 3,
        CborHeadValue::Float(CborFloat::F32(_)) => 5,
        CborHeadValue::Float(CborFloat::F64(_)) => 9,
        CborHeadValue::Break => 1,
    };
    len
}

impl<const DET: bool> Prepare<CborHead> for CborHeadFmt<DET> {
    fn prepare(&self, head: &CborHead) -> Result<usize, PreSerializeError> {
        if !valid_head::<DET>(*head) {
            Err(PreSerializeError::custom("Invalid CBOR head"))
        } else {
            let len = head_len::<DET>(head);
            Ok(len)
        }
    }
}

impl<const DET: bool> ByteLen<CborHead> for CborHeadFmt<DET> {
    fn length(&self, head: &CborHead) -> usize {
        head_len::<DET>(head)
    }
}

mod derived_specs {
    use super::*;

    impl SpecParser for CborInitialFmt {
        type PVal = CborInitial;

        open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
            cbor_initial_fmt().spec_parse(input)
        }
    }

    impl Consistency for CborInitialFmt {
        type Val = CborInitial;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            cbor_initial_fmt().consistent(value)
        }
    }

    impl SpecSerializerDps for CborInitialFmt {
        type SValue = CborInitial;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, out: Seq<u8>) -> Seq<u8> {
            cbor_initial_fmt().spec_serialize_dps(value, out)
        }
    }

    impl SpecSerializer for CborInitialFmt {
        type SVal = CborInitial;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            cbor_initial_fmt().spec_serialize(value)
        }
    }

    impl SpecByteLen for CborInitialFmt {
        type T = CborInitial;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            cbor_initial_fmt().byte_len(value)
        }
    }

    impl<const DET: bool> SpecParser for CborHeadFmt<DET> {
        type PVal = CborHead;

        open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
            cbor_head_fmt::<DET>().spec_parse(input)
        }
    }

    impl<const DET: bool> Consistency for CborHeadFmt<DET> {
        type Val = CborHead;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            cbor_head_fmt::<DET>().consistent(value)
        }
    }

    impl<const DET: bool> SpecSerializerDps for CborHeadFmt<DET> {
        type SValue = CborHead;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, out: Seq<u8>) -> Seq<u8> {
            cbor_head_fmt::<DET>().spec_serialize_dps(value, out)
        }
    }

    impl<const DET: bool> SpecSerializer for CborHeadFmt<DET> {
        type SVal = CborHead;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            cbor_head_fmt::<DET>().spec_serialize(value)
        }
    }

    impl<const DET: bool> SpecByteLen for CborHeadFmt<DET> {
        type T = CborHead;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            cbor_head_fmt::<DET>().byte_len(value)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl SafeParser for CborInitialFmt {
        proof fn lemma_parse_safe(&self, input: Seq<u8>) {
            cbor_initial_fmt().lemma_parse_safe(input);
        }
    }

    impl Productive for CborInitialFmt {
        proof fn lemma_productive(&self, input: Seq<u8>) {
            cbor_initial_fmt().lemma_productive(input);
        }
    }

    impl SoundParser for CborInitialFmt {
        proof fn lemma_parse_sound_consumption(&self, input: Seq<u8>) {
            broadcast use lemma_initial_unpack_pack, lemma_initial_unpack_in_bounds;

            let fmt = cbor_initial_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(input);
        }

        proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
            broadcast use lemma_initial_unpack_pack, lemma_initial_unpack_in_bounds;

            let fmt = cbor_initial_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(input);
        }
    }

    impl NonTailFmt for CborInitialFmt {
        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, out: Seq<u8>) {
            cbor_initial_fmt().lemma_serialize_dps_prepend(value, out);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, out: Seq<u8>) {
            cbor_initial_fmt().lemma_serialize_dps_len(value, out);
        }
    }

    impl GoodSerializer for CborInitialFmt {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            cbor_initial_fmt().lemma_serialize_len(value);
        }
    }

    impl SPRoundTripDps for CborInitialFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, out: Seq<u8>) {
            broadcast use lemma_initial_pack_unpack;

            let fmt = cbor_initial_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(value, out);
        }
    }

    impl NonMalleable for CborInitialFmt {
        proof fn lemma_parse_non_malleable(&self, left: Seq<u8>, right: Seq<u8>) {
            broadcast use lemma_initial_unpack_pack, lemma_initial_unpack_in_bounds;

            cbor_initial_fmt().lemma_parse_non_malleable(left, right);
        }
    }

    impl NoLookAhead for CborInitialFmt {
        proof fn lemma_no_lookahead(&self, left: Seq<u8>, right: Seq<u8>) {
            cbor_initial_fmt().lemma_no_lookahead(left, right);
        }
    }

    impl EquivSerializersGeneral for CborInitialFmt {
        proof fn lemma_serialize_equiv(&self, value: Self::SVal, out: Seq<u8>) {
            cbor_initial_fmt().lemma_serialize_equiv(value, out);
        }
    }

    impl EquivSerializers for CborInitialFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            cbor_initial_fmt().lemma_serialize_equiv_on_empty(value);
        }
    }

    impl<const DET: bool> SafeParser for CborHeadFmt<DET> {
        proof fn lemma_parse_safe(&self, input: Seq<u8>) {
            cbor_head_fmt::<DET>().lemma_parse_safe(input);
        }
    }

    impl<const DET: bool> Productive for CborHeadFmt<DET> {
        proof fn lemma_productive(&self, input: Seq<u8>) {
            cbor_head_fmt::<DET>().lemma_productive(input);
        }
    }

    impl SoundParser for CborHeadFmt<true> {
        proof fn lemma_parse_sound_consumption(&self, input: Seq<u8>) {
            cbor_head_fmt::<true>().lemma_parse_sound_consumption(input);
        }

        proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
            cbor_head_fmt::<true>().lemma_parse_sound_value(input);
        }
    }

    impl<const DET: bool> GoodSerializer for CborHeadFmt<DET> {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            cbor_head_fmt::<DET>().lemma_serialize_len(value);
        }
    }

    impl<const DET: bool> NonTailFmt for CborHeadFmt<DET> {
        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, out: Seq<u8>) {
            cbor_head_fmt::<DET>().lemma_serialize_dps_prepend(value, out);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, out: Seq<u8>) {
            cbor_head_fmt::<DET>().lemma_serialize_dps_len(value, out);
        }
    }

    impl<const DET: bool> SPRoundTripDps for CborHeadFmt<DET> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, out: Seq<u8>) {
            cbor_head_fmt::<DET>().theorem_serialize_dps_parse_roundtrip(value, out);
        }
    }

    impl NonMalleable for CborHeadFmt<true> {
        proof fn lemma_parse_non_malleable(&self, left: Seq<u8>, right: Seq<u8>) {
            cbor_head_fmt::<true>().lemma_parse_non_malleable(left, right);
        }
    }

    impl<const DET: bool> NoLookAhead for CborHeadFmt<DET> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            cbor_head_fmt::<DET>().lemma_no_lookahead(i1, i2);
        }
    }

    impl<const DET: bool> EquivSerializersGeneral for CborHeadFmt<DET> {
        proof fn lemma_serialize_equiv(&self, value: Self::SVal, out: Seq<u8>) {
            cbor_head_fmt::<DET>().lemma_serialize_equiv(value, out);
        }
    }

    impl<const DET: bool> EquivSerializers for CborHeadFmt<DET> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            cbor_head_fmt::<DET>().lemma_serialize_equiv_on_empty(value);
        }
    }

}

} // verus!
