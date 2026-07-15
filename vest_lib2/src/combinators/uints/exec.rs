use super::spec::*;
use crate::combinators::bytes::spec::*;
use crate::combinators::Fixed;
use crate::core::exec::input::InputSlice;
use crate::core::exec::output::*;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, ComplianceErrorKind, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::spec::{SpecParser, SpecSerializer};
use vstd::prelude::*;
use OutputBuf;

verus! {

#[verifier::external_body]
#[inline(always)]
pub fn u16_from_le_bytes(bytes: [u8; 2]) -> (out: u16)
    ensures
        out == u16_le_from_bytes(bytes),
{
    u16::from_le_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn u16_from_be_bytes(bytes: [u8; 2]) -> (out: u16)
    ensures
        out == u16_be_from_bytes(bytes),
{
    u16::from_be_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn u16_to_le_bytes(value: u16) -> (bytes: [u8; 2])
    ensures
        bytes == u16_le_to_bytes(value),
{
    value.to_le_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn u16_to_be_bytes(value: u16) -> (bytes: [u8; 2])
    ensures
        bytes == u16_be_to_bytes(value),
{
    value.to_be_bytes()
}

#[inline(always)]
pub fn u24_from_le_bytes(bytes: [u8; 3]) -> (out: u32)
    ensures
        out == u24_le_from_bytes(bytes),
{
    (bytes[0] as u32) | ((bytes[1] as u32) << 8) | ((bytes[2] as u32) << 16)
}

#[inline(always)]
pub fn u24_from_be_bytes(bytes: [u8; 3]) -> (out: u32)
    ensures
        out == u24_be_from_bytes(bytes),
{
    ((bytes[0] as u32) << 16) | ((bytes[1] as u32) << 8) | (bytes[2] as u32)
}

#[inline(always)]
pub fn u24_to_le_bytes(value: u32) -> (bytes: [u8; 3])
    ensures
        bytes == u24_le_to_bytes(value),
{
    [(value & 0xff) as u8, ((value >> 8) & 0xff) as u8, ((value >> 16) & 0xff) as u8]
}

#[inline(always)]
pub fn u24_to_be_bytes(value: u32) -> (bytes: [u8; 3])
    ensures
        bytes == u24_be_to_bytes(value),
{
    [((value >> 16) & 0xff) as u8, ((value >> 8) & 0xff) as u8, (value & 0xff) as u8]
}

#[verifier::external_body]
#[inline(always)]
pub fn u32_from_le_bytes(bytes: [u8; 4]) -> (out: u32)
    ensures
        out == u32_le_from_bytes(bytes),
{
    u32::from_le_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn u32_from_be_bytes(bytes: [u8; 4]) -> (out: u32)
    ensures
        out == u32_be_from_bytes(bytes),
{
    u32::from_be_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn u32_to_le_bytes(value: u32) -> (bytes: [u8; 4])
    ensures
        bytes == u32_le_to_bytes(value),
{
    value.to_le_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn u32_to_be_bytes(value: u32) -> (bytes: [u8; 4])
    ensures
        bytes == u32_be_to_bytes(value),
{
    value.to_be_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn u64_from_le_bytes(bytes: [u8; 8]) -> (out: u64)
    ensures
        out == u64_le_from_bytes(bytes),
{
    u64::from_le_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn u64_from_be_bytes(bytes: [u8; 8]) -> (out: u64)
    ensures
        out == u64_be_from_bytes(bytes),
{
    u64::from_be_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn u64_to_le_bytes(value: u64) -> (bytes: [u8; 8])
    ensures
        bytes == u64_le_to_bytes(value),
{
    value.to_le_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn u64_to_be_bytes(value: u64) -> (bytes: [u8; 8])
    ensures
        bytes == u64_be_to_bytes(value),
{
    value.to_be_bytes()
}

impl Parser<&[u8]> for super::U8 {
    type PT = u8;

    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        if ibuf.len() < 1 {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((1, ibuf[0]))
        }
    }
}

impl<Output: OutputBuf> Serializer<Output, u8> for super::U8 {
    fn serialize_into(&self, v: &u8, obuf: &mut Output) {
        obuf.write_byte(*v);
    }
}

impl ByteLen<u8> for super::U8 {
    fn length(&self, _v: &u8) -> (len: usize) {
        1
    }
}

impl Prepare<u8> for super::U8 {
    fn prepare(&self, _v: &u8) -> (checked: Result<usize, PreSerializeError>) {
        Ok(1)
    }
}

impl Parser<&[u8]> for super::U16Le {
    type PT = u16;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U16_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U16_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1]];
        let value = u16_from_le_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, u16> for super::U16Le {
    fn serialize_into(&self, v: &u16, obuf: &mut Output) {
        let bytes = u16_to_le_bytes(*v);

        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<u16> for super::U16Le {
    fn length(&self, _v: &u16) -> (len: usize) {
        U16_BYTE_LEN
    }
}

impl Prepare<u16> for super::U16Le {
    fn prepare(&self, _v: &u16) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U16_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::U16Be {
    type PT = u16;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U16_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U16_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1]];
        let value = u16_from_be_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, u16> for super::U16Be {
    fn serialize_into(&self, v: &u16, obuf: &mut Output) {
        let bytes = u16_to_be_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<u16> for super::U16Be {
    fn length(&self, _v: &u16) -> (len: usize) {
        U16_BYTE_LEN
    }
}

impl Prepare<u16> for super::U16Be {
    fn prepare(&self, _v: &u16) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U16_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::U24Le {
    type PT = u32;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U24_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U24_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1], chunk[2]];
        let value = u24_from_le_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, u32> for super::U24Le {
    fn serialize_into(&self, v: &u32, obuf: &mut Output) {
        let bytes = u24_to_le_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<u32> for super::U24Le {
    fn length(&self, _v: &u32) -> (len: usize) {
        U24_BYTE_LEN
    }
}

impl Prepare<u32> for super::U24Le {
    fn prepare(&self, v: &u32) -> (checked: Result<usize, PreSerializeError>) {
        if *v < 0x01000000 {
            Ok(U24_BYTE_LEN)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
        }
    }
}

impl Parser<&[u8]> for super::U24Be {
    type PT = u32;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U24_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U24_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1], chunk[2]];
        let value = u24_from_be_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, u32> for super::U24Be {
    fn serialize_into(&self, v: &u32, obuf: &mut Output) {
        let bytes = u24_to_be_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<u32> for super::U24Be {
    fn length(&self, _v: &u32) -> (len: usize) {
        U24_BYTE_LEN
    }
}

impl Prepare<u32> for super::U24Be {
    fn prepare(&self, v: &u32) -> (checked: Result<usize, PreSerializeError>) {
        if *v < 0x01000000 {
            Ok(U24_BYTE_LEN)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
        }
    }
}

impl Parser<&[u8]> for super::U32Le {
    type PT = u32;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U32_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U32_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1], chunk[2], chunk[3]];
        let value = u32_from_le_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, u32> for super::U32Le {
    fn serialize_into(&self, v: &u32, obuf: &mut Output) {
        let bytes = u32_to_le_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<u32> for super::U32Le {
    fn length(&self, _v: &u32) -> (len: usize) {
        U32_BYTE_LEN
    }
}

impl Prepare<u32> for super::U32Le {
    fn prepare(&self, _v: &u32) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U32_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::U32Be {
    type PT = u32;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U32_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U32_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1], chunk[2], chunk[3]];
        let value = u32_from_be_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, u32> for super::U32Be {
    fn serialize_into(&self, v: &u32, obuf: &mut Output) {
        let bytes = u32_to_be_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<u32> for super::U32Be {
    fn length(&self, _v: &u32) -> (len: usize) {
        U32_BYTE_LEN
    }
}

impl Prepare<u32> for super::U32Be {
    fn prepare(&self, _v: &u32) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U32_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::U64Le {
    type PT = u64;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U64_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U64_BYTE_LEN as int));

        let bytes = [
            chunk[0],
            chunk[1],
            chunk[2],
            chunk[3],
            chunk[4],
            chunk[5],
            chunk[6],
            chunk[7],
        ];
        let value = u64_from_le_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, u64> for super::U64Le {
    fn serialize_into(&self, v: &u64, obuf: &mut Output) {
        let bytes = u64_to_le_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<u64> for super::U64Le {
    fn length(&self, _v: &u64) -> (len: usize) {
        U64_BYTE_LEN
    }
}

impl Prepare<u64> for super::U64Le {
    fn prepare(&self, _v: &u64) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U64_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::U64Be {
    type PT = u64;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U64_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U64_BYTE_LEN as int));

        let bytes = [
            chunk[0],
            chunk[1],
            chunk[2],
            chunk[3],
            chunk[4],
            chunk[5],
            chunk[6],
            chunk[7],
        ];
        let value = u64_from_be_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, u64> for super::U64Be {
    fn serialize_into(&self, v: &u64, obuf: &mut Output) {
        let bytes = u64_to_be_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<u64> for super::U64Be {
    fn length(&self, _v: &u64) -> (len: usize) {
        U64_BYTE_LEN
    }
}

impl Prepare<u64> for super::U64Be {
    fn prepare(&self, _v: &u64) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U64_BYTE_LEN)
    }
}

} // verus!
