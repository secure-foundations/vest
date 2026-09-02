//! Executable fixed-width signed integer formats.
use crate::combinators::sints::spec::*;
use crate::combinators::Fixed;
use crate::core::exec::input::InputSlice;
use crate::core::exec::output::*;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use vstd::prelude::*;
use OutputBuf;

verus! {

use crate::combinators::bytes::spec::*;

#[verifier::external_body]
#[inline(always)]
pub fn i16_from_le_bytes(bytes: [u8; 2]) -> (out: i16)
    ensures
        out == i16_le_from_bytes(bytes),
{
    i16::from_le_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn i16_from_be_bytes(bytes: [u8; 2]) -> (out: i16)
    ensures
        out == i16_be_from_bytes(bytes),
{
    i16::from_be_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn i16_to_le_bytes(value: i16) -> (bytes: [u8; 2])
    ensures
        bytes == i16_le_to_bytes(value),
{
    value.to_le_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn i16_to_be_bytes(value: i16) -> (bytes: [u8; 2])
    ensures
        bytes == i16_be_to_bytes(value),
{
    value.to_be_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn i32_from_le_bytes(bytes: [u8; 4]) -> (out: i32)
    ensures
        out == i32_le_from_bytes(bytes),
{
    i32::from_le_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn i32_from_be_bytes(bytes: [u8; 4]) -> (out: i32)
    ensures
        out == i32_be_from_bytes(bytes),
{
    i32::from_be_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn i32_to_le_bytes(value: i32) -> (bytes: [u8; 4])
    ensures
        bytes == i32_le_to_bytes(value),
{
    value.to_le_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn i32_to_be_bytes(value: i32) -> (bytes: [u8; 4])
    ensures
        bytes == i32_be_to_bytes(value),
{
    value.to_be_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn i64_from_le_bytes(bytes: [u8; 8]) -> (out: i64)
    ensures
        out == i64_le_from_bytes(bytes),
{
    i64::from_le_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn i64_from_be_bytes(bytes: [u8; 8]) -> (out: i64)
    ensures
        out == i64_be_from_bytes(bytes),
{
    i64::from_be_bytes(bytes)
}

#[verifier::external_body]
#[inline(always)]
pub fn i64_to_le_bytes(value: i64) -> (bytes: [u8; 8])
    ensures
        bytes == i64_le_to_bytes(value),
{
    value.to_le_bytes()
}

#[verifier::external_body]
#[inline(always)]
pub fn i64_to_be_bytes(value: i64) -> (bytes: [u8; 8])
    ensures
        bytes == i64_be_to_bytes(value),
{
    value.to_be_bytes()
}

impl Parser<&[u8]> for super::I8 {
    type PT = i8;

    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        if ibuf.len() < 1 {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((1, ibuf[0] as i8))
        }
    }
}

impl<Output: OutputBuf> Serializer<Output, i8> for super::I8 {
    fn serialize_into(&self, v: &i8, obuf: &mut Output) {
        obuf.write_byte(*v as u8);
    }
}

impl ByteLen<i8> for super::I8 {
    fn length(&self, _v: &i8) -> (len: usize) {
        U8_BYTE_LEN
    }
}

impl Prepare<i8> for super::I8 {
    fn prepare(&self, _v: &i8) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U8_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::I16Le {
    type PT = i16;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U16_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U16_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1]];
        let value = i16_from_le_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, i16> for super::I16Le {
    fn serialize_into(&self, v: &i16, obuf: &mut Output) {
        let bytes = i16_to_le_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<i16> for super::I16Le {
    fn length(&self, _v: &i16) -> (len: usize) {
        U16_BYTE_LEN
    }
}

impl Prepare<i16> for super::I16Le {
    fn prepare(&self, _v: &i16) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U16_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::I16Be {
    type PT = i16;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U16_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U16_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1]];
        let value = i16_from_be_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, i16> for super::I16Be {
    fn serialize_into(&self, v: &i16, obuf: &mut Output) {
        let bytes = i16_to_be_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<i16> for super::I16Be {
    fn length(&self, _v: &i16) -> (len: usize) {
        U16_BYTE_LEN
    }
}

impl Prepare<i16> for super::I16Be {
    fn prepare(&self, _v: &i16) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U16_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::I32Le {
    type PT = i32;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U32_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U32_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1], chunk[2], chunk[3]];
        let value = i32_from_le_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, i32> for super::I32Le {
    fn serialize_into(&self, v: &i32, obuf: &mut Output) {
        let bytes = i32_to_le_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<i32> for super::I32Le {
    fn length(&self, _v: &i32) -> (len: usize) {
        U32_BYTE_LEN
    }
}

impl Prepare<i32> for super::I32Le {
    fn prepare(&self, _v: &i32) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U32_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::I32Be {
    type PT = i32;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use lemma_array_from_seq_roundtrip;

        let (n, chunk) = Fixed::<U32_BYTE_LEN>.parse(ibuf)?;
        assert(chunk@ == ibuf@.take(U32_BYTE_LEN as int));

        let bytes = [chunk[0], chunk[1], chunk[2], chunk[3]];
        let value = i32_from_be_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, i32> for super::I32Be {
    fn serialize_into(&self, v: &i32, obuf: &mut Output) {
        let bytes = i32_to_be_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<i32> for super::I32Be {
    fn length(&self, _v: &i32) -> (len: usize) {
        U32_BYTE_LEN
    }
}

impl Prepare<i32> for super::I32Be {
    fn prepare(&self, _v: &i32) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U32_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::I64Le {
    type PT = i64;

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
        let value = i64_from_le_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, i64> for super::I64Le {
    fn serialize_into(&self, v: &i64, obuf: &mut Output) {
        let bytes = i64_to_le_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<i64> for super::I64Le {
    fn length(&self, _v: &i64) -> (len: usize) {
        U64_BYTE_LEN
    }
}

impl Prepare<i64> for super::I64Le {
    fn prepare(&self, _v: &i64) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U64_BYTE_LEN)
    }
}

impl Parser<&[u8]> for super::I64Be {
    type PT = i64;

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
        let value = i64_from_be_bytes(bytes);

        assert(bytes@ == chunk@);

        Ok((n, value))
    }
}

impl<Output: OutputBuf> Serializer<Output, i64> for super::I64Be {
    fn serialize_into(&self, v: &i64, obuf: &mut Output) {
        let bytes = i64_to_be_bytes(*v);
        obuf.write_bytes(&bytes);
    }
}

impl ByteLen<i64> for super::I64Be {
    fn length(&self, _v: &i64) -> (len: usize) {
        U64_BYTE_LEN
    }
}

impl Prepare<i64> for super::I64Be {
    fn prepare(&self, _v: &i64) -> (checked: Result<usize, PreSerializeError>) {
        Ok(U64_BYTE_LEN)
    }
}

} // verus!
