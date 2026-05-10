use super::spec::*;
use crate::combinators::bytes::spec::*;
use crate::combinators::Fixed;
use crate::core::exec::input::InputSlice;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::Serializer,
    ParseError,
};
use crate::core::spec::{SpecParser, SpecSerializer};
use vstd::prelude::*;

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

impl Serializer<u8> for super::U8 {
    fn ex_serialize(&self, v: u8, obuf: &mut Vec<u8>) {
        obuf.push(v);
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

impl Serializer<u16> for super::U16Le {
    fn ex_serialize(&self, v: u16, obuf: &mut Vec<u8>) {
        let bytes = u16_to_le_bytes(v);

        obuf.extend_from_slice(&bytes);
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

impl Serializer<u16> for super::U16Be {
    fn ex_serialize(&self, v: u16, obuf: &mut Vec<u8>) {
        let bytes = u16_to_be_bytes(v);
        obuf.extend_from_slice(&bytes);
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

impl Serializer<u32> for super::U32Le {
    fn ex_serialize(&self, v: u32, obuf: &mut Vec<u8>) {
        let bytes = u32_to_le_bytes(v);
        obuf.extend_from_slice(&bytes);
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

impl Serializer<u32> for super::U32Be {
    fn ex_serialize(&self, v: u32, obuf: &mut Vec<u8>) {
        let bytes = u32_to_be_bytes(v);
        obuf.extend_from_slice(&bytes);
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

impl Serializer<u64> for super::U64Le {
    fn ex_serialize(&self, v: u64, obuf: &mut Vec<u8>) {
        let bytes = u64_to_le_bytes(v);
        obuf.extend_from_slice(&bytes);
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

impl Serializer<u64> for super::U64Be {
    fn ex_serialize(&self, v: u64, obuf: &mut Vec<u8>) {
        let bytes = u64_to_be_bytes(v);
        obuf.extend_from_slice(&bytes);
    }
}

} // verus!
