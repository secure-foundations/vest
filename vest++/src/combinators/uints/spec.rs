use crate::combinators::bytes::spec::*;
use crate::combinators::mapped::spec::FnSpecMapper;
use crate::combinators::{Fixed, Mapped};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub const U8_BYTE_LEN: usize = 1;

pub const U16_BYTE_LEN: usize = 2;

pub const U32_BYTE_LEN: usize = 4;

pub type U16LeFmt = Mapped<Fixed<2>, FnSpecMapper<Seq<u8>, u16>>;

pub type U16BeFmt = Mapped<Fixed<2>, FnSpecMapper<Seq<u8>, u16>>;

pub type U32LeFmt = Mapped<Fixed<4>, FnSpecMapper<Seq<u8>, u32>>;

pub type U32BeFmt = Mapped<Fixed<4>, FnSpecMapper<Seq<u8>, u32>>;

pub open spec fn u16_le_fmt() -> U16LeFmt {
    Mapped {
        inner: Fixed::<2>,
        mapper: (|i: Seq<u8>| u16_le_from_bytes(array_from_seq(i)), |o: u16| u16_le_to_bytes(o)@),
    }
}

pub open spec fn u16_be_fmt() -> U16BeFmt {
    Mapped {
        inner: Fixed::<2>,
        mapper: (|i: Seq<u8>| u16_be_from_bytes(array_from_seq(i)), |o: u16| u16_be_to_bytes(o)@),
    }
}

pub open spec fn u32_le_fmt() -> U32LeFmt {
    Mapped {
        inner: Fixed::<4>,
        mapper: (|i: Seq<u8>| u32_le_from_bytes(array_from_seq(i)), |o: u32| u32_le_to_bytes(o)@),
    }
}

pub open spec fn u32_be_fmt() -> U32BeFmt {
    Mapped {
        inner: Fixed::<4>,
        mapper: (|i: Seq<u8>| u32_be_from_bytes(array_from_seq(i)), |o: u32| u32_be_to_bytes(o)@),
    }
}

pub open spec fn u16_le_from_bytes(i: [u8; 2]) -> u16 {
    (i[0] as u16) | (i[1] as u16) << 8
}

pub open spec fn u16_le_to_bytes(o: u16) -> [u8; 2] {
    [(o & 0xff) as u8, ((o >> 8) & 0xff) as u8]
}

pub broadcast proof fn lemma_u16_le_bytes_roundtrip(i: [u8; 2])
    ensures
        #[trigger] u16_le_to_bytes(u16_le_from_bytes(i)) == i,
{
    let x = u16_le_from_bytes(i);
    let i0 = i[0] as u16;
    let i1 = i[1] as u16;
    assert(((x == i0 | i1 << 8) && (i0 < 256) && (i1 < 256)) ==> i0 == (x & 0xff) && i1 == ((x >> 8)
        & 0xff)) by (bit_vector);
}

pub broadcast proof fn lemma_u16_le_value_roundtrip(o: u16)
    ensures
        #[trigger] u16_le_from_bytes(u16_le_to_bytes(o)) == o,
{
    assert({
        &&& o & 0xff < 256
        &&& (o >> 8) & 0xff < 256
    }) by (bit_vector);
    assert(o == ((o & 0xff) | ((o >> 8) & 0xff) << 8)) by (bit_vector);
}

pub open spec fn u16_be_from_bytes(i: [u8; 2]) -> u16 {
    (i[0] as u16) << 8 | (i[1] as u16)
}

pub open spec fn u16_be_to_bytes(o: u16) -> [u8; 2] {
    [((o >> 8) & 0xff) as u8, (o & 0xff) as u8]
}

pub broadcast proof fn lemma_u16_be_bytes_roundtrip(i: [u8; 2])
    ensures
        #[trigger] u16_be_to_bytes(u16_be_from_bytes(i)) == i,
{
    let x = u16_be_from_bytes(i);
    let i0 = i[0] as u16;
    let i1 = i[1] as u16;
    assert(((x == i0 << 8 | i1) && (i0 < 256) && (i1 < 256)) ==> i0 == ((x >> 8) & 0xff) && i1 == (x
        & 0xff)) by (bit_vector);
}

pub broadcast proof fn lemma_u16_be_value_roundtrip(o: u16)
    ensures
        #[trigger] u16_be_from_bytes(u16_be_to_bytes(o)) == o,
{
    assert({
        &&& o & 0xff < 256
        &&& (o >> 8) & 0xff < 256
    }) by (bit_vector);
    assert(o == (((o >> 8) & 0xff) << 8 | (o & 0xff))) by (bit_vector);
}

pub open spec fn u32_le_from_bytes(i: [u8; 4]) -> u32 {
    (i[0] as u32) | (i[1] as u32) << 8 | (i[2] as u32) << 16 | (i[3] as u32) << 24
}

pub open spec fn u32_le_to_bytes(o: u32) -> [u8; 4] {
    [(o & 0xff) as u8, ((o >> 8) & 0xff) as u8, ((o >> 16) & 0xff) as u8, ((o >> 24) & 0xff) as u8]
}

pub broadcast proof fn lemma_u32_le_bytes_roundtrip(i: [u8; 4])
    ensures
        #[trigger] u32_le_to_bytes(u32_le_from_bytes(i)) == i,
{
    let x = u32_le_from_bytes(i);
    let i0 = i[0] as u32;
    let i1 = i[1] as u32;
    let i2 = i[2] as u32;
    let i3 = i[3] as u32;
    assert(((x == i0 | i1 << 8 | i2 << 16 | i3 << 24) && (i0 < 256) && (i1 < 256) && (i2 < 256) && (
    i3 < 256)) ==> i0 == (x & 0xff) && i1 == ((x >> 8) & 0xff) && i2 == ((x >> 16) & 0xff) && i3
        == ((x >> 24) & 0xff)) by (bit_vector);
}

pub broadcast proof fn lemma_u32_le_value_roundtrip(o: u32)
    ensures
        #[trigger] u32_le_from_bytes(u32_le_to_bytes(o)) == o,
{
    assert({
        &&& o & 0xff < 256
        &&& (o >> 8) & 0xff < 256
        &&& (o >> 16) & 0xff < 256
        &&& (o >> 24) & 0xff < 256
    }) by (bit_vector);
    assert(o == ((o & 0xff) | ((o >> 8) & 0xff) << 8 | ((o >> 16) & 0xff) << 16 | ((o >> 24) & 0xff)
        << 24)) by (bit_vector);
}

pub open spec fn u32_be_from_bytes(i: [u8; 4]) -> u32 {
    (i[0] as u32) << 24 | (i[1] as u32) << 16 | (i[2] as u32) << 8 | (i[3] as u32)
}

pub open spec fn u32_be_to_bytes(o: u32) -> [u8; 4] {
    [((o >> 24) & 0xff) as u8, ((o >> 16) & 0xff) as u8, ((o >> 8) & 0xff) as u8, (o & 0xff) as u8]
}

pub broadcast proof fn lemma_u32_be_bytes_roundtrip(i: [u8; 4])
    ensures
        #[trigger] u32_be_to_bytes(u32_be_from_bytes(i)) == i,
{
    let x = u32_be_from_bytes(i);
    let i0 = i[0] as u32;
    let i1 = i[1] as u32;
    let i2 = i[2] as u32;
    let i3 = i[3] as u32;
    assert(((x == i0 << 24 | i1 << 16 | i2 << 8 | i3) && (i0 < 256) && (i1 < 256) && (i2 < 256) && (
    i3 < 256)) ==> i0 == ((x >> 24) & 0xff) && i1 == ((x >> 16) & 0xff) && i2 == ((x >> 8) & 0xff)
        && i3 == (x & 0xff)) by (bit_vector);
}

pub broadcast proof fn lemma_u32_be_value_roundtrip(o: u32)
    ensures
        #[trigger] u32_be_from_bytes(u32_be_to_bytes(o)) == o,
{
    assert({
        &&& o & 0xff < 256
        &&& (o >> 8) & 0xff < 256
        &&& (o >> 16) & 0xff < 256
        &&& (o >> 24) & 0xff < 256
    }) by (bit_vector);
    assert(o == (((o >> 24) & 0xff) << 24 | ((o >> 16) & 0xff) << 16 | ((o >> 8) & 0xff) << 8 | (o
        & 0xff))) by (bit_vector);
}

impl SpecParser for super::U8 {
    type PVal = u8;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u8)> {
        if ibuf.len() >= 1 {
            Some((1, ibuf[0]))
        } else {
            None
        }
    }
}

impl Consistency for super::U8 {
    type Val = u8;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::U8 {
    type ST = u8;

    open spec fn spec_serialize_dps(&self, v: u8, obuf: Seq<u8>) -> Seq<u8> {
        seq![v] + obuf
    }
}

impl SpecSerializer for super::U8 {
    type SVal = u8;

    open spec fn spec_serialize(&self, v: u8) -> Seq<u8> {
        seq![v]
    }
}

impl SafeParser for super::U8 {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }
}

impl SoundParser for super::U8 {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

impl NonTailFmt for super::U8 {
    proof fn lemma_serialize_dps_prepend(&self, v: u8, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == seq![v] + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u8, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf).len() - obuf.len() == 1);
    }
}

impl GoodSerializer for super::U8 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        assert(self.spec_serialize(v).len() == 1);
    }
}

impl SpecByteLen for super::U8 {
    type T = u8;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U8_BYTE_LEN as nat
    }
}

impl StaticByteLen for super::U8 {
    open spec fn static_byte_len() -> nat {
        U8_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::U8 {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U8_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::U16Le {
    type PVal = u16;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u16)> {
        u16_le_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::U16Le {
    type Val = u16;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::U16Le {
    type ST = u16;

    open spec fn spec_serialize_dps(&self, v: u16, obuf: Seq<u8>) -> Seq<u8> {
        u16_le_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U16Le {
    type SVal = u16;

    open spec fn spec_serialize(&self, v: u16) -> Seq<u8> {
        u16_le_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::U16Le {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        u16_le_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::U16Le {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use lemma_u16_le_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u16_le_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use lemma_u16_le_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u16_le_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::U16Le {
    proof fn lemma_serialize_dps_prepend(&self, v: u16, obuf: Seq<u8>) {
        u16_le_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u16, obuf: Seq<u8>) {
        u16_le_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U16Le {
    proof fn lemma_serialize_len(&self, v: u16) {
        u16_le_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::U16Le {
    type T = u16;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U16_BYTE_LEN as nat
    }
}

impl StaticByteLen for super::U16Le {
    open spec fn static_byte_len() -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::U16Le {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::U16Be {
    type PVal = u16;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u16)> {
        u16_be_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::U16Be {
    type Val = u16;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::U16Be {
    type ST = u16;

    open spec fn spec_serialize_dps(&self, v: u16, obuf: Seq<u8>) -> Seq<u8> {
        u16_be_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U16Be {
    type SVal = u16;

    open spec fn spec_serialize(&self, v: u16) -> Seq<u8> {
        u16_be_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::U16Be {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        u16_be_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::U16Be {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use lemma_u16_be_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u16_be_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use lemma_u16_be_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u16_be_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::U16Be {
    proof fn lemma_serialize_dps_prepend(&self, v: u16, obuf: Seq<u8>) {
        u16_be_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u16, obuf: Seq<u8>) {
        u16_be_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U16Be {
    proof fn lemma_serialize_len(&self, v: u16) {
        u16_be_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::U16Be {
    type T = u16;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U16_BYTE_LEN as nat
    }
}

impl StaticByteLen for super::U16Be {
    open spec fn static_byte_len() -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::U16Be {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::U32Le {
    type PVal = u32;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u32)> {
        u32_le_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::U32Le {
    type Val = u32;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::U32Le {
    type ST = u32;

    open spec fn spec_serialize_dps(&self, v: u32, obuf: Seq<u8>) -> Seq<u8> {
        u32_le_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U32Le {
    type SVal = u32;

    open spec fn spec_serialize(&self, v: u32) -> Seq<u8> {
        u32_le_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::U32Le {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        u32_le_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::U32Le {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use lemma_u32_le_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u32_le_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use lemma_u32_le_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u32_le_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::U32Le {
    proof fn lemma_serialize_dps_prepend(&self, v: u32, obuf: Seq<u8>) {
        u32_le_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u32, obuf: Seq<u8>) {
        u32_le_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U32Le {
    proof fn lemma_serialize_len(&self, v: u32) {
        u32_le_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::U32Le {
    type T = u32;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U32_BYTE_LEN as nat
    }
}

impl StaticByteLen for super::U32Le {
    open spec fn static_byte_len() -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::U32Le {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::U32Be {
    type PVal = u32;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u32)> {
        u32_be_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::U32Be {
    type Val = u32;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::U32Be {
    type ST = u32;

    open spec fn spec_serialize_dps(&self, v: u32, obuf: Seq<u8>) -> Seq<u8> {
        u32_be_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U32Be {
    type SVal = u32;

    open spec fn spec_serialize(&self, v: u32) -> Seq<u8> {
        u32_be_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::U32Be {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        u32_be_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::U32Be {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use lemma_u32_be_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u32_be_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use lemma_u32_be_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u32_be_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::U32Be {
    proof fn lemma_serialize_dps_prepend(&self, v: u32, obuf: Seq<u8>) {
        u32_be_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u32, obuf: Seq<u8>) {
        u32_be_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U32Be {
    proof fn lemma_serialize_len(&self, v: u32) {
        u32_be_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::U32Be {
    type T = u32;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U32_BYTE_LEN as nat
    }
}

impl StaticByteLen for super::U32Be {
    open spec fn static_byte_len() -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::U32Be {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

} // verus!
