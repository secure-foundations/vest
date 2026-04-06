use crate::combinators::mapped::spec::{LosslessMapper, LossyMapper, Mapper};
use crate::combinators::{Fixed, Mapped};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub const U8_BYTE_LEN: usize = 1;

pub const U16_BYTE_LEN: usize = 2;

pub const U32_BYTE_LEN: usize = 4;

/// Isomorphic mapper: `[u8; 2]` ↔ `u16` in **little-endian** byte order.
///
/// Forward: `[lo, hi]` → `lo | (hi << 8)`.
/// Reverse: `v` → `[(v & 0xff) as u8, ((v >> 8) & 0xff) as u8]`.
pub struct U16LeMapper;

impl Mapper for U16LeMapper {
    type In = [u8; 2];

    type Out = u16;

    open spec fn spec_map(i: Self::In) -> Self::Out {
        (i[0] as u16) | (i[1] as u16) << 8
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        [(o & 0xff) as u8, ((o >> 8) & 0xff) as u8]
    }
}

impl LossyMapper for U16LeMapper {
    proof fn lemma_sound_mapper(o: Self::Out) {
        assert({
            &&& o & 0xff < 256
            &&& (o >> 8) & 0xff < 256
        }) by (bit_vector);
        assert(o == ((o & 0xff) | ((o >> 8) & 0xff) << 8)) by (bit_vector);
    }
}

impl LosslessMapper for U16LeMapper {
    proof fn lemma_lossless_mapper(i: Self::In) {
        let x = Self::spec_map(i);
        let i0 = i[0] as u16;
        let i1 = i[1] as u16;
        assert(((x == i0 | i1 << 8) && (i0 < 256) && (i1 < 256)) ==> i0 == (x & 0xff) && i1 == ((x
            >> 8) & 0xff)) by (bit_vector);
        assert(Self::spec_map_rev(Self::spec_map(i)) == i);
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
}

/// Isomorphic mapper: `[u8; 2]` ↔ `u16` in **big-endian** byte order.
///
/// Forward: `[hi, lo]` → `(hi << 8) | lo`.
/// Reverse: `v` → `[((v >> 8) & 0xff) as u8, (v & 0xff) as u8]`.
pub struct U16BeMapper;

impl Mapper for U16BeMapper {
    type In = [u8; 2];

    type Out = u16;

    open spec fn spec_map(i: Self::In) -> Self::Out {
        (i[0] as u16) << 8 | (i[1] as u16)
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        [((o >> 8) & 0xff) as u8, (o & 0xff) as u8]
    }
}

impl LossyMapper for U16BeMapper {
    proof fn lemma_sound_mapper(o: Self::Out) {
        assert({
            &&& o & 0xff < 256
            &&& (o >> 8) & 0xff < 256
        }) by (bit_vector);
        assert(o == (((o >> 8) & 0xff) << 8 | (o & 0xff))) by (bit_vector);
    }
}

impl LosslessMapper for U16BeMapper {
    proof fn lemma_lossless_mapper(i: Self::In) {
        let x = Self::spec_map(i);
        let i0 = i[0] as u16;
        let i1 = i[1] as u16;
        assert(((x == i0 << 8 | i1) && (i0 < 256) && (i1 < 256)) ==> i0 == ((x >> 8) & 0xff) && i1
            == (x & 0xff)) by (bit_vector);
        assert(Self::spec_map_rev(Self::spec_map(i)) == i);
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
}

/// Isomorphic mapper: `[u8; 4]` ↔ `u32` in **little-endian** byte order.
///
/// Forward: `[b0, b1, b2, b3]` → `b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)`.
/// Reverse: `v` → `[(v & 0xff) as u8, ((v >> 8) & 0xff) as u8, ((v >> 16) & 0xff) as u8, ((v >> 24) & 0xff) as u8]`.
pub struct U32LeMapper;

impl Mapper for U32LeMapper {
    type In = [u8; 4];

    type Out = u32;

    open spec fn spec_map(i: Self::In) -> Self::Out {
        (i[0] as u32) | (i[1] as u32) << 8 | (i[2] as u32) << 16 | (i[3] as u32) << 24
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        [
            (o & 0xff) as u8,
            ((o >> 8) & 0xff) as u8,
            ((o >> 16) & 0xff) as u8,
            ((o >> 24) & 0xff) as u8,
        ]
    }
}

impl LossyMapper for U32LeMapper {
    proof fn lemma_sound_mapper(o: Self::Out) {
        assert({
            &&& o & 0xff < 256
            &&& (o >> 8) & 0xff < 256
            &&& (o >> 16) & 0xff < 256
            &&& (o >> 24) & 0xff < 256
        }) by (bit_vector);
        assert(o == ((o & 0xff) | ((o >> 8) & 0xff) << 8 | ((o >> 16) & 0xff) << 16 | ((o >> 24)
            & 0xff) << 24)) by (bit_vector);
    }
}

impl LosslessMapper for U32LeMapper {
    proof fn lemma_lossless_mapper(i: Self::In) {
        let x = Self::spec_map(i);
        let i0 = i[0] as u32;
        let i1 = i[1] as u32;
        let i2 = i[2] as u32;
        let i3 = i[3] as u32;
        assert(((x == i0 | i1 << 8 | i2 << 16 | i3 << 24) && (i0 < 256) && (i1 < 256) && (i2 < 256)
            && (i3 < 256)) ==> i0 == (x & 0xff) && i1 == ((x >> 8) & 0xff) && i2 == ((x >> 16)
            & 0xff) && i3 == ((x >> 24) & 0xff)) by (bit_vector);
        assert(Self::spec_map_rev(Self::spec_map(i)) == i);
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
}

/// Isomorphic mapper: `[u8; 4]` ↔ `u32` in **big-endian** byte order.
///
/// Forward: `[b3, b2, b1, b0]` → `(b3 << 24) | (b2 << 16) | (b1 << 8) | b0`.
/// Reverse: `v` → `[((v >> 24) & 0xff) as u8, ((v >> 16) & 0xff) as u8, ((v >> 8) & 0xff) as u8, (v & 0xff) as u8]`.
pub struct U32BeMapper;

impl Mapper for U32BeMapper {
    type In = [u8; 4];

    type Out = u32;

    open spec fn spec_map(i: Self::In) -> Self::Out {
        (i[0] as u32) << 24 | (i[1] as u32) << 16 | (i[2] as u32) << 8 | (i[3] as u32)
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        [
            ((o >> 24) & 0xff) as u8,
            ((o >> 16) & 0xff) as u8,
            ((o >> 8) & 0xff) as u8,
            (o & 0xff) as u8,
        ]
    }
}

impl LossyMapper for U32BeMapper {
    proof fn lemma_sound_mapper(o: Self::Out) {
        assert({
            &&& o & 0xff < 256
            &&& (o >> 8) & 0xff < 256
            &&& (o >> 16) & 0xff < 256
            &&& (o >> 24) & 0xff < 256
        }) by (bit_vector);
        assert(o == (((o >> 24) & 0xff) << 24 | ((o >> 16) & 0xff) << 16 | ((o >> 8) & 0xff) << 8
            | (o & 0xff))) by (bit_vector);
    }
}

impl LosslessMapper for U32BeMapper {
    proof fn lemma_lossless_mapper(i: Self::In) {
        let x = Self::spec_map(i);
        let i0 = i[0] as u32;
        let i1 = i[1] as u32;
        let i2 = i[2] as u32;
        let i3 = i[3] as u32;
        assert(((x == i0 << 24 | i1 << 16 | i2 << 8 | i3) && (i0 < 256) && (i1 < 256) && (i2 < 256)
            && (i3 < 256)) ==> i0 == ((x >> 24) & 0xff) && i1 == ((x >> 16) & 0xff) && i2 == ((x
            >> 8) & 0xff) && i3 == (x & 0xff)) by (bit_vector);
        assert(Self::spec_map_rev(Self::spec_map(i)) == i);
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
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

impl SoundParser for super::U8 {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

impl Unambiguity for super::U8 {
    open spec fn unambiguous(&self) -> bool {
        true
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

impl SpecParser for super::U16Le {
    type PVal = u16;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u16)> {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.spec_parse(ibuf)
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
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U16Le {
    type SVal = u16;

    open spec fn spec_serialize(&self, v: u16) -> Seq<u8> {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.spec_serialize(v)
    }
}

impl SoundParser for super::U16Le {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_parse_sound_value(ibuf);
    }
}

impl Unambiguity for super::U16Le {
    open spec fn unambiguous(&self) -> bool {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.unambiguous()
    }
}

impl NonTailFmt for super::U16Le {
    proof fn lemma_serialize_dps_prepend(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U16Le {
    proof fn lemma_serialize_len(&self, v: u16) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_len(v);
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

impl SpecParser for super::U16Be {
    type PVal = u16;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u16)> {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.spec_parse(ibuf)
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
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U16Be {
    type SVal = u16;

    open spec fn spec_serialize(&self, v: u16) -> Seq<u8> {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.spec_serialize(v)
    }
}

impl SoundParser for super::U16Be {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_parse_sound_value(ibuf);
    }
}

impl Unambiguity for super::U16Be {
    open spec fn unambiguous(&self) -> bool {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.unambiguous()
    }
}

impl NonTailFmt for super::U16Be {
    proof fn lemma_serialize_dps_prepend(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U16Be {
    proof fn lemma_serialize_len(&self, v: u16) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_len(v);
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

impl SpecParser for super::U32Le {
    type PVal = u32;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u32)> {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.spec_parse(ibuf)
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
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U32Le {
    type SVal = u32;

    open spec fn spec_serialize(&self, v: u32) -> Seq<u8> {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.spec_serialize(v)
    }
}

impl SoundParser for super::U32Le {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_parse_sound_value(ibuf);
    }
}

impl Unambiguity for super::U32Le {
    open spec fn unambiguous(&self) -> bool {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.unambiguous()
    }
}

impl NonTailFmt for super::U32Le {
    proof fn lemma_serialize_dps_prepend(&self, v: u32, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u32, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U32Le {
    proof fn lemma_serialize_len(&self, v: u32) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_serialize_len(v);
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

impl SpecParser for super::U32Be {
    type PVal = u32;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u32)> {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.spec_parse(ibuf)
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
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U32Be {
    type SVal = u32;

    open spec fn spec_serialize(&self, v: u32) -> Seq<u8> {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.spec_serialize(v)
    }
}

impl SoundParser for super::U32Be {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_parse_sound_value(ibuf);
    }
}

impl Unambiguity for super::U32Be {
    open spec fn unambiguous(&self) -> bool {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.unambiguous()
    }
}

impl NonTailFmt for super::U32Be {
    proof fn lemma_serialize_dps_prepend(&self, v: u32, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u32, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U32Be {
    proof fn lemma_serialize_len(&self, v: u32) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_serialize_len(v);
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

} // verus!
