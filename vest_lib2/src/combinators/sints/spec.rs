use crate::combinators::bytes::spec::*;
use crate::combinators::mapped::spec::{FnSpecMapper, LosslessMapper, LossyMapper, SpecMapper};
use crate::combinators::uints::spec::*;
use crate::combinators::{Fixed, Mapped};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub const U8_BYTE_LEN: usize = 1;

pub const U16_BYTE_LEN: usize = 2;

pub const U32_BYTE_LEN: usize = 4;

pub const U64_BYTE_LEN: usize = 8;

pub type I8Fmt = Mapped<Fixed<1>, FnSpecMapper<Seq<u8>, i8>>;

pub type I16LeFmt = Mapped<Fixed<2>, FnSpecMapper<Seq<u8>, i16>>;

pub type I16BeFmt = Mapped<Fixed<2>, FnSpecMapper<Seq<u8>, i16>>;

pub type I32LeFmt = Mapped<Fixed<4>, FnSpecMapper<Seq<u8>, i32>>;

pub type I32BeFmt = Mapped<Fixed<4>, FnSpecMapper<Seq<u8>, i32>>;

pub type I64LeFmt = Mapped<Fixed<8>, FnSpecMapper<Seq<u8>, i64>>;

pub type I64BeFmt = Mapped<Fixed<8>, FnSpecMapper<Seq<u8>, i64>>;

pub open spec fn i8_fmt() -> I8Fmt {
    Mapped { inner: Fixed::<1>, mapper: (|i: Seq<u8>| i[0] as i8, |o: i8| seq![o as u8]) }
}

pub open spec fn i16_le_fmt() -> I16LeFmt {
    Mapped {
        inner: Fixed::<2>,
        mapper: (|i: Seq<u8>| i16_le_from_bytes(array_from_seq(i)), |o: i16| i16_le_to_bytes(o)@),
    }
}

pub open spec fn i16_be_fmt() -> I16BeFmt {
    Mapped {
        inner: Fixed::<2>,
        mapper: (|i: Seq<u8>| i16_be_from_bytes(array_from_seq(i)), |o: i16| i16_be_to_bytes(o)@),
    }
}

pub open spec fn i32_le_fmt() -> I32LeFmt {
    Mapped {
        inner: Fixed::<4>,
        mapper: (|i: Seq<u8>| i32_le_from_bytes(array_from_seq(i)), |o: i32| i32_le_to_bytes(o)@),
    }
}

pub open spec fn i32_be_fmt() -> I32BeFmt {
    Mapped {
        inner: Fixed::<4>,
        mapper: (|i: Seq<u8>| i32_be_from_bytes(array_from_seq(i)), |o: i32| i32_be_to_bytes(o)@),
    }
}

pub open spec fn i64_le_fmt() -> I64LeFmt {
    Mapped {
        inner: Fixed::<8>,
        mapper: (|i: Seq<u8>| i64_le_from_bytes(array_from_seq(i)), |o: i64| i64_le_to_bytes(o)@),
    }
}

pub open spec fn i64_be_fmt() -> I64BeFmt {
    Mapped {
        inner: Fixed::<8>,
        mapper: (|i: Seq<u8>| i64_be_from_bytes(array_from_seq(i)), |o: i64| i64_be_to_bytes(o)@),
    }
}

pub broadcast proof fn lemma_i8_bytes_roundtrip(b: u8)
    by (bit_vector)
    ensures
        #[trigger] ((b as i8) as u8) == b,
{
}

pub broadcast proof fn lemma_i8_seq_roundtrip(i: Seq<u8>)
    requires
        i.len() == 1,
    ensures
        seq![(#[trigger] (i[0] as i8) as u8)] == i,
{
    broadcast use lemma_i8_bytes_roundtrip;

}

pub broadcast proof fn lemma_i8_value_roundtrip(o: i8)
    by (bit_vector)
    ensures
        #[trigger] ((o as u8) as i8) == o,
{
}

pub open spec fn i16_le_from_bytes(i: [u8; 2]) -> i16 {
    u16_le_from_bytes(i) as i16
}

pub open spec fn i16_le_to_bytes(o: i16) -> [u8; 2] {
    u16_le_to_bytes(o as u16)
}

pub broadcast proof fn lemma_i16_le_bytes_roundtrip(i: [u8; 2])
    ensures
        #[trigger] i16_le_to_bytes(i16_le_from_bytes(i)) == i,
{
    let x = u16_le_from_bytes(i);
    lemma_u16_le_bytes_roundtrip(i);
    assert(((x as i16) as u16) == x) by (bit_vector);
}

pub broadcast proof fn lemma_i16_le_value_roundtrip(o: i16)
    ensures
        #[trigger] i16_le_from_bytes(i16_le_to_bytes(o)) == o,
{
    lemma_u16_le_value_roundtrip(o as u16);
    assert(((o as u16) as i16) == o) by (bit_vector);
}

pub open spec fn i16_be_from_bytes(i: [u8; 2]) -> i16 {
    u16_be_from_bytes(i) as i16
}

pub open spec fn i16_be_to_bytes(o: i16) -> [u8; 2] {
    u16_be_to_bytes(o as u16)
}

pub broadcast proof fn lemma_i16_be_bytes_roundtrip(i: [u8; 2])
    ensures
        #[trigger] i16_be_to_bytes(i16_be_from_bytes(i)) == i,
{
    let x = u16_be_from_bytes(i);
    lemma_u16_be_bytes_roundtrip(i);
    assert(((x as i16) as u16) == x) by (bit_vector);
}

pub broadcast proof fn lemma_i16_be_value_roundtrip(o: i16)
    ensures
        #[trigger] i16_be_from_bytes(i16_be_to_bytes(o)) == o,
{
    lemma_u16_be_value_roundtrip(o as u16);
    assert(((o as u16) as i16) == o) by (bit_vector);
}

pub open spec fn i32_le_from_bytes(i: [u8; 4]) -> i32 {
    u32_le_from_bytes(i) as i32
}

pub open spec fn i32_le_to_bytes(o: i32) -> [u8; 4] {
    u32_le_to_bytes(o as u32)
}

pub broadcast proof fn lemma_i32_le_bytes_roundtrip(i: [u8; 4])
    ensures
        #[trigger] i32_le_to_bytes(i32_le_from_bytes(i)) == i,
{
    let x = u32_le_from_bytes(i);
    lemma_u32_le_bytes_roundtrip(i);
    assert(((x as i32) as u32) == x) by (bit_vector);
}

pub broadcast proof fn lemma_i32_le_value_roundtrip(o: i32)
    ensures
        #[trigger] i32_le_from_bytes(i32_le_to_bytes(o)) == o,
{
    lemma_u32_le_value_roundtrip(o as u32);
    assert(((o as u32) as i32) == o) by (bit_vector);
}

pub open spec fn i32_be_from_bytes(i: [u8; 4]) -> i32 {
    u32_be_from_bytes(i) as i32
}

pub open spec fn i32_be_to_bytes(o: i32) -> [u8; 4] {
    u32_be_to_bytes(o as u32)
}

pub broadcast proof fn lemma_i32_be_bytes_roundtrip(i: [u8; 4])
    ensures
        #[trigger] i32_be_to_bytes(i32_be_from_bytes(i)) == i,
{
    let x = u32_be_from_bytes(i);
    lemma_u32_be_bytes_roundtrip(i);
    assert(((x as i32) as u32) == x) by (bit_vector);
}

pub broadcast proof fn lemma_i32_be_value_roundtrip(o: i32)
    ensures
        #[trigger] i32_be_from_bytes(i32_be_to_bytes(o)) == o,
{
    lemma_u32_be_value_roundtrip(o as u32);
    assert(((o as u32) as i32) == o) by (bit_vector);
}

pub open spec fn i64_le_from_bytes(i: [u8; 8]) -> i64 {
    u64_le_from_bytes(i) as i64
}

pub open spec fn i64_le_to_bytes(o: i64) -> [u8; 8] {
    u64_le_to_bytes(o as u64)
}

pub broadcast proof fn lemma_i64_le_bytes_roundtrip(i: [u8; 8])
    ensures
        #[trigger] i64_le_to_bytes(i64_le_from_bytes(i)) == i,
{
    let x = u64_le_from_bytes(i);
    lemma_u64_le_bytes_roundtrip(i);
    assert(((x as i64) as u64) == x) by (bit_vector);
}

pub broadcast proof fn lemma_i64_le_value_roundtrip(o: i64)
    ensures
        #[trigger] i64_le_from_bytes(i64_le_to_bytes(o)) == o,
{
    lemma_u64_le_value_roundtrip(o as u64);
    assert(((o as u64) as i64) == o) by (bit_vector);
}

pub open spec fn i64_be_from_bytes(i: [u8; 8]) -> i64 {
    u64_be_from_bytes(i) as i64
}

pub open spec fn i64_be_to_bytes(o: i64) -> [u8; 8] {
    u64_be_to_bytes(o as u64)
}

pub broadcast proof fn lemma_i64_be_bytes_roundtrip(i: [u8; 8])
    ensures
        #[trigger] i64_be_to_bytes(i64_be_from_bytes(i)) == i,
{
    let x = u64_be_from_bytes(i);
    lemma_u64_be_bytes_roundtrip(i);
    assert(((x as i64) as u64) == x) by (bit_vector);
}

pub broadcast proof fn lemma_i64_be_value_roundtrip(o: i64)
    ensures
        #[trigger] i64_be_from_bytes(i64_be_to_bytes(o)) == o,
{
    lemma_u64_be_value_roundtrip(o as u64);
    assert(((o as u64) as i64) == o) by (bit_vector);
}

impl SpecParser for super::I8 {
    type PVal = i8;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, i8)> {
        i8_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::I8 {
    type Val = i8;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::I8 {
    type SValue = i8;

    open spec fn spec_serialize_dps(&self, v: i8, obuf: Seq<u8>) -> Seq<u8> {
        i8_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::I8 {
    type SVal = i8;

    open spec fn spec_serialize(&self, v: i8) -> Seq<u8> {
        i8_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::I8 {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        i8_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::I8 {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use lemma_i8_seq_roundtrip;

        i8_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use lemma_i8_seq_roundtrip;

        i8_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::I8 {
    proof fn lemma_serialize_dps_prepend(&self, v: i8, obuf: Seq<u8>) {
        i8_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: i8, obuf: Seq<u8>) {
        i8_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::I8 {
    proof fn lemma_serialize_len(&self, v: i8) {
        i8_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::I8 {
    type T = i8;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U8_BYTE_LEN as nat
    }
}

impl MinMaxByteLen for super::I8 {
    open spec fn min(&self) -> nat {
        U8_BYTE_LEN as nat
    }

    open spec fn max(&self) -> nat {
        U8_BYTE_LEN as nat
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
    }
}

impl StaticByteLen for super::I8 {
    open spec fn static_byte_len() -> nat {
        U8_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::I8 {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U8_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::I16Le {
    type PVal = i16;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, i16)> {
        i16_le_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::I16Le {
    type Val = i16;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::I16Le {
    type SValue = i16;

    open spec fn spec_serialize_dps(&self, v: i16, obuf: Seq<u8>) -> Seq<u8> {
        i16_le_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::I16Le {
    type SVal = i16;

    open spec fn spec_serialize(&self, v: i16) -> Seq<u8> {
        i16_le_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::I16Le {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        i16_le_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::I16Le {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i16_le_bytes_roundtrip;

        i16_le_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i16_le_bytes_roundtrip;

        i16_le_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::I16Le {
    proof fn lemma_serialize_dps_prepend(&self, v: i16, obuf: Seq<u8>) {
        i16_le_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: i16, obuf: Seq<u8>) {
        i16_le_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::I16Le {
    proof fn lemma_serialize_len(&self, v: i16) {
        i16_le_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::I16Le {
    type T = i16;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U16_BYTE_LEN as nat
    }
}

impl MinMaxByteLen for super::I16Le {
    open spec fn min(&self) -> nat {
        U16_BYTE_LEN as nat
    }

    open spec fn max(&self) -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
    }
}

impl StaticByteLen for super::I16Le {
    open spec fn static_byte_len() -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::I16Le {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::I16Be {
    type PVal = i16;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, i16)> {
        i16_be_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::I16Be {
    type Val = i16;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::I16Be {
    type SValue = i16;

    open spec fn spec_serialize_dps(&self, v: i16, obuf: Seq<u8>) -> Seq<u8> {
        i16_be_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::I16Be {
    type SVal = i16;

    open spec fn spec_serialize(&self, v: i16) -> Seq<u8> {
        i16_be_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::I16Be {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        i16_be_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::I16Be {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i16_be_bytes_roundtrip;

        i16_be_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i16_be_bytes_roundtrip;

        i16_be_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::I16Be {
    proof fn lemma_serialize_dps_prepend(&self, v: i16, obuf: Seq<u8>) {
        i16_be_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: i16, obuf: Seq<u8>) {
        i16_be_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::I16Be {
    proof fn lemma_serialize_len(&self, v: i16) {
        i16_be_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::I16Be {
    type T = i16;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U16_BYTE_LEN as nat
    }
}

impl MinMaxByteLen for super::I16Be {
    open spec fn min(&self) -> nat {
        U16_BYTE_LEN as nat
    }

    open spec fn max(&self) -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
    }
}

impl StaticByteLen for super::I16Be {
    open spec fn static_byte_len() -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::I16Be {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U16_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::I32Le {
    type PVal = i32;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, i32)> {
        i32_le_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::I32Le {
    type Val = i32;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::I32Le {
    type SValue = i32;

    open spec fn spec_serialize_dps(&self, v: i32, obuf: Seq<u8>) -> Seq<u8> {
        i32_le_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::I32Le {
    type SVal = i32;

    open spec fn spec_serialize(&self, v: i32) -> Seq<u8> {
        i32_le_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::I32Le {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        i32_le_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::I32Le {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i32_le_bytes_roundtrip;

        i32_le_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i32_le_bytes_roundtrip;

        i32_le_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::I32Le {
    proof fn lemma_serialize_dps_prepend(&self, v: i32, obuf: Seq<u8>) {
        i32_le_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: i32, obuf: Seq<u8>) {
        i32_le_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::I32Le {
    proof fn lemma_serialize_len(&self, v: i32) {
        i32_le_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::I32Le {
    type T = i32;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U32_BYTE_LEN as nat
    }
}

impl MinMaxByteLen for super::I32Le {
    open spec fn min(&self) -> nat {
        U32_BYTE_LEN as nat
    }

    open spec fn max(&self) -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
    }
}

impl StaticByteLen for super::I32Le {
    open spec fn static_byte_len() -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::I32Le {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::I32Be {
    type PVal = i32;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, i32)> {
        i32_be_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::I32Be {
    type Val = i32;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::I32Be {
    type SValue = i32;

    open spec fn spec_serialize_dps(&self, v: i32, obuf: Seq<u8>) -> Seq<u8> {
        i32_be_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::I32Be {
    type SVal = i32;

    open spec fn spec_serialize(&self, v: i32) -> Seq<u8> {
        i32_be_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::I32Be {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        i32_be_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::I32Be {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i32_be_bytes_roundtrip;

        i32_be_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i32_be_bytes_roundtrip;

        i32_be_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::I32Be {
    proof fn lemma_serialize_dps_prepend(&self, v: i32, obuf: Seq<u8>) {
        i32_be_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: i32, obuf: Seq<u8>) {
        i32_be_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::I32Be {
    proof fn lemma_serialize_len(&self, v: i32) {
        i32_be_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::I32Be {
    type T = i32;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U32_BYTE_LEN as nat
    }
}

impl MinMaxByteLen for super::I32Be {
    open spec fn min(&self) -> nat {
        U32_BYTE_LEN as nat
    }

    open spec fn max(&self) -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
    }
}

impl StaticByteLen for super::I32Be {
    open spec fn static_byte_len() -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::I32Be {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U32_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::I64Le {
    type PVal = i64;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, i64)> {
        i64_le_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::I64Le {
    type Val = i64;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::I64Le {
    type SValue = i64;

    open spec fn spec_serialize_dps(&self, v: i64, obuf: Seq<u8>) -> Seq<u8> {
        i64_le_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::I64Le {
    type SVal = i64;

    open spec fn spec_serialize(&self, v: i64) -> Seq<u8> {
        i64_le_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::I64Le {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        i64_le_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::I64Le {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i64_le_bytes_roundtrip;

        i64_le_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i64_le_bytes_roundtrip;

        i64_le_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::I64Le {
    proof fn lemma_serialize_dps_prepend(&self, v: i64, obuf: Seq<u8>) {
        i64_le_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: i64, obuf: Seq<u8>) {
        i64_le_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::I64Le {
    proof fn lemma_serialize_len(&self, v: i64) {
        i64_le_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::I64Le {
    type T = i64;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U64_BYTE_LEN as nat
    }
}

impl MinMaxByteLen for super::I64Le {
    open spec fn min(&self) -> nat {
        U64_BYTE_LEN as nat
    }

    open spec fn max(&self) -> nat {
        U64_BYTE_LEN as nat
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
    }
}

impl StaticByteLen for super::I64Le {
    open spec fn static_byte_len() -> nat {
        U64_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::I64Le {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U64_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::I64Be {
    type PVal = i64;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, i64)> {
        i64_be_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::I64Be {
    type Val = i64;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SpecSerializerDps for super::I64Be {
    type SValue = i64;

    open spec fn spec_serialize_dps(&self, v: i64, obuf: Seq<u8>) -> Seq<u8> {
        i64_be_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::I64Be {
    type SVal = i64;

    open spec fn spec_serialize(&self, v: i64) -> Seq<u8> {
        i64_be_fmt().spec_serialize(v)
    }
}

impl SafeParser for super::I64Be {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        i64_be_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::I64Be {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i64_be_bytes_roundtrip;

        i64_be_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i64_be_bytes_roundtrip;

        i64_be_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for super::I64Be {
    proof fn lemma_serialize_dps_prepend(&self, v: i64, obuf: Seq<u8>) {
        i64_be_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: i64, obuf: Seq<u8>) {
        i64_be_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::I64Be {
    proof fn lemma_serialize_len(&self, v: i64) {
        i64_be_fmt().lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::I64Be {
    type T = i64;

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        U64_BYTE_LEN as nat
    }
}

impl MinMaxByteLen for super::I64Be {
    open spec fn min(&self) -> nat {
        U64_BYTE_LEN as nat
    }

    open spec fn max(&self) -> nat {
        U64_BYTE_LEN as nat
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
    }
}

impl StaticByteLen for super::I64Be {
    open spec fn static_byte_len() -> nat {
        U64_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::I64Be {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        U64_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

} // verus!
