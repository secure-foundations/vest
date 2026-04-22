use std::prelude::v1;

use crate::combinators::bytes::ExactLen;
use crate::combinators::implicit::{TLVOf, TLVal, TagValNode, Uninhabited};
use crate::combinators::implicit::{TVNode, VLData, VLDataOf};
use crate::combinators::mapped::spec::{LosslessMapper, LossyMapper, SpecMapper};
use crate::combinators::tuple::Pair;
use crate::combinators::{
    disjoint::*, Alt, DepPair, Empty, Preceded, Refined, RepeatN, Void, VoidTag,
};
use crate::combinators::{
    Choice, Cond, DepCombinator, Eof, Fixed, FnDepCombinator, Implicit, Mapped, Repeat, Sum,
    TVLeaf, TVOr, Tag, Tagged, Tail, U16Le, U32Le, Varied, U8,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

proof fn test_dependent_varied_u8() {
    let fmt = Implicit(U8, VLData());
    let value = seq![0xAAu8, 0xBBu8, 0xCCu8];

    assert(fmt.unambiguous());
    assert(fmt.consistent(value));
    fmt.theorem_serialize_parse_roundtrip(value);

    let ibuf = fmt.spec_serialize(value);
    assert(fmt.spec_parse(ibuf) == Some((ibuf.len() as int, value)));
}

proof fn test_dependent_nary_tagval() {
    broadcast use lemma_disjoint_cond;

    #[verusfmt::skip]
    let fmt = Implicit(U8,
        TVOr(0u8, U16Le,
        TVOr(1u8, U32Le,
        TVOr(2u8, Empty, Uninhabited()))),
    );

    let v0 = Sum::Inl(0x1234u16);
    let v1 = Sum::Inr(Sum::Inl(0x78563412u32));
    let v2 = Sum::Inr(Sum::Inr(Sum::Inl(())));

    assert(fmt.unambiguous());
    assert(fmt.consistent(v0));
    assert(fmt.consistent(v1));
    assert(fmt.consistent(v2));

    fmt.theorem_serialize_parse_roundtrip(v0);
    fmt.theorem_serialize_parse_roundtrip(v1);
    fmt.theorem_serialize_parse_roundtrip(v2);
}

proof fn test_dependent_nary_custom_tag() {
    broadcast use lemma_disjoint_cond;
    broadcast use lemma_disjoint_tag;
    broadcast use lemma_disjoint_choice;

    let my_tag = Mapped {
        inner: Choice(
            Tag { inner: U8, tag: 1u8 },
            Choice(Tag { inner: U8, tag: 2u8 }, Tag { inner: U8, tag: 3u8 }),
        ),
        mapper: MyTagMapper,
    };

    use MyTag::*;
    #[verusfmt::skip]
    let fmt = Implicit(
        my_tag,
        TVOr(A, U16Le,
        TVOr(B, U32Le,
        TVOr(C, Empty,
        Uninhabited()))),
    );

    let v0 = Sum::Inl(0x1234u16);
    let v1 = Sum::Inr(Sum::Inl(0x78563412u32));
    let v2 = Sum::Inr(Sum::Inr(Sum::Inl(())));

    assert(fmt.unambiguous());
    assert(fmt.consistent(v0));
    assert(fmt.consistent(v1));
    assert(fmt.consistent(v2));

    fmt.theorem_serialize_parse_roundtrip(v0);
    fmt.theorem_serialize_parse_roundtrip(v1);
    fmt.theorem_serialize_parse_roundtrip(v2);
}

proof fn test_dependent_n_consecutive_lengths_values() {
    let fmt = Implicit(Pair(U8, Pair(U16Le, U8)), Pair(VLData(), Pair(VLData(), VLData())));
    let value = (
        seq![0x6Eu8; u8::MAX as nat],
        (seq![0x69u8; u16::MAX as nat], seq![0x34u8; u8::MAX as nat]),
    );

    assert(fmt.unambiguous());
    assert(fmt.consistent(value));
    fmt.theorem_serialize_parse_roundtrip(value);

    let ibuf = fmt.spec_serialize(value);
    assert(fmt.spec_parse(ibuf) == Some((ibuf.len() as int, value)));
}

proof fn test_dependent_simple_tlv() {
    // tlv = {
    //   @tag: u16
    //   @len: u8
    //   v: [u8; @len] >>= choose(@tag) {
    //    0 => Tail,
    //    1 => Tail,
    //    2 => Repeat(u16le, Eof),
    //    _ => Void,
    //   }
    // }
    //
    #[verusfmt::skip]
    let tlv =
        Implicit(Pair(U16Le, U8),
        TLVOf(
        TVNode(
            TVNode(
                TVLeaf(0u16, Tail), TVLeaf(1u16, Tail)
            ),
            TVNode(
                TVLeaf(2u16, Repeat(U16Le, Eof)), Uninhabited()
            )
        )),
    );

    let v0 = Sum::Inl(Sum::Inl(seq![0xAAu8, 0xBBu8]));
    let v1 = Sum::Inl(Sum::Inr(seq![0xCCu8, 0xDDu8]));
    let v2 = Sum::Inr(Sum::Inl((seq![], ())));

    assert(tlv.unambiguous());
    assert(tlv.consistent(v0));
    assert(tlv.consistent(v1));
    assert(tlv.consistent(v2));

    tlv.theorem_serialize_parse_roundtrip(v0);
    tlv.theorem_serialize_parse_roundtrip(v1);
    tlv.theorem_serialize_parse_roundtrip(v2);
}

type ComplexVal = (
    Seq<u8>,
    (Seq<u8>, (Sum<Seq<u8>, Sum<Seq<u8>, Sum<(Seq<u16>, ()), !>>>, Seq<u8>)),
);

type ComplexBody = Pair<
    Fixed<3>,
    Pair<
        Varied,
        Pair<
            ExactLen<
                Choice<Cond<Tail>, Choice<Cond<Tail>, Choice<Cond<Repeat<U16Le, Eof>>, Void>>>,
            >,
            Refined<Fixed::<4>, spec_fn(Seq<u8>) -> bool>,
        >,
    >,
>;

type V2Fmt = TLVal<
    u8,
    u8,
    TVOr<u8, Tail, TVOr<u8, Tail, TVOr<u8, Repeat<U16Le, Eof>, VoidTag<u8>>>>,
>;

#[verusfmt::skip]
pub open spec fn v2_fmt() -> V2Fmt {
    TLVOf(
        TVOr(0u8, Tail,
        TVOr(1u8, Tail,
        TVOr(2u8, Repeat(U16Le, Eof),
        Uninhabited()))),
    )
}

struct TLVRest;

impl DepCombinator for TLVRest {
    type Key = (u8, (u8, u8));

    type Val = ComplexVal;

    type Body = ComplexBody;

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        let (tag, (len1, len2)) = key;
        let padding_fmt = Fixed::<3>;
        let v1_fmt = VLData().apply(len1);
        let v2_fmt = v2_fmt().apply((tag, len2));
        let magic_fmt = Refined {
            inner: Fixed::<4>,
            pred: |x: Seq<u8>| x == seq![0x12u8, 0x34u8, 0x56u8, 0x78u8],
        };
        Pair(padding_fmt, Pair(v1_fmt, Pair(v2_fmt, magic_fmt)))
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        let (padding, (v1, (v2, magic))) = value;
        let (tag, len2) = v2_fmt().recover(v2);
        let len1 = VLData().recover(v1);
        (tag, (len1, len2))
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
    }
}

proof fn test_dependent_complex_tlv() {
    // tlv = {
    //   @tag: u8
    //   @len1: u8
    //   @len2: u16
    //   padding: [u8; 3]
    //   v1: [u8; @len1]
    //   v2: [u8; @len2] >>= choose(@tag) {
    //     0 => Tail,
    //     1 => Tail,
    //     2 => Repeat(u16le, Eof),
    //   },
    //   const magic: [u8; 4] = [0x12u8, 0x34u8, 0x56u8, 0x78u8],
    // }
    broadcast use lemma_disjoint_cond;

    let tlv = Implicit(Pair(U8, Pair(U8, U8)), TLVRest);

    let padding = seq![0xDEu8, 0xADu8, 0xBEu8];
    let v1 = seq![0xffu8; 5];

    let v2_1 = Sum::Inl(seq![0xEFu8, 0xBEu8]);
    let v2_2 = Sum::Inr(Sum::Inl(seq![0x12u8, 0x34u8, 0x56u8, 0x78u8]));
    let v2_3 = Sum::Inr(Sum::Inr(Sum::Inl((seq![], ()))));

    let magic = seq![0x12u8, 0x34u8, 0x56u8, 0x78u8];

    let msg1 = (padding, (v1, (v2_1, magic)));
    let msg2 = (padding, (v1, (v2_2, magic)));
    let msg3 = (padding, (v1, (v2_3, magic)));

    assert(tlv.unambiguous());
    assert(tlv.consistent(msg1));
    assert(tlv.consistent(msg2));
    assert(tlv.consistent(msg3));

    tlv.theorem_serialize_parse_roundtrip(msg1);
    tlv.theorem_serialize_parse_roundtrip(msg2);
    tlv.theorem_serialize_parse_roundtrip(msg3);
}

type TXSegwitRestRestVal = (Seq<u8>, (Seq<u8>, u32));

type TXSegwitRestVal = (Seq<u8>, TXSegwitRestRestVal);

type TXSegwitRestRest = FnDepCombinator<u8, TXSegwitRestRestVal, Pair<Varied, Pair<Varied, U32Le>>>;

type TXSegwitRest = FnDepCombinator<
    u8,
    TXSegwitRestVal,
    Pair<Varied, Implicit<U8, TXSegwitRestRest>>,
>;

proof fn test_bitcoin_tx() {
    use super::choice::{
        canonical_u16_varint_value,
        canonical_u32_varint_value,
        canonical_u8_varint_value,
        varint_u16_form,
        varint_u32_form,
        varint_u8_form,
    };

    let u8_form = Refined { inner: varint_u8_form(), pred: |v| canonical_u8_varint_value(v) };
    let u16_form = Refined { inner: varint_u16_form(), pred: |v| canonical_u16_varint_value(v) };
    let u32_form = Refined { inner: varint_u32_form(), pred: |v| canonical_u32_varint_value(v) };

    let varint = Alt(u32_form, Alt(u16_form, u8_form));
    // tx_segwit = {
    //   const flag: u8 = 1,
    //   @txin_count: btc_varint,
    //   txins: [txin; @txin_count],
    //   @txout_count: btc_varint,
    //   txouts: [txout; @txout_count],
    //   witness: [witness; @txin_count],
    //   lock_time: lock_time,
    // }
    //
    // Equivalent to:
    //
    // tx_segwit = {
    //  const flag: u8 = 1,
    //  @txin_count: u8,
    //  rest: tx_segwit_rest(@txin_count),
    // }
    //
    // tx_segwit_rest(@txin_count) = {
    //   txins: [txin; @txin_count],
    //   @txout_count: u8,
    //   tx_segit_rest_rest(@txin_count, @txout_count),
    // }
    //
    // tx_segwit_rest_rest(@txin_count, @txout_count) = {
    //   txouts: [txout; @txout_count],
    //   witness: [witness; @txin_count],
    //   lock_time: u32le,
    // }
    #[verusfmt::skip]
    let tx_segwit_fmt =
        Preceded(Tag { inner: U8, tag: 1u8 },
        DepPair(varint, |txin_count: u32|
        Pair(RepeatN(txin_count, U8),
        DepPair(varint, |txout_count: u32|
        Pair(RepeatN(txout_count, U16Le),
        Pair(RepeatN(txin_count, U32Le),
        U32Le))))));
    #[verusfmt::skip]
    let tx_segwit =
        Tagged(U8, 1u8,
        Implicit(U8, (|txin_count: u8|
        Pair(Varied(txin_count),
        Implicit(U8, (|txout_count: u8|
        Pair(Varied(txout_count),
        Pair(Varied(txin_count),
        U32Le)),
        |value: TXSegwitRestRestVal|
        {
            let (txouts, (_witness, _lock_time)) = value;
            Varied::<u8>::value_byte_len(txouts) as u8
        }))
        ),
        |value: TXSegwitRestVal|
        {
            let (txins, _rest) = value;
            Varied::<u8>::value_byte_len(txins) as u8
        })),
    );

    let txins = seq![0x01u8, 0x02u8, 0x03u8];
    let txouts = seq![0xAAu8; u8::MAX as nat];
    let witness = seq![0x11u8, 0x22u8, 0x33u8];
    let lock_time = 0x78563412u32;

    let value = (txins, (txouts, (witness, lock_time)));

    assert(tx_segwit.unambiguous());
    assert(tx_segwit.sound_inv());
    assert(tx_segwit.nonmal_inv());
    assert(tx_segwit.consistent(value));
    tx_segwit.theorem_serialize_parse_roundtrip(value);

    let ibuf = tx_segwit.spec_serialize(value);
    assert(tx_segwit.spec_parse(ibuf) == Some((ibuf.len() as int, value)));
}

pub enum MyTag {
    A = 1,
    B = 2,
    C = 3,
}

pub type MyTagIn = Sum<u8, Sum<u8, u8>>;

pub struct MyTagMapper;

impl SpecMapper for MyTagMapper {
    type In = MyTagIn;

    type Out = MyTag;

    open spec fn wf_in(i: Self::In) -> bool {
        match i {
            Sum::Inl(v) => v == 1u8,
            Sum::Inr(Sum::Inl(v)) => v == 2u8,
            Sum::Inr(Sum::Inr(v)) => v == 3u8,
        }
    }

    open spec fn spec_map(i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(_) => MyTag::A,
            Sum::Inr(Sum::Inl(_)) => MyTag::B,
            Sum::Inr(Sum::Inr(_)) => MyTag::C,
        }
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        match o {
            MyTag::A => Sum::Inl(1u8),
            MyTag::B => Sum::Inr(Sum::Inl(2u8)),
            MyTag::C => Sum::Inr(Sum::Inr(3u8)),
        }
    }
}

impl LossyMapper for MyTagMapper {
    proof fn lemma_sound_mapper(o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(o: Self::Out) {
    }
}

impl LosslessMapper for MyTagMapper {
    proof fn lemma_lossless_mapper(i: Self::In) {
        match i {
            Sum::Inl(vl) => {
                assert(vl == 1u8);
            },
            Sum::Inr(vr) => {
                match vr {
                    Sum::Inl(vl) => {
                        assert(vl == 2u8);
                    },
                    Sum::Inr(vr) => {
                        assert(vr == 3u8);
                    },
                }
            },
        }
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
}

} // verus!
