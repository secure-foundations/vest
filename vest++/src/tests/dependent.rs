use std::prelude::v1;

use crate::combinators::bytes::ExactLen;
use crate::combinators::dependent::{TLVOf, TLVal, TagValNode, Uninhabited};
use crate::combinators::dependent::{TVNode, VLData, VLDataOf};
use crate::combinators::mapped::spec::{IsoMapper, Mapper};
use crate::combinators::{disjoint::*, Empty, Refined, Void, VoidTag};
use crate::combinators::{
    Bind, Choice, Cond, DepCombinator, Eof, Fixed, Mapped, Repeat, Sum, TVLeaf, TVOr, Tag, Tagged,
    Tail, U16Le, U32Le, Varied, U8,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

proof fn test_dependent_varied_u8() {
    let fmt = Bind(U8, VLData());
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
    let fmt = Bind(U8,
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
    let fmt = Bind(
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
    let fmt = Bind((U8, (U16Le, U8)), (VLData(), (VLData(), VLData())));
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
        Bind((U16Le, U8),
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
    [u8; 3],
    (Seq<u8>, (Sum<Seq<u8>, Sum<Seq<u8>, Sum<(Seq<u16>, ()), !>>>, [u8; 4])),
);

type ComplexBody = (
    Fixed<3>,
    (
        Varied,
        (
            ExactLen<
                Choice<Cond<Tail>, Choice<Cond<Tail>, Choice<Cond<Repeat<U16Le, Eof>>, Void>>>,
            >,
            Refined<Fixed::<4>, spec_fn([u8; 4]) -> bool>,
        ),
    ),
);

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
            pred: |x: [u8; 4]| x == [0x12u8, 0x34u8, 0x56u8, 0x78u8],
        };
        (padding_fmt, (v1_fmt, (v2_fmt, magic_fmt)))
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

    let tlv = Bind((U8, (U8, U8)), TLVRest);

    let padding = [0xDEu8, 0xADu8, 0xBEu8];
    let v1 = seq![0xffu8; 5];

    let v2_1 = Sum::Inl(seq![0xEFu8, 0xBEu8]);
    let v2_2 = Sum::Inr(Sum::Inl(seq![0x12u8, 0x34u8, 0x56u8, 0x78u8]));
    let v2_3 = Sum::Inr(Sum::Inr(Sum::Inl((seq![], ()))));

    let magic = [0x12u8, 0x34u8, 0x56u8, 0x78u8];

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

struct TXSegwitRest;

impl DepCombinator for TXSegwitRest {
    type Key = u8;

    type Val = (Seq<u8>, <TXSegwitRestRest as DepCombinator>::Val);

    type Body = (Varied, Bind<U8, TXSegwitRestRest>);

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        let txin_count = key;
        let txins_fmt = VLData().apply(txin_count);
        let rest_fmt = Bind(U8, TXSegwitRestRest { txin_count });
        (txins_fmt, rest_fmt)
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        let (txins, rest_val) = value;
        let (txouts, (witness, lock_time)) = rest_val;
        let txin_count = VLData().recover(txins);
        txin_count
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
        if self.apply(key).consistent(value) {
            let (txins, rest_val) = value;
            VLData().lemma_recover_consistent(key, txins);
        }
    }
}

pub struct TXSegwitRestRest {
    pub txin_count: u8,
}

impl DepCombinator for TXSegwitRestRest {
    type Key = u8;

    type Val = (Seq<u8>, (Seq<u8>, u32));

    type Body = (Varied, (Varied, U32Le));

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        let txin_count = self.txin_count;
        let txout_count = key;
        let txouts_fmt = VLData().apply(txout_count);
        let witness_fmt = VLData().apply(txin_count);
        let lock_time_fmt = U32Le;
        (txouts_fmt, (witness_fmt, lock_time_fmt))
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        let (txouts, (witness, lock_time)) = value;
        let txout_count = VLData().recover(txouts);
        txout_count
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
        if self.apply(key).consistent(value) {
            let txouts = value.0;
            assert(self.apply(key).0.consistent(txouts));
            VLData().lemma_recover_consistent(key, txouts);
        }
    }
}

proof fn test_bitcoin_tx() {
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
    let tx_segwit = Tagged(
        U8,
        1u8,
        Bind(
            U8,
            TXSegwitRest,
        )
    );

    let txins = seq![0x01u8, 0x02u8, 0x03u8];
    let txouts = seq![0xAAu8];
    let witness = seq![0x11u8, 0x22u8, 0x33u8];
    let lock_time = 0x78563412u32;

    let value = (txins, (txouts, (witness, lock_time)));

    assert(tx_segwit.unambiguous());
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

pub type MyTagIn = Sum<(), Sum<(), ()>>;

pub struct MyTagMapper;

impl Mapper for MyTagMapper {
    type In = MyTagIn;

    type Out = MyTag;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(()) => MyTag::A,
            Sum::Inr(Sum::Inl(())) => MyTag::B,
            Sum::Inr(Sum::Inr(())) => MyTag::C,
        }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            MyTag::A => Sum::Inl(()),
            MyTag::B => Sum::Inr(Sum::Inl(())),
            MyTag::C => Sum::Inr(Sum::Inr(())),
        }
    }
}

impl IsoMapper for MyTagMapper {
    proof fn lemma_map_iso(&self, i: Self::In) {
        match i {
            Sum::Inl(vl) => {},
            Sum::Inr(vr) => {
                match vr {
                    Sum::Inl(vl) => {},
                    Sum::Inr(vr) => {},
                }
            },
        }
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

} // verus!
