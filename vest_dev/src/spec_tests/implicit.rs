use crate::combinators::bytes::ExactLen;
use crate::combinators::mapped::spec::{LosslessMapper, SpecMapper};
use crate::combinators::tuple::Pair;
use crate::combinators::{disjoint::*, Dispatch, Eof, Fixed, Repeat, Star, Tail};
use crate::combinators::{Bind, Choice, Cond, Implicit, Mapped, Sum, U16Le, U32Le, Varied, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

proof fn test_bind_fmt1_roundtrip() {
    let fmt1 = Bind(U8, |len: u8| Varied(len));
    let v = (3u8, seq![0xAAu8, 0xBBu8, 0xCCu8]);

    assert(fmt1.unambiguous());
    assert(fmt1.consistent(v));
    fmt1.theorem_serialize_parse_roundtrip(v);

    let ibuf = fmt1.spec_serialize(v);
    assert(fmt1.spec_parse(ibuf) == Some((ibuf.len() as int, v)));
}

proof fn test_bind_fmt3_roundtrip() {
    broadcast use lemma_disjoint_cond;

    let fmt3 = Bind(U8, |tag: u8| { Choice(Cond(tag == 0u8, U16Le), Cond(tag == 1u8, U32Le)) });

    let v0 = (0u8, Sum::Inl(0x1234u16));
    let v1 = (1u8, Sum::Inr(0x78563412u32));

    assert(fmt3.unambiguous());

    assert(fmt3.consistent(v0));
    fmt3.theorem_serialize_parse_roundtrip(v0);
    let ibuf0 = fmt3.spec_serialize(v0);
    assert(fmt3.spec_parse(ibuf0) == Some((ibuf0.len() as int, v0)));
    let buf0 = seq![0u8, 0x34u8, 0x12u8];
    if let Some((n0, (_, parsed0))) = fmt3.spec_parse(buf0) {
        assert(n0 == 3int);
        assert(parsed0 is Inl);
    }
    assert(fmt3.consistent(v1));
    fmt3.theorem_serialize_parse_roundtrip(v1);
    let ibuf1 = fmt3.spec_serialize(v1);
    assert(fmt3.spec_parse(ibuf1) == Some((ibuf1.len() as int, v1)));
    let buf1 = seq![1u8, 0x12u8, 0x34u8, 0x56u8, 0x78u8];
    if let Some((n1, (_, parsed1))) = fmt3.spec_parse(buf1) {
        assert(n1 == 5int);
        assert(parsed1 is Inr);
    }
}

proof fn test_implicit_inferred_fmt2_roundtrip() {
    // fmt2 = {
    //   @len1: u8
    //   fixed: [u8; 3]
    //   @len2: u16
    //   varied1: [u8; @len1]
    //   varied2: [u8; @len2]
    //   varied3: [u8; @len1]
    // }
    #[verusfmt::skip]
    let fmt2 =
        // Format:
        Implicit(U8, (|len1: u8|
        Pair(Fixed::<3>,
        Implicit(U16Le, (|len2: u16|
        Pair(Varied(len1),
        Pair(Varied(len2),
         Varied(len1))),
        // Recovery logics:
        |v: (Seq<u8>, (Seq<u8>, Seq<u8>))| v.1.0.len() as u16))),
        |v: (Seq<u8>, (Seq<u8>, (Seq<u8>, Seq<u8>)))| v.1.0.len() as u8));

    let v = (
        seq![0x10u8, 0x20u8, 0x30u8],
        (seq![0x10u8, 0x20u8], (seq![0x30u8, 0x40u8, 0x50u8], seq![0x30u8, 0x40u8])),
    );
    assert(fmt2.unambiguous());
    assert(fmt2.consistent(v));
    fmt2.theorem_serialize_parse_roundtrip(v);

    let ibuf = fmt2.spec_serialize(v);
    assert(fmt2.spec_parse(ibuf) == Some((ibuf.len() as int, v)));
}

proof fn test_implicit_inferred_fmt3_roundtrip() {
    broadcast use lemma_disjoint_cond;
    // fmt3 = {
    //   @tag: u8
    //   val: choose(@tag) {
    //     0 => u16le,
    //     1 => u32le,
    //     2 => [u8; 1],
    //   }
    // }

    #[verusfmt::skip]
    let fmt3 =
        // Format:
        Implicit(U8, (|tag|
            Choice(Cond(tag == 0u8, U16Le),
            Choice(Cond(tag == 1u8, U32Le),
                   Cond(tag == 2u8, Fixed::<0>))),
        // Recovery logics:
        |v: Sum<u16, Sum<u32, Seq<u8>>>|
            {
                match v {
                    Sum::Inl(_) => 0u8,
                    Sum::Inr(Sum::Inl(_)) => 1u8,
                    Sum::Inr(Sum::Inr(_)) => 2u8,
                }
            },
    ));

    let v0 = Sum::Inl(0x1234u16);
    let v1 = Sum::Inr(Sum::Inl(0x78563412u32));
    let v2 = Sum::Inr(Sum::Inr(seq![]));

    assert(fmt3.unambiguous());
    assert(fmt3.consistent(v0));
    assert(fmt3.consistent(v1));
    assert(fmt3.consistent(v2));

    fmt3.theorem_serialize_parse_roundtrip(v0);
    fmt3.theorem_serialize_parse_roundtrip(v1);
    fmt3.theorem_serialize_parse_roundtrip(v2);
}

type PayloadFmt = Choice<Cond<Tail>, Choice<Cond<Varied<u16>>, Cond<Repeat<U16Le, Eof>>>>;

proof fn test_tlv_implicit_inferred_choice_exactlen_roundtrip() {
    broadcast use lemma_disjoint_cond;
    broadcast use lemma_value_len_matches_byte_len;

    use Sum::Inl as L;
    use Sum::Inr as R;

    // tlv = {
    //   @tag: u8
    //   @len1: u8
    //   padding: [u8; 3]
    //   @len2: u16
    //   v1: [u8; @len1]
    //   v2: [u8; @len2] >>= choose(@tag) {
    //     0 => Tail,
    //     1 => [u8; @len2],
    //     2 => Repeat(u16le, Eof),
    //   }
    // }
    #[verusfmt::skip]
    let payload_fmt = |tag, len2| -> PayloadFmt {
        Choice(Cond(tag == 0u8, Tail),
        Choice(Cond(tag == 1u8, Varied(len2)),
               Cond(tag == 2u8, Repeat(U16Le, Eof))))
    };
    #[verusfmt::skip]
    let tlv =
        // Format:
        Implicit(U8, (|tag: u8|
        Implicit(U8, (|len1: u8|
        Pair(Fixed::<3>,
        Implicit(U16Le, (|len2: u16|
        Pair(Varied(len1),
        ExactLen(len2, payload_fmt(tag, len2))),
        // Recovery logics:
        |v: (Seq<u8>, <PayloadFmt as SpecByteLen>::T)| {
            let (v1, v2) = v;
            let len2 = PayloadFmt::value_byte_len(v2);
            len2 as u16
        }))),
        |v: (Seq<u8>, (Seq<u8>, <PayloadFmt as SpecByteLen>::T))| {
           let (padding, (v1, v2)) = v;
            let len1 = Varied::<u8>::value_byte_len(v1);
            len1 as u8
        })),
        |v: (Seq<u8>, (Seq<u8>, <PayloadFmt as SpecByteLen>::T))| {
            let (padding, (v1, v2)) = v;
            let tag = match v2 {
                L(_) => 0u8,
                R(L(_)) => 1u8,
                R(R(_)) => 2u8,
            };
            tag
        }));

    let padding = seq![0xDEu8, 0xADu8, 0xBEu8];
    let v1 = seq![0xffu8; 5];

    let v2_1 = L(seq![0xEFu8, 0xBEu8]);
    let v2_2 = R(L(seq![0x12u8, 0x34u8, 0x56u8, 0x78u8]));
    // let v2_3 = Inr(Inr((seq![0xEFu16, 0xBEu16], ())));

    let msg1 = (padding, (v1, v2_1));
    let msg2 = (padding, (v1, v2_2));
    // let msg3 = (padding, (v1, v2_3));

    assert(tlv.unambiguous());
    assert(tlv.sound_inv());
    assert(tlv.nonmal_inv());
    assert(tlv.consistent(msg1));
    assert(tlv.consistent(msg2));
    // assert(tlv.consistent(msg3));

    tlv.theorem_serialize_parse_roundtrip(msg1);
    tlv.theorem_serialize_parse_roundtrip(msg2);

    let ibuf16 = tlv.spec_serialize(msg1);
    let ibuf32 = tlv.spec_serialize(msg2);
    assert(tlv.spec_parse(ibuf16) == Some((ibuf16.len() as int, msg1)));
    assert(tlv.spec_parse(ibuf32) == Some((ibuf32.len() as int, msg2)));

    // #[verusfmt::skip]
    // let payload_fmt = |tag, len2| {
    //     ExactLen(len2, Dispatch(tag, [
    //         (0u8, L(Tail)),
    //         (1u8, R(L(Varied(len2)))),
    //         (2u8, R(R(Repeat(U16Le, Eof)))),
    //     ]))
    // };
    #[verusfmt::skip]
    let tlv2 =
        Bind(U8, |tag: u8|
        Bind(U8, |len1: u8|
        Pair(Fixed::<3>,
        Bind(U16Le, |len2: u16|
        Pair(Varied(len1),
        payload_fmt(tag, len2))))));

    let msg1 = (
        0u8,
        (
            Varied::<u8>::value_byte_len(v1) as u8,
            (padding, (PayloadFmt::value_byte_len(v2_1) as u16, (v1, v2_1))),
        ),
    );
    let msg2 = (
        1u8,
        (
            Varied::<u8>::value_byte_len(v1) as u8,
            (padding, (PayloadFmt::value_byte_len(v2_2) as u16, (v1, v2_2))),
        ),
    );

    assert(tlv2.unambiguous());
    assert(tlv2.consistent(msg1));
    assert(tlv2.consistent(msg2));
    assert(tlv2.nonmal_inv());

    tlv2.theorem_serialize_parse_roundtrip(msg1);
    tlv2.theorem_serialize_parse_roundtrip(msg2);
}

} // verus!
