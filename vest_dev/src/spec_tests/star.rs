use crate::combinators::{Array, Const, Refined, Repeat, RepeatN, U16Le, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

proof fn test_repeat_roundtrip_basic() {
    let inner = Refined(U8, |x: u8| x != 0xFFu8);
    // let inner = Const(U8, 0xAAu8);
    let term = Const(U8, 0xFFu8);
    let rep = Repeat(inner, term);
    let obuf = Seq::empty();
    // let v: (Seq<()>, ()) = (seq![(), ()], ());
    let v: (Seq<u8>, u8) = (seq![0x00u8, 0x01u8], 0xFFu8);

    assert(rep.consistent(v));
    assert(rep.unambiguous());
    let ibuf = rep.spec_serialize_dps(v, obuf);
    let n = rep.byte_len(v) as int;
    rep.theorem_serialize_dps_parse_roundtrip(v, obuf);
    assert(rep.spec_parse(ibuf) == Some((n, v)));
}

proof fn test_repeat_roundtrip_empty() {
    let inner = Const(U8, 0xAAu8);
    let term = Const(U8, 0xFFu8);
    let rep = Repeat(inner, term);
    let obuf = Seq::empty();
    let v: (Seq<u8>, u8) = (Seq::empty(), 0xFFu8);

    assert(rep.consistent(v));
    assert(rep.unambiguous());
    let ibuf = rep.spec_serialize_dps(v, obuf);
    let n = rep.byte_len(v) as int;
    rep.theorem_serialize_dps_parse_roundtrip(v, obuf);
    assert(rep.spec_parse(ibuf) == Some((n, v)));
}

proof fn test_repeat_needs_distinct_terminator() {
    let inner = Const(U8, 0xAAu8);
    let term_same = Const(U8, 0xAAu8);
    let rep_bad = Repeat(inner, term_same);
    let obuf = Seq::empty();
    let term_buf = term_same.spec_serialize_dps(0xAAu8, obuf);
    assert(inner.spec_parse(term_buf) is Some);
    assert(!parser_fails_on(inner, term_buf));
    assert(!rep_bad.unambiguous());
}

proof fn test_repeat_with_tuple_inner() {
    let inner = Const(U16Le, 0x1234u16);
    let term = Const(U16Le, 0xFFFFu16);
    let rep = Repeat(inner, term);
    let obuf = Seq::empty();
    let v: (Seq<u16>, u16) = (seq![0x1234u16, 0x1234u16], 0xFFFFu16);

    assert(rep.consistent(v));
    assert(rep.unambiguous());
    let ibuf = rep.spec_serialize_dps(v, obuf);
    let n = rep.byte_len(v) as int;
    rep.theorem_serialize_dps_parse_roundtrip(v, obuf);
    assert(rep.spec_parse(ibuf) == Some((n, v)));
}

proof fn test_repeatn_roundtrip_basic() {
    let inner = Refined(U8, |x: u8| x < 0x80u8);
    let rep = RepeatN(3u8, inner);
    let v: Seq<u8> = seq![0x00u8, 0x01u8, 0x02u8];

    assert(rep.consistent(v));
    assert(rep.unambiguous());
    let ibuf = rep.spec_serialize(v);
    let n = ibuf.len() as int;
    rep.theorem_serialize_parse_roundtrip(v);
    assert(rep.spec_parse(ibuf) == Some((n, v)));
}

proof fn test_array_roundtrip_basic() {
    let inner = Refined(U8, |x: u8| x != 0xFFu8);
    let arr = Array::<3, _>(inner);
    let v: [u8; 3] = [0x10u8, 0x20u8, 0x30u8];

    assert(arr.consistent(v));
    assert(arr.unambiguous());
    let ibuf = arr.spec_serialize(v);
    let n = ibuf.len() as int;
    arr.theorem_serialize_parse_roundtrip(v);
    assert(arr.spec_parse(ibuf) == Some((n, v)));
}

} // verus!
