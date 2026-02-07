use crate::combinators::{Refined, Repeat, Tag, U16Le, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

proof fn test_repeat_roundtrip_basic() {
    let inner = Refined { inner: U8, pred: |x: u8| x != 0xFFu8 };
    // let inner = Tag { inner: U8, tag: 0xAAu8 };
    let term = Tag { inner: U8, tag: 0xFFu8 };
    let rep = Repeat(inner, term);
    let obuf = Seq::empty();
    // let v: (Seq<()>, ()) = (seq![(), ()], ());
    let v: (Seq<u8>, ()) = (seq![0x00u8, 0x01u8], ());

    assert(rep.consistent(v));
    assert(rep.unambiguous());
    let ibuf = rep.spec_serialize_dps(v, obuf);
    let n = rep.byte_len(v) as int;
    rep.theorem_serialize_dps_parse_roundtrip(v, obuf);
    assert(rep.spec_parse(ibuf) == Some((n, v)));
}

proof fn test_repeat_roundtrip_empty() {
    let inner = Tag { inner: U8, tag: 0xAAu8 };
    let term = Tag { inner: U8, tag: 0xFFu8 };
    let rep = Repeat(inner, term);
    let obuf = Seq::empty();
    let v: (Seq<()>, ()) = (Seq::empty(), ());

    assert(rep.consistent(v));
    assert(rep.unambiguous());
    let ibuf = rep.spec_serialize_dps(v, obuf);
    let n = rep.byte_len(v) as int;
    rep.theorem_serialize_dps_parse_roundtrip(v, obuf);
    assert(rep.spec_parse(ibuf) == Some((n, v)));
}

proof fn test_repeat_needs_distinct_terminator() {
    let inner = Tag { inner: U8, tag: 0xAAu8 };
    let term_same = Tag { inner: U8, tag: 0xAAu8 };
    let rep_bad = Repeat(inner, term_same);
    let obuf = Seq::empty();
    let term_buf = term_same.spec_serialize_dps((), obuf);
    assert(inner.spec_parse(term_buf) is Some);
    assert(!parser_fails_on(inner, term_buf));
    assert(!rep_bad.unambiguous());
}

proof fn test_repeat_with_tuple_inner() {
    let inner = Tag { inner: U16Le, tag: 0x1234u16 };
    let term = Tag { inner: U16Le, tag: 0xFFFFu16 };
    let rep = Repeat(inner, term);
    let obuf = Seq::empty();
    let v: (Seq<()>, ()) = (seq![(), ()], ());

    assert(rep.consistent(v));
    assert(rep.unambiguous());
    let ibuf = rep.spec_serialize_dps(v, obuf);
    let n = rep.byte_len(v) as int;
    rep.theorem_serialize_dps_parse_roundtrip(v, obuf);
    assert(rep.spec_parse(ibuf) == Some((n, v)));
}

} // verus!
