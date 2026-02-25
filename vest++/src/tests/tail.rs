use crate::combinators::bytes::ExactLen;
use crate::combinators::dependent::VLDataOf;
use crate::combinators::disjoint::{
    lemma_disjoint_eof, lemma_disjoint_optional, lemma_disjoint_repeat, lemma_disjoint_tag,
};
use crate::combinators::{
    Bind, Cond, Eof, Fixed, Optional, OptionalEof, Repeat, RepeatUtilEof, Tag, Tagged, Tail, U16Le,
    U32Le, U8,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

proof fn test_tail_compose() {
    let c = (U8, Tail);
    let obuf = Seq::empty();
    let v1 = (1u8, seq![3u8, 4u8, 5u8]);
    assert(c.unambiguous());
    let ibuf = c.spec_serialize_dps(v1, obuf);
    c.theorem_serialize_parse_roundtrip(v1);
    assert(c.spec_parse(ibuf) == Some((4int, v1)));
}

proof fn test_tail_ill_composed() {
    let c = (Tail, U8);
    let obuf = Seq::<u8>::empty();
    let v1 = (seq![3u8, 4u8, 5u8], 1u8);
    // the following line fails to compile, which is what we want
    // c.theorem_serialize_dps_parse_roundtrip(v1, obuf);
}

proof fn test_chain_end_with_tailopt() {
    let f1 = U8;
    let f2 = Fixed::<3>;
    let f3 = Tagged(U8, 0xA2, Fixed::<1>);
    let f4 = Tagged(U8, 0xB2, U16Le);
    let f5 = Tagged(U8, 0xC2, U32Le);

    #[verusfmt::skip]
    let c =
        (f1,
        (f2,
        Optional(f3,
        Repeat(f4,
        OptionalEof(f5)))));

    let v = (
        0x11u8,
        (
            [0x22u8, 0x33u8, 0x44u8],
            (Some([0x00u8]), (seq![0x1122u16, 0x3344u16], Some(0x66778899u32))),
        ),
    );

    assert(c.consistent(v));
    assert(c.unambiguous());
    c.theorem_serialize_parse_roundtrip(v);
}

proof fn test_chain_end_with_tailrepeat() {
    let f1 = U8;
    let f2 = Fixed::<3>;
    let f3 = Tagged(U8, 0xA2, U8);
    let f4 = Tagged(U8, 0xB2, Bind(U16Le, VLDataOf(RepeatUtilEof(U16Le))));
    let f5 = U32Le;

    #[verusfmt::skip]
    let c =
        (f1,
        (f2,
        Optional(f3,
        (f4,
        RepeatUtilEof(f5)))));

    let v = (0x11u8, ([0x22u8, 0x33u8, 0x44u8], (None::<u8>, (seq![], seq![0x99u32, 0xffu32]))));

    assert(c.consistent(v));
    assert(c.unambiguous());
    c.theorem_serialize_parse_roundtrip(v);
}

proof fn requires_no_lookahead<C: NoLookAhead>(parser: C) {
}

proof fn test_exactlen_recovers_no_lookahead() {
    // These intentionally fail to compile (raw combinators are not NoLookAhead):
    // requires_no_lookahead(Tail);
    // requires_no_lookahead(Eof);
    // requires_no_lookahead(TailOpt(U8));
    // requires_no_lookahead(TailRepeat(U8));
    // ExactLen recovers NoLookAhead.
    requires_no_lookahead(ExactLen(2u8, Tail));
    requires_no_lookahead(ExactLen(0u8, Eof));
    requires_no_lookahead(ExactLen(1u8, OptionalEof(U8)));
    requires_no_lookahead(ExactLen(2u8, RepeatUtilEof(U8)));
}

} // verus!
