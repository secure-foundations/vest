use crate::combinators::{Choice, Either, Refined, Tag, U16Le, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

proof fn test_choice_compose() {
    let c = Choice(Tag { inner: U8, tag: 0u8 }, Tag { inner: U8, tag: 2u8 });
    let obuf = Seq::empty();
    let v = Either::Right(());
    assert(v.wf());
    assert(c.unambiguous());
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v);
    assert(c.spec_parse(ibuf) == Some((1int, v)));
}

proof fn test_choice_compose1() {
    let tag1 = Tag { inner: U16Le, tag: 0u16 };
    let tag2 = Tag { inner: U16Le, tag: 2u16 };
    let c = Choice(tag1, tag2);
    let obuf = Seq::empty();
    let v = Either::Right(());
    assert(v.wf());
    tag1.theorem_serialize_parse_roundtrip(());
    tag2.theorem_serialize_parse_roundtrip(());
    // assert(c.unambiguous());
    assert(c.unambiguous()) by {
        assert forall|vb: (), obuf: Seq<u8>| vb.wf() implies parser_fails_on(
            tag1,
            #[trigger] tag2.spec_serialize_dps(vb, obuf),
        ) by {
            U16Le.theorem_serialize_dps_parse_roundtrip(tag2.tag, obuf);
        }
    }
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v);
    assert(c.spec_parse(ibuf) == Some((2int, v)));
}

} // verus!
