use crate::asn1::BerBool;
use crate::combinators::choice::spec::*;
use crate::combinators::disjoint::*;
use crate::combinators::mapped::spec::{LosslessMapper, LossyMapper, SpecMapper};
use crate::combinators::{
    Alt, Choice, Const, Dispatch, Fixed, Mapped, Refined, Sum, Tagged, U16Le, U32Le, U8,
};
use crate::core::{proof::*, spec::*};
use vstd::pervasive::*;
use vstd::prelude::*;

verus! {

proof fn test_choice_compose() {
    let c = Choice(Const(U8, 0u8), Const(U8, 2u8));
    let obuf = Seq::empty();
    let v = Sum::Inr(2u8);
    assert(c.unambiguous());
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v);
    assert(c.spec_parse(ibuf) == Some((1int, v)));
}

proof fn test_choice_compose1() {
    let tag1 = Const(U16Le, 0u16);
    let tag2 = Const(U16Le, 2u16);
    let c = Choice(tag1, tag2);
    let obuf = Seq::empty();
    let v = Sum::Inr(2u16);
    tag1.theorem_serialize_parse_roundtrip(0u16);
    tag2.theorem_serialize_parse_roundtrip(2u16);
    assert(c.unambiguous());
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v);
    assert(c.spec_parse(ibuf) == Some((2int, v)));
}

proof fn test_choice_balanced() {
    let tag1 = Const(U16Le, 1u16);
    let tag2 = Const(U16Le, 2u16);
    let tag3 = Const(U16Le, 3u16);
    let tag4 = Const(U16Le, 4u16);
    let c = Choice(Choice(tag1, tag2), Choice(tag3, tag4));
    broadcast use lemma_disjoint_choice;

    assert(c.unambiguous());
}

proof fn test_alt_tag() {
    let tag_v1 = Const(U8, 0x01u8);
    let tag_v2 = Const(U8, 0x02u8);
    let alt_parser = Alt(tag_v1, tag_v2);
    assert(alt_parser.unambiguous());

    let buf_v1: Seq<u8> = seq![0x01u8];
    let buf_v2: Seq<u8> = seq![0x02u8];
    let buf_invalid: Seq<u8> = seq![0x03u8];

    assert(alt_parser.spec_parse(buf_v1) == Some((1int, 0x01u8)));
    assert(alt_parser.spec_parse(buf_v2) == Some((1int, 0x02u8)));
    assert(alt_parser.spec_parse(buf_invalid) is None);
}

pub enum MyEnum {
    A = 1,
    B = 2,
    C = 3,
}

pub enum MyTag {
    A(u16),
    B(u32),
    C(Seq<u8>),
}

use Sum::*;

pub type MyTagInner = Sum<u16, Sum<u32, Seq<u8>>>;

pub struct MyTagMapper;

impl SpecMapper for MyTagMapper {
    type In = MyTagInner;

    type Out = MyTag;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Inl(v) => MyTag::A(v),
            Inr(Inl(v)) => MyTag::B(v),
            Inr(Inr(v)) => MyTag::C(v),
        }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            MyTag::A(v) => Inl(v),
            MyTag::B(v) => Inr(Inl(v)),
            MyTag::C(v) => Inr(Inr(v)),
        }
    }
}

impl LossyMapper for MyTagMapper {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
    }
}

impl LosslessMapper for MyTagMapper {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

proof fn test_dispatch_tag() {
    use MyEnum::*;
    use Sum::Inl as L;
    use Sum::Inr as R;
    #[verusfmt::skip]
    let dispatch = Dispatch(
        B,
        [
            (A, Mapped { inner: L(U16Le), mapper: MyTagMapper }),
            (B, Mapped { inner: R(L(U32Le)), mapper: MyTagMapper }),
            (C, Mapped { inner: R(R(Fixed::<5>)), mapper: MyTagMapper }),
        ],
    );
    #[verusfmt::skip]
    let dispatch = Mapped {
        inner: Dispatch(
            B,
            [
                (A, L(U16Le)),
                (B, R(L(U32Le))),
                (C, R(R(Fixed::<5>))),
            ],
        ),
        mapper: MyTagMapper,
    };
    let obuf = Seq::empty();
    let v = MyTag::B(42u32);
    let buf = dispatch.spec_serialize(v);

    dispatch.inner.lemma_active_branch_is(1);
    assert(dispatch.consistent(v));
    assert(dispatch.unambiguous());
    assert(dispatch.spec_serialize_dps(v, obuf) == buf);

    dispatch.lemma_parse_safe(buf);
    dispatch.lemma_parse_sound_value(buf);
    dispatch.lemma_parse_sound_consumption(buf);
    dispatch.lemma_parse_non_malleable(buf, buf);
    dispatch.lemma_serialize_len(v);
    dispatch.lemma_serialize_dps_len(v, obuf);
    dispatch.lemma_no_lookahead(buf, buf);
    dispatch.theorem_serialize_parse_roundtrip(v);
    dispatch.theorem_parse_serialize_roundtrip(buf);
}

proof fn test_alt_flexible_length_encoding() {
    let not_81 = Refined(U8, |value: u8| value != 0x81u8);
    let short_form = not_81;
    let long_form = Tagged(U8, 0x81u8, not_81);
    let alt_parser = Alt(long_form, short_form);
    assert(alt_parser.unambiguous());

    let buf_short: Seq<u8> = seq![42u8];
    let buf_long: Seq<u8> = seq![0x81u8, 42u8];

    assert(alt_parser.spec_parse(buf_short) == Some((1int, 42u8)));
    assert(alt_parser.spec_parse(buf_long) == Some((2int, 42u8)));
}

} // verus!
