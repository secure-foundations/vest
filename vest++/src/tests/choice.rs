use crate::asn1::BerBool;
use crate::combinators::disjoint::*;
use crate::combinators::mapped::spec::{LosslessMapper, LossyMapper, Mapper};
use crate::combinators::{
    Alt, Choice, Dispatch, Fixed, Mapped, Refined, Sum, Tag, Tagged, Terminated, U16Le, U32Le, U8,
};
use crate::core::{proof::*, spec::*};
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

proof fn test_choice_compose() {
    let c = Choice(Tag { inner: U8, tag: 0u8 }, Tag { inner: U8, tag: 2u8 });
    let obuf = Seq::empty();
    let v = Sum::Inr(2u8);
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
    let v = Sum::Inr(2u16);
    tag1.theorem_serialize_parse_roundtrip(0u16);
    tag2.theorem_serialize_parse_roundtrip(2u16);
    assert(c.unambiguous());
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v);
    assert(c.spec_parse(ibuf) == Some((2int, v)));
}

proof fn test_choice_balanced() {
    let tag1 = Tag { inner: U16Le, tag: 1u16 };
    let tag2 = Tag { inner: U16Le, tag: 2u16 };
    let tag3 = Tag { inner: U16Le, tag: 3u16 };
    let tag4 = Tag { inner: U16Le, tag: 4u16 };
    let c = Choice(Choice(tag1, tag2), Choice(tag3, tag4));
    broadcast use lemma_disjoint_choice;

    assert(c.unambiguous());
}

proof fn test_alt_tag() {
    let tag_v1 = Tag { inner: U8, tag: 0x01u8 };
    let tag_v2 = Tag { inner: U8, tag: 0x02u8 };
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
    C([u8; 5]),
}

use Sum::*;

pub type MyTagInner = Sum<u16, Sum<u32, [u8; 5]>>;

pub struct MyTagMapper;

impl Mapper for MyTagMapper {
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
    let not_81 = Refined { inner: U8, pred: |value: u8| value != 0x81u8 };
    let short_form = not_81;
    let long_form = Tagged(U8, 0x81u8, not_81);
    let alt_parser = Alt(long_form, short_form);
    assert(alt_parser.unambiguous());

    let buf_short: Seq<u8> = seq![42u8];
    let buf_long: Seq<u8> = seq![0x81u8, 42u8];

    assert(alt_parser.spec_parse(buf_short) == Some((1int, 42u8)));
    assert(alt_parser.spec_parse(buf_long) == Some((2int, 42u8)));
}

// =============================================================================
// Simplified Bitcoin Varint with both malleable and canonical encodings
// =============================================================================
//
// This format reserves 0xFD and 0xFE as length-extension tags:
// - Any other one-byte value is encoded directly
// - 0xFD prefix + 2 bytes encodes the u16 form (little-endian)
// - 0xFE prefix + 4 bytes encodes the u32 form (little-endian)
//
// Without a shortest-form restriction, the format is malleable:
// e.g., value 100 can be encoded as
//   - [0x64]
//   - [0xFD, 0x64, 0x00]
//   - [0xFE, 0x64, 0x00, 0x00, 0x00]
pub const VARINT_TAG_U16: u8 = 0xFDu8;

pub const VARINT_TAG_U32: u8 = 0xFEu8;

// Mapper: u8 -> u32
pub struct U8AsU32;

impl Mapper for U8AsU32 {
    type In = u8;

    type Out = u32;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as u32
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o <= u8::MAX
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        o as u8
    }
}

impl LossyMapper for U8AsU32 {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }
}

impl LosslessMapper for U8AsU32 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

// Mapper: u16 -> u32
pub struct U16AsU32;

impl Mapper for U16AsU32 {
    type In = u16;

    type Out = u32;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as u32
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o <= u16::MAX
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o & 0xFFFF) as u16
    }
}

impl LossyMapper for U16AsU32 {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        assert(((o & 0xFFFF) as u16) as u32 == o) by (bit_vector)
            requires
                self.wf_out(o),
        ;
    }
}

impl LosslessMapper for U16AsU32 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        assert(((i as u32) & 0xFFFF) as u16 == i) by (bit_vector);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        assert(i as u32 <= 0xFFFF);
    }
}

// Direct one-byte form: every byte except VARINT_TAG_U16 and VARINT_TAG_U32 is encoded directly as a u8
pub open spec fn varint_u8_form() -> Refined<Mapped<U8, U8AsU32>, spec_fn(u32) -> bool> {
    Refined {
        inner: Mapped { inner: U8, mapper: U8AsU32 },
        pred: |v: u32| v != VARINT_TAG_U16 as u32 && v != VARINT_TAG_U32 as u32,
    }
}

// u16 form: 0xFD prefix + 2 bytes little-endian
pub open spec fn varint_u16_form() -> Mapped<Tagged<U8, U16Le>, U16AsU32> {
    Mapped {
        inner: Tagged(U8, VARINT_TAG_U16, U16Le),
        mapper: U16AsU32,
    }
    // Equivalently:
    // Tagged(U8, VARINT_TAG_U16, Mapped { inner: U16Le, mapper: U16ToU32Mapper })

}

// u32 form: 0xFE prefix + 4 bytes little-endian
pub open spec fn varint_u32_form() -> Tagged<U8, U32Le> {
    Tagged(U8, VARINT_TAG_U32, U32Le)
}

proof fn test_malleable_varint() {
    let u8_form = varint_u8_form();
    let u16_form = varint_u16_form();
    let u32_form = varint_u32_form();
    let varint = Alt(u32_form, Alt(u16_form, u8_form));

    assert(varint.unambiguous());
    let val = 100u32;
    // `val` is consistent with all three forms
    assert(u32_form.consistent(val));
    assert(u16_form.consistent(val));
    assert(u8_form.consistent(val));
    // but the overall varint parser is not non-malleable, since it accepts multiple encodings of the same value
    assert(!varint.nonmal_inv());

    let serialized = varint.spec_serialize(val);

    // Value 100 (0x64) - can be encoded three ways:
    let buf_u8 = seq![0x64u8];
    let buf_u16 = seq![0xFDu8, 0x64u8, 0x00u8];
    let buf_u32 = seq![0xFEu8, 0x64u8, 0x00u8, 0x00u8, 0x00u8];

    // Some bitvector proofs for the little-endian encodings of 100
    assert(U16Le.spec_serialize(100u16) == seq![0x64u8, 0x00u8]) by {
        assert((100u16 & 0xff) as u8 == 0x64u8) by (bit_vector);
        assert(((100u16 >> 8) & 0xff) as u8 == 0x00u8) by (bit_vector);
    }
    assert(U32Le.spec_serialize(100u32) == seq![0x64u8, 0x00u8, 0x00u8, 0x00u8]) by {
        assert((100u32 & 0xff) as u8 == 0x64u8) by (bit_vector);
        assert(((100u32 >> 8) & 0xff) as u8 == 0x00u8) by (bit_vector);
        assert(((100u32 >> 16) & 0xff) as u8 == 0x00u8) by (bit_vector);
        assert(((100u32 >> 24) & 0xff) as u8 == 0x00u8) by (bit_vector);
    }

    // Invoke the roundtrip theorems for u16 and u32 forms
    assert(u16_form.spec_parse(buf_u16) == Some((3int, 100u32))) by {
        let u16_form_inner = Tagged(U8, VARINT_TAG_U16, U16Le);
        u16_form_inner.theorem_serialize_parse_roundtrip(100u16);
        let tag = Tag { inner: U8, tag: VARINT_TAG_U16 };
        assert(tag.consistent(VARINT_TAG_U16));
        assert(u16_form_inner.spec_serialize(100u16) == buf_u16) by {}
    }
    assert(u32_form.spec_parse(buf_u32) == Some((5int, 100u32))) by {
        u32_form.theorem_serialize_parse_roundtrip(100u32);
        let tag = Tag { inner: U8, tag: VARINT_TAG_U32 };
        assert(tag.consistent(VARINT_TAG_U32));
        assert(u32_form.spec_serialize(100u32) == buf_u32) by {}
    }

    // varint serializer non-deterministically picks one of the three encodings
    assert({
        ||| serialized == buf_u8
        ||| serialized == buf_u16
        ||| serialized == buf_u32
    });

    // Different encodings consume different byte counts
    // All three encodings represent the same logical value (100)
    assert({
        &&& varint.spec_parse(buf_u8) == Some((1int, 100u32))
        &&& varint.spec_parse(buf_u16) == Some((3int, 100u32))
        &&& varint.spec_parse(buf_u32) == Some((5int, 100u32))
    });
}

/*
 * Canonicality restrictions:
 * - Values less than VARINT_TAG_U16 must use the u8 form
 * - Values between VARINT_TAG_U16 and u16::MAX must use the u16 form
 * - Values above u16::MAX must use the u32 form
 * These restrictions ensure that each value has a unique encoding, making the overall varint parser non-malleable.
 */

pub open spec fn canonical_u8_varint_value(v: u32) -> bool {
    v < VARINT_TAG_U16 as u32
}

pub open spec fn canonical_u16_varint_value(v: u32) -> bool {
    VARINT_TAG_U16 as u32 <= v <= u16::MAX
}

pub open spec fn canonical_u32_varint_value(v: u32) -> bool {
    u16::MAX < v
}

proof fn test_canonical_varint_roundtrip() {
    let u8_form = Refined { inner: varint_u8_form(), pred: |v| canonical_u8_varint_value(v) };
    let u16_form = Refined { inner: varint_u16_form(), pred: |v| canonical_u16_varint_value(v) };
    let u32_form = Refined { inner: varint_u32_form(), pred: |v| canonical_u32_varint_value(v) };

    let varint = Alt(u32_form, Alt(u16_form, u8_form));
    assert(varint.unambiguous());

    let v_u8 = 100u32;
    let v_u16 = VARINT_TAG_U32 as u32;
    let v_u32 = 0x1_0000u32;

    assert(u32_form.consistent(v_u32));
    assert(u16_form.consistent(v_u16));
    assert(u8_form.consistent(v_u8));

    // Canonicality restrictions prevent non-deterministic encodings of the same value
    assert(!u32_form.consistent(v_u16));
    assert(!u32_form.consistent(v_u8));
    assert(!u16_form.consistent(v_u8));
    // And the overall varint parser is now non-malleable, since each value has a unique encoding
    assert(varint.nonmal_inv());

    let buf_u8 = seq![0x64u8];
    // let buf_u16 = seq![VARINT_TAG_U16, VARINT_TAG_U32, 0x00u8];
    let buf_u16 = varint.spec_serialize(v_u16);
    let buf_u32 = seq![VARINT_TAG_U32, 0x00u8, 0x00u8, 0x01u8, 0x00u8];

    varint.theorem_serialize_parse_roundtrip(v_u8);
    varint.theorem_serialize_parse_roundtrip(v_u16);
    varint.theorem_serialize_parse_roundtrip(v_u32);
    let arbitrary_input = choose|i| varint.spec_parse(i) == Some((3int, v_u16));
    varint.lemma_parse_non_malleable(buf_u16, arbitrary_input);
    assert(arbitrary_input.take(3) == buf_u16.take(3));

}

} // verus!
