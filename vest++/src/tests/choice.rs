use crate::combinators::disjoint::*;
use crate::combinators::mapped::spec::{IsoMapper, Mapper};
use crate::combinators::{
    Alt, BerBool, Choice, Dispatch, Fixed, Mapped, Refined, Sum, Tag, Tagged, Terminated, U16Le,
    U32Le, U8,
};
use crate::core::{proof::*, spec::*};
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

proof fn test_choice_compose() {
    let c = Choice(Tag { inner: U8, tag: 0u8 }, Tag { inner: U8, tag: 2u8 });
    let obuf = Seq::empty();
    let v = Sum::Inr(());
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
    let v = Sum::Inr(());
    tag1.theorem_serialize_parse_roundtrip(());
    tag2.theorem_serialize_parse_roundtrip(());
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

    assert(alt_parser.spec_parse(buf_v1) == Some((1int, ())));
    assert(alt_parser.spec_parse(buf_v2) == Some((1int, ())));
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

impl IsoMapper for MyTagMapper {
    proof fn lemma_map_iso(&self, i: Self::In) {
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
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
// Malleable Bitcoin Varint (simplified to u8, u16, u32 variants)
// =============================================================================
//
// Bitcoin varint encoding:
// - Values 0x00-0xFC: encoded as single byte
// - Values 0xFD-0xFFFF: 0xFD prefix + 2 bytes (little-endian u16)
// - Values 0x10000-0xFFFFFFFF: 0xFE prefix + 4 bytes (little-endian u32)
//
// Without enforcement of shortest representation, this is MALLEABLE:
// e.g., value 100 can be encoded as:
//   - [0x64]           (1 byte, direct)
//   - [0xFD, 0x64, 0x00] (3 bytes, u16 form)
//   - [0xFE, 0x64, 0x00, 0x00, 0x00] (5 bytes, u32 form)
pub const VARINT_TAG_U16: u8 = 0xFDu8;

pub const VARINT_TAG_U32: u8 = 0xFEu8;

// Predicate: byte is NOT a tag (valid for direct u8 encoding)
pub struct NotVarintTag;

impl SpecPred<u8> for NotVarintTag {
    open spec fn apply(&self, value: u8) -> bool {
        value != VARINT_TAG_U16 && value != VARINT_TAG_U32
    }
}

// Mapper: u8 -> u32
struct U8ToU32Mapper;

impl Mapper for U8ToU32Mapper {
    type In = u8;

    type Out = u32;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as u32
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o & 0xFF) as u8
    }
}

// Mapper: u16 -> u32
struct U16ToU32Mapper;

impl Mapper for U16ToU32Mapper {
    type In = u16;

    type Out = u32;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as u32
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o & 0xFFFF) as u16
    }
}

proof fn test_malleable_varint_parsing() {
    // Direct u8 form: values 0x00-0xFC encoded as single byte
    let u8_form = Mapped {
        inner: Refined { inner: U8, pred: NotVarintTag },
        mapper: U8ToU32Mapper,
    };

    // u16 form: 0xFD prefix + 2 bytes little-endian
    let u16_form = Mapped { inner: Tagged(U8, VARINT_TAG_U16, U16Le), mapper: U16ToU32Mapper };

    // u32 form: 0xFE prefix + 4 bytes little-endian
    let u32_form = Tagged(U8, VARINT_TAG_U32, U32Le);

    let varint = Alt(u32_form, Alt(u16_form, u8_form));
    assert(varint.unambiguous());

    // Value 100 (0x64) - can be encoded three ways:
    let buf_direct: Seq<u8> = seq![0x64u8];
    let buf_u16: Seq<u8> = seq![0xFDu8, 0x64u8, 0x00u8];
    let buf_u32: Seq<u8> = seq![0xFEu8, 0x64u8, 0x00u8, 0x00u8, 0x00u8];

    assert(varint.spec_parse(buf_direct) is Some);
    assert(varint.spec_parse(buf_u16) is Some);
    assert(varint.spec_parse(buf_u32) is Some);

    // Different encodings consume different byte counts
    // All three encodings represent the same logical value (100)
    if let Some((n1, _v1)) = varint.spec_parse(buf_direct) {
        assert(n1 == 1);
    }
    if let Some((n2, _v2)) = varint.spec_parse(buf_u16) {
        assert(n2 == 3);
    }
    if let Some((n3, _v3)) = varint.spec_parse(buf_u32) {
        assert(n3 == 5);
    }
}

} // verus!
