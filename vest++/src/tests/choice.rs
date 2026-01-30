use crate::combinators::disjoint::*;
use crate::combinators::mapped::spec::{IsoMapper, Mapper};
use crate::combinators::{
    Alt, BerBool, Choice, Either, Fixed, Mapped, Preceded, Refined, Tag, Terminated, U16Le, U32Le,
    U8,
};
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

struct Not0x81;

impl SpecPred<u8> for Not0x81 {
    open spec fn apply(&self, value: u8) -> bool {
        value != 0x81u8
    }
}

proof fn test_alt_flexible_length_encoding() {
    let not_81 = Refined { inner: U8, pred: Not0x81 };
    let short_form = not_81;
    let long_form_prefix = Tag { inner: U8, tag: 0x81u8 };
    let long_form = Preceded(long_form_prefix, not_81);
    let alt_parser = Alt(long_form, short_form);
    assert(().wf());
    assert(alt_parser.unambiguous());

    let buf_short: Seq<u8> = seq![42u8];
    let buf_long: Seq<u8> = seq![0x81u8, 42u8];

    assert(alt_parser.spec_parse(buf_short) matches Some((_, Subset { val: 42u8, pred: _ })));
    assert(alt_parser.spec_parse(buf_long) matches Some((_, Subset { val: 42u8, pred: _ })));
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
    type In = Subset<u8, NotVarintTag>;

    type Out = u32;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i.val as u32
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        Subset { val: (o & 0xFF) as u8, pred: NotVarintTag }
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
    let u16_tag = Tag { inner: U8, tag: VARINT_TAG_U16 };
    let u32_tag = Tag { inner: U8, tag: VARINT_TAG_U32 };

    // Direct u8 form: values 0x00-0xFC encoded as single byte
    let u8_form = Mapped {
        inner: Refined { inner: U8, pred: NotVarintTag },
        mapper: U8ToU32Mapper,
    };

    // u16 form: 0xFD prefix + 2 bytes little-endian
    let u16_form = Mapped { inner: Preceded(u16_tag, U16Le), mapper: U16ToU32Mapper };

    // u32 form: 0xFE prefix + 4 bytes little-endian
    let u32_form = Preceded(u32_tag, U32Le);

    let varint = Alt(u32_form, Alt(u16_form, u8_form));
    assert(().wf());
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
