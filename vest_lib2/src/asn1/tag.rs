use crate::combinators::{Bind, Empty, Sum};
use crate::primitives::base128::*;
use crate::{
    combinators::{implicit::*, mapped::spec::FnSpecMapper, Mapped, Refined, U8},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

/// Bit-mask for the class bits (bits 7–6) of the first tag byte.
pub const TAG_CLASS_MASK: u8 = 0b1100_0000u8;

/// Bit-mask for the "constructed" bit (bit 5) of the first tag byte.
pub const TAG_CONSTRUCTED_MASK: u8 = 0b0010_0000u8;

/// Bit-mask for the tag-number bits (bits 4–0) of the first tag byte.
pub const TAG_NUMBER_MASK: u8 = 0b0001_1111u8;

/// Sentinel value in bits 4–0 signalling the long (high-tag) form.
pub const TAG_LONG_FORM_SENTINEL: u8 = 0b0001_1111u8;

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
#[verifier::ext_equal]
pub enum UniversalTag {
    Boolean,  // 1
    Integer,  // 2
    BitString,  // 3
    OctetString,  // 4
    Null,  // 5
    ObjectIdentifier,  // 6
    Real,  // 9
    Enumerated,  // 10
    Utf8String,  // 12
    RelativeOid,  // 13
    Sequence,  // 16
    Set,  // 17
    NumericString,  // 18
    PrintableString,  // 19
    TeletexString,  // 20
    VideotexString,  // 21
    Ia5String,  // 22
    UtcTime,  // 23
    GeneralizedTime,  // 24
    VisibleString,  // 26
    GeneralString,  // 27
    BmpString,  // 30
}

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
#[verifier::ext_equal]
pub enum Class {
    Universal,
    Application,
    ContextSpecific,
    Private,
}

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
#[verifier::ext_equal]
pub struct Tag {
    pub class: Class,
    pub constructed: bool,
    pub number: UInt,
}

impl DeepView for UniversalTag {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepView for Class {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepView for Tag {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

pub open spec fn class_of_first_byte(b1: u8) -> Class {
    match b1 & TAG_CLASS_MASK {
        0b0000_0000u8 => Class::Universal,
        0b0100_0000u8 => Class::Application,
        0b1000_0000u8 => Class::ContextSpecific,
        _ => Class::Private,
    }
}

pub open spec fn class_bits(class: Class) -> u8 {
    match class {
        Class::Universal => 0b0000_0000u8,
        Class::Application => 0b0100_0000u8,
        Class::ContextSpecific => 0b1000_0000u8,
        Class::Private => 0b1100_0000u8,
    }
}

pub open spec fn constructed_of_first_byte(b1: u8) -> bool {
    b1 & TAG_CONSTRUCTED_MASK != 0
}

pub open spec fn constructed_bit(constructed: bool) -> u8 {
    if constructed {
        TAG_CONSTRUCTED_MASK
    } else {
        0u8
    }
}

pub open spec fn first_byte_from_parts(class: Class, constructed: bool, low_bits: u8) -> u8 {
    class_bits(class) | constructed_bit(constructed) | (low_bits & TAG_NUMBER_MASK)
}

type TagWire = Bind<U8, spec_fn(u8) -> Sum<Empty, Refined<Base128Fmt<true>, PredFnSpec<UInt>>>>;

type TagFmt__ = Mapped<TagWire, FnSpecMapper<(u8, Sum<(), UInt>), Tag>>;

#[verusfmt::skip]
pub(super) open(super) spec fn tag_wire() -> TagWire {
    Bind(U8, |b1: u8| {
        if b1 & TAG_NUMBER_MASK == TAG_LONG_FORM_SENTINEL {
            R(Refined(Base128Fmt::<true>, |n: UInt| n >= TAG_LONG_FORM_SENTINEL as UInt))
        } else {
            L(Empty)
        }
    })
}

pub(super) open(super) spec fn tag_fmt() -> TagFmt__ {
    Mapped {
        inner: tag_wire(),
        mapper: (
            |r: (u8, Sum<(), UInt>)|
                {
                    let (b1, rest) = r;
                    Tag {
                        class: class_of_first_byte(b1),
                        constructed: constructed_of_first_byte(b1),
                        number: match rest {
                            L(()) => (b1 & TAG_NUMBER_MASK) as UInt,
                            R(n) => n,
                        },
                    }
                },
            |tag: Tag|
                {
                    if tag.number < TAG_LONG_FORM_SENTINEL as UInt {
                        (first_byte_from_parts(tag.class, tag.constructed, tag.number as u8), L(()))
                    } else {
                        (
                            first_byte_from_parts(
                                tag.class,
                                tag.constructed,
                                TAG_LONG_FORM_SENTINEL,
                            ),
                            R(tag.number),
                        )
                    }
                },
        ),
    }
}

// ── Bit-vector helpers ────────────────────────────────────────────────────────
proof fn lemma_class_bits_roundtrip(b1: u8)
    ensures
        class_bits(class_of_first_byte(b1)) == (b1 & TAG_CLASS_MASK),
{
    let cls = b1 & TAG_CLASS_MASK;
    assert({
        ||| cls == 0b0000_0000u8
        ||| cls == 0b0100_0000u8
        ||| cls == 0b1000_0000u8
        ||| cls == 0b1100_0000u8
    }) by (bit_vector)
        requires
            cls == (b1 & TAG_CLASS_MASK),
    ;
}

proof fn lemma_class_bits_only_class_mask(class: Class)
    ensures
        class_bits(class) & TAG_CONSTRUCTED_MASK == 0u8,
        class_bits(class) & TAG_NUMBER_MASK == 0u8,
        class_bits(class) & TAG_CLASS_MASK == class_bits(class),
{
    assert(forall|cls: u8|
        {
            ||| cls == 0b0000_0000u8
            ||| cls == 0b0100_0000u8
            ||| cls == 0b1000_0000u8
            ||| cls == 0b1100_0000u8
        } ==> (cls & TAG_CONSTRUCTED_MASK == 0u8 && cls & TAG_NUMBER_MASK == 0u8 && (cls
            & TAG_CLASS_MASK) == cls)) by (bit_vector);
}

proof fn lemma_first_byte_from_parts_roundtrip(class: Class, constructed: bool, low_bits: u8)
    ensures
        class_of_first_byte(first_byte_from_parts(class, constructed, low_bits)) == class,
        constructed_of_first_byte(first_byte_from_parts(class, constructed, low_bits))
            == constructed,
{
    let fb = first_byte_from_parts(class, constructed, low_bits);
    let cb = class_bits(class);
    lemma_class_bits_only_class_mask(class);

    assert(fb & TAG_CLASS_MASK == cb && (fb & TAG_CONSTRUCTED_MASK != 0u8) == constructed)
        by (bit_vector)
        requires
            fb == cb | constructed_bit(constructed) | (low_bits & TAG_NUMBER_MASK),
            cb & TAG_CONSTRUCTED_MASK == 0u8,
            cb & TAG_NUMBER_MASK == 0u8,
            (cb & TAG_CLASS_MASK) == cb,
    ;
}

proof fn lemma_first_byte_roundtrip(b1: u8)
    ensures
        first_byte_from_parts(
            class_of_first_byte(b1),
            constructed_of_first_byte(b1),
            b1 & TAG_NUMBER_MASK,
        ) == b1,
{
    lemma_class_bits_roundtrip(b1);
    let fb = first_byte_from_parts(
        class_of_first_byte(b1),
        constructed_of_first_byte(b1),
        b1 & TAG_NUMBER_MASK,
    );
    let cb = class_bits(class_of_first_byte(b1));
    assert(fb == b1) by (bit_vector)
        requires
            fb == cb | constructed_bit(constructed_of_first_byte(b1)) | ((b1 & TAG_NUMBER_MASK)
                & TAG_NUMBER_MASK),
            cb == (b1 & TAG_CLASS_MASK),
    ;
}

proof fn lemma_tag_fmt_sound_nonmal_inv()
    ensures
        tag_fmt().sound_inv(),
        tag_fmt().nonmal_inv(),
{
    let fmt = tag_fmt();
    assert forall|v| fmt.inner.consistent(v) implies (fmt.mapper.1)((fmt.mapper.0)(v)) == v by {
        let (b1, rest) = v;
        lemma_first_byte_roundtrip(b1);
        if b1 & TAG_NUMBER_MASK == TAG_LONG_FORM_SENTINEL {
        } else {
            let num = (b1 & TAG_NUMBER_MASK) as UInt;
            assert(num < TAG_LONG_FORM_SENTINEL as UInt) by (bit_vector)
                requires
                    (b1 & TAG_NUMBER_MASK) != TAG_LONG_FORM_SENTINEL,
                    num == (b1 & TAG_NUMBER_MASK) as UInt,
            ;
        }
    }
}

proof fn lemma_tag_fmt_unambiguous()
    ensures
        tag_fmt().unambiguous(),
{
    let fmt = tag_fmt();
    assert forall|tag: Tag| fmt.consistent(tag) implies (fmt.mapper.0)((fmt.mapper.1)(tag))
        == tag by {
        if tag.number < TAG_LONG_FORM_SENTINEL as UInt {
            let num = tag.number;
            let low = num as u8;
            let cons_flag = tag.constructed;
            lemma_first_byte_from_parts_roundtrip(tag.class, cons_flag, low);
            lemma_class_bits_only_class_mask(tag.class);
            let fb = first_byte_from_parts(tag.class, cons_flag, low);
            let cb = class_bits(tag.class);
            assert((fb & TAG_NUMBER_MASK) as UInt == num) by (bit_vector)
                requires
                    fb == cb | constructed_bit(cons_flag) | (low & TAG_NUMBER_MASK),
                    cb & TAG_NUMBER_MASK == 0u8,
                    low == num as u8,
                    num < TAG_LONG_FORM_SENTINEL as UInt,
            ;
        } else {
            lemma_first_byte_from_parts_roundtrip(
                tag.class,
                tag.constructed,
                TAG_LONG_FORM_SENTINEL,
            );
        }
    }
}

mod derived_specs {
    use super::*;
    use super::super::TagFmt;

    impl SpecParser for TagFmt {
        type PVal = Tag;

        open(super) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            tag_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for TagFmt {
        type Val = Tag;

        open(super) spec fn consistent(&self, v: Self::Val) -> bool {
            tag_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for TagFmt {
        type SValue = Tag;

        open(super) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            tag_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TagFmt {
        type SVal = Tag;

        open(super) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            tag_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for TagFmt {
        type T = Tag;

        open(super) spec fn byte_len(&self, v: Self::T) -> nat {
            tag_fmt().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::TagFmt;

    impl SafeParser for TagFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            tag_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TagFmt {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            tag_fmt().lemma_productive(s);
        }
    }

    impl SoundParser for TagFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_tag_fmt_sound_nonmal_inv();
            tag_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_tag_fmt_sound_nonmal_inv();
            tag_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TagFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            tag_fmt().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            tag_fmt().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TagFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            tag_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TagFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_tag_fmt_unambiguous();
            tag_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NoLookAhead for TagFmt {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            tag_fmt().lemma_no_lookahead(i1, i2);
        }
    }

    impl NonMalleable for TagFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_tag_fmt_sound_nonmal_inv();
            tag_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TagFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            tag_fmt().lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TagFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            tag_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

}

} // verus!
