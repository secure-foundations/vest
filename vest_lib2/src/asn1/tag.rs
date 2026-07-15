use crate::combinators::{Bind, Empty, Sum};
use crate::core::exec::input::*;
use crate::core::exec::output::*;
use crate::core::exec::{parser::*, serializer::*, ParseError, ParseErrorKind};
use crate::primitives::base128::*;
use crate::{
    combinators::{
        implicit::*,
        mapped::spec::{FnSpecMapper, SpecMap},
        Mapped, Refined, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::prelude::*;
use OutputBuf;
use Sum::Inl as L;
use Sum::Inr as R;

#[cfg(verus_only)]
use vstd::std_specs::convert::FromSpecImpl;

verus! {

/// Bit-mask for the class bits (bits 7–6) of the first tag byte.
pub const TAG_CLASS_MASK: u8 = 0b1100_0000u8;

/// Bit-mask for the "constructed" bit (bit 5) of the first tag byte.
pub const TAG_CONSTRUCTED_MASK: u8 = 0b0010_0000u8;

/// Bit-mask for the tag-number bits (bits 4–0) of the first tag byte.
pub const TAG_NUMBER_MASK: u8 = 0b0001_1111u8;

/// Sentinel value in bits 4–0 signalling the long (high-tag) form.
pub const TAG_LONG_FORM_SENTINEL: u8 = 0b0001_1111u8;

#[derive(StructuralEq, Clone, Copy, PartialEq, Eq, Debug)]
#[verifier::ext_equal]
#[repr(u64)]
pub enum TagNumber {
    EOC = 0,
    Boolean = 1,
    Integer = 2,
    BitString = 3,
    OctetString = 4,
    Null = 5,
    ObjectIdentifier = 6,
    Real = 9,
    Enumerated = 10,
    Utf8String = 12,
    RelativeOid = 13,
    Sequence = 16,
    Set = 17,
    NumericString = 18,
    PrintableString = 19,
    TeletexString = 20,
    VideotexString = 21,
    Ia5String = 22,
    UtcTime = 23,
    GeneralizedTime = 24,
    VisibleString = 26,
    GeneralString = 27,
    BmpString = 30,
    Other { tag_num: UInt },
}

#[derive(StructuralEq, Clone, Copy, PartialEq, Eq, Debug)]
#[verifier::ext_equal]
pub enum Class {
    Universal,
    Application,
    ContextSpecific,
    Private,
}

#[derive(StructuralEq, Clone, Copy, PartialEq, Eq, Debug)]
#[verifier::ext_equal]
pub struct Tag {
    pub class: Class,
    pub constructed: bool,
    pub number: TagNumber,
}

pub open spec fn tag_num_to_uint(num: TagNumber) -> UInt {
    match num {
        TagNumber::EOC => 0,
        TagNumber::Boolean => 1,
        TagNumber::Integer => 2,
        TagNumber::BitString => 3,
        TagNumber::OctetString => 4,
        TagNumber::Null => 5,
        TagNumber::ObjectIdentifier => 6,
        TagNumber::Real => 9,
        TagNumber::Enumerated => 10,
        TagNumber::Utf8String => 12,
        TagNumber::RelativeOid => 13,
        TagNumber::Sequence => 16,
        TagNumber::Set => 17,
        TagNumber::NumericString => 18,
        TagNumber::PrintableString => 19,
        TagNumber::TeletexString => 20,
        TagNumber::VideotexString => 21,
        TagNumber::Ia5String => 22,
        TagNumber::UtcTime => 23,
        TagNumber::GeneralizedTime => 24,
        TagNumber::VisibleString => 26,
        TagNumber::GeneralString => 27,
        TagNumber::BmpString => 30,
        TagNumber::Other { tag_num } => tag_num,
    }
}

pub open spec fn uint_to_tag_num(num: UInt) -> TagNumber {
    match num {
        0 => TagNumber::EOC,
        1 => TagNumber::Boolean,
        2 => TagNumber::Integer,
        3 => TagNumber::BitString,
        4 => TagNumber::OctetString,
        5 => TagNumber::Null,
        6 => TagNumber::ObjectIdentifier,
        9 => TagNumber::Real,
        10 => TagNumber::Enumerated,
        12 => TagNumber::Utf8String,
        13 => TagNumber::RelativeOid,
        16 => TagNumber::Sequence,
        17 => TagNumber::Set,
        18 => TagNumber::NumericString,
        19 => TagNumber::PrintableString,
        20 => TagNumber::TeletexString,
        21 => TagNumber::VideotexString,
        22 => TagNumber::Ia5String,
        23 => TagNumber::UtcTime,
        24 => TagNumber::GeneralizedTime,
        26 => TagNumber::VisibleString,
        27 => TagNumber::GeneralString,
        30 => TagNumber::BmpString,
        other => TagNumber::Other { tag_num: other },
    }
}

pub open spec fn tag_number_wf(num: TagNumber) -> bool {
    num matches TagNumber::Other { tag_num } ==> {
        &&& !matches!(tag_num, 0 | 1 | 2 | 3 | 4 | 5 | 6 | 9 | 10 | 12 | 13 | 16 | 17 | 18 | 19 | 20 | 21
            | 22 | 23 | 24 | 26 | 27 | 30)
        &&& nat_to_base128(tag_num as nat).len() <= BASE128_MAX_BYTES
    }
}

impl From<u64> for TagNumber {
    fn from(num: u64) -> Self {
        match num {
            0 => TagNumber::EOC,
            1 => TagNumber::Boolean,
            2 => TagNumber::Integer,
            3 => TagNumber::BitString,
            4 => TagNumber::OctetString,
            5 => TagNumber::Null,
            6 => TagNumber::ObjectIdentifier,
            9 => TagNumber::Real,
            10 => TagNumber::Enumerated,
            12 => TagNumber::Utf8String,
            13 => TagNumber::RelativeOid,
            16 => TagNumber::Sequence,
            17 => TagNumber::Set,
            18 => TagNumber::NumericString,
            19 => TagNumber::PrintableString,
            20 => TagNumber::TeletexString,
            21 => TagNumber::VideotexString,
            22 => TagNumber::Ia5String,
            23 => TagNumber::UtcTime,
            24 => TagNumber::GeneralizedTime,
            26 => TagNumber::VisibleString,
            27 => TagNumber::GeneralString,
            30 => TagNumber::BmpString,
            other => TagNumber::Other { tag_num: other as UInt },
        }
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<u64> for TagNumber {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: u64) -> TagNumber {
        uint_to_tag_num(v as UInt)
    }
}

impl DeepView for TagNumber {
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
pub(crate) open(crate) spec fn tag_wire() -> TagWire {
    Bind(U8, |b1: u8| {
        if b1 & TAG_NUMBER_MASK == TAG_LONG_FORM_SENTINEL {
            R(Refined(Base128Fmt::<true>, |n: UInt| n >= TAG_LONG_FORM_SENTINEL as UInt))
        } else {
            L(Empty)
        }
    })
}

pub(crate) open(crate) spec fn tag_fmt() -> TagFmt__ {
    Mapped {
        inner: tag_wire(),
        mapper: (
            |r: (u8, Sum<(), UInt>)|
                {
                    let (b1, rest) = r;
                    let num = match rest {
                        L(()) => (b1 & TAG_NUMBER_MASK) as UInt,
                        R(n) => n,
                    };
                    Tag {
                        class: class_of_first_byte(b1),
                        constructed: constructed_of_first_byte(b1),
                        number: uint_to_tag_num(num),
                    }
                },
            |tag: Tag|
                {
                    let num = tag_num_to_uint(tag.number);
                    if num < TAG_LONG_FORM_SENTINEL as UInt {
                        (first_byte_from_parts(tag.class, tag.constructed, num as u8), L(()))
                    } else {
                        (
                            first_byte_from_parts(
                                tag.class,
                                tag.constructed,
                                TAG_LONG_FORM_SENTINEL,
                            ),
                            R(num),
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
        first_byte_from_parts(class, constructed, low_bits) & TAG_NUMBER_MASK == low_bits
            & TAG_NUMBER_MASK,
{
    let fb = first_byte_from_parts(class, constructed, low_bits);
    let cb = class_bits(class);
    let cbit = constructed_bit(constructed);
    lemma_class_bits_only_class_mask(class);

    assert(fb & TAG_CLASS_MASK == cb && (fb & TAG_CONSTRUCTED_MASK != 0u8) == constructed && fb
        & TAG_NUMBER_MASK == low_bits & TAG_NUMBER_MASK) by (bit_vector)
        requires
            fb == cb | cbit | (low_bits & TAG_NUMBER_MASK),
            cb & TAG_CONSTRUCTED_MASK == 0u8,
            cb & TAG_NUMBER_MASK == 0u8,
            (cb & TAG_CLASS_MASK) == cb,
            cbit == TAG_CONSTRUCTED_MASK || cbit == 0u8,
            constructed ==> cbit == TAG_CONSTRUCTED_MASK,
            !constructed ==> cbit == 0u8,
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

proof fn lemma_tag_fmt_unambiguous(tag: Tag)
    requires
        tag_fmt().consistent(tag),
        tag_number_wf(tag.number),
    ensures
        (tag_fmt().mapper.0)((tag_fmt().mapper.1)(tag)) == tag,
{
    let num = tag_num_to_uint(tag.number);
    if num < TAG_LONG_FORM_SENTINEL as UInt {
        let low = num as u8;
        lemma_first_byte_from_parts_roundtrip(tag.class, tag.constructed, low);
        assert(low & TAG_NUMBER_MASK == low) by (bit_vector)
            requires
                low == num as u8,
                num < TAG_LONG_FORM_SENTINEL as UInt,
        ;
    } else {
        lemma_first_byte_from_parts_roundtrip(tag.class, tag.constructed, TAG_LONG_FORM_SENTINEL);
    }
}

proof fn lemma_tag_wf_implies_tag_fmt_consistent(tag: Tag)
    requires
        tag_number_wf(tag.number),
    ensures
        tag_fmt().consistent(tag),
{
    let num = tag_num_to_uint(tag.number);
    assert(TAG_LONG_FORM_SENTINEL & TAG_NUMBER_MASK == TAG_LONG_FORM_SENTINEL) by (bit_vector);
    if num < TAG_LONG_FORM_SENTINEL as UInt {
        let low = num as u8;
        lemma_first_byte_from_parts_roundtrip(tag.class, tag.constructed, low);
        assert(low & TAG_NUMBER_MASK == low) by (bit_vector)
            requires
                low == num as u8,
                num < TAG_LONG_FORM_SENTINEL as UInt,
        ;
    } else {
        lemma_first_byte_from_parts_roundtrip(tag.class, tag.constructed, TAG_LONG_FORM_SENTINEL);
        lemma_base128_fmt_consistent::<true>(num);
    }
}

mod derived_specs {
    use super::*;
    use super::super::TagFmt;

    impl SpecParser for TagFmt {
        type PVal = Tag;

        open(crate) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            tag_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for TagFmt {
        type Val = Tag;

        open(crate) spec fn consistent(&self, v: Self::Val) -> bool {
            tag_number_wf(v.number)
        }
    }

    impl SpecSerializerDps for TagFmt {
        type SValue = Tag;

        open(crate) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            tag_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TagFmt {
        type SVal = Tag;

        open(crate) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            tag_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for TagFmt {
        type T = Tag;

        open(crate) spec fn byte_len(&self, v: Self::T) -> nat {
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
            lemma_tag_wf_implies_tag_fmt_consistent(v);
            lemma_tag_fmt_unambiguous(v);
            tag_fmt().inner.theorem_serialize_dps_parse_roundtrip(tag_fmt().mapper.1(v), obuf);
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

impl Parser<&[u8]> for super::TagFmt {
    type PT = Tag;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use crate::core::spec::SoundParser::lemma_parse_sound_value;

        let _ = ibuf.len();

        let (n1, b1): (usize, u8) = U8.parse(ibuf)?;
        let rest = ibuf.skip(n1);

        let (n2, num) = if b1 & TAG_NUMBER_MASK == TAG_LONG_FORM_SENTINEL {
            let (n2, num) = Base128Fmt::<true>.parse(&rest)?;
            if num < TAG_LONG_FORM_SENTINEL as UInt {
                return Err(ParseError::non_canonical());
            }
            (n2, num)
        } else {
            (0, (b1 & TAG_NUMBER_MASK) as UInt)
        };

        let class = match b1 & TAG_CLASS_MASK {
            0b0000_0000u8 => Class::Universal,
            0b0100_0000u8 => Class::Application,
            0b1000_0000u8 => Class::ContextSpecific,
            _ => Class::Private,
        };
        let constructed = b1 & TAG_CONSTRUCTED_MASK != 0;
        let number = match num {
            0 => TagNumber::EOC,
            1 => TagNumber::Boolean,
            2 => TagNumber::Integer,
            3 => TagNumber::BitString,
            4 => TagNumber::OctetString,
            5 => TagNumber::Null,
            6 => TagNumber::ObjectIdentifier,
            9 => TagNumber::Real,
            10 => TagNumber::Enumerated,
            12 => TagNumber::Utf8String,
            13 => TagNumber::RelativeOid,
            16 => TagNumber::Sequence,
            17 => TagNumber::Set,
            18 => TagNumber::NumericString,
            19 => TagNumber::PrintableString,
            20 => TagNumber::TeletexString,
            21 => TagNumber::VideotexString,
            22 => TagNumber::Ia5String,
            23 => TagNumber::UtcTime,
            24 => TagNumber::GeneralizedTime,
            26 => TagNumber::VisibleString,
            27 => TagNumber::GeneralString,
            30 => TagNumber::BmpString,
            other => TagNumber::Other { tag_num: other },
        };

        Ok((n1 + n2, Tag { class, constructed, number }))
    }
}

impl<Output: OutputBuf> Serializer<Output, Tag> for super::TagFmt {
    fn serialize_into(&self, v: &Tag, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        let num = match v.number {
            TagNumber::EOC => 0,
            TagNumber::Boolean => 1,
            TagNumber::Integer => 2,
            TagNumber::BitString => 3,
            TagNumber::OctetString => 4,
            TagNumber::Null => 5,
            TagNumber::ObjectIdentifier => 6,
            TagNumber::Real => 9,
            TagNumber::Enumerated => 10,
            TagNumber::Utf8String => 12,
            TagNumber::RelativeOid => 13,
            TagNumber::Sequence => 16,
            TagNumber::Set => 17,
            TagNumber::NumericString => 18,
            TagNumber::PrintableString => 19,
            TagNumber::TeletexString => 20,
            TagNumber::VideotexString => 21,
            TagNumber::Ia5String => 22,
            TagNumber::UtcTime => 23,
            TagNumber::GeneralizedTime => 24,
            TagNumber::VisibleString => 26,
            TagNumber::GeneralString => 27,
            TagNumber::BmpString => 30,
            TagNumber::Other { tag_num } => tag_num,
        };

        let class_bits = match v.class {
            Class::Universal => 0b0000_0000u8,
            Class::Application => 0b0100_0000u8,
            Class::ContextSpecific => 0b1000_0000u8,
            Class::Private => 0b1100_0000u8,
        };
        let constructed_bit = if v.constructed {
            TAG_CONSTRUCTED_MASK
        } else {
            0u8
        };
        proof {
            lemma_tag_wf_implies_tag_fmt_consistent(*v);
        }
        if num < TAG_LONG_FORM_SENTINEL as UInt {
            let low = num as u8;
            let b1 = class_bits | constructed_bit | (low & TAG_NUMBER_MASK);
            U8.serialize_into(&b1, obuf);
        } else {
            let b1 = class_bits | constructed_bit | TAG_LONG_FORM_SENTINEL & TAG_NUMBER_MASK;
            U8.serialize_into(&b1, obuf);
            Base128Fmt::<true>.serialize_into(&num, obuf);
        }
    }
}

impl Prepare<Tag> for super::TagFmt {
    fn prepare(&self, v: &Tag) -> Result<usize, PreSerializeError> {
        let num = match v.number {
            TagNumber::EOC => 0,
            TagNumber::Boolean => 1,
            TagNumber::Integer => 2,
            TagNumber::BitString => 3,
            TagNumber::OctetString => 4,
            TagNumber::Null => 5,
            TagNumber::ObjectIdentifier => 6,
            TagNumber::Real => 9,
            TagNumber::Enumerated => 10,
            TagNumber::Utf8String => 12,
            TagNumber::RelativeOid => 13,
            TagNumber::Sequence => 16,
            TagNumber::Set => 17,
            TagNumber::NumericString => 18,
            TagNumber::PrintableString => 19,
            TagNumber::TeletexString => 20,
            TagNumber::VideotexString => 21,
            TagNumber::Ia5String => 22,
            TagNumber::UtcTime => 23,
            TagNumber::GeneralizedTime => 24,
            TagNumber::VisibleString => 26,
            TagNumber::GeneralString => 27,
            TagNumber::BmpString => 30,
            TagNumber::Other { tag_num } => {
                if matches!(tag_num, 0 | 1 | 2 | 3 | 4 | 5 | 6 | 9 | 10 | 12 | 13 | 16 | 17 | 18 | 19 | 20 | 21
                    | 22 | 23 | 24 | 26 | 27 | 30) {
                    return Err(PreSerializeError::custom("Invalid tag number"));
                }
                tag_num
            },
        };

        proof {
            lemma_to_base128_len_bounds();
            lemma_base128_fmt_byte_len::<true>(num);
        }
        let nbytes = Base128Fmt::<true>.length(&num);
        if nbytes > BASE128_MAX_BYTES {
            return Err(PreSerializeError::length_too_large());
        }
        proof {
            assert(tag_number_wf(v.deep_view().number));
            lemma_tag_wf_implies_tag_fmt_consistent(v.deep_view());
        }

        if num < TAG_LONG_FORM_SENTINEL as UInt {
            Ok(1)
        } else {
            Ok(1 + nbytes)
        }
    }
}

impl ByteLen<Tag> for super::TagFmt {
    fn length(&self, v: &Tag) -> usize {
        let num = match v.number {
            TagNumber::EOC => 0,
            TagNumber::Boolean => 1,
            TagNumber::Integer => 2,
            TagNumber::BitString => 3,
            TagNumber::OctetString => 4,
            TagNumber::Null => 5,
            TagNumber::ObjectIdentifier => 6,
            TagNumber::Real => 9,
            TagNumber::Enumerated => 10,
            TagNumber::Utf8String => 12,
            TagNumber::RelativeOid => 13,
            TagNumber::Sequence => 16,
            TagNumber::Set => 17,
            TagNumber::NumericString => 18,
            TagNumber::PrintableString => 19,
            TagNumber::TeletexString => 20,
            TagNumber::VideotexString => 21,
            TagNumber::Ia5String => 22,
            TagNumber::UtcTime => 23,
            TagNumber::GeneralizedTime => 24,
            TagNumber::VisibleString => 26,
            TagNumber::GeneralString => 27,
            TagNumber::BmpString => 30,
            TagNumber::Other { tag_num } => tag_num,
        };

        proof {
            lemma_to_base128_len_bounds();
            lemma_base128_fmt_byte_len::<true>(num);
            lemma_first_byte_from_parts_roundtrip(v.class, v.constructed, TAG_LONG_FORM_SENTINEL);
            assert(TAG_LONG_FORM_SENTINEL & TAG_NUMBER_MASK == TAG_LONG_FORM_SENTINEL)
                by (bit_vector);
        }
        let nbytes = Base128Fmt::<true>.length(&num);

        if num < TAG_LONG_FORM_SENTINEL as UInt {
            1
        } else {
            1 + nbytes
        }
    }
}

impl super::TagFmt {
    pub const EOC: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::EOC,
    };

    pub const BOOLEAN: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::Boolean,
    };

    pub const INTEGER: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::Integer,
    };

    pub const NULL: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::Null,
    };

    pub const OBJECT_IDENTIFIER: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::ObjectIdentifier,
    };

    pub const REAL: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::Real,
    };

    pub const ENUMERATED: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::Enumerated,
    };

    pub const RELATIVE_OID: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::RelativeOid,
    };

    pub const BIT_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::BitString,
    };

    pub const OCTET_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::OctetString,
    };

    pub const UTF8_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::Utf8String,
    };

    pub const NUMERIC_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::NumericString,
    };

    pub const PRINTABLE_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::PrintableString,
    };

    pub const TELETEX_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::TeletexString,
    };

    pub const VIDEOTEX_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::VideotexString,
    };

    pub const IA5_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::Ia5String,
    };

    pub const UTC_TIME: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::UtcTime,
    };

    pub const GENERALIZED_TIME: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::GeneralizedTime,
    };

    pub const VISIBLE_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::VisibleString,
    };

    pub const GENERAL_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::GeneralString,
    };

    pub const BMP_STRING: Tag = Tag {
        class: Class::Universal,
        constructed: false,
        number: TagNumber::BmpString,
    };

    pub const BIT_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::BitString,
    };

    pub const OCTET_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::OctetString,
    };

    pub const UTF8_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::Utf8String,
    };

    pub const NUMERIC_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::NumericString,
    };

    pub const PRINTABLE_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::PrintableString,
    };

    pub const TELETEX_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::TeletexString,
    };

    pub const VIDEOTEX_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::VideotexString,
    };

    pub const IA5_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::Ia5String,
    };

    pub const UTC_TIME_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::UtcTime,
    };

    pub const GENERALIZED_TIME_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::GeneralizedTime,
    };

    pub const VISIBLE_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::VisibleString,
    };

    pub const GENERAL_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::GeneralString,
    };

    pub const BMP_STRING_CONSTRUCTED: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::BmpString,
    };

    pub const SEQUENCE: Tag = Tag {
        class: Class::Universal,
        constructed: true,
        number: TagNumber::Sequence,
    };

    pub const SET: Tag = Tag { class: Class::Universal, constructed: true, number: TagNumber::Set };
}

use crate::combinators::Const;

pub broadcast proof fn lemma_const_tag_fmt_exec_inv(fmt: Const<super::TagFmt, Tag>)
    ensures
        #![all_triggers]
        <_ as Parser<&[u8]>>::exec_inv(&fmt),
        <_ as Prepare<Tag>>::exec_inv(&fmt),
{
    crate::combinators::refined::exec::lemma_const_exec_inv(&fmt);
}

} // verus!
/*
*
some test functions
*/
verus! {

fn test_exec_const_fmt(buf: &&[u8]) -> PResult<u16> {
    use crate::combinators::U16Be;
    let const_u16_fmt = Const(U16Be, 0x1234u16);
    let (n, v) = const_u16_fmt.parse(buf)?;
    if let Ok(len) = const_u16_fmt.prepare(&v) {
        let mut obuf = vec![0; len];
        const_u16_fmt.serialize(&v, &mut obuf);
        proof {
            const_u16_fmt.theorem_parse_serialize_roundtrip(buf@);
            assert(obuf@ == buf@.take(n as int));
        }
    }
    Err(ParseError::custom("Test function, not meant to succeed"))
}

fn test_exec_tag_fmt(buf: &&[u8]) -> PResult<Tag> {
    broadcast use lemma_const_tag_fmt_exec_inv;

    let asn_bool_tag_fmt = Const(super::TagFmt, super::TagFmt::BOOLEAN);
    let (n, tag) = asn_bool_tag_fmt.parse(buf)?;
    if let Ok(len) = asn_bool_tag_fmt.prepare(&tag) {
        let mut obuf = vec![0; len];
        asn_bool_tag_fmt.serialize(&tag, &mut obuf);

        proof {
            asn_bool_tag_fmt.theorem_parse_serialize_roundtrip(buf@);
            assert(obuf@ == buf@.take(n as int));
        }
    }
    Err(ParseError::custom("Test function, not meant to succeed"))
}

} // verus!
/*
// somehow needed for regular `cargo check/build/test`
 *
 */
#[cfg(not(verus_keep_ghost))]
unsafe impl Structural for TagNumber {}
#[cfg(not(verus_keep_ghost))]
unsafe impl Structural for Class {}
#[cfg(not(verus_keep_ghost))]
unsafe impl Structural for Tag {}
