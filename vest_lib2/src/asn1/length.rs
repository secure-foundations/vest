use crate::combinators::{Bind, Empty, Sum, Void};
use crate::core::exec::input::*;
use crate::core::exec::output::*;
use crate::core::exec::{parser::*, serializer::*, ParseError, ParseErrorKind};
use crate::primitives::base256::*;
use crate::Never;
use crate::{
    combinators::{
        implicit::*,
        length::AsLen,
        mapped::spec::{FnSpecMapper, LosslessMapper, LossyMapper, SpecMapper},
        Alt, Choice, Const, Implicit, Mapped, Refined, TryMap, Varied, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::arithmetic::power::*;
use vstd::prelude::*;
use OutputBuf;
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

pub const SHORT_FORM_MAX: u8 = 0x7F;

pub const LONG_FORM_MIN_COUNT: u8 = 1;

pub const LONG_FORM_MAX_COUNT: u8 = 126;

type LengthWireFmt<const DER: bool, const BOUNDED: bool = false> = Bind<
    U8,
    spec_fn(u8) -> Sum<Empty, Sum<Refined<Varied<u8>, PredFnSpec<Seq<u8>>>, Void>>,
>;

type NatLengthFmt<const DER: bool> = Mapped<
    LengthWireFmt<DER>,
    FnSpecMapper<(u8, Sum<(), Sum<Seq<u8>, Never>>), nat>,
>;

type LengthFmt<const DER: bool> = Mapped<
    LengthWireFmt<DER, true>,
    FnSpecMapper<(u8, Sum<(), Sum<Seq<u8>, Never>>), usize>,
>;

type BerLengthFmt__ = Mapped<
    Choice<Const<U8, u8>, super::LengthFmt<false>>,
    FnSpecMapper<Sum<u8, usize>, super::BerLength>,
>;

pub open spec fn ber_length_fmt() -> BerLengthFmt__ {
    Mapped {
        inner: Choice(Const(U8, 0x80u8), super::LengthFmt::<false>),
        mapper: (
            |v: Sum<u8, usize>|
                match v {
                    L(_) => super::BerLength::Indefinite,
                    R(n) => super::BerLength::Definite(n),
                },
            |v: super::BerLength|
                match v {
                    super::BerLength::Indefinite => L(0x80u8),
                    super::BerLength::Definite(n) => R(n),
                },
        ),
    }
}

/// 8.1.3.5 In the long form, the length octets shall consist of an initial octet and **one or more** subsequent octets. The initial
/// octet shall be encoded as follows:
///
/// a) bit 8 shall be one;
/// b) bits 7 to 1 shall encode the number of subsequent octets in the length octets, as an unsigned binary integer with
/// bit 7 as the most significant bit;
/// c) the value 11111111 shall not be used.
#[verusfmt::skip]
pub(super) open(super) spec fn length_wire<const DER: bool, const BOUNDED: bool>() -> LengthWireFmt<DER, BOUNDED > {
    Bind(U8, |b1: u8| {
        match b1 {
            b if b <= SHORT_FORM_MAX => L(Empty),
            b if 0b1000_0000 < b < 0b1111_1111 => R(L(
                Refined(Varied(b & 0b0111_1111),  // clear the high bit to get the count
                    |bytes: Seq<u8>| {
                        &&& DER ==> der_long_len_bytes_minimal(bytes)
                        &&& BOUNDED ==> bytes.len() <= size_of_usize()
                    }),
                ),
            ),
            _ => R(R(Void("Invalid first byte for ASN1 length"))),
        }
    })
}

pub(super) open(super) spec fn nat_length_fmt<const DER: bool>() -> NatLengthFmt<DER> {
    Mapped {
        inner: length_wire::<DER, false>(),
        mapper: (
            |r: (u8, Sum<(), Sum<Seq<u8>, Never>>)|
                {
                    let (b1, rest) = r;
                    match rest {
                        L(()) => b1 as nat,
                        R(L(bytes)) => nat_from_be_bytes(bytes),
                        _ => arbitrary(),  // unreachable
                    }
                },
            |n: nat|
                if n <= SHORT_FORM_MAX as nat {
                    (n as u8, L(()))
                } else {
                    let bytes = nat_to_be_bytes(n);
                    // set the high bit to indicate long form
                    (0b1000_0000 | (bytes.len() as u8), R(L(bytes)))
                },
        ),
    }
}

pub(super) open(super) spec fn length_fmt<const DER: bool>() -> LengthFmt<DER> {
    Mapped {
        inner: length_wire::<DER, true>(),
        mapper: (
            |r: (u8, Sum<(), Sum<Seq<u8>, Never>>)|
                {
                    let (b1, rest) = r;
                    match rest {
                        L(()) => b1 as usize,
                        R(L(bytes)) => nat_from_be_bytes(bytes) as usize,
                        _ => arbitrary(),  // unreachable
                    }
                },
            |n: usize|
                if n <= SHORT_FORM_MAX as usize {
                    (n as u8, L(()))
                } else {
                    let bytes = nat_to_be_bytes(n as nat);
                    (0b1000_0000 | (bytes.len() as u8), R(L(bytes)))
                },
        ),
    }
}

/// DER requires minimality, so
/// 1. for single-byte length in the long form, the value must be > 127 (i.e. not encodable in short form)
/// 2. for multi-byte length in the long form, the first byte must be non-zero (i.e. no leading zeros)
pub open spec fn der_long_len_bytes_minimal(bytes: Seq<u8>) -> bool {
    &&& bytes.len() == 1 ==> bytes[0] > SHORT_FORM_MAX
    &&& bytes.len() > 1 ==> bytes[0] != 0x00u8
}

proof fn lemma_length_wire_long_form_roundtrip(b1: u8, bytes: Seq<u8>)
    requires
        0b1000_0000u8 < b1 < 0b1111_1111u8,
        der_long_len_bytes_minimal(bytes),
        bytes.len() == (b1 & 0b0111_1111) as nat,
    ensures
        nat_to_be_bytes(nat_from_be_bytes(bytes)) == bytes,
        (0b1000_0000u8 | (bytes.len() as u8)) == b1,
{
    assert(bytes.len() > 0) by {
        assert((b1 & 0b0111_1111u8) >= 1u8) by (bit_vector)
            requires
                0b1000_0000u8 < b1 < 0b1111_1111u8,
        ;
    }
    lemma_from_to_be_bytes_roundtrip(bytes);
    assert((0b1000_0000u8 | (b1 & 0b0111_1111u8)) == b1) by (bit_vector)
        requires
            0b1000_0000u8 < b1 < 0b1111_1111u8,
    ;
}

proof fn lemma_length_fmt_sound_nonmal_inv()
    ensures
        nat_length_fmt::<true>().sound_inv(),
        nat_length_fmt::<true>().nonmal_inv(),
{
    assert forall|v| nat_length_fmt::<true>().inner.consistent(v) implies (nat_length_fmt::<
        true,
    >().mapper.1)((nat_length_fmt::<true>().mapper.0)(v)) == v by {
        let (b1, rest) = v;
        if b1 <= SHORT_FORM_MAX {
        } else if 0b1000_0000 < b1 < 0b1111_1111 {
            match rest {
                R(L(bytes)) => {
                    lemma_length_wire_long_form_roundtrip(b1, bytes);
                },
                _ => {},
            }
        }
    }
}

proof fn lemma_length_fmt_unambiguous<const DER: bool>()
    ensures
        nat_length_fmt::<DER>().unambiguous(),
{
    assert forall|o: nat| nat_length_fmt::<DER>().consistent(o) implies (nat_length_fmt::<
        DER,
    >().mapper.0)((nat_length_fmt::<DER>().mapper.1)(o)) == o by {
        if nat_length_fmt::<DER>().consistent(o) {
            if o <= SHORT_FORM_MAX as nat {
            } else {
                lemma_to_from_be_bytes_roundtrip(o);
            }
        }
    }
}

proof fn lemma_length_fmt_usize_sound_nonmal_inv()
    ensures
        length_fmt::<true>().sound_inv(),
        length_fmt::<true>().nonmal_inv(),
{
    assert forall|v| length_fmt::<true>().inner.consistent(v) implies (length_fmt::<
        true,
    >().mapper.1)((length_fmt::<true>().mapper.0)(v)) == v by {
        let (b1, rest) = v;
        if b1 <= SHORT_FORM_MAX {
        } else if 0b1000_0000 < b1 < 0b1111_1111 {
            match rest {
                R(L(bytes)) => {
                    assert(bytes.len() <= size_of_usize());
                    lemma_nat_from_be_bytes_fits_usize(bytes);
                    lemma_length_wire_long_form_roundtrip(b1, bytes);
                },
                _ => {},
            }
        }
    }
}

/// The usize unambiguous invariant reduces to the nat one via the cast identity.
proof fn lemma_length_fmt_usize_unambiguous<const DER: bool>()
    ensures
        length_fmt::<DER>().unambiguous(),
{
    assert forall|o: usize| length_fmt::<DER>().consistent(o) implies (length_fmt::<
        DER,
    >().mapper.0)((length_fmt::<DER>().mapper.1)(o)) == o by {
        if length_fmt::<DER>().consistent(o) {
            if o <= SHORT_FORM_MAX as usize {
            } else {
                lemma_to_from_be_bytes_roundtrip(o as nat);
            }
        }
    }
}

proof fn lemma_length_fmt_usize_props<const DER: bool>(o: usize)
    ensures
        length_fmt::<DER>().consistent(o),
        length_fmt::<DER>().byte_len(o) == if o <= SHORT_FORM_MAX as usize {
            1
        } else {
            1 + nat_to_be_bytes(o as nat).len()
        },
{
    lemma_to_be_bytes_props(o as nat);
    lemma_usize_to_be_bytes_len_bound(o);
    if o <= SHORT_FORM_MAX as usize {
    } else {
        let bytes = nat_to_be_bytes(o as nat);
        let count = bytes.len() as u8;
        let b1 = 0b1000_0000u8 | count;
        if DER {
            assert(der_long_len_bytes_minimal(bytes)) by {
                reveal_with_fuel(nat_to_be_bytes, 2);
            }
        }
        assert(0b1000_0000u8 < b1 < 0b1111_1111u8 && (b1 & 0b0111_1111u8) == count) by (bit_vector)
            requires
                0u8 < count <= 8u8,
                b1 == (0b1000_0000u8 | count),
        ;
    }
}

pub(crate) proof fn lemma_length_fmt_byte_len_bound<const DER: bool>(value: usize)
    ensures
        super::LengthFmt::<DER>.byte_len(value) <= 1 + size_of::<usize>(),
{
    lemma_length_fmt_usize_props::<DER>(value);
    lemma_usize_to_be_bytes_len_bound(value);
}

pub(crate) broadcast proof fn lemma_length_fmt_short_byte_len<const DER: bool>(o: usize)
    requires
        o <= SHORT_FORM_MAX as usize,
    ensures
        #[trigger] super::LengthFmt::<DER>.byte_len(o) == 1,
{
    lemma_length_fmt_usize_props::<DER>(o);
}

mod derived_specs {
    use super::*;
    use super::super::{NatLengthFmt, LengthFmt};

    impl<const DER: bool> SpecParser for NatLengthFmt<DER> {
        type PVal = nat;

        open(super) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            nat_length_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for NatLengthFmt<DER> {
        type Val = nat;

        open(super) spec fn consistent(&self, v: Self::Val) -> bool {
            nat_length_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for NatLengthFmt<DER> {
        type SValue = nat;

        open(super) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            nat_length_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for NatLengthFmt<DER> {
        type SVal = nat;

        open(super) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            nat_length_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for NatLengthFmt<DER> {
        type T = nat;

        open(super) spec fn byte_len(&self, v: Self::T) -> nat {
            nat_length_fmt::<DER>().byte_len(v)
        }
    }

    impl<const DER: bool> SpecParser for LengthFmt<DER> {
        type PVal = usize;

        open(super) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            length_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for LengthFmt<DER> {
        type Val = usize;

        open(super) spec fn consistent(&self, v: Self::Val) -> bool {
            length_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for LengthFmt<DER> {
        type SValue = usize;

        open(super) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            length_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for LengthFmt<DER> {
        type SVal = usize;

        open(super) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            length_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for LengthFmt<DER> {
        type T = usize;

        open(super) spec fn byte_len(&self, v: Self::T) -> nat {
            length_fmt::<DER>().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::{NatLengthFmt, LengthFmt};

    impl<const DER: bool> SafeParser for NatLengthFmt<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for NatLengthFmt<DER> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_productive(s);
        }
    }

    impl SoundParser for NatLengthFmt<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_sound_nonmal_inv();
            nat_length_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_sound_nonmal_inv();
            nat_length_fmt::<true>().lemma_parse_sound_value(ibuf);
        }
    }

    impl<const DER: bool> NonTailFmt for NatLengthFmt<DER> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const DER: bool> GoodSerializer for NatLengthFmt<DER> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            nat_length_fmt::<DER>().lemma_serialize_len(v);
        }
    }

    impl<const DER: bool> SPRoundTripDps for NatLengthFmt<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_length_fmt_unambiguous::<DER>();
            nat_length_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const DER: bool> NoLookAhead for NatLengthFmt<DER> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_no_lookahead(i1, i2);
        }
    }

    impl NonMalleable for NatLengthFmt<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_length_fmt_sound_nonmal_inv();
            nat_length_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const DER: bool> EquivSerializersGeneral for NatLengthFmt<DER> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const DER: bool> EquivSerializers for NatLengthFmt<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            nat_length_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const DER: bool> SafeParser for LengthFmt<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            length_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for LengthFmt<DER> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            length_fmt::<DER>().lemma_productive(s);
        }
    }

    impl SoundParser for LengthFmt<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_usize_sound_nonmal_inv();
            length_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_usize_sound_nonmal_inv();
            length_fmt::<true>().lemma_parse_sound_value(ibuf);
        }
    }

    impl<const DER: bool> NonTailFmt for LengthFmt<DER> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            length_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            length_fmt::<DER>().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const DER: bool> GoodSerializer for LengthFmt<DER> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            length_fmt::<DER>().lemma_serialize_len(v);
        }
    }

    impl<const DER: bool> SPRoundTripDps for LengthFmt<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_length_fmt_usize_unambiguous::<DER>();
            length_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const DER: bool> NoLookAhead for LengthFmt<DER> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            length_fmt::<DER>().lemma_no_lookahead(i1, i2);
        }
    }

    impl NonMalleable for LengthFmt<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_length_fmt_usize_sound_nonmal_inv();
            length_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const DER: bool> EquivSerializersGeneral for LengthFmt<DER> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            length_fmt::<DER>().lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const DER: bool> EquivSerializers for LengthFmt<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            length_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<const DER: bool> Parser<&[u8]> for super::LengthFmt<DER> {
    type PT = usize;

    fn parse(&self, ibuf: &&[u8]) -> PResult<usize> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use crate::core::spec::SoundParser::lemma_parse_sound_value;

        let (n1, b1): (usize, u8) = U8.parse(ibuf)?;
        let rest = ibuf.skip(n1);

        if b1 <= SHORT_FORM_MAX {
            Ok((n1, b1 as usize))
        } else if 0b1000_0000 < b1 && b1 < 0b1111_1111 {
            let count = b1 & 0b0111_1111;
            let (n2, len_bytes) = Varied(count).parse(&rest)?;
            if DER {
                if count == 1 && len_bytes[0] <= SHORT_FORM_MAX {
                    return Err(ParseError::non_canonical());
                }
                if count > 1 && len_bytes[0] == 0x00u8 {
                    return Err(ParseError::non_canonical());
                }
            }
            match usize::BITS {
                32 if len_bytes.len() > 4 => return Err(ParseError::overflow()),
                64 if len_bytes.len() > 8 => return Err(ParseError::overflow()),
                _ => {},
            }
            let value = usize_from_be_bytes_exec(len_bytes);
            Ok((n1 + n2, value))
        } else {
            Err(ParseError::invalid_length())
        }
    }
}

impl<Output: OutputBuf, const DER: bool> Serializer<Output, usize> for super::LengthFmt<DER> {
    fn serialize_into(&self, v: &usize, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        if *v <= SHORT_FORM_MAX as usize {
            U8.serialize_into(&(*v as u8), obuf);
        } else {
            let count = usize_to_be_bytes_len(*v);
            let mut bytes = [0u8;size_of::<usize>()];
            let (encoded, _) = bytes.split_at_mut(count);
            usize_to_be_bytes_in_place(*v, encoded);
            U8.serialize_into(&(0b1000_0000 | (count as u8)), obuf);
            Varied(count).serialize_into(&bytes[0..count], obuf);
        }
    }
}

impl<const DER: bool> Prepare<usize> for super::LengthFmt<DER> {
    fn prepare(&self, v: &usize) -> Result<usize, PreSerializeError> {
        proof {
            lemma_length_fmt_usize_props::<DER>(*v);
        }
        if *v <= SHORT_FORM_MAX as usize {
            Ok(1usize)
        } else {
            Ok(1 + usize_to_be_bytes_len(*v))
        }
    }
}

impl<const DER: bool> ByteLen<usize> for super::LengthFmt<DER> {
    fn length(&self, v: &usize) -> usize {
        proof {
            lemma_length_fmt_usize_props::<DER>(*v);
        }
        if *v <= SHORT_FORM_MAX as usize {
            1
        } else {
            1 + usize_to_be_bytes_len(*v)
        }
    }
}

impl SpecParser for super::BerLengthFmt {
    type PVal = super::BerLength;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        ber_length_fmt().spec_parse(ibuf)
    }
}

impl Consistency for super::BerLengthFmt {
    type Val = super::BerLength;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        ber_length_fmt().consistent(v)
    }
}

impl SpecSerializerDps for super::BerLengthFmt {
    type SValue = super::BerLength;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        ber_length_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::BerLengthFmt {
    type SVal = super::BerLength;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        ber_length_fmt().spec_serialize(v)
    }
}

impl SpecByteLen for super::BerLengthFmt {
    type T = super::BerLength;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        ber_length_fmt().byte_len(v)
    }
}

impl SafeParser for super::BerLengthFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        ber_length_fmt().lemma_parse_safe(ibuf)
    }
}

impl Productive for super::BerLengthFmt {
    proof fn lemma_productive(&self, ibuf: Seq<u8>) {
        ber_length_fmt().lemma_productive(ibuf)
    }
}

impl NonTailFmt for super::BerLengthFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        ber_length_fmt().lemma_serialize_dps_prepend(v, obuf)
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        ber_length_fmt().lemma_serialize_dps_len(v, obuf)
    }
}

impl GoodSerializer for super::BerLengthFmt {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        ber_length_fmt().lemma_serialize_len(v)
    }
}

impl SPRoundTripDps for super::BerLengthFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        reveal(disjoint_domains);
        assert(disjoint_domains(Const(U8, 0x80u8), super::LengthFmt::<false>));
        ber_length_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf)
    }
}

impl NoLookAhead for super::BerLengthFmt {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        reveal(disjoint_domains);
        assert(disjoint_domains(Const(U8, 0x80u8), super::LengthFmt::<false>));
        ber_length_fmt().lemma_no_lookahead(i1, i2)
    }
}

impl EquivSerializersGeneral for super::BerLengthFmt {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        ber_length_fmt().lemma_serialize_equiv(v, obuf)
    }
}

impl EquivSerializers for super::BerLengthFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        ber_length_fmt().lemma_serialize_equiv_on_empty(v)
    }
}

impl Parser<&[u8]> for super::BerLengthFmt {
    type PT = super::BerLength;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        let (n, first) = U8.parse(ibuf)?;
        if first == 0x80u8 {
            Ok((n, super::BerLength::Indefinite))
        } else {
            let (n, len) = super::LengthFmt::<false>.parse(ibuf)?;
            Ok((n, super::BerLength::Definite(len)))
        }
    }
}

impl<Output: OutputBuf> Serializer<Output, super::BerLength> for super::BerLengthFmt {
    fn serialize_into(&self, v: &super::BerLength, obuf: &mut Output) {
        match v {
            super::BerLength::Indefinite => U8.serialize_into(&0x80u8, obuf),
            super::BerLength::Definite(n) => super::LengthFmt::<false>.serialize_into(n, obuf),
        }
    }
}

impl Prepare<super::BerLength> for super::BerLengthFmt {
    fn prepare(&self, v: &super::BerLength) -> Result<usize, PreSerializeError> {
        match v {
            super::BerLength::Indefinite => Ok(1),
            super::BerLength::Definite(n) => super::LengthFmt::<false>.prepare(n),
        }
    }
}

impl ByteLen<super::BerLength> for super::BerLengthFmt {
    fn length(&self, v: &super::BerLength) -> usize {
        match v {
            super::BerLength::Indefinite => 1,
            super::BerLength::Definite(n) => super::LengthFmt::<false>.length(n),
        }
    }
}

} // verus!
