use crate::combinators::{Bind, Empty, Sum, Void};
use crate::core::exec::input::*;
use crate::core::exec::{parser::*, serializer::*, ParseError, ParseErrorKind};
use crate::primitives::base256::*;
use crate::Never;
use crate::{
    combinators::{
        implicit::*,
        length::AsLen,
        mapped::spec::{FnSpecMapper, LosslessMapper, LossyMapper, SpecMapper},
        Alt, Implicit, Mapped, Refined, TryMap, Varied, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::arithmetic::power::*;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

pub const SHORT_FORM_MAX: u8 = 0x7F;

pub const LONG_FORM_MIN_COUNT: u8 = 1;

pub const LONG_FORM_MAX_COUNT: u8 = 126;

type LengthWire<const DER: bool, const BOUNDED: bool = false> = Bind<
    U8,
    spec_fn(u8) -> Sum<Empty, Sum<Refined<Varied<u8>, PredFnSpec<Seq<u8>>>, Void>>,
>;

type NatLengthFmt<const DER: bool> = Mapped<
    LengthWire<DER>,
    FnSpecMapper<(u8, Sum<(), Sum<Seq<u8>, Never>>), nat>,
>;

type LengthFmt<const DER: bool> = Mapped<
    LengthWire<DER, true>,
    FnSpecMapper<(u8, Sum<(), Sum<Seq<u8>, Never>>), usize>,
>;

/// 8.1.3.5 In the long form, the length octets shall consist of an initial octet and **one or more** subsequent octets. The initial
/// octet shall be encoded as follows:
///
/// a) bit 8 shall be one;
/// b) bits 7 to 1 shall encode the number of subsequent octets in the length octets, as an unsigned binary integer with
/// bit 7 as the most significant bit;
/// c) the value 11111111 shall not be used.
#[verusfmt::skip]
pub(super) open(super) spec fn length_wire<const DER: bool, const BOUNDED: bool>() -> LengthWire<DER, BOUNDED > {
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

mod derived_specs {
    use super::*;
    use super::super::{NatLength, Length};

    impl<const DER: bool> SpecParser for NatLength<DER> {
        type PVal = nat;

        open(super) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            nat_length_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for NatLength<DER> {
        type Val = nat;

        open(super) spec fn consistent(&self, v: Self::Val) -> bool {
            nat_length_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for NatLength<DER> {
        type SValue = nat;

        open(super) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            nat_length_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for NatLength<DER> {
        type SVal = nat;

        open(super) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            nat_length_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for NatLength<DER> {
        type T = nat;

        open(super) spec fn byte_len(&self, v: Self::T) -> nat {
            nat_length_fmt::<DER>().byte_len(v)
        }
    }

    impl<const DER: bool> SpecParser for Length<DER> {
        type PVal = usize;

        open(super) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            length_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for Length<DER> {
        type Val = usize;

        open(super) spec fn consistent(&self, v: Self::Val) -> bool {
            length_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for Length<DER> {
        type SValue = usize;

        open(super) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            length_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for Length<DER> {
        type SVal = usize;

        open(super) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            length_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for Length<DER> {
        type T = usize;

        open(super) spec fn byte_len(&self, v: Self::T) -> nat {
            length_fmt::<DER>().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::{NatLength, Length};

    impl<const DER: bool> SafeParser for NatLength<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for NatLength<DER> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_productive(s);
        }
    }

    impl SoundParser for NatLength<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_sound_nonmal_inv();
            nat_length_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_sound_nonmal_inv();
            nat_length_fmt::<true>().lemma_parse_sound_value(ibuf);
        }
    }

    impl<const DER: bool> NonTailFmt for NatLength<DER> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const DER: bool> GoodSerializer for NatLength<DER> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            nat_length_fmt::<DER>().lemma_serialize_len(v);
        }
    }

    impl<const DER: bool> SPRoundTripDps for NatLength<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_length_fmt_unambiguous::<DER>();
            nat_length_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const DER: bool> NoLookAhead for NatLength<DER> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_no_lookahead(i1, i2);
        }
    }

    impl NonMalleable for NatLength<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_length_fmt_sound_nonmal_inv();
            nat_length_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const DER: bool> EquivSerializersGeneral for NatLength<DER> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            nat_length_fmt::<DER>().lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const DER: bool> EquivSerializers for NatLength<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            nat_length_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const DER: bool> SafeParser for Length<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            length_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for Length<DER> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            length_fmt::<DER>().lemma_productive(s);
        }
    }

    impl SoundParser for Length<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_usize_sound_nonmal_inv();
            length_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_usize_sound_nonmal_inv();
            length_fmt::<true>().lemma_parse_sound_value(ibuf);
        }
    }

    impl<const DER: bool> NonTailFmt for Length<DER> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            length_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            length_fmt::<DER>().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const DER: bool> GoodSerializer for Length<DER> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            length_fmt::<DER>().lemma_serialize_len(v);
        }
    }

    impl<const DER: bool> SPRoundTripDps for Length<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_length_fmt_usize_unambiguous::<DER>();
            length_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const DER: bool> NoLookAhead for Length<DER> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            length_fmt::<DER>().lemma_no_lookahead(i1, i2);
        }
    }

    impl NonMalleable for Length<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_length_fmt_usize_sound_nonmal_inv();
            length_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const DER: bool> EquivSerializersGeneral for Length<DER> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            length_fmt::<DER>().lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const DER: bool> EquivSerializers for Length<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            length_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<const DER: bool> Parser<&[u8]> for super::Length<DER> {
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

impl<const DER: bool> Serializer<usize> for super::Length<DER> {
    fn serialize(&self, v: &usize, obuf: &mut Vec<u8>) {
        if *v <= SHORT_FORM_MAX as usize {
            U8.serialize(&(*v as u8), obuf);
        } else {
            let bytes = usize_to_be_bytes_exec(*v);
            let count = bytes.len();
            U8.serialize(&(0b1000_0000 | (count as u8)), obuf);
            Varied(count).serialize(&bytes, obuf);
        }
    }
}

impl<const DER: bool> Prepare<usize> for super::Length<DER> {
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

impl<const DER: bool> ByteLen<usize> for super::Length<DER> {
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

} // verus!
