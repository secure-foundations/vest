use crate::combinators::{Bind, Empty, Sum, Void};
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

type LengthFmt<const DER: bool> = Mapped<
    Bind<U8, spec_fn(u8) -> Sum<Empty, Sum<Refined<Varied<u8>, PredFnSpec<Seq<u8>>>, Void>>>,
    FnSpecMapper<(u8, Sum<(), Sum<Seq<u8>, Never>>), nat>,
>;

/// 8.1.3.5 In the long form, the length octets shall consist of an initial octet and **one or more** subsequent octets. The initial
/// octet shall be encoded as follows:
///
/// a) bit 8 shall be one;
/// b) bits 7 to 1 shall encode the number of subsequent octets in the length octets, as an unsigned binary integer with
/// bit 7 as the most significant bit;
/// c) the value 11111111 shall not be used.
pub(super) open(super) spec fn length_fmt<const DER: bool>() -> LengthFmt<DER> {
    Mapped {
        inner: Bind(
            U8,
            |b1: u8|
                {
                    match b1 {
                        b if b <= SHORT_FORM_MAX => L(Empty),
                        b if 0b1000_0000 < b < 0b1111_1111 => R(
                            L(
                                Refined(
                                    Varied(b & 0b0111_1111),  // clear the high bit to get the count
                                    |bytes: Seq<u8>| DER ==> der_long_len_bytes_minimal(bytes),
                                ),
                            ),
                        ),
                        _ => R(R(Void("Invalid first byte for ASN1 length"))),
                    }
                },
        ),
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

/// DER requires minimality, so
/// 1. for single-byte length in the long form, the value must be > 127 (i.e. not encodable in short form)
/// 2. for multi-byte length in the long form, the first byte must be non-zero (i.e. no leading zeros)
pub open spec fn der_long_len_bytes_minimal(bytes: Seq<u8>) -> bool {
    &&& bytes.len() == 1 ==> bytes[0] > SHORT_FORM_MAX
    &&& bytes.len() > 1 ==> bytes[0] != 0x00u8
}

proof fn lemma_length_fmt_sound_nonmal_inv()
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
                L(()) => {},
                R(L(bytes)) => {
                    assert(LONG_FORM_MIN_COUNT <= b1 & 0b0111_1111 <= LONG_FORM_MAX_COUNT)
                        by (bit_vector)
                        requires
                            0b1000_0000u8 < b1 < 0b1111_1111u8,
                    ;
                    lemma_from_to_be_bytes_roundtrip(bytes);

                    assert((0b1000_0000u8 | (b1 & 0b0111_1111u8)) == b1) by (bit_vector)
                        requires
                            0b1000_0000u8 < b1 < 0b1111_1111u8,
                    ;
                },
                R(_) => {},
            }
        }
    }
}

proof fn lemma_length_fmt_unambiguous<const DER: bool>()
    ensures
        length_fmt::<DER>().unambiguous(),
{
    assert forall|o: nat| length_fmt::<DER>().consistent(o) implies (length_fmt::<DER>().mapper.0)(
        (length_fmt::<DER>().mapper.1)(o),
    ) == o by {
        if length_fmt::<DER>().consistent(o) {
            if o <= SHORT_FORM_MAX as nat {
            } else {
                lemma_to_from_be_bytes_roundtrip(o);
            }
        }
    }
}

mod derived_specs {
    use super::*;
    use super::super::Length;

    impl<const DER: bool> SpecParser for Length<DER> {
        type PVal = nat;

        open(super) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            length_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for Length<DER> {
        type Val = nat;

        open(super) spec fn consistent(&self, v: Self::Val) -> bool {
            length_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for Length<DER> {
        type SValue = nat;

        open(super) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            length_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for Length<DER> {
        type SVal = nat;

        open(super) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            length_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for Length<DER> {
        type T = nat;

        open(super) spec fn byte_len(&self, v: Self::T) -> nat {
            length_fmt::<DER>().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::Length;

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
            lemma_length_fmt_sound_nonmal_inv();
            length_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_length_fmt_sound_nonmal_inv();
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
            lemma_length_fmt_unambiguous::<DER>();
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
            lemma_length_fmt_sound_nonmal_inv();
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

} // verus!
