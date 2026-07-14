use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::output::*;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, ComplianceErrorKind, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::{
    combinators::{mapped::spec::FnSpecMapper, Mapped, Refined, U8},
    core::{proof::*, spec::*},
};
use OutputBuf;

use vstd::prelude::*;

verus! {

pub const BOOL_BYTE_LEN: usize = 1;

pub const FALSE_BYTE: u8 = 0x00;

pub const CANONICAL_TRUE_BYTE: u8 = 0xFF;

pub struct BoolMapper<const DER: bool>;

#[verifier::allow_in_spec]
pub fn non_zero(b: u8) -> bool
    returns
        b != FALSE_BYTE,
{
    b != FALSE_BYTE
}

#[verifier::allow_in_spec]
pub fn der_bool_byte(b: u8) -> bool
    returns
        b == CANONICAL_TRUE_BYTE || b == FALSE_BYTE,
{
    b == CANONICAL_TRUE_BYTE || b == FALSE_BYTE
}

pub open spec fn true_byte<const DER: bool>() -> u8 {
    if DER {
        CANONICAL_TRUE_BYTE
    } else {
        choose|x: u8| non_zero(x)
    }
}

pub type BoolFmt<const DER: bool> = Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<u8, bool>>;

pub open spec fn bool_fmt<const DER: bool>() -> BoolFmt<DER> {
    Mapped {
        inner: Refined(U8, |b: u8| DER ==> der_bool_byte(b)),
        mapper: (
            |b: u8| non_zero(b),
            |b: bool|
                if b {
                    true_byte::<DER>()
                } else {
                    FALSE_BYTE
                },
        ),
    }
}

mod derived_specs {
    use super::*;
    use super::super::Bool;

    impl<const DER: bool> SpecParser for Bool<DER> {
        type PVal = bool;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            bool_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for Bool<DER> {
        type Val = bool;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            bool_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for Bool<DER> {
        type SValue = bool;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            bool_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for Bool<DER> {
        type SVal = bool;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            bool_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for Bool<DER> {
        type T = bool;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            BOOL_BYTE_LEN as nat
        }
    }

    impl<const DER: bool> MinMaxByteLen for Bool<DER> {
        open spec fn min(&self) -> nat {
            BOOL_BYTE_LEN as nat
        }

        open spec fn max(&self) -> nat {
            BOOL_BYTE_LEN as nat
        }

        proof fn lemma_min_max_byte_len(&self, v: Self::T) {
        }
    }

    impl<const DER: bool> StaticByteLen for Bool<DER> {
        open spec fn static_byte_len() -> nat {
            BOOL_BYTE_LEN as nat
        }

        proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
            bool_fmt::<DER>().lemma_static_len_matches_byte_len(v);
        }
    }

    impl<const DER: bool> ValueByteLen for Bool<DER> {
        open spec fn value_byte_len(_v: Self::T) -> nat {
            BOOL_BYTE_LEN as nat
        }

        proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
            bool_fmt::<DER>().lemma_static_len_matches_byte_len(v);
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::Bool;

    impl<const DER: bool> SafeParser for Bool<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            bool_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for Bool<DER> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            bool_fmt::<DER>().lemma_productive(s);
        }
    }

    impl<const DER: bool> SoundParser for Bool<DER> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        }
    }

    impl<const DER: bool> NonTailFmt for Bool<DER> {
        proof fn lemma_serialize_dps_prepend(&self, v: bool, obuf: Seq<u8>) {
            bool_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: bool, obuf: Seq<u8>) {
            bool_fmt::<DER>().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const DER: bool> GoodSerializer for Bool<DER> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            bool_fmt::<DER>().lemma_serialize_len(v);
        }
    }

    impl<const DER: bool> SPRoundTripDps for Bool<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            assert(non_zero(CANONICAL_TRUE_BYTE));
            bool_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const DER: bool> NoLookAhead for Bool<DER> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            bool_fmt::<DER>().lemma_no_lookahead(i1, i2);
        }
    }

    impl NonMalleable for Bool<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            bool_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const DER: bool> EquivSerializersGeneral for Bool<DER> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            bool_fmt::<DER>().lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const DER: bool> EquivSerializers for Bool<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            bool_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<const DER: bool> Parser<&[u8]> for super::Bool<DER> {
    type PT = bool;

    fn parse(&self, ibuf: &&[u8]) -> PResult<bool> {
        let (n, b) = U8.parse(ibuf)?;
        if DER && !der_bool_byte(b) {
            Err(ParseError::non_canonical())
        } else {
            Ok((n, non_zero(b)))
        }
    }
}

impl<Output: OutputBuf + ?Sized> Serializer<Output, bool> for super::Bool<true> {
    fn serialize_into(&self, v: &bool, obuf: &mut Output) {
        let b = if *v {
            CANONICAL_TRUE_BYTE
        } else {
            FALSE_BYTE
        };
        U8.serialize_into(&b, obuf);
    }
}

impl Prepare<bool> for super::Bool<true> {
    fn prepare(&self, _v: &bool) -> Result<usize, PreSerializeError> {
        Ok(BOOL_BYTE_LEN)
    }
}

impl ByteLen<bool> for super::Bool<true> {
    fn length(&self, _v: &bool) -> usize {
        BOOL_BYTE_LEN
    }
}

} // verus!
