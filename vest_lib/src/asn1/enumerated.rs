//! ASN.1 ENUMERATED contents.
//!
//! X.690 §8.4 specifies that ENUMERATED contents are encoded exactly like the
//! corresponding INTEGER value. This module therefore delegates to [`super::IntegerFmt`]
//! at every layer while retaining a distinct format marker for the ENUMERATED tag.
use crate::core::exec::output::OutputBuf;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::{EnumeratedFmt, Integer, IntegerFmt};

verus! {

/// Executable ENUMERATED values use the same exact integer representation as INTEGER.
pub type Enumerated<'a> = Integer<'a>;

mod derived_specs {
    use super::*;
    use super::super::{EnumeratedFmt, IntegerFmt};

    impl SpecParser for EnumeratedFmt {
        type PVal = int;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            IntegerFmt.spec_parse(ibuf)
        }
    }

    impl Consistency for EnumeratedFmt {
        type Val = int;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            IntegerFmt.consistent(v)
        }
    }

    impl SpecSerializerDps for EnumeratedFmt {
        type SValue = int;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            IntegerFmt.spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for EnumeratedFmt {
        type SVal = int;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            IntegerFmt.spec_serialize(v)
        }
    }

    impl SpecByteLen for EnumeratedFmt {
        type T = int;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            IntegerFmt.byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::{EnumeratedFmt, IntegerFmt};

    impl SafeParser for EnumeratedFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            IntegerFmt.lemma_parse_safe(ibuf);
        }
    }

    impl Productive for EnumeratedFmt {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            IntegerFmt.lemma_productive(ibuf);
        }
    }

    impl SoundParser for EnumeratedFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            IntegerFmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            IntegerFmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for EnumeratedFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            IntegerFmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for EnumeratedFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            IntegerFmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for EnumeratedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            IntegerFmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for EnumeratedFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            IntegerFmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<'i> Parser<&'i [u8]> for EnumeratedFmt {
    type PT = Enumerated<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        IntegerFmt.parse(ibuf)
    }
}

impl<'i, Output: OutputBuf> Serializer<Output, Enumerated<'i>> for EnumeratedFmt {
    fn serialize_into(&self, v: &Enumerated<'i>, obuf: &mut Output) {
        IntegerFmt.serialize_into(v, obuf);
    }
}

impl<'i> Prepare<Enumerated<'i>> for EnumeratedFmt {
    fn prepare(&self, v: &Enumerated<'i>) -> Result<usize, PreSerializeError> {
        IntegerFmt.prepare(v)
    }
}

impl<'i> ByteLen<Enumerated<'i>> for EnumeratedFmt {
    fn length(&self, v: &Enumerated<'i>) -> usize {
        IntegerFmt.length(v)
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::*;
    use crate::asn1::der::ENUMERATED;
    use crate::core::exec::{Parser, Prepare, SerializerExt};

    #[test]
    fn enumerated_uses_integer_contents_rules() {
        let input = [0x0a, 0x01, 0x02];
        let (_, value) = ENUMERATED.parse(&&input[..]).unwrap();
        match value {
            Integer::Small { v } => assert_eq!(v, 2),
            Integer::Big { .. } => panic!("small ENUMERATED value parsed as a big integer"),
        }

        let mut output = vec![0; ENUMERATED.prepare(&value).unwrap()];
        ENUMERATED.serialize(&value, &mut output);
        assert_eq!(output, input);

        let nonminimal = [0x0a, 0x02, 0x00, 0x02];
        assert!(ENUMERATED.parse(&&nonminimal[..]).is_err());
    }
}
