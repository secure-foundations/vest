//! ASN.1 ENUMERATED contents.
//!
//! X.690 §8.4 specifies that ENUMERATED contents are encoded exactly like the
//! corresponding INTEGER value. This module therefore delegates to [`super::Integer`]
//! at every layer while retaining a distinct format marker for the ENUMERATED tag.
use crate::core::exec::output::OutputBuf;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::{Enumerated, IntVal, Integer};

verus! {

mod derived_specs {
    use super::*;
    use super::super::{Enumerated, Integer};

    impl SpecParser for Enumerated {
        type PVal = int;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Integer.spec_parse(ibuf)
        }
    }

    impl Consistency for Enumerated {
        type Val = int;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Integer.consistent(v)
        }
    }

    impl SpecSerializerDps for Enumerated {
        type SValue = int;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Integer.spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Enumerated {
        type SVal = int;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Integer.spec_serialize(v)
        }
    }

    impl SpecByteLen for Enumerated {
        type T = int;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Integer.byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::{Enumerated, Integer};

    impl SafeParser for Enumerated {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Integer.lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Enumerated {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            Integer.lemma_productive(ibuf);
        }
    }

    impl SoundParser for Enumerated {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            Integer.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            Integer.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for Enumerated {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            Integer.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Enumerated {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            Integer.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Enumerated {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            Integer.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for Enumerated {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            Integer.lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<'i> Parser<&'i [u8]> for Enumerated {
    type PT = IntVal<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        Integer.parse(ibuf)
    }
}

impl<'i, Output: OutputBuf> Serializer<Output, IntVal<'i>> for Enumerated {
    fn serialize_into(&self, v: &IntVal<'i>, obuf: &mut Output) {
        Integer.serialize_into(v, obuf);
    }
}

impl<'i> Prepare<IntVal<'i>> for Enumerated {
    fn prepare(&self, v: &IntVal<'i>) -> Result<usize, PreSerializeError> {
        Integer.prepare(v)
    }
}

impl<'i> ByteLen<IntVal<'i>> for Enumerated {
    fn length(&self, v: &IntVal<'i>) -> usize {
        Integer.length(v)
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
            IntVal::Small { v } => assert_eq!(v, 2),
            IntVal::Big { .. } => panic!("small ENUMERATED value parsed as a big integer"),
        }

        let mut output = vec![0; ENUMERATED.prepare(&value).unwrap()];
        ENUMERATED.serialize(&value, &mut output);
        assert_eq!(output, input);

        let nonminimal = [0x0a, 0x02, 0x00, 0x02];
        assert!(ENUMERATED.parse(&&nonminimal[..]).is_err());
    }
}
