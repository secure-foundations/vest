use crate::{combinators::Fixed, core::spec::{SpecCombinator, SpecParser, SpecSerializer, SpecType}};
use vstd::prelude::*;

verus! {

impl SpecType for super::BerBool {
    type Type = bool;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
}

impl SpecParser for super::BerBool {
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match Fixed::<1>.spec_parse(ibuf) {
            Some((n, byte_seq)) => {
                let byte = byte_seq[0];
                let value = byte != 0u8;
                Some((n, value))
            },
            None => None,
        }
    }

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

pub open spec fn non_zero_byte(b: u8) -> bool {
    b != 0x00u8
}

impl SpecSerializer for super::BerBool {
    open spec fn spec_serialize_dps(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        // Serialize FALSE as 0x00, TRUE as n for arbitrary choice of non-zero n
        let n = choose|x: u8| non_zero_byte(x);
        let byte = if v { n } else { 0x00u8 };
        seq![byte] + obuf
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        let serialized = self.spec_serialize_dps(v, obuf);
        assert(serialized.len() == 1 + obuf.len());
    }
}

impl SpecCombinator for super::BerBool {

}

} // verus!
