use crate::{
    combinators::Fixed,
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl SpecParser for super::BerBool {
    type PVal = bool;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if ibuf.len() >= 1 {
            let byte = ibuf[0];
            let value = byte != 0u8;
            Some((1, value))
        } else {
            None
        }
    }
}

impl GoodParser for super::BerBool {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

pub open spec fn non_zero_byte(b: u8) -> bool {
    b != 0x00u8
}

impl SpecSerializerDps for super::BerBool {
    type ST = bool;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        // Serialize FALSE as 0x00, TRUE as n for arbitrary choice of non-zero n
        let n = choose|x: u8| non_zero_byte(x);
        let byte = if v {
            n
        } else {
            0x00u8
        };
        seq![byte] + obuf
    }
}

impl SpecSerializer for super::BerBool {
    type SVal = bool;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let n = choose|x: u8| non_zero_byte(x);
        let byte = if v {
            n
        } else {
            0x00u8
        };
        seq![byte]
    }
}

impl Serializability for super::BerBool {

}

impl Unambiguity for super::BerBool {

}

impl GoodSerializerDps for super::BerBool {
    proof fn lemma_serialize_dps_buf(&self, v: bool, obuf: Seq<u8>) {
        if v.wf() {
            let serialized = self.spec_serialize_dps(v, obuf);
            assert(serialized.len() == 1 + obuf.len());
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: bool, obuf: Seq<u8>) {
    }
}

impl GoodSerializer for super::BerBool {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
    }
}

impl SpecByteLen for super::BerBool {
    type T = bool;
}

} // verus!
