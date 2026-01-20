use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl SpecParser for super::Tail {
    type PVal = Seq<u8>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Some((ibuf.len() as int, ibuf))
    }
}

impl GoodParser for super::Tail {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Tail {
    type ST = Seq<u8>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        v
    }
}

impl SpecSerializer for super::Tail {
    type SVal = Seq<u8>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        v
    }
}

// impl Serializability for super::Tail {
//     open spec fn serializable(&self, _v: Self::ST, obuf: Seq<u8>) -> bool {
//         obuf.len() == 0
//     }
// }
impl Unambiguity for super::Tail {

}

// impl GoodSerializer for super::Tail {
//     proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
//         if v.wf() {
//             assert(self.spec_serialize_dps(v, obuf) == v + obuf);
//         }
//     }
// }
} // verus!
