use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for super::Terminated<A, B> where A: SpecParser, B: SpecParser {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match (self.0, self.1).spec_parse(ibuf) {
            Some((n, (va, _vb))) => Some((n, va)),
            None => None,
        }
    }
}

impl<A, B> GoodParser for super::Terminated<A, B> where A: GoodParser, B: GoodParser {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_wf(ibuf);
    }
}

// impl<A, B> SpecSerializerDps for super::Terminated<A, B> where
//     A: SpecSerializerDps,
//     B: Serializability,
//  {
//     type ST = A::ST;
//     open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
//         // Use an arbitrary witness value for B that satisfies the serializable constraint
//         let vb = choose|vb: B::ST| #![auto] vb.wf() && self.1.serializable(vb, obuf);
//         (self.0, self.1).spec_serialize_dps((v, vb), obuf)
//     }
// }
impl<A, B> SpecSerializerDps for super::Terminated<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        // Use an arbitrary witness value for B that satisfies the serializable constraint
        let vb = choose|vb: B::ST| #![auto] vb.wf();
        (self.0, self.1).spec_serialize_dps((v, vb), obuf)
    }
}

impl<A, B> SpecSerializer for super::Terminated<A, B> where A: SpecSerializer, B: SpecSerializer {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let vb = choose|vb: B::SVal| vb.wf();
        (self.0, self.1).spec_serialize((v, vb))
    }
}

// impl<A, B> Serializability for super::Terminated<A, B> where
//     A: Serializability,
//     B: Serializability,
//  {
//     open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
//         // To serialize Terminated, we need a witness value for B
//         // We require that there exists some B value that can be serialized after A
//         &&& exists|vb: B::ST| #![trigger vb.wf()] { vb.wf() && self.1.serializable(vb, obuf) }
//         &&& self.0.serializable(
//             v,
//             self.1.spec_serialize_dps(
//                 choose|vb: B::ST| #![trigger vb.wf()] vb.wf() && self.1.serializable(vb, obuf),
//                 obuf,
//             ),
//         )
//     }
// }
impl<A: Unambiguity, B: Unambiguity> Unambiguity for super::Terminated<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& (self.0, self.1).unambiguous()
        &&& exists|vb: B::PVal| vb.wf()
    }
}

impl<A, B> GoodSerializerDps for super::Terminated<A, B> where
    A: GoodSerializerDps,
    B: GoodSerializerDps,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        let vb = choose|vb: B::ST| #![auto] vb.wf();
        (self.0, self.1).lemma_serialize_dps_buf((v, vb), obuf);

    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let vb = choose|vb: B::ST| #![auto] vb.wf();
        (self.0, self.1).lemma_serialize_dps_len((v, vb), obuf);
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Terminated<A, B> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let vb = choose|vb: B::SVal| #![auto] vb.wf();
        (self.0, self.1).lemma_serialize_len((v, vb));
    }
}

impl<A: SpecByteLen, B: SpecByteLen> SpecByteLen for super::Terminated<A, B> {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let vb = choose|vb: B::T| vb.wf();
        (self.0, self.1).byte_len((v, vb))
    }
}

} // verus!
