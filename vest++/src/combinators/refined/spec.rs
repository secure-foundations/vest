use crate::core::spec::{SpecCombinator, SpecParser, SpecSerializer, SpecType};
use vstd::prelude::*;

verus! {

impl<A: SpecType> SpecType for super::Refined<A> {
    type Type = A::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.inner.wf(v) && (self.pred)(v)
    }
}

impl<A: SpecParser> SpecParser for super::Refined<A> {
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => {
                if (self.pred)(v) {
                    Some((n, v))
                } else {
                    None
                }
            },
            None => None,
        }
    }

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_wf(ibuf);
    }
}

impl<A: SpecSerializer> SpecSerializer for super::Refined<A> {
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        self.inner.serializable(v, obuf)
    }

    open spec fn spec_serialize_dps(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v, obuf)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.lemma_serialize_buf(v, obuf);
    }
}

impl<A: SpecCombinator> SpecCombinator for super::Refined<A> {

}

} // verus!
