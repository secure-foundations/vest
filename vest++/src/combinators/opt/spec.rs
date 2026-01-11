use crate::core::spec::{
    GoodCombinator, GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer,
    SpecSerializerDps, SpecType,
};
use vstd::prelude::*;

verus! {

impl<A> SpecType for super::Opt<A> where A: SpecType {
    type Type = Option<A::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            None => true,
            Some(vv) => self.0.wf(vv),
        }
    }
}

impl<A> SpecParser for super::Opt<A> where A: SpecParser {
    type PT = Option<A::PT>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match self.0.spec_parse(ibuf) {
            Some((n, v)) => Some((n, Some(v))),
            None => Some((0, None)),
        }
    }
}

impl<A> GoodParser for super::Opt<A> where A: GoodParser {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_wf(ibuf);
    }
}

impl<A> SpecSerializerDps for super::Opt<A> where A: SpecSerializerDps {
    type ST = Option<A::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            None => obuf,
            Some(vv) => self.0.spec_serialize_dps(vv, obuf),
        }
    }
}

impl<A> SpecSerializer for super::Opt<A> where A: SpecSerializer {
    type ST = Option<A::ST>;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        match v {
            None => Seq::empty(),
            Some(vv) => self.0.spec_serialize(vv),
        }
    }
}

impl<A> GoodSerializer for super::Opt<A> where A: GoodSerializer + SpecParser {
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        match v {
            // To ensure the parser will not try to consume serialized bytes in
            // `obuf` when the value is `None`
            None => self.0.spec_parse(obuf) is None,
            Some(vv) => self.0.serializable(vv, obuf),
        }
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        match v {
            None => {
                assert(self.spec_serialize_dps(v, obuf) == Seq::empty() + obuf);
            },
            Some(vv) => {
                if self.wf(v) {
                    self.0.lemma_serialize_buf(vv, obuf);
                }
            },
        }
    }
}

} // verus!
