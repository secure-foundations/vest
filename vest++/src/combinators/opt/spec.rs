use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A> SpecParser for super::Opt<A> where A: SpecParser {
    type PVal = Option<A::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
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
    type SVal = Option<A::SVal>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        match v {
            None => Seq::empty(),
            Some(vv) => self.0.spec_serialize(vv),
        }
    }
}

impl<A> Serializability for super::Opt<A> where A: Serializability + SpecParser {
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        match v {
            // To ensure the parser will not try to consume serialized bytes in
            // `obuf` when the value is `None`
            None => self.0.spec_parse(obuf) is None,
            Some(vv) => self.0.serializable(vv, obuf),
        }
    }
}

impl<A: Unambiguity> Unambiguity for super::Opt<A> {
    open spec fn unambiguous(&self) -> bool {
        self.0.unambiguous()
    }
}

impl<A> GoodSerializerDps for super::Opt<A> where A: GoodSerializerDps {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            None => {
                assert(self.spec_serialize_dps(v, obuf) == Seq::empty() + obuf);
            },
            Some(vv) => {
                self.0.lemma_serialize_dps_buf(vv, obuf);
            },
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            None => {},
            Some(vv) => {
                self.0.lemma_serialize_dps_len(vv, obuf);
            },
        }
    }
}

impl<A: GoodSerializer> GoodSerializer for super::Opt<A> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        match v {
            None => {},
            Some(vv) => {
                self.0.lemma_serialize_len(vv);
            },
        }
    }
}

impl<Inner: SpecByteLen> SpecByteLen for super::Opt<Inner> {
    type T = Option<Inner::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        match v {
            None => 0,
            Some(vv) => self.0.byte_len(vv),
        }
    }
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Optional<A, B> {
    type PVal = (Option<A::PVal>, B::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (super::Opt(self.0), self.1).spec_parse(ibuf)
    }
}

impl<A: GoodParser, B: GoodParser> GoodParser for super::Optional<A, B> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_parse_length(ibuf)
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_parse_wf(ibuf)
    }
}

impl<A: SpecSerializerDps, B: SpecSerializerDps> SpecSerializerDps for super::Optional<A, B> {
    type ST = (Option<A::ST>, B::ST);

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (super::Opt(self.0), self.1).spec_serialize_dps(v, obuf)
    }
}

impl<A: GoodSerializerDps, B: GoodSerializerDps> GoodSerializerDps for super::Optional<A, B> {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_serialize_dps_buf(v, obuf)
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_serialize_dps_len(v, obuf);
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Optional<A, B> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        (super::Opt(self.0), self.1).lemma_serialize_len(v);
    }
}

impl<A: SpecByteLen, B: SpecByteLen> SpecByteLen for super::Optional<A, B> {
    type T = (Option<A::T>, B::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (super::Opt(self.0), self.1).byte_len(v)
    }
}

impl<A: SpecSerializer, B: SpecSerializer> SpecSerializer for super::Optional<A, B> {
    type SVal = (Option<A::SVal>, B::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (super::Opt(self.0), self.1).spec_serialize(v)
    }
}

impl<A: Unambiguity + SpecParser, B: Unambiguity> Unambiguity for super::Optional<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& forall|vb: B::ST, obuf: Seq<u8>|
            vb.wf() ==> parser_fails_on(self.0, #[trigger] self.1.spec_serialize_dps(vb, obuf))
    }
}

} // verus!
