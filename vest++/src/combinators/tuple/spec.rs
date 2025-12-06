use vstd::prelude::*;
use crate::core::spec::SpecCombinator;

verus! {

impl<A, B> SpecCombinator for (A, B) where A: SpecCombinator, B: SpecCombinator {
    type Type = (A::Type, B::Type);

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v.0) && self.1.wf(v.1)
    }

    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        self.1.serializable(v.1, obuf) && self.0.serializable(v.0, self.1.spec_serialize(v.1, obuf))
    }

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, v1)) => match self.1.spec_parse(ibuf.skip(n1)) {
                Some((n2, v2)) => Some((n1 + n2, (v1, v2))),
                None => None,
            },
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        self.0.spec_serialize(v.0, self.1.spec_serialize(v.1, obuf))
    }
}

} // verus!
