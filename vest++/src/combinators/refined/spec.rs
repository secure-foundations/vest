use vstd::prelude::*;
use crate::core::spec::SpecCombinator;

verus! {

impl<A: SpecCombinator> SpecCombinator for crate::combinators::refined::Refined<A> {
    type Type = A::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.inner.wf(v) && (self.pred)(v)
    }

    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        self.inner.serializable(v, obuf)
    }

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

    open spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize(v, obuf)
    }
}

} // verus!
