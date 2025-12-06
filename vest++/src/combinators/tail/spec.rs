use vstd::prelude::*;
use crate::core::spec::SpecCombinator;

verus! {

impl SpecCombinator for crate::combinators::tail::Tail {
    type Type = Seq<u8>;

    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        obuf.len() == 0
    }

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        Some((ibuf.len() as int, ibuf))
    }

    open spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        v + obuf
    }
}

} // verus!
