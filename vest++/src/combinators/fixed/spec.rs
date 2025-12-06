use vstd::prelude::*;
use crate::core::spec::SpecCombinator;

verus! {

impl<const N: usize> SpecCombinator for crate::combinators::fixed::Fixed<N> {
    type Type = Seq<u8>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        v.len() == N as int
    }

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        if ibuf.len() < N as int {
            None
        } else {
            Some((N as int, ibuf.take(N as int)))
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        v + obuf
    }
}

} // verus!
