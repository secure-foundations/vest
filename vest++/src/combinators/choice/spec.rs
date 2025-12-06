use vstd::prelude::*;
use crate::core::spec::SpecCombinator;

verus! {

pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A: SpecCombinator, B: SpecCombinator> SpecCombinator for crate::combinators::choice::Choice<A, B> {
    type Type = Either<A::Type, B::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            Either::Left(va) => self.0.wf(va),
            Either::Right(vb) => self.1.wf(vb),
        }
    }

    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        match v {
            Either::Left(va) => self.0.serializable(va, obuf),
            Either::Right(vb) => {
                &&& self.1.serializable(vb, obuf) 
                &&& self.0.spec_parse(self.1.spec_serialize(vb, obuf)) is None
            }
        }
    }

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.0.spec_parse(ibuf) {
            Some((n, va)) => Some((n, Either::Left(va))),
            None => match self.1.spec_parse(ibuf) {
                Some((n, vb)) => Some((n, Either::Right(vb))),
                None => None,
            },
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            Either::Left(va) => self.0.spec_serialize(va, obuf),
            Either::Right(vb) => self.1.spec_serialize(vb, obuf),
        }
    }
}

} // verus!
