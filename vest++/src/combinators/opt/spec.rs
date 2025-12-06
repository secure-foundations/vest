use vstd::prelude::*;
use crate::core::spec::SpecCombinator;

verus! {

impl<A> SpecCombinator for crate::combinators::opt::Opt<A> where A: SpecCombinator {
    type Type = Option<A::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            None => true,
            Some(vv) => self.0.wf(vv),
        }
    }

    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        match v {
            None => self.0.spec_parse(obuf) is None,
            Some(vv) => self.0.serializable(vv, obuf),
        }
    }

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.0.spec_parse(ibuf) {
            Some((n, v)) => Some((n, Some(v))),
            None => Some((0, None)),
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            None => obuf,
            Some(vv) => self.0.spec_serialize(vv, obuf),
        }
    }
}

} // verus!
