use vstd::prelude::*;
use super::spec::SpecCombinator;

verus! {

pub trait SpecCombinatorProof: SpecCombinator {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
    ;

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>)
        requires
            self.serializable(v, obuf),
        ensures
            self.wf(v) ==> exists|new_buf: Seq<u8>| self.spec_serialize(v, obuf) == new_buf + obuf,
    ;

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>)
        requires
            self.serializable(v, obuf),
        ensures
            self.wf(v) ==> self.spec_parse(self.spec_serialize(v, obuf)) == Some(
                ((self.spec_serialize(v, obuf).len() - obuf.len()), v),
            ),
    ;

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> {
                &&& self.wf(v)
                &&& self.spec_serialize(v, obuf) == ibuf.take(n) + obuf
            },
    ;
}

} // verus!
