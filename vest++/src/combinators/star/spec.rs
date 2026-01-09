use crate::core::spec::{GoodCombinator, GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer, SpecType};
use vstd::prelude::*;

verus! {

impl<A: SpecType> super::Star<A> {
    pub open spec fn wf(&self, v: Seq<A::Type>) -> bool {
        forall|i: int| 0 <= i < v.len() ==> #[trigger] self.inner.wf(v[i])
    }
}

impl<A: SpecType> SpecType for super::Star<A> {
    type Type = Seq<A::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.wf(v)
    }
}

impl<A: SpecParser> super::Star<A> {
    /// Recursive helper function for parsing.
    /// Since `Star` always succeeds, this function is total.
    pub open spec fn parse_rec(&self, ibuf: Seq<u8>) -> (int, Seq<A::Type>)
        decreases ibuf.len(),
    {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if 0 < n <= ibuf.len() => {
                let (n_rest, vs) = self.parse_rec(ibuf.skip(n));
                (n + n_rest, seq![v] + vs)
            },
            _ => (0, Seq::empty()),
        }
    }
}

impl<A: GoodParser> super::Star<A> {
    proof fn lemma_parse_rec_length(&self, ibuf: Seq<u8>)
        ensures
            0 <= self.parse_rec(ibuf).0 <= ibuf.len(),
        decreases ibuf.len(),
    {
        self.inner.lemma_parse_length(ibuf);
        if let Some((n, v)) = self.inner.spec_parse(ibuf) {
            if 0 < n <= ibuf.len() {
                self.lemma_parse_rec_length(ibuf.skip(n));
            }
        }
    }

    proof fn lemma_parse_rec_wf(&self, ibuf: Seq<u8>)
        ensures
            self.wf(self.parse_rec(ibuf).1),
        decreases ibuf.len(),
    {
        self.inner.lemma_parse_wf(ibuf);
        if let Some((n, v)) = self.inner.spec_parse(ibuf) {
            if 0 < n <= ibuf.len() {
                self.lemma_parse_rec_wf(ibuf.skip(n));
            }
        }
    }
}

impl<A: SpecParser> SpecParser for super::Star<A> {
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        let (n, vs) = self.parse_rec(ibuf);
        Some((n, vs))
    }
}

impl<A: GoodParser> GoodParser for super::Star<A> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.lemma_parse_rec_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.lemma_parse_rec_wf(ibuf);
    }
}

impl<A: SpecSerializer> super::Star<A> {
    pub open spec fn rfold_serialize_dps(&self, vs: Seq<A::Type>, obuf: Seq<u8>) -> Seq<u8>
        decreases vs.len(),
    {
        vs.fold_right_alt(|elem, buf| self.inner.spec_serialize_dps(elem, buf), obuf)
    }

    /// all elements are serializable with the appropriate intermediate buffers
    pub open spec fn elems_serializable(&self, vs: Seq<A::Type>, obuf: Seq<u8>) -> bool {
        forall|i: int|
            #![auto]
            0 <= i < vs.len() ==> self.inner.serializable(
                vs[i],
                self.rfold_serialize_dps(vs.skip(i + 1), obuf),
            )
    }
}

impl<A: GoodSerializer> super::Star<A> {
    proof fn lemma_rfold_serialize_buf(&self, vs: Seq<A::Type>, obuf: Seq<u8>)
        requires
            self.elems_serializable(vs, obuf),
            self.wf(vs),
        ensures
            exists|new_buf: Seq<u8>| self.rfold_serialize_dps(vs, obuf) == new_buf + obuf,
        decreases vs.len(),
    {
        if vs.len() == 0 {
            assert(self.rfold_serialize_dps(vs, obuf) == Seq::<u8>::empty() + obuf);
        } else {
            let rest = vs.skip(1);
            let rest_buf = self.rfold_serialize_dps(rest, obuf);

            // precond: rest is serializable
            assert forall|i: int| 0 <= i < rest.len() implies self.inner.serializable(
                rest[i],
                self.rfold_serialize_dps(rest.skip(i + 1), obuf),
            ) by {
                assert(rest.skip(i + 1) == vs.skip(i + 2));
            }

            // induction
            self.lemma_rfold_serialize_buf(rest, obuf);
            let rest_witness = choose|wit: Seq<u8>|
                self.rfold_serialize_dps(rest, obuf) == wit + obuf;

            // base
            self.inner.lemma_serialize_buf(vs[0], rest_buf);
            let fst_witness = choose|wit: Seq<u8>|
                self.inner.spec_serialize_dps(vs[0], rest_buf) == wit + rest_buf;

            assert(self.rfold_serialize_dps(vs, obuf) == (fst_witness + rest_witness) + obuf);
        }
    }
}

impl<A: SpecSerializer + SpecParser> SpecSerializer for super::Star<A> {
    open spec fn serializable(&self, vs: Self::Type, obuf: Seq<u8>) -> bool {
        // make sure the inner parser won't accidentally consume `obuf`
        &&& self.inner.spec_parse(obuf) is None
        &&& self.elems_serializable(vs, obuf)
    }

    open spec fn spec_serialize_dps(&self, vs: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        self.rfold_serialize_dps(vs, obuf)
    }

    open spec fn spec_serialize(&self, vs: Self::Type) -> Seq<u8> {
        vs.fold_left(Seq::empty(), |buf: Seq<u8>, elem| buf + self.inner.spec_serialize(elem))
    }
}

impl<A: GoodSerializer + SpecParser> GoodSerializer for super::Star<A> {
    proof fn lemma_serialize_buf(&self, vs: Self::Type, obuf: Seq<u8>) {
        if self.wf(vs) {
            self.lemma_rfold_serialize_buf(vs, obuf);
        }
    }
}

impl<A: SpecCombinator> SpecCombinator for super::Star<A> {

}

impl<A: GoodCombinator> GoodCombinator for super::Star<A> {
}

} // verus!
