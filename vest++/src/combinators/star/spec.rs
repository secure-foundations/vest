use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SpecParser> super::Star<A> {
    /// Recursive helper function for parsing.
    /// Since `Star` always succeeds, this function is total.
    pub open spec fn parse_rec(&self, ibuf: Seq<u8>) -> (int, Seq<A::PT>)
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
            self.parse_rec(ibuf).1.wf(),
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
    type PT = Seq<A::PT>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
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

impl<A: SpecSerializerDps> super::Star<A> {
    pub open spec fn rfold_serialize_dps(&self, vs: Seq<A::ST>, obuf: Seq<u8>) -> Seq<u8>
        decreases vs.len(),
    {
        vs.fold_right_alt(|elem, buf| self.inner.spec_serialize_dps(elem, buf), obuf)
    }
}

impl<A: Serializability> super::Star<A> {
    /// all elements are serializable with the appropriate intermediate buffers
    pub open spec fn elems_serializable(&self, vs: Seq<A::ST>, obuf: Seq<u8>) -> bool {
        forall|i: int|
            #![auto]
            0 <= i < vs.len() ==> self.inner.serializable(
                vs[i],
                self.rfold_serialize_dps(vs.skip(i + 1), obuf),
            )
    }
}

impl<A: Unambiguity> Unambiguity for super::Star<A> {
    open spec fn unambiguous(&self) -> bool {
        self.inner.unambiguous()
    }
}

impl<A: GoodSerializer> super::Star<A> {
    proof fn lemma_rfold_serialize_buf(&self, vs: Seq<A::ST>, obuf: Seq<u8>)
        ensures
            exists|new_buf: Seq<u8>| self.rfold_serialize_dps(vs, obuf) == new_buf + obuf,
        decreases vs.len(),
    {
        if vs.len() == 0 {
            assert(self.rfold_serialize_dps(vs, obuf) == Seq::<u8>::empty() + obuf);
        } else {
            let rest = vs.skip(1);
            let rest_buf = self.rfold_serialize_dps(rest, obuf);

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

impl<A> SpecSerializerDps for super::Star<A> where A: SpecSerializerDps {
    type ST = Seq<A::ST>;

    open spec fn spec_serialize_dps(&self, vs: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.rfold_serialize_dps(vs, obuf)
    }
}

impl<A> SpecSerializer for super::Star<A> where A: SpecSerializer {
    type ST = Seq<A::ST>;

    open spec fn spec_serialize(&self, vs: Self::ST) -> Seq<u8> {
        vs.fold_left(Seq::empty(), |buf: Seq<u8>, elem| buf + self.inner.spec_serialize(elem))
    }
}

impl<A> Serializability for super::Star<A> where A: Serializability + SpecParser {
    open spec fn serializable(&self, vs: Self::ST, obuf: Seq<u8>) -> bool {
        // make sure the inner parser won't accidentally consume `obuf`
        &&& self.inner.spec_parse(obuf) is None
        &&& self.elems_serializable(vs, obuf)
    }
}

impl<A> GoodSerializer for super::Star<A> where A: GoodSerializer {
    proof fn lemma_serialize_buf(&self, vs: Self::ST, obuf: Seq<u8>) {
        self.lemma_rfold_serialize_buf(vs, obuf);
    }
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Repeat<A, B> {
    type PT = (Seq<A::PT>, B::PT);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        (super::Star { inner: self.0 }, self.1).spec_parse(ibuf)
    }
}

impl<A: GoodParser, B: GoodParser> GoodParser for super::Repeat<A, B> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_parse_length(ibuf)
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_parse_wf(ibuf)
    }
}

impl<A: SpecSerializerDps, B: SpecSerializerDps> SpecSerializerDps for super::Repeat<A, B> {
    type ST = (Seq<A::ST>, B::ST);

    open spec fn spec_serialize_dps(&self, vs: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (super::Star { inner: self.0 }, self.1).spec_serialize_dps(vs, obuf)
    }
}

impl<A: SpecSerializer, B: SpecSerializer> SpecSerializer for super::Repeat<A, B> {
    type ST = (Seq<A::ST>, B::ST);

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        (super::Star { inner: self.0 }, self.1).spec_serialize(v)
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Repeat<A, B> {
    proof fn lemma_serialize_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_serialize_buf(v, obuf)
    }
}

impl<A: Unambiguity + SpecParser, B: Unambiguity> Unambiguity for super::Repeat<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& forall|vb: B::ST, obuf: Seq<u8>|
            vb.wf() ==> parser_fails_on(self.0, #[trigger] self.1.spec_serialize_dps(vb, obuf))
    }
}

} // verus!
