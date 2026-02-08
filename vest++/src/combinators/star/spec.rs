use crate::combinators::star::proof::lemma_fold_left_accumulate_nat;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SpecParser> super::Star<A> {
    /// Recursive helper function for parsing.
    /// Since `Star` always succeeds, this function is total.
    pub open spec fn parse_rec(&self, ibuf: Seq<u8>) -> (int, Seq<A::PVal>)
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
    proof fn lemma_byte_len_cons(&self, v: A::T, vs: Seq<A::T>)
        ensures
            self.byte_len(seq![v] + vs) == self.inner.byte_len(v) + self.byte_len(vs),
    {
        let f = |acc: nat, elem: A::T| acc + self.inner.byte_len(elem);
        (seq![v] + vs).lemma_fold_left_alt(0, f);
        vs.lemma_fold_left_alt(self.inner.byte_len(v), f);
        lemma_fold_left_accumulate_nat(vs, self.inner.byte_len(v), f);
        assert((seq![v] + vs).skip(1) == vs);
    }

    proof fn lemma_parse_rec_length(&self, ibuf: Seq<u8>)
        ensures
            0 <= self.parse_rec(ibuf).0 <= ibuf.len(),
        decreases ibuf.len(),
    {
        self.inner.lemma_parse_len_bound(ibuf);
        if let Some((n, v)) = self.inner.spec_parse(ibuf) {
            if 0 < n <= ibuf.len() {
                self.lemma_parse_rec_length(ibuf.skip(n));
            }
        }
    }

    proof fn lemma_parse_rec_consistent(&self, ibuf: Seq<u8>)
        ensures
            self.consistent(self.parse_rec(ibuf).1),
        decreases ibuf.len(),
    {
        self.inner.lemma_parse_consistent(ibuf);
        if let Some((n, v)) = self.inner.spec_parse(ibuf) {
            if 0 < n <= ibuf.len() {
                self.lemma_parse_rec_consistent(ibuf.skip(n));
            }
        }
    }

    proof fn lemma_parse_rec_byte_len(&self, ibuf: Seq<u8>)
        ensures
            self.parse_rec(ibuf).0 == self.byte_len(self.parse_rec(ibuf).1),
        decreases ibuf.len(),
    {
        self.inner.lemma_parse_byte_len(ibuf);
        if let Some((n, v)) = self.inner.spec_parse(ibuf) {
            if 0 < n <= ibuf.len() {
                let (n_rest, vs) = self.parse_rec(ibuf.skip(n));
                self.lemma_parse_rec_byte_len(ibuf.skip(n));
                self.lemma_byte_len_cons(v, vs);
            }
        }
    }
}

impl<A: SpecParser> SpecParser for super::Star<A> {
    type PVal = Seq<A::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let (n, vs) = self.parse_rec(ibuf);
        Some((n, vs))
    }
}

impl<A> Consistency for super::Star<A> where A: Consistency {
    type Val = Seq<A::Val>;

    open spec fn consistent(&self, vs: Self::Val) -> bool {
        forall|i: int| 0 <= i < vs.len() ==> #[trigger] self.inner.consistent(vs[i])
    }
}

impl<A> GoodParser for super::Star<A> where A: GoodParser {
    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        self.lemma_parse_rec_length(ibuf);
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        self.lemma_parse_rec_byte_len(ibuf);
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        self.lemma_parse_rec_consistent(ibuf);
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

impl<A: GoodSerializerDps> super::Star<A> {
    proof fn lemma_rfold_serialize_buf(&self, vs: Seq<A::ST>, obuf: Seq<u8>)
        ensures
            exists|new_buf: Seq<u8>| self.rfold_serialize_dps(vs, obuf) == new_buf + obuf,
        decreases vs.len(),
    {
        if vs.len() == 0 {
            assert(self.rfold_serialize_dps(vs, obuf) == Seq::empty() + obuf);
        } else {
            let rest = vs.skip(1);
            let rest_buf = self.rfold_serialize_dps(rest, obuf);

            // induction
            self.lemma_rfold_serialize_buf(rest, obuf);
            let rest_witness = choose|wit: Seq<u8>|
                self.rfold_serialize_dps(rest, obuf) == wit + obuf;

            // base
            self.inner.lemma_serialize_dps_buf(vs[0], rest_buf);
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
    type SVal = Seq<A::SVal>;

    open spec fn spec_serialize(&self, vs: Self::SVal) -> Seq<u8> {
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

impl<A> GoodSerializerDps for super::Star<A> where A: GoodSerializerDps {
    proof fn lemma_serialize_dps_buf(&self, vs: Self::ST, obuf: Seq<u8>) {
        self.lemma_rfold_serialize_buf(vs, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, vs: Self::ST, obuf: Seq<u8>)
        decreases vs.len(),
    {
        if vs.len() == 0 {
        } else {
            let v0 = vs[0];
            let rest = vs.skip(1);
            let rest_buf = self.rfold_serialize_dps(rest, obuf);
            // base
            self.inner.lemma_serialize_dps_len(v0, rest_buf);
            // induction
            self.lemma_serialize_dps_len(rest, obuf);
            // fold_left lemmas
            let f = |acc: nat, elem: A::ST| acc + self.inner.byte_len(elem);
            vs.lemma_fold_left_alt(0, f);
            rest.lemma_fold_left_alt(self.inner.byte_len(v0), f);
            lemma_fold_left_accumulate_nat(rest, self.inner.byte_len(v0), f);
        }
    }
}

impl<A: GoodSerializer> GoodSerializer for super::Star<A> {
    proof fn lemma_serialize_len(&self, v: Self::SVal)
        decreases v.len(),
    {
        if v.len() == 0 {
        } else {
            let v_last = v.last();
            self.inner.lemma_serialize_len(v_last);
            self.lemma_serialize_len(v.drop_last());
        }
    }
}

impl<A: SpecByteLen> SpecByteLen for super::Star<A> {
    type T = Seq<A::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        v.fold_left(0, |acc: nat, elem| acc + self.inner.byte_len(elem))
    }
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Repeat<A, B> {
    type PVal = (Seq<A::PVal>, B::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (super::Star { inner: self.0 }, self.1).spec_parse(ibuf)
    }
}

impl<A, B> Consistency for super::Repeat<A, B> where A: Consistency, B: Consistency {
    type Val = (Seq<A::Val>, B::Val);

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (super::Star { inner: self.0 }, self.1).consistent(v)
    }
}

impl<A, B> GoodParser for super::Repeat<A, B> where A: GoodParser, B: GoodParser {
    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_parse_len_bound(ibuf)
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_parse_byte_len(ibuf)
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_parse_consistent(ibuf)
    }
}

impl<A: SpecSerializerDps, B: SpecSerializerDps> SpecSerializerDps for super::Repeat<A, B> {
    type ST = (Seq<A::ST>, B::ST);

    open spec fn spec_serialize_dps(&self, vs: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (super::Star { inner: self.0 }, self.1).spec_serialize_dps(vs, obuf)
    }
}

impl<A: SpecSerializer, B: SpecSerializer> SpecSerializer for super::Repeat<A, B> {
    type SVal = (Seq<A::SVal>, B::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (super::Star { inner: self.0 }, self.1).spec_serialize(v)
    }
}

impl<A: GoodSerializerDps, B: GoodSerializerDps> GoodSerializerDps for super::Repeat<A, B> {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_serialize_dps_buf(v, obuf)
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_serialize_dps_len(v, obuf);
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Repeat<A, B> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        (super::Star { inner: self.0 }, self.1).lemma_serialize_len(v);
    }
}

impl<A: SpecByteLen, B: SpecByteLen> SpecByteLen for super::Repeat<A, B> {
    type T = (Seq<A::T>, B::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (super::Star { inner: self.0 }, self.1).byte_len(v)
    }
}

impl<A: Unambiguity, B: Unambiguity> Unambiguity for super::Repeat<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }
}

} // verus!
