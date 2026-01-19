use crate::core::{proof::*, spec::*};
use vstd::{calc, prelude::*};

verus! {

impl<A> super::Star<A> where A: SPRoundTrip + GoodSerializer {
    proof fn lemma_serialize_parse_roundtrip_rec(&self, vs: Seq<A::PT>, obuf: Seq<u8>)
        requires
            self.inner.unambiguous(),
            parser_fails_on(self.inner, obuf),
            vs.wf(),
        ensures
            self.spec_parse(self.spec_serialize_dps(vs, obuf)) == Some(
                ((self.spec_serialize_dps(vs, obuf).len() - obuf.len()) as int, vs),
            ),
        decreases vs.len(),
    {
        if vs.len() == 0 {
            assert(self.inner.spec_parse(obuf) is None);
        } else {
            let v = vs[0];
            let rest = vs.skip(1);
            let rest_buf = self.spec_serialize_dps(rest, obuf);
            let serialized = self.spec_serialize_dps(vs, obuf);
            assert(serialized == self.inner.spec_serialize_dps(v, rest_buf));

            // induction
            self.lemma_serialize_parse_roundtrip_rec(rest, obuf);

            // base
            self.inner.theorem_serialize_parse_roundtrip(v, rest_buf);
            self.inner.lemma_serialize_buf(v, rest_buf);

            let n0 = (serialized.len() - rest_buf.len()) as int;
            assert(self.inner.spec_parse(serialized) == Some((n0, v)));
            assert(serialized.skip(n0) == rest_buf);

            if 0 < n0 <= serialized.len() {
                assert(self.spec_parse(rest_buf) == Some(self.parse_rec(rest_buf)));
                let (n1, v1) = self.parse_rec(rest_buf);
                assert(self.spec_parse(serialized) == Some((n0 + n1, seq![v] + v1)));
            } else {
                assert(n0 == 0);
                assert(serialized == rest_buf);
                assert(self.inner.spec_parse(rest_buf) == Some((0int, v)));

                // from the definition
                assert(self.parse_rec(rest_buf) == (0int, Seq::<A::PT>::empty()));
                // from I.H.:
                assert(self.parse_rec(rest_buf) == (rest_buf.len() - obuf.len(), rest));
                self.lemma_serialize_buf(rest, obuf);

                // therefore:
                assert(rest_buf == obuf);
                assert(rest == Seq::<A::PT>::empty());

                // contradiction
                assert(self.inner.spec_parse(obuf) is Some);
                assert(self.inner.spec_parse(obuf) is None);
            }
        }
    }
}

impl<A: NonMalleable> super::Star<A> {
    proof fn lemma_parse_non_malleable_rec(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        ensures
            ({
                let (n1, v1) = self.parse_rec(buf1);
                let (n2, v2) = self.parse_rec(buf2);
                v1 == v2 ==> buf1.take(n1) == buf2.take(n2)
            }),
        decreases buf1.len(),
    {
        let (n1, v1) = self.parse_rec(buf1);
        let (n2, v2) = self.parse_rec(buf2);
        if v1 == v2 {
            match (self.inner.spec_parse(buf1), self.inner.spec_parse(buf2)) {
                (Some((m1, a1)), Some((m2, a2))) => {
                    if 0 < m1 <= buf1.len() && 0 < m2 <= buf2.len() {
                        let (n1_rest, rest1) = self.parse_rec(buf1.skip(m1));
                        let (n2_rest, rest2) = self.parse_rec(buf2.skip(m2));

                        assert(n1 == m1 + n1_rest);
                        assert(n2 == m2 + n2_rest);
                        assert(v1 == seq![a1] + rest1);
                        assert(v2 == seq![a2] + rest2);

                        assert(a1 == a2) by {
                            assert(a1 == v1[0] && a2 == v2[0]);
                        }
                        assert(rest1 == rest2) by {
                            assert(rest1 == v1.skip(1));
                            assert(rest2 == v2.skip(1));
                        }

                        // base
                        self.inner.lemma_parse_non_malleable(buf1, buf2);
                        assert(buf1.take(m1) == buf2.take(m2));

                        // induction
                        self.lemma_parse_non_malleable_rec(buf1.skip(m1), buf2.skip(m2));
                        assert(buf1.skip(m1).take(n1_rest) == buf2.skip(m2).take(n2_rest));

                        // need to show buf1.take(n1) == buf2.take(n2)
                        self.lemma_parse_length(buf1.skip(m1));
                        self.lemma_parse_length(buf2.skip(m2));
                        assert(buf1.take(n1) == buf1.take(m1) + buf1.skip(m1).take(n1_rest));
                        assert(buf2.take(n2) == buf2.take(m2) + buf2.skip(m2).take(n2_rest));
                    }
                },
                _ => {},
            }
        }
    }
}

impl<A: NonMalleable> NonMalleable for super::Star<A> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.lemma_parse_non_malleable_rec(buf1, buf2);
    }
}

impl<A> super::Star<A> where A: Deterministic {
    proof fn lemma_serialize_equiv_rec(&self, vs: Seq<<A as SpecSerializer>::ST>, obuf: Seq<u8>)
        ensures
            self.rfold_serialize_dps(vs, obuf) == self.spec_serialize(vs) + obuf,
        decreases vs.len(),
    {
        let f = |buf: Seq<u8>, elem: <A as SpecSerializer>::ST|
            buf + self.inner.spec_serialize(elem);

        if vs.len() == 0 {
        } else {
            let v0 = vs[0];
            let rest = vs.skip(1);

            let rest_foldr = self.rfold_serialize_dps(rest, obuf);
            let rest_foldl = rest.fold_left(Seq::<u8>::empty(), f);

            calc! {
                (==)
                self.rfold_serialize_dps(vs, obuf); {  // definition
                }
                self.inner.spec_serialize_dps(v0, rest_foldr); {
                    // base
                    self.inner.lemma_serialize_equiv(v0, rest_foldr);
                }
                self.inner.spec_serialize(v0) + rest_foldr; {
                    // induction
                    self.lemma_serialize_equiv_rec(rest, obuf);
                }
                self.inner.spec_serialize(v0) + (rest_foldl + obuf); {}
                (self.inner.spec_serialize(v0) + rest_foldl) + obuf;
            }

            // need to show: fold_left(vs, empty, f) == inner.serialize(v0) + rest_foldl

            calc! {
                (==)
                vs.fold_left(Seq::<u8>::empty(), f); {
                    vs.lemma_fold_left_alt(Seq::<u8>::empty(), f);
                }
                vs.fold_left_alt(Seq::<u8>::empty(), f); {}
                rest.fold_left_alt(f(Seq::<u8>::empty(), v0), f); {}
                rest.fold_left_alt(self.inner.spec_serialize(v0), f); {
                    rest.lemma_fold_left_alt(self.inner.spec_serialize(v0), f);
                }
                rest.fold_left(self.inner.spec_serialize(v0), f); {
                    assert forall|acc: Seq<u8>, x: Seq<u8>, y: <A as SpecSerializer>::ST|
                     #[trigger]
                        f(acc + x, y) == acc + #[trigger] f(x, y) by {}
                    Self::lemma_fold_left_accumulate(rest, self.inner.spec_serialize(v0), f);
                }
                self.inner.spec_serialize(v0) + rest_foldl;
            }
        }
    }

    proof fn lemma_fold_left_accumulate<T, U>(
        vs: Seq<T>,
        init: Seq<U>,
        f: spec_fn(Seq<U>, T) -> Seq<U>,
    )
        requires
            forall|acc: Seq<U>, x: Seq<U>, y: T| #[trigger]
                f(acc + x, y) == acc + #[trigger] f(x, y),
        ensures
            vs.fold_left(init, f) == init + vs.fold_left(Seq::<U>::empty(), f),
        decreases vs.len(),
    {
        if vs.len() == 0 {
        } else {
            let last = vs.last();
            let prefix = vs.drop_last();
            Self::lemma_fold_left_accumulate(prefix, init, f);
        }
    }
}

impl<A> Deterministic for super::Star<A> where A: Deterministic {
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializer>::ST, obuf: Seq<u8>) {
            self.lemma_serialize_equiv_rec(v, obuf);
    }
}

impl<A: SPRoundTrip + GoodSerializer, B: SPRoundTrip> SPRoundTrip for super::Repeat<A, B> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>) {
        let star = super::Star { inner: self.0 };
        if v.wf() {
            let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
            self.1.theorem_serialize_parse_roundtrip(v.1, obuf);
            let serialized0 = star.spec_serialize_dps(v.0, serialized1);
            star.lemma_serialize_parse_roundtrip_rec(v.0, serialized1);
            let n0 = serialized0.len() - serialized1.len();
            star.lemma_serialize_buf(v.0, serialized1);
            assert(serialized0.skip(n0) == serialized1);
        }
    }
}


impl<A: PSRoundTrip + GoodSerializer, B: PSRoundTrip> PSRoundTrip for super::Repeat<A, B> {
}

impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Repeat<A, B> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
    {
        (super::Star { inner: self.0 }, self.1).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: Deterministic, B: Deterministic> Deterministic for super::Repeat<A, B> {
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializer>::ST, obuf: Seq<u8>) {
            (super::Star { inner: self.0 }, self.1).lemma_serialize_equiv(v, obuf);
    }
}

} // verus!
