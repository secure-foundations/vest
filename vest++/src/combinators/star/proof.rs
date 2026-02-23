use crate::combinators::bytes::spec::{array_from_seq, axiom_array_from_seq};
use crate::combinators::length::AsLen;
use crate::combinators::tuple::proof::lemma_take_skip;
use crate::core::{proof::*, spec::*};
use vstd::{calc, prelude::*};

verus! {

impl<A> super::Star<A> where A: SPRoundTripDps + GoodSerializerDps {
    proof fn lemma_serialize_parse_roundtrip_rec(&self, vs: Seq<A::PVal>, obuf: Seq<u8>)
        requires
            self.inner.unambiguous(),
            parser_fails_on(self.inner, obuf),
            self.consistent(vs),
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
            assert(self.consistent(rest));
            self.lemma_serialize_parse_roundtrip_rec(rest, obuf);

            // base
            assert(self.inner.consistent(v));
            self.inner.theorem_serialize_dps_parse_roundtrip(v, rest_buf);
            self.inner.lemma_serialize_dps_buf(v, rest_buf);
            self.inner.lemma_serialize_dps_len(v, rest_buf);

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
                assert(self.parse_rec(rest_buf) == (0int, Seq::<A::PVal>::empty()));
                // from I.H.:
                assert(self.parse_rec(rest_buf) == (rest_buf.len() - obuf.len(), rest));
                self.lemma_serialize_dps_buf(rest, obuf);

                // therefore:
                assert(rest_buf == obuf);
                assert(rest == Seq::<A::PVal>::empty());

                // contradiction
                assert(self.inner.spec_parse(obuf) is Some);
                assert(self.inner.spec_parse(obuf) is None);
            }
        }
    }
}

impl<A: NonMalleable> super::Star<A> {
    proof fn lemma_parse_non_malleable_rec(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.inv(),
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
                        self.lemma_parse_len_bound(buf1.skip(m1));
                        self.lemma_parse_len_bound(buf2.skip(m2));
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

impl<A: NoLookAhead> super::Star<A> {
    proof fn lemma_parse_rec_no_lookahead_conditional(&self, i1: Seq<u8>, i2: Seq<u8>)
        requires
            self.inv(),
            self.inner.unambiguous(),
            parser_fails_on(self.inner, i2.skip(self.parse_rec(i1).0)),
        ensures
            ({
                let r = self.parse_rec(i1);
                0 <= r.0 <= i2.len() ==> i2.take(r.0) == i1.take(r.0) ==> self.parse_rec(i2) == r
            }),
        decreases i1.len(),
    {
        broadcast use vstd::seq_lib::group_seq_properties;

        let (n, vs) = self.parse_rec(i1);
        match self.inner.spec_parse(i1) {
            Some((m, v)) if 0 < m <= i1.len() => {
                let i1_rest = i1.skip(m);
                let i2_rest = i2.skip(m);
                let (n_rest, vs_rest) = self.parse_rec(i1_rest);
                self.lemma_parse_len_bound(i1_rest);
                if 0 <= n <= i2.len() {
                    if i2.take(n) == i1.take(n) {
                        assert(i2.take(m) == i1.take(m));
                        self.inner.lemma_no_lookahead(i1, i2);
                        assert(i2_rest.take(n_rest) == i1_rest.take(n_rest)) by {
                            lemma_take_skip(i1, m, n_rest);
                            lemma_take_skip(i2, m, n_rest);
                        };
                        assert(parser_fails_on(self.inner, i2_rest.skip(n_rest))) by {
                            broadcast use vstd::seq_lib::lemma_seq_skip_of_skip;

                        };
                        self.lemma_parse_rec_no_lookahead_conditional(i1_rest, i2_rest);
                        assert(self.parse_rec(i2) == (m + n_rest, seq![v] + vs_rest));
                    }
                }
            },
            _ => {},
        }
    }
}

impl<A> super::Star<A> where A: EquivSerializersGeneral {
    proof fn lemma_serialize_equiv_rec(&self, vs: Seq<A::SVal>, obuf: Seq<u8>)
        ensures
            self.rfold_serialize_dps(vs, obuf) == self.spec_serialize(vs) + obuf,
        decreases vs.len(),
    {
        let f = |buf: Seq<u8>, elem: A::SVal| buf + self.inner.spec_serialize(elem);

        if vs.len() == 0 {
        } else {
            let v0 = vs[0];
            let rest = vs.skip(1);

            let rest_foldr = self.rfold_serialize_dps(rest, obuf);
            let rest_foldl = rest.fold_left(Seq::empty(), f);

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
                vs.fold_left(Seq::empty(), f); {
                    vs.lemma_fold_left_alt(Seq::empty(), f);
                }
                vs.fold_left_alt(Seq::empty(), f); {}
                rest.fold_left_alt(f(Seq::empty(), v0), f); {}
                rest.fold_left_alt(self.inner.spec_serialize(v0), f); {
                    rest.lemma_fold_left_alt(self.inner.spec_serialize(v0), f);
                }
                rest.fold_left(self.inner.spec_serialize(v0), f); {
                    assert forall|acc: Seq<u8>, x: Seq<u8>, y: A::SVal| #[trigger]
                        f(acc + x, y) == acc + #[trigger] f(x, y) by {}
                    lemma_fold_left_accumulate_seq(rest, self.inner.spec_serialize(v0), f);
                }
                self.inner.spec_serialize(v0) + rest_foldl;
            }
        }
    }
}

pub(crate) proof fn lemma_fold_left_accumulate_seq<T, U>(
    vs: Seq<T>,
    init: Seq<U>,
    f: spec_fn(Seq<U>, T) -> Seq<U>,
)
    requires
        forall|acc: Seq<U>, x: Seq<U>, y: T| #[trigger] f(acc + x, y) == acc + #[trigger] f(x, y),
    ensures
        vs.fold_left(init, f) == init + vs.fold_left(Seq::<U>::empty(), f),
    decreases vs.len(),
{
    if vs.len() == 0 {
    } else {
        let last = vs.last();
        let prefix = vs.drop_last();
        lemma_fold_left_accumulate_seq(prefix, init, f);
    }
}

pub(crate) proof fn lemma_fold_left_accumulate_nat<T>(
    vs: Seq<T>,
    init: nat,
    f: spec_fn(nat, T) -> nat,
)
    requires
        forall|acc: nat, x: nat, y: T| #[trigger] f(acc + x, y) == acc + #[trigger] f(x, y),
    ensures
        vs.fold_left(init, f) == init + vs.fold_left(0, f),
    decreases vs.len(),
{
    if vs.len() == 0 {
    } else {
        let last = vs.last();
        let prefix = vs.drop_last();
        lemma_fold_left_accumulate_nat(prefix, init, f);
    }
}

impl<A> EquivSerializersGeneral for super::Star<A> where A: EquivSerializersGeneral {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.lemma_serialize_equiv_rec(v, obuf);
    }
}

impl<A> EquivSerializers for super::Star<A> where A: EquivSerializersGeneral {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.lemma_serialize_equiv_rec(v, Seq::empty());
    }
}

impl<C, N> super::RepeatN<C, N> where C: SPRoundTripDps + GoodSerializerDps, N: AsLen {
    proof fn lemma_serialize_parse_roundtrip_rec(&self, vs: Seq<C::PVal>, count: nat, obuf: Seq<u8>)
        requires
            self.1.unambiguous(),
            vs.len() == count,
            (super::Star { inner: self.1 }.consistent(vs)),
        ensures
            self.parse_n_rec(count, self.spec_serialize_dps(vs, obuf)) == Some(
                ((self.spec_serialize_dps(vs, obuf).len() - obuf.len()) as int, vs),
            ),
        decreases count,
    {
        if count == 0 {
        } else {
            let v0 = vs[0];
            let rest = vs.skip(1);
            let rest_buf = self.spec_serialize_dps(rest, obuf);
            let serialized = self.spec_serialize_dps(vs, obuf);

            self.lemma_serialize_parse_roundtrip_rec(rest, (count - 1) as nat, obuf);

            self.1.theorem_serialize_dps_parse_roundtrip(v0, rest_buf);
            self.1.lemma_serialize_dps_buf(v0, rest_buf);
            self.1.lemma_serialize_dps_len(v0, rest_buf);

            let n0 = (serialized.len() - rest_buf.len()) as int;
            assert(serialized.skip(n0) == rest_buf);
        }
    }
}

impl<C, N> SPRoundTripDps for super::RepeatN<C, N> where
    C: SPRoundTripDps + GoodSerializerDps,
    N: AsLen,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.lemma_serialize_parse_roundtrip_rec(v, self.0.as_usize() as nat, obuf);
        self.lemma_serialize_dps_len(v, obuf);
    }
}

impl<C: NonMalleable, N: AsLen> super::RepeatN<C, N> {
    #[verusfmt::skip]
    proof fn lemma_parse_non_malleable_rec(&self, count: nat, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.1.inv(),
        ensures
            self.parse_n_rec(count, buf1) matches Some((n1, v1)) ==>
            self.parse_n_rec(count, buf2) matches Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
        decreases count,
    {
        broadcast use vstd::seq_lib::group_seq_properties;

        if count == 0 {
        } else {
            if let Some((n1, v1)) = self.parse_n_rec(count, buf1) {
                if let Some((n2, v2)) = self.parse_n_rec(count, buf2) {
                    if v1 == v2 {
                        let (m1, a1) = self.1.spec_parse(buf1)->0;
                        let (m2, a2) = self.1.spec_parse(buf2)->0;
                        let (r1, rest1) = self.parse_n_rec((count - 1) as nat, buf1.skip(m1))->0;
                        let (r2, rest2) = self.parse_n_rec((count - 1) as nat, buf2.skip(m2))->0;
                        assert(v1 == seq![a1] + rest1);
                        assert(v2 == seq![a2] + rest2);
                        assert(a1 == a2) by {
                            assert(a1 == v1[0]);
                            assert(a2 == v2[0]);
                        }
                        assert(rest1 == rest2) by {
                            assert(rest1 == v1.skip(1));
                            assert(rest2 == v2.skip(1));
                        }

                        self.1.lemma_parse_len_bound(buf1);
                        self.1.lemma_parse_len_bound(buf2);
                        self.lemma_parse_n_len_bound((count - 1) as nat, buf1.skip(m1));
                        self.lemma_parse_n_len_bound((count - 1) as nat, buf2.skip(m2));
                        self.1.lemma_parse_non_malleable(buf1, buf2);
                        assert(buf1.take(m1) == buf2.take(m2));

                        self.lemma_parse_non_malleable_rec((count - 1) as nat, buf1.skip(m1), buf2.skip(m2));
                        assert(buf1.skip(m1).take(r1) == buf2.skip(m2).take(r2));

                        assert(n1 == m1 + r1);
                        assert(n2 == m2 + r2);
                        assert(buf1.take(n1) == buf1.take(m1) + buf1.skip(m1).take(r1));
                        assert(buf2.take(n2) == buf2.take(m2) + buf2.skip(m2).take(r2));
                    }
                }
            }
        }
    }
}

impl<C: NonMalleable, N: AsLen> NonMalleable for super::RepeatN<C, N> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.lemma_parse_non_malleable_rec(self.0.as_usize() as nat, buf1, buf2);
    }
}

impl<C: NoLookAhead, N: AsLen> super::RepeatN<C, N> {
    proof fn lemma_no_lookahead_rec(&self, count: nat, i1: Seq<u8>, i2: Seq<u8>)
        requires
            self.1.inv(),
            self.1.unambiguous(),
        ensures
            self.parse_n_rec(count, i1) matches Some((n, v)) ==> 0 <= n <= i2.len() ==> i2.take(n)
                == i1.take(n) ==> self.parse_n_rec(count, i2) == Some((n, v)),
        decreases count,
    {
        broadcast use vstd::seq_lib::group_seq_properties;

        if count == 0 {
        } else {
            if let Some((n, v)) = self.parse_n_rec(count, i1) {
                if 0 <= n <= i2.len() {
                    if i2.take(n) == i1.take(n) {
                        let (m, a) = self.1.spec_parse(i1)->0;
                        let (r, rest) = self.parse_n_rec((count - 1) as nat, i1.skip(m))->0;
                        assert(v == seq![a] + rest);
                        assert(n == m + r);
                        self.1.lemma_parse_len_bound(i1);
                        self.lemma_parse_n_len_bound((count - 1) as nat, i1.skip(m));
                        assert(0 <= m <= n);
                        assert(i2.take(m) == i1.take(m));
                        self.1.lemma_no_lookahead(i1, i2);
                        assert(i2.skip(m).take(r) == i1.skip(m).take(r)) by {
                            lemma_take_skip(i1, m, r);
                            lemma_take_skip(i2, m, r);
                        };
                        self.lemma_no_lookahead_rec((count - 1) as nat, i1.skip(m), i2.skip(m));
                    }
                }
            }
        }
    }
}

impl<C: NoLookAhead, N: AsLen> NoLookAhead for super::RepeatN<C, N> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        self.lemma_no_lookahead_rec(self.0.as_usize() as nat, i1, i2);
    }
}

impl<C: EquivSerializersGeneral, N: AsLen> EquivSerializersGeneral for super::RepeatN<C, N> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        super::Star { inner: self.1 }.lemma_serialize_equiv(v, obuf);
    }
}

impl<C: EquivSerializersGeneral, N: AsLen> EquivSerializers for super::RepeatN<C, N> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        super::Star { inner: self.1 }.lemma_serialize_equiv_on_empty(v);
    }
}

impl<const N: usize, C> SPRoundTripDps for super::Array<N, C> where
    C: SPRoundTripDps + GoodSerializerDps,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        broadcast use axiom_array_from_seq;

        let rep = super::RepeatN(N, self.0);
        rep.theorem_serialize_dps_parse_roundtrip(v@, obuf);
    }
}

impl<const N: usize, C: NonMalleable> NonMalleable for super::Array<N, C> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;

        let rep = super::RepeatN(N, self.0);
        rep.lemma_parse_exactly_n_times(buf1);
        rep.lemma_parse_exactly_n_times(buf2);
        rep.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<const N: usize, C: NoLookAhead> NoLookAhead for super::Array<N, C> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        broadcast use axiom_array_from_seq;

        let rep = super::RepeatN(N, self.0);
        rep.lemma_parse_exactly_n_times(i1);
        rep.lemma_no_lookahead(i1, i2);
        rep.lemma_parse_exactly_n_times(i2);
    }
}

impl<const N: usize, C: EquivSerializersGeneral> EquivSerializersGeneral for super::Array<N, C> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        super::RepeatN(N, self.0).lemma_serialize_equiv(v@, obuf);
    }
}

impl<const N: usize, C: EquivSerializersGeneral> EquivSerializers for super::Array<N, C> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        super::RepeatN(N, self.0).lemma_serialize_equiv_on_empty(v@);
    }
}

impl<A: SPRoundTripDps + GoodSerializerDps, B: SPRoundTripDps> SPRoundTripDps for super::Repeat<
    A,
    B,
> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let star = super::Star { inner: self.0 };
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        self.1.theorem_serialize_dps_parse_roundtrip(v.1, obuf);
        let serialized0 = star.spec_serialize_dps(v.0, serialized1);
        star.lemma_serialize_parse_roundtrip_rec(v.0, serialized1);
        let n0 = serialized0.len() - serialized1.len();
        star.lemma_serialize_dps_buf(v.0, serialized1);
        star.lemma_serialize_dps_len(v.0, serialized1);
        assert(serialized0.skip(n0) == serialized1);
    }
}

// impl<
//     A: PSRoundTrip + GoodSerializerDps + EquivSerializersGeneral,
//     B: PSRoundTrip,
// > PSRoundTrip for super::Repeat<A, B> {
// }
impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Repeat<A, B> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: NoLookAhead, B: NoLookAhead> NoLookAhead for super::Repeat<A, B> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        broadcast use vstd::seq_lib::group_seq_properties;

        let star = super::Star { inner: self.0 };
        self.lemma_parse_len_bound(i1);
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    if let Some((n0, v0)) = star.spec_parse(i1) {
                        if let Some((n1, v1)) = self.1.spec_parse(i1.skip(n0)) {
                            star.lemma_parse_len_bound(i1);
                            self.1.lemma_parse_len_bound(i1.skip(n0));
                            assert(i2.take(n0) == i1.take(n0));
                            assert(i2.skip(n0).take(n1) == i1.skip(n0).take(n1)) by {
                                lemma_take_skip(i1, n0, n1);
                                lemma_take_skip(i2, n0, n1);
                            };
                            self.1.lemma_no_lookahead(i1.skip(n0), i2.skip(n0));
                            assert(disjoint_domains(self.0, self.1));
                            star.lemma_parse_rec_no_lookahead_conditional(i1, i2);
                        }
                    }
                }
            }
        }
    }
}

impl<
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
> EquivSerializersGeneral for super::Repeat<A, B> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        (super::Star { inner: self.0 }, self.1).lemma_serialize_equiv(v, obuf);
    }
}

impl<A: EquivSerializersGeneral, B: EquivSerializers> EquivSerializers for super::Repeat<A, B> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        (super::Star { inner: self.0 }, self.1).lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
