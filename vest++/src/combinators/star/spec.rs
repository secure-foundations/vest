use crate::combinators::length::AsLen;
use crate::combinators::Pair;
use crate::core::{proof::*, spec::*};
use vstd::calc;
use vstd::prelude::*;

verus! {

proof fn lemma_static_seq_byte_len<A: StaticByteLen>(inner: A, vs: Seq<A::T>)
    ensures
        (super::Star { inner }).byte_len(vs) == vs.len() * A::static_byte_len(),
    decreases vs.len(),
{
    use crate::combinators::star::proof::lemma_fold_left_accumulate_nat;

    let star = super::Star { inner };
    if vs.len() == 0 {
    } else {
        let v0 = vs[0];
        let rest = vs.skip(1);
        let k = A::static_byte_len();
        let f = |acc: nat, elem: A::T| acc + inner.byte_len(elem);

        calc! {
            (==)
            star.byte_len(vs); {
                assert(vs == seq![v0] + rest);
            }
            (seq![v0] + rest).fold_left(0, f); {
                (seq![v0] + rest).lemma_fold_left_alt(0, f);
            }
            (seq![v0] + rest).fold_left_alt(0, f); {}
            rest.fold_left_alt(inner.byte_len(v0), f); {
                rest.lemma_fold_left_alt(inner.byte_len(v0), f);
            }
            rest.fold_left(inner.byte_len(v0), f); {
                lemma_fold_left_accumulate_nat(rest, inner.byte_len(v0), f);
            }
            inner.byte_len(v0) + rest.fold_left(0, f); {}
            inner.byte_len(v0) + star.byte_len(rest); {
                inner.lemma_static_len_matches_byte_len(v0);
            }
            k + star.byte_len(rest); {
                lemma_static_seq_byte_len(inner, rest);
            }
            k + rest.len() * k;
        }
        assert(k + rest.len() * k == (rest.len() + 1) * k) by (nonlinear_arith);
        assert((rest.len() + 1) * k == vs.len() * k);
    }
}

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

impl<A: SoundParser> super::Star<A> {
    proof fn lemma_byte_len_cons(&self, v: A::T, vs: Seq<A::T>)
        ensures
            self.byte_len(seq![v] + vs) == self.inner.byte_len(v) + self.byte_len(vs),
    {
        use crate::combinators::star::proof::lemma_fold_left_accumulate_nat;

        let f = |acc: nat, elem: A::T| acc + self.inner.byte_len(elem);
        (seq![v] + vs).lemma_fold_left_alt(0, f);
        vs.lemma_fold_left_alt(self.inner.byte_len(v), f);
        lemma_fold_left_accumulate_nat(vs, self.inner.byte_len(v), f);
        assert((seq![v] + vs).skip(1) == vs);
    }

    proof fn lemma_parse_rec_length(&self, ibuf: Seq<u8>)
        requires
            self.inner.sound_inv(),
        ensures
            0 <= self.parse_rec(ibuf).0 <= ibuf.len(),
        decreases ibuf.len(),
    {
        self.inner.lemma_parse_safe(ibuf);
        if let Some((n, v)) = self.inner.spec_parse(ibuf) {
            if 0 < n <= ibuf.len() {
                self.lemma_parse_rec_length(ibuf.skip(n));
            }
        }
    }

    proof fn lemma_parse_rec_consistent(&self, ibuf: Seq<u8>)
        requires
            self.inner.sound_inv(),
        ensures
            self.consistent(self.parse_rec(ibuf).1),
        decreases ibuf.len(),
    {
        self.inner.lemma_parse_sound_value(ibuf);
        if let Some((n, v)) = self.inner.spec_parse(ibuf) {
            if 0 < n <= ibuf.len() {
                self.lemma_parse_rec_consistent(ibuf.skip(n));
            }
        }
    }

    proof fn lemma_parse_rec_byte_len(&self, ibuf: Seq<u8>)
        requires
            self.inner.sound_inv(),
        ensures
            self.parse_rec(ibuf).0 == self.byte_len(self.parse_rec(ibuf).1),
        decreases ibuf.len(),
    {
        self.inner.lemma_parse_sound_consumption(ibuf);
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

impl<A> SoundParser for super::Star<A> where A: SoundParser {
    open spec fn sound_inv(&self) -> bool {
        self.inner.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.lemma_parse_rec_length(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.lemma_parse_rec_byte_len(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
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

impl<A: Unambiguity> Unambiguity for super::Star<A> {
    open spec fn unambiguous(&self) -> bool {
        self.inner.unambiguous()
    }
}

impl<A: NonTailFmt> super::Star<A> {
    proof fn lemma_rfold_serialize_buf(&self, vs: Seq<A::ST>, obuf: Seq<u8>)
        requires
            self.serialize_dps_inv(),
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
            self.inner.lemma_serialize_dps_prepend(vs[0], rest_buf);
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

impl<A> NonTailFmt for super::Star<A> where A: NonTailFmt {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, vs: Self::ST, obuf: Seq<u8>) {
        self.lemma_rfold_serialize_buf(vs, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, vs: Self::ST, obuf: Seq<u8>)
        decreases vs.len(),
    {
        use crate::combinators::star::proof::lemma_fold_left_accumulate_nat;

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
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

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

impl<C: SpecParser, N: AsLen> super::RepeatN<C, N> {
    pub open spec fn parse_n_rec(&self, count: nat, ibuf: Seq<u8>) -> Option<(int, Seq<C::PVal>)>
        decreases count,
    {
        if count == 0 {
            Some((0, Seq::empty()))
        } else {
            match self.1.spec_parse(ibuf) {
                Some((n0, v0)) => match self.parse_n_rec((count - 1) as nat, ibuf.skip(n0)) {
                    Some((n1, vs1)) => Some((n0 + n1, seq![v0] + vs1)),
                    None => None,
                },
                None => None,
            }
        }
    }

    proof fn lemma_parse_n_rec_count(&self, count: nat, ibuf: Seq<u8>)
        ensures
            self.parse_n_rec(count, ibuf) matches Some((_, vs)) ==> vs.len() == count,
        decreases count,
    {
        if count == 0 {
        } else {
            if let Some((n0, v0)) = self.1.spec_parse(ibuf) {
                self.lemma_parse_n_rec_count((count - 1) as nat, ibuf.skip(n0));
            }
        }
    }

    pub proof fn lemma_parse_exactly_n_times(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((_, vs)) ==> vs.len() == self.0.as_usize(),
    {
        self.lemma_parse_n_rec_count(self.0.as_usize() as nat, ibuf);
    }
}

impl<C: SpecParser, N: AsLen> SpecParser for super::RepeatN<C, N> {
    type PVal = Seq<C::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.parse_n_rec(self.0.as_usize() as nat, ibuf)
    }
}

impl<C: Consistency, N: AsLen> Consistency for super::RepeatN<C, N> {
    type Val = Seq<C::Val>;

    open spec fn consistent(&self, vs: Self::Val) -> bool {
        &&& vs.len() == self.0.as_usize()
        &&& super::Star { inner: self.1 }.consistent(vs)
    }
}

impl<C: SoundParser, N: AsLen> super::RepeatN<C, N> {
    pub(crate) proof fn lemma_parse_n_len_bound(&self, count: nat, ibuf: Seq<u8>)
        requires
            self.1.sound_inv(),
        ensures
            self.parse_n_rec(count, ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
        decreases count,
    {
        if count == 0 {
        } else {
            self.1.lemma_parse_safe(ibuf);
            if let Some((n0, _v0)) = self.1.spec_parse(ibuf) {
                self.lemma_parse_n_len_bound((count - 1) as nat, ibuf.skip(n0));
            }
        }
    }

    proof fn lemma_parse_n_byte_len(&self, count: nat, ibuf: Seq<u8>)
        requires
            self.1.sound_inv(),
        ensures
            self.parse_n_rec(count, ibuf) matches Some((n, vs)) ==> n == (super::Star {
                inner: self.1,
            }).byte_len(vs),
        decreases count,
    {
        if count == 0 {
        } else {
            self.1.lemma_parse_sound_consumption(ibuf);
            if let Some((n0, v0)) = self.1.spec_parse(ibuf) {
                self.lemma_parse_n_byte_len((count - 1) as nat, ibuf.skip(n0));
                if let Some((n1, vs1)) = self.parse_n_rec((count - 1) as nat, ibuf.skip(n0)) {
                    let star = super::Star { inner: self.1 };
                    star.lemma_byte_len_cons(v0, vs1);
                }
            }
        }
    }

    proof fn lemma_parse_n_consistent(&self, count: nat, ibuf: Seq<u8>)
        requires
            self.1.sound_inv(),
        ensures
            self.parse_n_rec(count, ibuf) matches Some((_, vs)) ==> {
                &&& vs.len() == count
                &&& super::Star { inner: self.1 }.consistent(vs)
            },
        decreases count,
    {
        if count == 0 {
        } else {
            self.1.lemma_parse_sound_value(ibuf);
            if let Some((n0, v0)) = self.1.spec_parse(ibuf) {
                self.lemma_parse_n_consistent((count - 1) as nat, ibuf.skip(n0));
            }
        }
    }
}

impl<C: SoundParser, N: AsLen> SoundParser for super::RepeatN<C, N> {
    open spec fn sound_inv(&self) -> bool {
        self.1.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.lemma_parse_n_len_bound(self.0.as_usize() as nat, ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.lemma_parse_n_byte_len(self.0.as_usize() as nat, ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.lemma_parse_n_consistent(self.0.as_usize() as nat, ibuf);
    }
}

impl<C: SpecSerializerDps, N: AsLen> SpecSerializerDps for super::RepeatN<C, N> {
    type ST = Seq<C::ST>;

    open spec fn spec_serialize_dps(&self, vs: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        super::Star { inner: self.1 }.spec_serialize_dps(vs, obuf)
    }
}

impl<C: SpecSerializer, N: AsLen> SpecSerializer for super::RepeatN<C, N> {
    type SVal = Seq<C::SVal>;

    open spec fn spec_serialize(&self, vs: Self::SVal) -> Seq<u8> {
        super::Star { inner: self.1 }.spec_serialize(vs)
    }
}

impl<C: Unambiguity, N: AsLen> Unambiguity for super::RepeatN<C, N> {
    open spec fn unambiguous(&self) -> bool {
        self.1.unambiguous()
    }
}

impl<C: NonTailFmt, N: AsLen> NonTailFmt for super::RepeatN<C, N> {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.1.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        super::Star { inner: self.1 }.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        super::Star { inner: self.1 }.lemma_serialize_dps_len(v, obuf);
    }
}

impl<C: GoodSerializer, N: AsLen> GoodSerializer for super::RepeatN<C, N> {
    open spec fn serialize_inv(&self) -> bool {
        self.1.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        super::Star { inner: self.1 }.lemma_serialize_len(v);
    }
}

impl<C: SpecByteLen, N: AsLen> SpecByteLen for super::RepeatN<C, N> {
    type T = Seq<C::T>;

    open spec fn byte_len(&self, vs: Self::T) -> nat {
        super::Star { inner: self.1 }.byte_len(vs)
    }
}

impl<const N: usize, C: SpecParser> SpecParser for super::Array<N, C> {
    type PVal = [C::PVal; N];

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        use crate::combinators::bytes::spec::array_from_seq;

        match super::RepeatN(N, self.0).spec_parse(ibuf) {
            Some((n, vs)) => Some((n, array_from_seq::<N, C::PVal>(vs))),
            _ => None,
        }
    }
}

impl<const N: usize, C: Consistency> Consistency for super::Array<N, C> {
    type Val = [C::Val; N];

    open spec fn consistent(&self, v: Self::Val) -> bool {
        super::RepeatN(N, self.0).consistent(v@)
    }
}

impl<const N: usize, C: SoundParser> SoundParser for super::Array<N, C> {
    open spec fn sound_inv(&self) -> bool {
        super::RepeatN(N, self.0).sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        super::RepeatN(N, self.0).lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use super::super::bytes::spec::axiom_array_from_seq;

        let rep = super::RepeatN(N, self.0);
        rep.lemma_parse_sound_consumption(ibuf);
        rep.lemma_parse_exactly_n_times(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use super::super::bytes::spec::axiom_array_from_seq;

        let rep = super::RepeatN(N, self.0);
        rep.lemma_parse_sound_value(ibuf);
    }
}

impl<const N: usize, C: SpecSerializerDps> SpecSerializerDps for super::Array<N, C> {
    type ST = [C::ST; N];

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        super::RepeatN(N, self.0).spec_serialize_dps(v@, obuf)
    }
}

impl<const N: usize, C: SpecSerializer> SpecSerializer for super::Array<N, C> {
    type SVal = [C::SVal; N];

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        super::RepeatN(N, self.0).spec_serialize(v@)
    }
}

impl<const N: usize, C: Unambiguity> Unambiguity for super::Array<N, C> {
    open spec fn unambiguous(&self) -> bool {
        super::RepeatN(N, self.0).unambiguous()
    }
}

impl<const N: usize, C: NonTailFmt> NonTailFmt for super::Array<N, C> {
    open spec fn serialize_dps_inv(&self) -> bool {
        super::RepeatN(N, self.0).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        super::RepeatN(N, self.0).lemma_serialize_dps_prepend(v@, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        super::RepeatN(N, self.0).lemma_serialize_dps_len(v@, obuf);
    }
}

impl<const N: usize, C: GoodSerializer> GoodSerializer for super::Array<N, C> {
    open spec fn serialize_inv(&self) -> bool {
        super::RepeatN(N, self.0).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        super::RepeatN(N, self.0).lemma_serialize_len(v@);
    }
}

impl<const N: usize, C: SpecByteLen> SpecByteLen for super::Array<N, C> {
    type T = [C::T; N];

    open spec fn byte_len(&self, v: Self::T) -> nat {
        super::RepeatN(N, self.0).byte_len(v@)
    }
}

impl<const N: usize, C: StaticByteLen> StaticByteLen for super::Array<N, C> {
    open spec fn static_byte_len() -> nat {
        N as nat * C::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        let star = super::Star { inner: self.0 };
        lemma_static_seq_byte_len(star.inner, v@);
        assert(self.byte_len(v) == star.byte_len(v@));
        assert(v@.len() == N as nat);
        assert(self.byte_len(v) == v@.len() * C::static_byte_len());
    }
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Repeat<A, B> {
    type PVal = (Seq<A::PVal>, B::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Pair(super::Star { inner: self.0 }, self.1).spec_parse(ibuf)
    }
}

impl<A, B> Consistency for super::Repeat<A, B> where A: Consistency, B: Consistency {
    type Val = (Seq<A::Val>, B::Val);

    open spec fn consistent(&self, v: Self::Val) -> bool {
        Pair(super::Star { inner: self.0 }, self.1).consistent(v)
    }
}

impl<A, B> SoundParser for super::Repeat<A, B> where A: SoundParser, B: SoundParser {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Pair(super::Star { inner: self.0 }, self.1).lemma_parse_safe(ibuf)
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        Pair(super::Star { inner: self.0 }, self.1).lemma_parse_sound_consumption(ibuf)
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Pair(super::Star { inner: self.0 }, self.1).lemma_parse_sound_value(ibuf)
    }
}

impl<A: SpecSerializerDps, B: SpecSerializerDps> SpecSerializerDps for super::Repeat<A, B> {
    type ST = (Seq<A::ST>, B::ST);

    open spec fn spec_serialize_dps(&self, vs: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Pair(super::Star { inner: self.0 }, self.1).spec_serialize_dps(vs, obuf)
    }
}

impl<A: SpecSerializer, B: SpecSerializer> SpecSerializer for super::Repeat<A, B> {
    type SVal = (Seq<A::SVal>, B::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Pair(super::Star { inner: self.0 }, self.1).spec_serialize(v)
    }
}

impl<A: NonTailFmt, B: NonTailFmt> NonTailFmt for super::Repeat<A, B> {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        Pair(super::Star { inner: self.0 }, self.1).lemma_serialize_dps_prepend(v, obuf)
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        Pair(super::Star { inner: self.0 }, self.1).lemma_serialize_dps_len(v, obuf);
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Repeat<A, B> {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.1.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        Pair(super::Star { inner: self.0 }, self.1).lemma_serialize_len(v);
    }
}

impl<A: SpecByteLen, B: SpecByteLen> SpecByteLen for super::Repeat<A, B> {
    type T = (Seq<A::T>, B::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        Pair(super::Star { inner: self.0 }, self.1).byte_len(v)
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
