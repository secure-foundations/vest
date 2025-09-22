use vstd::prelude::*;

verus! {

pub trait SpecCombinator {
    type Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }

    open spec fn requires(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        true
    }

    spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)>;

    spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8>;

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
    ;

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>)
        requires
            self.requires(v, obuf),
        ensures
            self.wf(v) ==> exists|new_buf: Seq<u8>| self.spec_serialize(v, obuf) == new_buf + obuf,
    ;

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>)
        requires
            self.requires(v, obuf),
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

pub struct Fixed<const N: usize>;

impl<const N: usize> SpecCombinator for Fixed<N> {
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

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            assert(self.spec_serialize(v, obuf) == v + obuf);
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
    }
}

impl<A, B> SpecCombinator for (A, B) where A: SpecCombinator, B: SpecCombinator {
    type Type = (A::Type, B::Type);

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v.0) && self.1.wf(v.1)
    }

    open spec fn requires(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        self.1.requires(v.1, obuf) && self.0.requires(v.0, self.1.spec_serialize(v.1, obuf))
    }

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, v1)) => match self.1.spec_parse(ibuf.skip(n1)) {
                Some((n2, v2)) => Some((n1 + n2, (v1, v2))),
                None => None,
            },
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        self.0.spec_serialize(v.0, self.1.spec_serialize(v.1, obuf))
    }

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_length(ibuf.skip(n1));
        }
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            let serialized1 = self.1.spec_serialize(v.1, obuf);
            let serialized0 = self.0.spec_serialize(v.0, serialized1);
            self.1.lemma_serialize_buf(v.1, obuf);
            self.0.lemma_serialize_buf(v.0, serialized1);
            let witness1 = choose|wit1: Seq<u8>| self.1.spec_serialize(v.1, obuf) == wit1 + obuf;
            let witness0 = choose|wit0: Seq<u8>|
                self.0.spec_serialize(v.0, serialized1) == wit0 + serialized1;
            assert(serialized0 == witness0 + witness1 + obuf);
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            let serialized1 = self.1.spec_serialize(v.1, obuf);
            let serialized0 = self.0.spec_serialize(v.0, serialized1);
            self.1.theorem_serialize_parse_roundtrip(v.1, obuf);
            self.0.theorem_serialize_parse_roundtrip(v.0, serialized1);
            self.1.lemma_serialize_buf(v.1, obuf);
            self.0.lemma_serialize_buf(v.0, serialized1);
            if let Some((n0, v0)) = self.0.spec_parse(serialized0) {
                assert(n0 == serialized0.len() - serialized1.len());
                assert(serialized0.skip(n0) == serialized1);
                if let Some((n1, v1)) = self.1.spec_parse(serialized0.skip(n0)) {
                    assert(n1 == serialized1.len() - obuf.len());
                    assert(v == (v0, v1));
                    assert(self.spec_parse(serialized0) == Some((n0 + n1, (v0, v1))));
                }
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_length(ibuf.skip(n1));
            if let Some((n2, v2)) = self.1.spec_parse(ibuf.skip(n1)) {
                let serialized2 = self.1.spec_serialize(v2, obuf);
                let serialized1 = self.0.spec_serialize(v1, serialized2);
                self.0.theorem_parse_serialize_roundtrip(ibuf, serialized2);
                self.1.theorem_parse_serialize_roundtrip(ibuf.skip(n1), obuf);
            }
        }
    }
}

pub struct Opt<A>(pub A);

impl<A> SpecCombinator for Opt<A> where A: SpecCombinator {
    type Type = Option<A::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            None => true,
            Some(vv) => self.0.wf(vv),
        }
    }

    open spec fn requires(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        // &&& self.0.spec_parse(obuf) is None  // <-- here
        match v {
            None => self.0.spec_parse(obuf) is None,
            Some(vv) => self.0.requires(vv, obuf),
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

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        match v {
            None => {
                assert(self.spec_serialize(v, obuf) == Seq::empty() + obuf);
            },
            Some(vv) => {
                if self.wf(v) {
                    self.0.lemma_serialize_buf(vv, obuf);
                }
            },
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        match v {
            None => {
                assert(self.spec_serialize(v, obuf) == obuf);
                if let Some((n, v)) = self.spec_parse(obuf) {
                    assert(n == 0);
                    assert(v == Option::<A::Type>::None);
                }
            },
            Some(vv) => {
                if self.wf(v) {
                    self.0.theorem_serialize_parse_roundtrip(vv, obuf);
                }
            },
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        if let Some((n, v)) = self.spec_parse(ibuf) {
            match v {
                None => {
                    assert(n == 0);
                    assert(self.spec_serialize(v, obuf) == obuf);
                },
                Some(vv) => {
                    self.0.theorem_parse_serialize_roundtrip(ibuf, obuf);
                },
            }
        }
    }
}

pub struct Refined<A: SpecCombinator> {
    pub inner: A,
    pub pred: spec_fn(A::Type) -> bool,
}

impl<A: SpecCombinator> SpecCombinator for Refined<A> {
    type Type = A::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.inner.wf(v) && (self.pred)(v)
    }

    open spec fn requires(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        self.inner.requires(v, obuf)
    }

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => {
                if (self.pred)(v) {
                    Some((n, v))
                } else {
                    None
                }
            },
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize(v, obuf)
    }

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.lemma_serialize_buf(v, obuf);
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.theorem_serialize_parse_roundtrip(v, obuf);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

pub struct Choice<A: SpecCombinator, B: SpecCombinator>(pub A, pub B);

pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A: SpecCombinator, B: SpecCombinator> SpecCombinator for Choice<A, B> {
    type Type = Either<A::Type, B::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            Either::Left(va) => self.0.wf(va),
            Either::Right(vb) => self.1.wf(vb),
        }
    }

    open spec fn requires(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        match v {
            Either::Left(va) => self.0.requires(va, obuf),
            Either::Right(vb) => {
                &&& self.1.requires(vb, obuf) 
                &&& self.0.spec_parse(self.1.spec_serialize(vb, obuf)) is None // <-- here
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

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        self.1.lemma_parse_length(ibuf);
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            match v {
                Either::Left(va) => {
                    self.0.lemma_serialize_buf(va, obuf);
                },
                Either::Right(vb) => {
                    self.1.lemma_serialize_buf(vb, obuf);
                },
            }
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            match v {
                Either::Left(va) => {
                    self.0.theorem_serialize_parse_roundtrip(va, obuf);
                },
                Either::Right(vb) => {
                    self.1.theorem_serialize_parse_roundtrip(vb, obuf);
                },
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(ibuf, obuf);
        self.1.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

proof fn test_opt_compose() {
    let c = (
        (
            Opt(Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 2u8 }),
            Opt(Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 1u8 }),
        ),
        Opt(Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 2u8 }),
    );
    let obuf = seq![0u8; 10];
    // let v = ((Some(seq![2u8]), Some(seq![1u8])), Some(seq![2u8]));
    let v = ((Some(seq![2u8]), None), Some(seq![2u8]));
    // let v = (Some(seq![0u8]), (Some(seq![1u8]), Some(seq![2u8])));
    // let v1 = (Some(seq![0u8]), (Some(seq![1u8]), None));
    // let v2 = (Some(seq![0u8]), (None, Some(seq![2u8])));
    // let v3 = (None, (Some(seq![1u8]), Some(seq![2u8])));
    assert(c.wf(v));
    assert(c.requires(v, obuf));
    // assert(c.wf(v1));
    // assert(c.wf(v2));
    // assert(c.wf(v3));
    let ibuf = c.spec_serialize(v, obuf);
    // let ibuf = c.spec_serialize(v1, obuf);
    // let ibuf = c.spec_serialize(v2, obuf);
    // let ibuf = c.spec_serialize(v3, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) == Some((2int, v)));
    // assert(c.spec_parse(ibuf) == Some((2int, v1)));
    // assert(c.spec_parse(ibuf) == Some((2int, v2)));
    // assert(c.spec_parse(ibuf) == Some((2int, v3)));
    // c.theorem_parse_serialize_roundtrip(ibuf, obuf);
}

proof fn test_choice_compose() {
    let c = Choice(
        Choice(
            Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 0u8 },
            Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 2u8 },
        ),
        Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 2u8 },
    );
    let obuf = Seq::empty();
    let v = Either::Left(Either::Right(seq![2u8]));
    // let v = Either::Right(seq![2u8]);
    assert(c.wf(v));
    assert(c.requires(v, obuf));
    let ibuf = c.spec_serialize(v, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) == Some((1int, v)));
}

} // verus!
