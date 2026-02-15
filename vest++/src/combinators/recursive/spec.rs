use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub trait Height {
    spec fn height(&self) -> nat;
}

pub trait RecBody {
    type Val: Height;

    spec fn parse_body(&self, rec: ParserFnSpec<Self::Val>) -> ParserFnSpec<Self::Val>;

    spec fn byte_len_body(&self, rec: ByteLenFnSpec<Self::Val>) -> ByteLenFnSpec<Self::Val>;

    spec fn consistent_body(&self, rec: PredFnSpec<Self::Val>) -> PredFnSpec<Self::Val>;

    proof fn lemma_body_smaller_height(
        &self,
        rec: ParserFnSpec<Self::Val>,
        ibuf: Seq<u8>,
        rem: Seq<u8>,
        ni: int,
        nr: int,
        vi: Self::Val,
        vr: Self::Val,
    )
        requires
            rem.len() < ibuf.len(),
            self.parse_body(rec)(ibuf) == Some((ni, vi)),
            rec(rem) == Some((nr, vr)),
        ensures
            vr.height() < vi.height(),
    ;
}

impl<Body: RecBody> SpecParser for super::Fix<Body> {
    type PVal = Body::Val;

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)>
        decreases input.len(), 1nat,
    {
        self.0.parse_body(self.parse_callback(input))(input)
    }
}

impl<Body: RecBody> Consistency for super::Fix<Body> {
    type Val = Body::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool
        decreases v.height(), 1nat,
    {
        self.0.consistent_body(self.consistent_callback(v))(v)
    }
}

impl<Body: RecBody> SpecByteLen for super::Fix<Body> {
    type T = Body::Val;

    open spec fn byte_len(&self, v: Self::T) -> nat
        decreases v.height(), 1nat,
    {
        self.0.byte_len_body(self.byte_len_callback(v))(v)
    }
}

pub open spec fn good_parser<T>(
    parser: ParserFnSpec<T>,
    consistent: PredFnSpec<T>,
    byte_len: ByteLenFnSpec<T>,
) -> bool {
    forall|input: Seq<u8>| #[trigger]
        parser(input) matches Some((n, v)) ==> {
            &&& 0 <= n <= input.len()
            &&& consistent(v)
            &&& byte_len(v) == n
        }
}

impl<Body: RecBody> super::Fix<Body> {
    pub open spec fn parse_callback(&self, input: Seq<u8>) -> ParserFnSpec<Body::Val>
        decreases input.len(), 0nat,
    {
        |rem: Seq<u8>|
            {
                if rem.len() < input.len() {
                    self.spec_parse(rem)
                } else {
                    None
                }
            }
    }

    pub open spec fn consistent_callback(&self, v: Body::Val) -> PredFnSpec<Body::Val>
        decreases v.height(), 0nat,
    {
        |vv: Body::Val|
            {
                if vv.height() < v.height() {
                    self.consistent(vv)
                } else {
                    false
                }
            }
    }

    pub open spec fn byte_len_callback(&self, v: Body::Val) -> ByteLenFnSpec<Body::Val>
        decreases v.height(), 0nat,
    {
        |vv: Body::Val|
            {
                if vv.height() < v.height() {
                    self.byte_len(vv)
                } else {
                    0
                }
            }
    }

    pub open spec fn induction(&self) -> bool {
        forall|
            p_rec: ParserFnSpec<Body::Val>,
            b_rec: ByteLenFnSpec<Body::Val>,
            c_rec: PredFnSpec<Body::Val>,
        |
            {
                good_parser(p_rec, c_rec, b_rec) ==> good_parser(
                    self.0.parse_body(p_rec),
                    self.0.consistent_body(c_rec),
                    self.0.byte_len_body(b_rec),
                )
            }
    }

    proof fn good_parser_by_induction(&self, input: Seq<u8>, n: int, v: Body::Val)
        requires
            self.induction(),
        ensures
            self.spec_parse(input) == Some((n, v)) ==> {
                &&& 0 <= n <= input.len()
                &&& self.consistent(v)
                &&& self.byte_len(v) == n
            },
        decreases input.len(),
    {
        // vacuous case
        if !(self.spec_parse(input) == Some((n, v))) {
            return ;
        }
        let callback_p = self.parse_callback(input);
        let callback_c = self.consistent_callback(v);
        let callback_b = self.byte_len_callback(v);

        // establish good_parser(callback_p, callback_c, callback_b)
        assert forall|rem: Seq<u8>| #[trigger]
            callback_p(rem) matches Some((nn, vv)) ==> {
                &&& 0 <= nn <= rem.len()
                &&& callback_c(vv)
                &&& callback_b(vv) == nn
            } by {
            if let Some((nn, vv)) = callback_p(rem) {
                if rem.len() < input.len() {
                    self.good_parser_by_induction(rem, nn, vv);
                    // IH gives: 0 <= nn <= rem.len(), self.consistent(vv), self.byte_len(vv) == nn
                    assert(0 <= nn <= rem.len());

                    assert(self.spec_parse(input) == Some((n, v)));
                    assert(self.spec_parse(rem) == Some((nn, vv)));
                    assert(self.0.parse_body(callback_p)(input) == Some((n, v)));
                    assert(callback_p(rem) == Some((nn, vv)));
                    self.0.lemma_body_smaller_height(callback_p, input, rem, n, nn, v, vv);
                    assert(vv.height() < v.height());
                    assert(self.consistent(vv) == callback_c(vv));
                    assert(self.byte_len(vv) == callback_b(vv));
                    assert(callback_c(vv));
                    assert(callback_b(vv) == nn);
                }
            }
        }

        assert(good_parser(callback_p, callback_c, callback_b));
        // By `self.induction()`
        assert(good_parser(
            self.0.parse_body(callback_p),
            self.0.consistent_body(callback_c),
            self.0.byte_len_body(callback_b),
        ));
        // By definition
        assert(self.spec_parse(input) == self.0.parse_body(callback_p)(input));
        assert(self.consistent(v) == self.0.consistent_body(callback_c)(v));
        assert(self.byte_len(v) == self.0.byte_len_body(callback_b)(v));
    }
}

impl<Body: RecBody> GoodParser for super::Fix<Body> {
    open spec fn inv(&self) -> bool {
        self.induction()
    }

    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.good_parser_by_induction(ibuf, n, v);
        }
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.good_parser_by_induction(ibuf, n, v);
        }
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.good_parser_by_induction(ibuf, n, v);
        }
    }
}

} // verus!
