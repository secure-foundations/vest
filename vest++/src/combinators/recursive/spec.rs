use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// Defines one level of a recursive format for use with [`super::Fix`].
pub trait RecBody {
    /// The type of values parsed/serialized by this recursive format.
    type Val;

    /// Parser for one level, given a recursive callback.
    spec fn parse_body(&self, rec: ParserFnSpec<Self::Val>) -> ParserFnSpec<Self::Val>;

    /// Byte-length function for one level, given a recursive callback.
    spec fn byte_len_body(&self, rec: ByteLenFnSpec<Self::Val>) -> ByteLenFnSpec<Self::Val>;

    /// Consistency predicate for one level, given a recursive callback.
    spec fn consistent_body(&self, rec: PredFnSpec<Self::Val>) -> PredFnSpec<Self::Val>;

    /// [`good_parser`] is preserved through one level of unfolding.
    proof fn lemma_body_preservation(
        &self,
        p_rec: ParserFnSpec<Self::Val>,
        c_rec: PredFnSpec<Self::Val>,
        b_rec: ByteLenFnSpec<Self::Val>,
    )
        requires
            good_parser(p_rec, c_rec, b_rec),
        ensures
            good_parser(
                self.parse_body(p_rec),
                self.consistent_body(c_rec),
                self.byte_len_body(b_rec),
            ),
    ;
}

impl<const LIMIT: usize, Body: RecBody> SpecParser for super::Fix<LIMIT, Body> {
    type PVal = Body::Val;

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.spec_parse_with_gas(LIMIT as nat, input)
    }
}

impl<const LIMIT: usize, Body: RecBody> Consistency for super::Fix<LIMIT, Body> {
    type Val = Body::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.consistent_with_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: RecBody> SpecByteLen for super::Fix<LIMIT, Body> {
    type T = Body::Val;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.byte_len_with_gas(LIMIT as nat, v)
    }
}

/// Bundled triple of parser, consistency, and byte-length spec functions.
pub type ParserSpecs<T> = (ParserFnSpec<T>, PredFnSpec<T>, ByteLenFnSpec<T>);

impl<T> SpecByteLen for ParserSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.2)(v)
    }
}

impl<T> SpecParser for ParserSpecs<T> {
    type PVal = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self.0)(ibuf)
    }
}

impl<T> Consistency for ParserSpecs<T> {
    type Val = T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (self.1)(v)
    }
}

impl<T> SoundParser for ParserSpecs<T> {
    open spec fn inv(&self) -> bool {
        let (p_fn, c_fn, b_fn) = *self;
        good_parser(p_fn, c_fn, b_fn)
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

/// The functional version of [`GoodParser`].
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

impl<const LIMIT: usize, Body: RecBody> super::Fix<LIMIT, Body> {
    /// Parse with a given amount of gas. Unfolds one level via
    /// `body.parse_body` with a callback that recurses at `gas - 1`.
    pub open spec fn spec_parse_with_gas(&self, gas: nat, input: Seq<u8>) -> Option<
        (int, Body::Val),
    >
        decreases gas, 1nat,
    {
        self.0.parse_body(self.parse_callback(gas))(input)
    }

    /// Consistency check with given gas.
    pub open spec fn consistent_with_gas(&self, gas: nat, v: Body::Val) -> bool
        decreases gas, 1nat,
    {
        self.0.consistent_body(self.consistent_callback(gas))(v)
    }

    /// Byte-length computation with given gas.
    pub open spec fn byte_len_with_gas(&self, gas: nat, v: Body::Val) -> nat
        decreases gas, 1nat,
    {
        self.0.byte_len_body(self.byte_len_callback(gas))(v)
    }

    /// Recursive parser callback: recurses at `gas - 1`, returns `None` at zero.
    pub open spec fn parse_callback(&self, gas: nat) -> ParserFnSpec<Body::Val>
        decreases gas, 0nat,
    {
        |ibuf: Seq<u8>|
            {
                if gas > 0 {
                    self.spec_parse_with_gas((gas - 1) as nat, ibuf)
                } else {
                    None
                }
            }
    }

    /// Recursive consistency callback: recurses at `gas - 1`, returns `false` at zero.
    pub open spec fn consistent_callback(&self, gas: nat) -> PredFnSpec<Body::Val>
        decreases gas, 0nat,
    {
        |vv: Body::Val|
            {
                if gas > 0 {
                    self.consistent_with_gas((gas - 1) as nat, vv)
                } else {
                    false
                }
            }
    }

    /// Recursive byte-length callback: recurses at `gas - 1`, returns `0` at zero.
    pub open spec fn byte_len_callback(&self, gas: nat) -> ByteLenFnSpec<Body::Val>
        decreases gas, 0nat,
    {
        |vv: Body::Val|
            {
                if gas > 0 {
                    self.byte_len_with_gas((gas - 1) as nat, vv)
                } else {
                    0
                }
            }
    }

    /// Inductive proof that `spec_parse_with_gas` satisfies [`good_parser`].
    proof fn good_parser_by_induction(&self, gas: nat, input: Seq<u8>, n: int, v: Body::Val)
        ensures
            self.spec_parse_with_gas(gas, input) == Some((n, v)) ==> {
                &&& 0 <= n <= input.len()
                &&& self.consistent_with_gas(gas, v)
                &&& self.byte_len_with_gas(gas, v) == n
            },
        decreases gas,
    {
        // vacuous case
        if !(self.spec_parse_with_gas(gas, input) == Some((n, v))) {
            return ;
        }
        let callback_p = self.parse_callback(gas);
        let callback_c = self.consistent_callback(gas);
        let callback_b = self.byte_len_callback(gas);

        // establish good_parser(callback_p, callback_c, callback_b)
        assert forall|rem: Seq<u8>| #[trigger]
            callback_p(rem) matches Some((nn, vv)) ==> {
                &&& 0 <= nn <= rem.len()
                &&& callback_c(vv)
                &&& callback_b(vv) == nn
            } by {
            if let Some((nn, vv)) = callback_p(rem) {
                self.good_parser_by_induction((gas - 1) as nat, rem, nn, vv);
                // IH gives: 0 <= nn <= rem.len(), consistent_with_gas(gas - 1, vv), byte_len_with_gas(gas - 1, vv) == nn
                assert(0 <= nn <= rem.len());

                assert(self.spec_parse_with_gas((gas - 1) as nat, rem) == Some((nn, vv)));
                assert(self.consistent_with_gas((gas - 1) as nat, vv) == callback_c(vv));
                assert(self.byte_len_with_gas((gas - 1) as nat, vv) == callback_b(vv));
                assert(callback_c(vv));
                assert(callback_b(vv) == nn);
            }
        }

        assert(good_parser(callback_p, callback_c, callback_b));
        self.0.lemma_body_preservation(callback_p, callback_c, callback_b);
        // By definition
        assert(self.spec_parse_with_gas(gas, input) == self.0.parse_body(callback_p)(input));
        assert(self.consistent_with_gas(gas, v) == self.0.consistent_body(callback_c)(v));
        assert(self.byte_len_with_gas(gas, v) == self.0.byte_len_body(callback_b)(v));
    }
}

impl<const LIMIT: usize, Body: RecBody> SoundParser for super::Fix<LIMIT, Body> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.good_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.good_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.good_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }
}

/*
 * Example recursive parser: nested braces
 */

use crate::combinators::*;
use crate::combinators::mapped::spec::{IsoMapper, Mapper};

/// Example recursive value type: nested braces `{...}` or empty `\0`.
pub enum NestedBracesT {
    /// A brace-wrapped recursive value: `'{' inner '}'`.
    Brace(Box<NestedBracesT>),
    /// The empty (base case) value: `'\0'`.
    Eps,
}

/// Mapper between `Sum<NestedBracesT, ()>` and `NestedBracesT`.
pub struct NestedBracesMapper;

impl Mapper for NestedBracesMapper {
    type In = Sum<NestedBracesT, ()>;

    type Out = NestedBracesT;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(inner) => NestedBracesT::Brace(Box::new(inner)),
            Sum::Inr(()) => NestedBracesT::Eps,
        }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            NestedBracesT::Brace(inner) => Sum::Inl(*inner),
            NestedBracesT::Eps => Sum::Inr(()),
        }
    }
}

impl IsoMapper for NestedBracesMapper {
    proof fn lemma_map_iso(&self, i: Self::In) {
        match i {
            Sum::Inl(_) => {},
            Sum::Inr(u) => {
                assert(u == ());
            },
        }
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

/// One level of the nested-braces format: `'{' rec '}' | '\0'`.
pub open spec fn nested_braces_body<Rec>(rec: Rec) -> Mapped<
    Choice<Terminated<Preceded<Tag<U8, u8>, Rec>, Tag<U8, u8>>, Tag<U8, u8>>,
    NestedBracesMapper,
> {
    Mapped {
        inner: Choice(
            Terminated(
                Preceded(Tag { inner: U8, tag: 0x7Bu8 }, rec),
                Tag { inner: U8, tag: 0x7Du8 },
            ),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
    }
}

/// [`RecBody`] for the nested-braces example.
pub struct NestedBracesBody;

impl RecBody for NestedBracesBody {
    type Val = NestedBracesT;

    open spec fn parse_body(&self, rec: ParserFnSpec<Self::Val>) -> ParserFnSpec<Self::Val> {
        |input: Seq<u8>| nested_braces_body(rec).spec_parse(input)
    }

    open spec fn byte_len_body(&self, rec: ByteLenFnSpec<Self::Val>) -> ByteLenFnSpec<Self::Val> {
        |v: Self::Val| nested_braces_body(rec).byte_len(v)
    }

    open spec fn consistent_body(&self, rec: PredFnSpec<Self::Val>) -> PredFnSpec<Self::Val> {
        |v: Self::Val|
            nested_braces_body(rec).consistent(v)
        // |v: Self::Val|
        //     exists|p: ParserFnSpec<Self::Val>, b: ByteLenFnSpec<Self::Val>| #[trigger]
        //         nested_braces_body((p, rec, b)).consistent(v)

    }

    proof fn lemma_body_preservation(
        &self,
        p_rec: ParserFnSpec<Self::Val>,
        c_rec: PredFnSpec<Self::Val>,
        b_rec: ByteLenFnSpec<Self::Val>,
    ) {
        assert forall|input: Seq<u8>| #[trigger]
            self.parse_body(p_rec)(input) matches Some((n, v)) ==> {
                &&& 0 <= n <= input.len()
                &&& self.consistent_body(c_rec)(v)
                &&& self.byte_len_body(b_rec)(v) == n
            } by {
            let body = nested_braces_body((p_rec, c_rec, b_rec));
            body.lemma_parse_safe(input);
            body.lemma_parse_sound_consumption(input);
            body.lemma_parse_sound_value(input);
            let body_cons = nested_braces_body(c_rec);
            assert(body_cons.inner.0.0.0.consistent(()));
            assert(body_cons.inner.0.1.consistent(()));
        }
    }
}

proof fn nested_braces_good_parser() {
    let nested_braces = super::Fix::<10, _>(NestedBracesBody);

    let input = seq![0x7Bu8, 0x00u8, 0x7Du8];

    assert(nested_braces.spec_parse(input) == Some(
        (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
    )) by {
        let body10 = nested_braces_body(nested_braces.parse_callback(10nat));
        assert(body10.spec_parse(input) == Some(
            (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
        ));
    };

    nested_braces.lemma_parse_sound_consumption(input);
    nested_braces.lemma_parse_sound_value(input);
    nested_braces.lemma_parse_safe(input);
}

} // verus!
