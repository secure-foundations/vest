use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

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
    open spec fn sound_inv(&self) -> bool {
        let (p_fn, c_fn, b_fn) = *self;
        sound_parser(p_fn, c_fn, b_fn)
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

/// The functional version of [`GoodParser`].
pub open spec fn sound_parser<T>(
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

pub open spec fn parser_pair_some<T>(
    parser: ParserFnSpec<T>,
    buf1: Seq<u8>,
    buf2: Seq<u8>,
) -> Option<((int, T), (int, T))> {
    match parser(buf1) {
        Some((n1, v1)) => match parser(buf2) {
            Some((n2, v2)) => Some(((n1, v1), (n2, v2))),
            None => None,
        },
        None => None,
    }
}

/// Functional non-malleability for parser functions.
pub open spec fn non_malleable_parser<T>(parser: ParserFnSpec<T>) -> bool {
    forall|buf1: Seq<u8>, buf2: Seq<u8>| #[trigger]
        parser_pair_some(parser, buf1, buf2) matches Some(((n1, v1), (n2, v2))) ==> v1 == v2
            ==> buf1.take(n1) == buf2.take(n2)
}

impl<T> NonMalleable for ParserSpecs<T> {
    open spec fn nonmal_inv(&self) -> bool {
        let (p_fn, _, _) = *self;
        non_malleable_parser(p_fn)
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let p_fn = self.0;
                    assert(self.nonmal_inv());
                    assert(parser_pair_some(p_fn, buf1, buf2) == Some(((n1, v1), (n2, v2))));
                    assert(non_malleable_parser(p_fn));
                    assert(buf1.take(n1) == buf2.take(n2));
                }
            }
        }
    }
}

/// Defines one level of a recursive format for use with [`super::Fix`].
pub trait RecPBody {
    /// The type of values parsed/serialized by this recursive format.
    type T;

    /// The combinator type returned by [`Self::body`].
    type Body: SpecByteLen<T = Self::T> + SpecParser<PVal = Self::T> + Consistency<Val = Self::T>;

    /// Define the body for one level of the recursive format, where `rec`
    /// is the bundled callback for the recursive position.
    spec fn body(&self, rec: ParserSpecs<Self::T>) -> Self::Body;
}

/// Soundness for [`RecPBody`].
pub trait SoundRecPBody: RecPBody where Self::Body: SoundParser<T = Self::T> {
    /// Induction: if the callback `rec` satisfies `sound_inv`, then unfolding the body also satisfies `sound_inv`.
    proof fn lemma_body_sound_inv_preservation(&self, rec: ParserSpecs<Self::T>)
        requires
            rec.sound_inv(),
        ensures
            self.body(rec).sound_inv(),
    ;
}

/// Non-malleability for [`RecPBody`].
pub trait NonMalleableRecPBody: SoundRecPBody where Self::Body: NonMalleable<T = Self::T> {
    /// Induction: if the callback `rec` satisfies `sound_inv` and `nonmal_inv`,
    /// then unfolding the body also satisfies `nonmal_inv`.
    proof fn lemma_body_nonmal_inv_preservation(&self, rec: ParserSpecs<Self::T>)
        requires
            rec.sound_inv(),
            rec.nonmal_inv(),
        ensures
            self.body(rec).nonmal_inv(),
    ;
}

impl<const LIMIT: usize, Body: RecPBody> SpecParser for super::Fix<LIMIT, Body> {
    type PVal = Body::T;

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.spec_parse_with_gas(LIMIT as nat, input)
    }
}

impl<const LIMIT: usize, Body: RecPBody> Consistency for super::Fix<LIMIT, Body> {
    type Val = Body::T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.consistent_with_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: RecPBody> SpecByteLen for super::Fix<LIMIT, Body> {
    type T = Body::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.byte_len_with_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: RecPBody> super::Fix<LIMIT, Body> {
    /// Bundled recursive callback
    pub open spec fn specs_callback(&self, gas: nat) -> ParserSpecs<Body::T>
        decreases gas, 0nat,
    {
        (
            |ibuf: Seq<u8>|
                {
                    if gas > 0 {
                        self.spec_parse_with_gas((gas - 1) as nat, ibuf)
                    } else {
                        None
                    }
                },
            |vv: Body::T|
                {
                    if gas > 0 {
                        self.consistent_with_gas((gas - 1) as nat, vv)
                    } else {
                        false
                    }
                },
            |vv: Body::T|
                {
                    if gas > 0 {
                        self.byte_len_with_gas((gas - 1) as nat, vv)
                    } else {
                        0
                    }
                },
        )
    }

    /// Parse with a given amount of gas. Unfolds one level via
    /// `body` with a callback that recurses at `gas - 1`.
    pub open spec fn spec_parse_with_gas(&self, gas: nat, input: Seq<u8>) -> Option<(int, Body::T)>
        decreases gas, 1nat,
    {
        self.0.body(self.specs_callback(gas)).spec_parse(input)
    }

    /// Consistency check with given gas.
    pub open spec fn consistent_with_gas(&self, gas: nat, v: Body::T) -> bool
        decreases gas, 1nat,
    {
        self.0.body(self.specs_callback(gas)).consistent(v)
    }

    /// Byte-length computation with given gas.
    pub open spec fn byte_len_with_gas(&self, gas: nat, v: Body::T) -> nat
        decreases gas, 1nat,
    {
        self.0.body(self.specs_callback(gas)).byte_len(v)
    }
}

impl<const LIMIT: usize, Body: SoundRecPBody> super::Fix<LIMIT, Body> where
    Body::Body: SoundParser<T = Body::T>,
 {
    /// Inductive proof that `spec_parse_with_gas` satisfies [`sound_parser`].
    proof fn sound_parser_by_induction(&self, gas: nat, input: Seq<u8>, n: int, v: Body::T)
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
        let callback = self.specs_callback(gas);
        let callback_p = callback.0;
        let callback_c = callback.1;
        let callback_b = callback.2;

        // establish sound_parser(callback_p, callback_c, callback_b)
        assert forall|rem: Seq<u8>| #[trigger]
            callback_p(rem) matches Some((nn, vv)) ==> {
                &&& 0 <= nn <= rem.len()
                &&& callback_c(vv)
                &&& callback_b(vv) == nn
            } by {
            if let Some((nn, vv)) = callback_p(rem) {
                self.sound_parser_by_induction((gas - 1) as nat, rem, nn, vv);
                assert(0 <= nn <= rem.len());
                assert(self.spec_parse_with_gas((gas - 1) as nat, rem) == Some((nn, vv)));
                assert(self.consistent_with_gas((gas - 1) as nat, vv) == callback_c(vv));
                assert(self.byte_len_with_gas((gas - 1) as nat, vv) == callback_b(vv));
                assert(callback_c(vv));
                assert(callback_b(vv) == nn);
            }
        }

        assert(sound_parser(callback_p, callback_c, callback_b));
        assert(callback.sound_inv());

        self.0.lemma_body_sound_inv_preservation(callback);
        let body = self.0.body(callback);
        assert(body.sound_inv());

        body.lemma_parse_safe(input);
        body.lemma_parse_sound_consumption(input);
        body.lemma_parse_sound_value(input);

        // By definition
        assert(self.spec_parse_with_gas(gas, input) == body.spec_parse(input));
        assert(self.consistent_with_gas(gas, v) == body.consistent(v));
        assert(self.byte_len_with_gas(gas, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body: SoundRecPBody> SoundParser for super::Fix<LIMIT, Body> where
    Body::Body: SoundParser<T = Body::T>,
 {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.sound_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.sound_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.sound_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }
}

impl<const LIMIT: usize, Body: NonMalleableRecPBody> super::Fix<LIMIT, Body> where
    Body::Body: NonMalleable<T = Body::T>,
 {
    /// Inductive proof that `spec_parse_with_gas` is non-malleable.
    proof fn non_malleable_by_induction(
        &self,
        gas: nat,
        buf1: Seq<u8>,
        buf2: Seq<u8>,
        n1: int,
        n2: int,
        v1: Body::T,
        v2: Body::T,
    )
        ensures
            self.spec_parse_with_gas(gas, buf1) == Some((n1, v1)) ==> self.spec_parse_with_gas(
                gas,
                buf2,
            ) == Some((n2, v2)) ==> v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
        decreases gas,
    {
        if !(self.spec_parse_with_gas(gas, buf1) == Some((n1, v1))) {
            return ;
        }
        if !(self.spec_parse_with_gas(gas, buf2) == Some((n2, v2))) {
            return ;
        }
        if !(v1 == v2) {
            return ;
        }
        let callback = self.specs_callback(gas);
        let callback_p = callback.0;
        let callback_c = callback.1;
        let callback_b = callback.2;

        // establish sound_parser(callback_p, callback_c, callback_b)
        assert forall|rem: Seq<u8>| #[trigger]
            callback_p(rem) matches Some((nn, vv)) ==> {
                &&& 0 <= nn <= rem.len()
                &&& callback_c(vv)
                &&& callback_b(vv) == nn
            } by {
            if let Some((nn, vv)) = callback_p(rem) {
                self.sound_parser_by_induction((gas - 1) as nat, rem, nn, vv);
            }
        }

        // establish non_malleable_parser(callback_p)
        assert forall|rem1: Seq<u8>, rem2: Seq<u8>| #[trigger]
            parser_pair_some(callback_p, rem1, rem2) matches Some(((nn1, vv1), (nn2, vv2))) ==> vv1
                == vv2 ==> rem1.take(nn1) == rem2.take(nn2) by {
            if let Some(((nn1, vv1), (nn2, vv2))) = parser_pair_some(callback_p, rem1, rem2) {
                self.non_malleable_by_induction((gas - 1) as nat, rem1, rem2, nn1, nn2, vv1, vv2);
            }
        }

        assert(sound_parser(callback_p, callback_c, callback_b));
        assert(non_malleable_parser(callback_p));
        assert(callback.sound_inv());
        assert(callback.nonmal_inv());

        self.0.lemma_body_sound_inv_preservation(callback);
        self.0.lemma_body_nonmal_inv_preservation(callback);
        let body = self.0.body(callback);
        assert(body.sound_inv());
        assert(body.nonmal_inv());

        body.lemma_parse_non_malleable(buf1, buf2);

        // By definition
        assert(self.spec_parse_with_gas(gas, buf1) == body.spec_parse(buf1));
        assert(self.spec_parse_with_gas(gas, buf2) == body.spec_parse(buf2));
    }
}

impl<const LIMIT: usize, Body: NonMalleableRecPBody> NonMalleable for super::Fix<LIMIT, Body> where
    Body::Body: NonMalleable<T = Body::T>,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    self.non_malleable_by_induction(LIMIT as nat, buf1, buf2, n1, n2, v1, v2);
                }
            }
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
pub open spec fn nested_braces_body<Rec>(rec: Rec) -> NestedBracesBodyComb<Rec> {
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

type NestedBracesBodyComb<Rec> = Mapped<
    Choice<Terminated<Preceded<Tag<U8, u8>, Rec>, Tag<U8, u8>>, Tag<U8, u8>>,
    NestedBracesMapper,
>;

/// [`RecPBody`] for the nested-braces example.
pub struct NestedBracesBody;

impl RecPBody for NestedBracesBody {
    type T = NestedBracesT;

    type Body = NestedBracesBodyComb<ParserSpecs<NestedBracesT>>;

    open spec fn body(&self, rec: ParserSpecs<Self::T>) -> Self::Body {
        nested_braces_body(rec)
    }
}

impl SoundRecPBody for NestedBracesBody {
    proof fn lemma_body_sound_inv_preservation(&self, rec: ParserSpecs<Self::T>) {
        assert(self.body(rec).sound_inv());
    }
}

impl NonMalleableRecPBody for NestedBracesBody {
    proof fn lemma_body_nonmal_inv_preservation(&self, rec: ParserSpecs<Self::T>) {
        assert(self.body(rec).nonmal_inv());
    }
}

proof fn nested_braces_sound_parser() {
    let nested_braces = super::Fix::<10, _>(NestedBracesBody);

    let input = seq![0x7Bu8, 0x00u8, 0x7Du8];

    assert(nested_braces.spec_parse(input) == Some(
        (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
    )) by {
        let cb = nested_braces.specs_callback(10nat);
        let body10 = nested_braces_body(cb);
        assert(body10.spec_parse(input) == Some(
            (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
        ));
    };

    let input2 = seq![0x7Bu8, 0x00u8, 0x7Du8, 0x7Bu8, 0x00u8, 0x7Du8];

    nested_braces.lemma_parse_sound_consumption(input);
    nested_braces.lemma_parse_sound_value(input);
    nested_braces.lemma_parse_safe(input);
    nested_braces.lemma_parse_non_malleable(input, input2);
}

} // verus!
