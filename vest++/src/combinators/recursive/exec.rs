use super::{ParamRecSpecs, SafeParserRecBody, SpecRecBody};
use crate::core::exec::parser::*;
use crate::core::exec::serializer::Serializer;
use crate::core::exec::{input::InputBuf, ParseError};
use crate::core::spec::{SafeParser, SpecParser, SpecSerializer};
use vstd::prelude::*;

verus! {

/// Executable parsing for one recursive unfolding.
pub trait ParserRecBody<I: InputBuf>: SpecRecBody {
    type EP: DeepView<V = Self::Param>;

    type O: DeepView<V = Self::T>;

    /// Execute one recursive unfolding, using `exec_rec` for all recursive positions in the body.
    ///
    /// `spec_rec` is the ghost/spec callback bundle corresponding to `exec_rec`.
    fn parse_body<Exec>(
        &self,
        param: &Self::EP,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        ibuf: &I,
    ) -> (r: PResult<Self::O>) where Exec: Fn(&Self::EP, &I) -> PResult<Self::O>
        requires
            forall|p: Self::Param| #[trigger] spec_rec(p).safe_inv(),
            forall|pp: &Self::EP, i: &I| call_requires(exec_rec, (pp, i)),
            forall|pp: &Self::EP, i: &I, rr: PResult<Self::O>|
                call_ensures(exec_rec, (pp, i), rr) ==> parse_matches_spec(
                    rr,
                    spec_rec(pp.deep_view()).2(i@),
                ),
        ensures
            parse_matches_spec(r, Self::spec_body(param.deep_view(), spec_rec).spec_parse(ibuf@)),
    ;
}

/// Executable serialization for one recursive unfolding.
pub trait SerializerRecBody<ST>: SpecRecBody where ST: DeepView<V = Self::T> {
    type EP: DeepView<V = Self::Param>;

    /// Execute one recursive unfolding, using `exec_rec` for all recursive positions in the body.
    ///
    /// `spec_rec` is the ghost/spec callback bundle corresponding to `exec_rec`.
    fn serialize_body<Exec>(
        &self,
        param: &Self::EP,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: ST,
        obuf: &mut Vec<u8>,
    ) where Exec: Fn(&Self::EP, ST, &mut Vec<u8>)
        requires
            forall|pp: &Self::EP, vv: ST, out: &mut Vec<u8>| call_requires(exec_rec, (pp, vv, out)),
            forall|pp: &Self::EP, vv: ST, out: &mut Vec<u8>|
                call_ensures(exec_rec, (pp, vv, out), ()) ==> final(out)@ == out@ + spec_rec(
                    pp.deep_view(),
                ).3(vv.deep_view()),
        ensures
            final(obuf)@ == old(obuf)@ + Self::spec_body(
                param.deep_view(),
                spec_rec,
            ).spec_serialize(v.deep_view()),
    ;
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: SpecRecBody,
    Param: DeepView<V = Body::Param>,
 {
    fn parse_gas<I>(&self, gas: usize, param: &Param, ibuf: &I) -> (r: PResult<Body::O>) where
        I: InputBuf,
        Param: DeepView<V = Body::Param>,
        Body: ParserRecBody<I, EP = Param> + SafeParserRecBody,
        Body::Body: SafeParser,

        ensures
            parse_matches_spec(r, Self::spec_parse_gas(gas as nat, param.deep_view(), ibuf@)),
        decreases gas,
    {
        let exec_callback = |pp: &Param, i: &I| -> (rr: PResult<Body::O>)
            ensures
                parse_matches_spec(rr, Self::spec_parse_callback(gas as nat, pp.deep_view())(i@)),
            {
                if gas > 0 {
                    self.parse_gas((gas - 1) as usize, pp, i)
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            };

        let ghost spec_callback = Self::specs_callback(gas as nat);
        proof {
            assert forall|p: Body::Param, input: Seq<u8>| #[trigger]
                spec_callback(p).2(input) matches Some((n, _v)) ==> 0 <= n <= input.len() by {
                if let Some((n, v)) = spec_callback(p).2(input) {
                    if gas > 0 {
                        self.safe_parser_by_induction((gas - 1) as nat, p, input, n, v);
                    }
                }
            }
            assert forall|p: Body::Param| #[trigger] spec_callback(p).safe_inv() by {
                assert(spec_callback(p).safe_inv());
            }
        }

        self.0.parse_body(param, Ghost(spec_callback), exec_callback, ibuf)
    }

    fn serialize_gas<ST>(&self, gas: usize, param: &Param, v: ST, obuf: &mut Vec<u8>) where
        ST: DeepView<V = Body::T>,
        Param: DeepView<V = Body::Param>,
        Body: SerializerRecBody<ST, EP = Param>,

        ensures
            final(obuf)@ == old(obuf)@ + Self::spec_serialize_gas(
                gas as nat,
                param.deep_view(),
                v.deep_view(),
            ),
        decreases gas,
    {
        let exec_callback = |pp: &Param, vv: ST, oo: &mut Vec<u8>| -> ()
            ensures
                final(oo)@ == old(oo)@ + Self::spec_serialize_callback(gas as nat, pp.deep_view())(
                    vv.deep_view(),
                ),
            {
                if gas > 0 {
                    self.serialize_gas((gas - 1) as usize, pp, vv, oo);
                }
            };

        let ghost spec_callback = Self::specs_callback(gas as nat);
        self.0.serialize_body(param, Ghost(spec_callback), exec_callback, v, obuf)
    }
}

impl<const LIMIT: usize, Body, Param, I> Parser<I> for super::FixWith<LIMIT, Body, Param> where
    I: InputBuf,
    Param: DeepView<V = Body::Param>,
    Body: ParserRecBody<I, EP = Param> + SafeParserRecBody,
    Body::Body: SafeParser,
 {
    type PT = Body::O;

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        self.parse_gas(LIMIT, &self.1, ibuf)
    }
}

impl<ST, const LIMIT: usize, Body, Param> Serializer<ST> for super::FixWith<
    LIMIT,
    Body,
    Param,
> where
    ST: DeepView<V = Body::T>,
    Param: DeepView<V = Body::Param>,
    Body: SerializerRecBody<ST, EP = Param>,
 {
    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, &self.1, v, obuf)
    }
}

} // verus!
