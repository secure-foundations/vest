use super::{BundledSpecs, SafeParserRecBody, SpecRecBody};
use crate::core::exec::parser::*;
use crate::core::exec::{input::InputBuf, ParseError};
use crate::core::spec::{SafeParser, SpecParser};
use vstd::prelude::*;

verus! {

/// Executable parsing for one recursive unfolding.
pub trait ParserRecBody<I: InputBuf>: SpecRecBody {
    type O: DeepView<V = Self::T>;

    /// Execute one recursive unfolding, using `exec_rec` for all recursive positions in the body.
    ///
    /// `spec_rec` is the ghost/spec callback bundle corresponding to `exec_rec`.
    fn parse_body<Exec>(
        &self,
        Ghost(spec_rec): Ghost<BundledSpecs<Self::T>>,
        exec_rec: Exec,
        ibuf: &I,
    ) -> (r: PResult<Self::O>) where Exec: Fn(&I) -> PResult<Self::O>
        requires
            spec_rec.safe_inv(),
            forall|i: &I| call_requires(exec_rec, (i,)),
            forall|i: &I, rr: PResult<Self::O>|
                call_ensures(exec_rec, (i,), rr) ==> parse_matches_spec(rr, spec_rec.2(i@)),
        ensures
            parse_matches_spec(r, Self::spec_body(spec_rec).spec_parse(ibuf@)),
    ;
}

impl<const LIMIT: usize, Body> super::Fix<LIMIT, Body> {
    fn parse_gas<I>(&self, gas: usize, ibuf: &I) -> (r: PResult<Body::O>) where
        I: InputBuf,
        Body: ParserRecBody<I> + SafeParserRecBody,
        Body::Body: SafeParser,

        ensures
            parse_matches_spec(r, Self::spec_parse_gas(gas as nat, ibuf@)),
        decreases gas,
    {
        let exec_callback = |i: &I| -> (rr: PResult<Body::O>)
            ensures
                parse_matches_spec(rr, Self::spec_parse_callback(gas as nat)(i@)),
            {
                if gas > 0 {
                    self.parse_gas((gas - 1) as usize, i)
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            };

        let ghost spec_callback = Self::specs_callback(gas as nat);
        proof {
            assert forall|input: Seq<u8>| #[trigger]
                spec_callback.2(input) matches Some((n, _v)) ==> 0 <= n <= input.len() by {
                if let Some((n, v)) = spec_callback.2(input) {
                    if gas > 0 {
                        self.safe_parser_by_induction((gas - 1) as nat, input, n, v);
                    }
                }
            }
            assert(spec_callback.safe_inv());
        }

        self.0.parse_body(Ghost(spec_callback), exec_callback, ibuf)
    }
}

impl<const LIMIT: usize, Body, I> Parser<I> for super::Fix<LIMIT, Body> where
    I: InputBuf,
    Body: ParserRecBody<I> + SafeParserRecBody,
    Body::Body: SafeParser,
 {
    type PT = Body::O;

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        self.parse_gas(LIMIT, ibuf)
    }
}

} // verus!
