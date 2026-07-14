use super::{ParamRecSpecs, SafeParserRecBody, SpecRecBody};
use crate::core::exec::output::*;
use crate::core::exec::parser::*;
use crate::core::exec::serializer::{
    ByteLen, ComplianceErrorKind, PreSerializeError, Prepare, Serializer,
};
use crate::core::exec::{input::InputBuf, output::OutputBuf, ParseError};
use crate::core::spec::{
    Consistency, GoodSerializer, SafeParser, SpecByteLen, SpecParser, SpecSerializer,
};
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
            parse_matches_spec(r, self.spec_body(param.deep_view(), spec_rec).spec_parse(ibuf@)),
    ;
}

/// Executable serialization for one recursive unfolding.
pub trait SerializerRecBody<Output, T>: SpecRecBody where
    Output: OutputBuf + ?Sized,
    T: DeepView<V = Self::T>,
 {
    type EP: DeepView<V = Self::Param>;

    /// Execute one recursive unfolding, using `exec_rec` for all recursive positions in the body.
    ///
    /// `spec_rec` is the ghost/spec callback bundle corresponding to `exec_rec`.
    fn serialize_body<Exec>(
        &self,
        param: &Self::EP,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &T,
        obuf: &mut Output,
    ) where Exec: Fn(&Self::EP, &T, &mut Output)
        requires
            self.spec_body(param.deep_view(), spec_rec).consistent(v.deep_view()),
            old(obuf).wf(),
            fit(
                old(obuf).remaining(),
                self.spec_body(param.deep_view(), spec_rec).byte_len(v.deep_view()),
            ),
            forall|pp: &Self::EP, vv: &T, out: &mut Output|
                {
                    &&& spec_rec(pp.deep_view()).0(vv.deep_view())
                    &&& out.wf()
                    &&& fit(out.remaining(), spec_rec(pp.deep_view()).1(vv.deep_view()))
                } ==> call_requires(exec_rec, (pp, vv, out)),
            forall|pp: &Self::EP, vv: &T, out: &mut Output|
                call_ensures(exec_rec, (pp, vv, out), ()) ==> {
                    &&& final(out).wf()
                    &&& final(out)@ == out@ + spec_rec(pp.deep_view()).3(vv.deep_view())
                    &&& final(out).remaining() == consume(
                        out.remaining(),
                        spec_rec(pp.deep_view()).1(vv.deep_view()),
                    )
                    &&& final(out).final_target() == out.final_target()
                },
        ensures
            final(obuf).wf(),
            final(obuf)@ == old(obuf)@ + self.spec_body(param.deep_view(), spec_rec).spec_serialize(
                v.deep_view(),
            ),
            final(obuf).remaining() == consume(
                old(obuf).remaining(),
                self.spec_body(param.deep_view(), spec_rec).byte_len(v.deep_view()),
            ),
            final(obuf).final_target() == old(obuf).final_target(),
    ;
}

/// Executable pre-serialization analysis for one recursive unfolding.
pub trait PrepareRecBody<T>: SpecRecBody where T: DeepView<V = Self::T> {
    type EP: DeepView<V = Self::Param>;

    /// Execute one recursive unfolding, using `exec_rec` for all recursive positions in the body.
    ///
    /// `spec_rec` is the ghost/spec callback bundle corresponding to `exec_rec`.
    fn prepare_body<Exec>(
        &self,
        param: &Self::EP,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &T,
    ) -> (checked: Result<usize, PreSerializeError>) where
        Exec: Fn(&Self::EP, &T) -> Result<usize, PreSerializeError>,

        requires
            forall|pp: &Self::EP, vv: &T| call_requires(exec_rec, (pp, vv)),
            forall|pp: &Self::EP, vv: &T, rr: Result<usize, PreSerializeError>|
                call_ensures(exec_rec, (pp, vv), rr) ==> (rr matches Ok(len) ==> {
                    &&& spec_rec(pp.deep_view()).0(vv.deep_view())
                    &&& len == spec_rec(pp.deep_view()).1(vv.deep_view())
                }),
        ensures
            checked matches Ok(len) ==> {
                &&& self.spec_body(param.deep_view(), spec_rec).consistent(v.deep_view())
                &&& len == self.spec_body(param.deep_view(), spec_rec).byte_len(v.deep_view())
            },
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
            parse_matches_spec(
                r,
                Self::spec_parse_gas(&self.0, gas as nat, param.deep_view(), ibuf@),
            ),
        decreases gas,
    {
        let ghost body = self.0;
        let exec_callback = |pp: &Param, i: &I| -> (rr: PResult<Body::O>)
            ensures
                parse_matches_spec(
                    rr,
                    Self::spec_parse_callback(&body, gas as nat, pp.deep_view())(i@),
                ),
            {
                if gas > 0 {
                    self.parse_gas((gas - 1) as usize, pp, i)
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            };

        let ghost spec_callback = Self::specs_callback(&body, gas as nat);
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

    fn serialize_gas<Output, T>(&self, gas: usize, param: &Param, v: &T, obuf: &mut Output) where
        Output: OutputBuf + ?Sized,
        T: DeepView<V = Body::T>,
        Param: DeepView<V = Body::Param>,
        Body: SerializerRecBody<Output, T, EP = Param>,

        requires
            Self::consistent_gas(&self.0, gas as nat, param.deep_view(), v.deep_view()),
            old(obuf).wf(),
            fit(
                old(obuf).remaining(),
                Self::byte_len_gas(&self.0, gas as nat, param.deep_view(), v.deep_view()),
            ),
        ensures
            final(obuf).wf(),
            final(obuf)@ == old(obuf)@ + Self::spec_serialize_gas(
                &self.0,
                gas as nat,
                param.deep_view(),
                v.deep_view(),
            ),
            final(obuf).remaining() == consume(
                old(obuf).remaining(),
                Self::byte_len_gas(&self.0, gas as nat, param.deep_view(), v.deep_view()),
            ),
            final(obuf).final_target() == old(obuf).final_target(),
        decreases gas,
    {
        let ghost body = self.0;
        let exec_callback = |pp: &Param, vv: &T, oo: &mut Output| -> ()
            requires
                Self::consistent_callback(&body, gas as nat, pp.deep_view())(vv.deep_view()),
                old(oo).wf(),
                fit(
                    old(oo).remaining(),
                    Self::byte_len_callback(&body, gas as nat, pp.deep_view())(vv.deep_view()),
                ),
            ensures
                final(oo).wf(),
                final(oo)@ == old(oo)@ + Self::spec_serialize_callback(
                    &body,
                    gas as nat,
                    pp.deep_view(),
                )(vv.deep_view()),
                final(oo).remaining() == consume(
                    old(oo).remaining(),
                    Self::byte_len_callback(&body, gas as nat, pp.deep_view())(vv.deep_view()),
                ),
                final(oo).final_target() == old(oo).final_target(),
            {
                if gas > 0 {
                    self.serialize_gas((gas - 1) as usize, pp, vv, oo);
                }
            };

        let ghost spec_callback = Self::specs_callback(&body, gas as nat);
        self.0.serialize_body(param, Ghost(spec_callback), exec_callback, v, obuf)
    }

    fn prepare_gas<T>(&self, gas: usize, param: &Param, v: &T) -> (checked: Result<
        usize,
        PreSerializeError,
    >) where
        T: DeepView<V = Body::T>,
        Param: DeepView<V = Body::Param>,
        Body: PrepareRecBody<T, EP = Param>,

        ensures
            checked matches Ok(len) ==> {
                &&& Self::consistent_gas(&self.0, gas as nat, param.deep_view(), v.deep_view())
                &&& len == Self::byte_len_gas(&self.0, gas as nat, param.deep_view(), v.deep_view())
            },
        decreases gas,
    {
        let ghost body = self.0;
        let exec_callback = |pp: &Param, vv: &T| -> (rr: Result<usize, PreSerializeError>)
            ensures
                rr matches Ok(len) ==> {
                    &&& Self::consistent_callback(&body, gas as nat, pp.deep_view())(vv.deep_view())
                    &&& len == Self::byte_len_callback(&body, gas as nat, pp.deep_view())(
                        vv.deep_view(),
                    )
                },
            {
                if gas > 0 {
                    self.prepare_gas((gas - 1) as usize, pp, vv)
                } else {
                    Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    )
                }
            };

        let ghost spec_callback = Self::specs_callback(&body, gas as nat);
        self.0.prepare_body(param, Ghost(spec_callback), exec_callback, v)
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

impl<Output: OutputBuf + ?Sized, T, const LIMIT: usize, Body, Param> Serializer<
    Output,
    T,
> for super::FixWith<LIMIT, Body, Param> where
    T: DeepView<V = Body::T>,
    Param: DeepView<V = Body::Param>,
    Body: SerializerRecBody<Output, T, EP = Param>,
 {
    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        self.serialize_gas(LIMIT, &self.1, v, obuf)
    }
}

impl<T, const LIMIT: usize, Body, Param> Prepare<T> for super::FixWith<LIMIT, Body, Param> where
    T: DeepView<V = Body::T>,
    Param: DeepView<V = Body::Param>,
    Body: PrepareRecBody<T, EP = Param>,
 {
    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        self.prepare_gas(LIMIT, &self.1, v)
    }
}

} // verus!
