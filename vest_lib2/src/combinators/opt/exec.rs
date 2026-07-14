use crate::core::exec::output::*;
use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
        serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    },
    spec::{SafeParser, SpecParser},
};
use vstd::prelude::*;
use OutputBuf;

verus! {

impl<I, A> Parser<I> for super::Opt<A> where I: View<V = Seq<u8>>, A: Parser<I> {
    type PT = Option<A::PT>;

    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        match self.0.parse(ibuf) {
            Ok((n, v)) => Ok((n, Some(v))),
            Err(_) => {
                let none = None;
                assert(self.spec_parse(ibuf@) == Some((0int, none.deep_view())));
                Ok((0, none))
            },
        }
    }
}

impl<Output: OutputBuf + ?Sized, A, T> Serializer<Output, Option<T>> for super::Opt<A> where
    T: DeepView,
    A: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &Option<T>, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        match v {
            Some(vv) => self.0.serialize_into(vv, obuf),
            None => {},
        }
    }
}

impl<A, T> ByteLen<Option<T>> for super::Opt<A> where T: DeepView, A: ByteLen<T> {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &Option<T>) -> (len: usize) {
        match v {
            Some(vv) => self.0.length(vv),
            None => 0,
        }
    }
}

impl<A, T> Prepare<Option<T>> for super::Opt<A> where T: DeepView, A: Prepare<T> {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, v: &Option<T>) -> (checked: Result<usize, PreSerializeError>) {
        match v {
            Some(vv) => self.0.prepare(vv),
            None => Ok(0),
        }
    }
}

impl<I, A, B> Parser<I> for super::Optional<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
 {
    type PT = (Option<A::PT>, B::PT);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        crate::combinators::Pair(super::Opt(&self.0), &self.1).parse(ibuf)
    }
}

impl<Output: OutputBuf + ?Sized, A, B, TA, TB> Serializer<
    Output,
    (Option<TA>, TB),
> for super::Optional<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn serialize_into(&self, v: &(Option<TA>, TB), obuf: &mut Output) {
        crate::combinators::Pair(super::Opt(&self.0), &self.1).serialize_into(v, obuf);
    }
}

impl<A, B, TA, TB> ByteLen<(Option<TA>, TB)> for super::Optional<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: ByteLen<TA>,
    B: ByteLen<TB>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn length(&self, v: &(Option<TA>, TB)) -> (len: usize) {
        crate::combinators::Pair(super::Opt(&self.0), &self.1).length(v)
    }
}

impl<A, B, TA, TB> Prepare<(Option<TA>, TB)> for super::Optional<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn prepare(&self, v: &(Option<TA>, TB)) -> Result<usize, PreSerializeError> {
        crate::combinators::Pair(super::Opt(&self.0), &self.1).prepare(v)
    }
}

} // verus!
