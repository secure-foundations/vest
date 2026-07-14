use crate::combinators::{Eof, Opt, Optional, Pair, Repeat, Star};
use crate::core::exec::output::*;
use crate::core::exec::{
    input::InputBuf,
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::proof::Productive;
use crate::core::spec::SafeParser;
use crate::core::spec::{Consistency, SpecByteLen};
use vstd::prelude::*;
use OutputBuf;

verus! {

impl<I: InputBuf> Parser<I> for super::Tail {
    type PT = I;

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let len = ibuf.len();
        let tail = ibuf.take(len);
        proof {
            assert(tail.deep_view() == ibuf@);
        }
        Ok((len, tail))
    }
}

impl<Output: OutputBuf + ?Sized> Serializer<Output, [u8]> for super::Tail {
    fn serialize_into(&self, v: &[u8], obuf: &mut Output) {
        obuf.write_bytes(v);
    }
}

impl ByteLen<[u8]> for super::Tail {
    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn length(&self, v: &[u8]) -> (len: usize) {
        v.len()
    }
}

impl Prepare<[u8]> for super::Tail {
    fn prepare(&self, v: &[u8]) -> (checked: Result<usize, PreSerializeError>) {
        Ok(v.len())
    }
}

impl<I: InputBuf> Parser<I> for super::Eof {
    type PT = ();

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let len = ibuf.len();
        if len == 0 {
            Ok((0, ()))
        } else {
            Err(ParseError::expecting_eof())
        }
    }
}

impl<Output: OutputBuf + ?Sized> Serializer<Output, ()> for super::Eof {
    fn serialize_into(&self, _v: &(), _obuf: &mut Output) {
        broadcast use OutputBuf::lemma_same_destination_reflexive;

    }
}

impl ByteLen<()> for super::Eof {
    fn length(&self, _v: &()) -> (len: usize) {
        0
    }
}

impl Prepare<()> for super::Eof {
    fn prepare(&self, _v: &()) -> (checked: Result<usize, PreSerializeError>) {
        Ok(0)
    }
}

impl<A, B, AVal, BVal> ByteLen<(AVal, BVal)> for super::PairRev<A, B> where
    AVal: DeepView,
    BVal: DeepView,
    A: ByteLen<AVal>,
    B: ByteLen<BVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn length(&self, v: &(AVal, BVal)) -> (len: usize) {
        let la = self.1.length(&v.0);
        let lb = self.0.length(&v.1);
        proof {
            assert((la + lb) as nat == la as nat + lb as nat);
        }
        la + lb
    }
}

impl<A, B, AVal, BVal> Prepare<(AVal, BVal)> for super::PairRev<A, B> where
    AVal: DeepView,
    BVal: DeepView,
    A: Prepare<AVal>,
    B: Prepare<BVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn prepare(&self, v: &(AVal, BVal)) -> Result<usize, PreSerializeError> {
        let la = self.1.prepare(&v.0)?;
        let lb = self.0.prepare(&v.1)?;
        if let Some(total) = la.checked_add(lb) {
            Ok(total)
        } else {
            Err(PreSerializeError::length_too_large())
        }
    }
}

impl<I, A> Parser<I> for super::RepeatTillEnd<A> where
    I: InputBuf,
    A: Parser<I> + SafeParser + Productive + Copy,
 {
    type PT = Vec<A::PT>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.0.productive_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        let (n, (r, _)) = Repeat(self.0, super::Eof).parse(ibuf)?;
        Ok((n, r))
    }
}

impl<I, A> Parser<I> for super::OptionalEnd<A> where I: InputBuf, A: Parser<I> + SafeParser {
    type PT = Option<A::PT>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        let (n, (r, _)) = Optional(&self.0, super::Eof).parse(ibuf)?;
        Ok((n, r))
    }
}

impl<Output: OutputBuf + ?Sized, A, T> Serializer<Output, &[T]> for super::RepeatTillEnd<A> where
    A: Serializer<Output, T> + Copy,
    T: DeepView + Copy,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &&[T], obuf: &mut Output) {
        Star(self.0).serialize_into(v, obuf);
    }
}

impl<A, T> ByteLen<&[T]> for super::RepeatTillEnd<A> where A: ByteLen<T> + Copy, T: DeepView {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &&[T]) -> (len: usize) {
        Star(self.0).length(v)
    }
}

impl<A, T> Prepare<&[T]> for super::RepeatTillEnd<A> where A: Prepare<T> + Copy, T: DeepView {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, v: &&[T]) -> Result<usize, PreSerializeError> {
        Star(self.0).prepare(v)
    }
}

impl<Output: OutputBuf + ?Sized, A, T> Serializer<Output, Option<T>> for super::OptionalEnd<
    A,
> where A: Serializer<Output, T>, T: DeepView + Copy {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &Option<T>, obuf: &mut Output) {
        Opt(&self.0).serialize_into(v, obuf);
    }
}

impl<A, AST> ByteLen<Option<AST>> for super::OptionalEnd<A> where A: ByteLen<AST>, AST: DeepView {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &Option<AST>) -> (len: usize) {
        Opt(&self.0).length(v)
    }
}

impl<A, AST> Prepare<Option<AST>> for super::OptionalEnd<A> where A: Prepare<AST>, AST: DeepView {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, v: &Option<AST>) -> Result<usize, PreSerializeError> {
        Opt(&self.0).prepare(v)
    }
}

} // verus!
