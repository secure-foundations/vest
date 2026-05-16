use crate::combinators::AsLen;
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, Compliance, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::spec::SpecParser;
use vstd::prelude::*;

verus! {

impl<const N: usize, I: InputBuf> Parser<I> for super::Fixed<N> {
    type PT = I;

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        if ibuf.len() < N {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((N, ibuf.take(N)))
        }
    }
}

impl<'s, const N: usize> Serializer<&'s [u8]> for super::Fixed<N> {
    fn ex_serialize(&self, v: &'s [u8], obuf: &mut Vec<u8>) {
        obuf.extend_from_slice(v);
    }
}

impl<'s, const N: usize> Compliance<&'s [u8]> for super::Fixed<N> {
    fn check_compliance(&self, v: &'s [u8]) -> (yes: bool) {
        v.len() == N
    }
}

impl<'s, const N: usize> ByteLen<&'s [u8]> for super::Fixed<N> {
    fn length(&self, v: &'s [u8]) -> (len: usize) {
        v.len()
    }
}

impl<'s, const N: usize> Prepare<&'s [u8]> for super::Fixed<N> {
    fn prepare(&self, v: &'s [u8]) -> (checked: Result<usize, PreSerializeError>) {
        if v.len() == N {
            Ok(N)
        } else {
            Err(PreSerializeError::NotCompliant("Fixed"))
        }
    }
}

impl<Len: AsLen, I: InputBuf> Parser<I> for super::Varied<Len> {
    type PT = I;

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let len = self.0.get();
        if ibuf.len() < len {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((len, ibuf.take(len)))
        }
    }
}

impl<'s, Len: AsLen> Serializer<&'s [u8]> for super::Varied<Len> {
    fn ex_serialize(&self, v: &'s [u8], obuf: &mut Vec<u8>) {
        obuf.extend_from_slice(v);
    }
}

impl<'s, Len: AsLen> Compliance<&'s [u8]> for super::Varied<Len> {
    fn check_compliance(&self, v: &'s [u8]) -> (yes: bool) {
        v.len() == self.0.get()
    }
}

impl<'s, Len: AsLen> ByteLen<&'s [u8]> for super::Varied<Len> {
    fn length(&self, v: &'s [u8]) -> (len: usize) {
        v.len()
    }
}

impl<'s, Len: AsLen> Prepare<&'s [u8]> for super::Varied<Len> {
    fn prepare(&self, v: &'s [u8]) -> (checked: Result<usize, PreSerializeError>) {
        if v.len() == self.0.get() {
            Ok(v.len())
        } else {
            Err(PreSerializeError::NotCompliant("Varied"))
        }
    }
}

impl<I, Len, Inner> Parser<I> for super::ExactLen<Inner, Len> where
    I: InputBuf,
    Len: AsLen,
    Inner: Parser<I>,
 {
    type PT = Inner::PT;

    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        super::AndThen(super::Varied(self.0), &self.1).parse(ibuf)
    }
}

impl<I: InputBuf, A, Then> Parser<I> for super::AndThen<A, Then> where
    A: Parser<I, PT = I, PVal = Seq<u8>>,
    Then: Parser<I>,
 {
    type PT = Then::PT;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        assert(self.exec_inv());

        let (len_a, chunk) = self.0.parse(ibuf)?;
        proof {
            chunk.deep_view_eq_view();
        }
        let (len_b, v) = self.1.parse(&chunk)?;
        if len_b == len_a {
            Ok((len_b, v))
        } else {
            Err(ParseError::length_mismatch())
        }
    }
}

impl<Len, Inner, InnerST> Serializer<InnerST> for super::ExactLen<Inner, Len> where
    Len: AsLen,
    Inner: Serializer<InnerST>,
    InnerST: DeepView<V = Inner::SVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn ex_serialize(&self, v: InnerST, obuf: &mut Vec<u8>) {
        self.1.ex_serialize(v, obuf);
    }
}

// impl<Len, Inner, InnerST> Compliance<InnerST> for super::ExactLen<Inner, Len> where
//     Len: AsLen,
//     InnerST: DeepView + Copy,
//     Inner: Compliance<InnerST> + ByteLen<InnerST>,
//  {
//     fn check_compliance(&self, v: InnerST) -> (yes: bool) {
//         self.1.check_compliance(v) && self.1.length(v) == self.0.get()
//     }
// }
impl<Len, Inner, InnerST> ByteLen<InnerST> for super::ExactLen<Inner, Len> where
    Len: AsLen,
    InnerST: DeepView,
    Inner: ByteLen<InnerST>,
 {
    fn length(&self, v: InnerST) -> (len: usize) {
        self.1.length(v)
    }
}

impl<Len, Inner, InnerST> Prepare<InnerST> for super::ExactLen<Inner, Len> where
    Len: AsLen,
    InnerST: DeepView,
    Inner: Prepare<InnerST>,
 {
    fn prepare(&self, v: InnerST) -> (checked: Result<usize, PreSerializeError>) {
        let len = self.1.prepare(v)?;
        if len == self.0.get() {
            Ok(len)
        } else {
            Err(PreSerializeError::NotCompliant("ExactLen"))
        }
    }
}

impl<A, Then, ThenST> ByteLen<ThenST> for super::AndThen<A, Then> where
    ThenST: DeepView,
    Then: ByteLen<ThenST>,
 {
    fn length(&self, v: ThenST) -> (len: usize) {
        self.1.length(v)
    }
}

} // verus!
