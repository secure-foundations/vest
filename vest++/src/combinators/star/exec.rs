use super::spec::*;
use crate::combinators::length::AsLen;
use crate::combinators::preceded;
use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
        serializer::Serializer,
        ParseError,
    },
    spec::{SafeParser, SpecParser, SpecSerializer},
};
use vstd::prelude::*;

verus! {

impl<I, Inner> Parser<I> for super::Star<Inner> where I: InputBuf, Inner: Parser<I> + SafeParser {
    type PT = Vec<Inner::PT>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.inner.exec_inv()
        &&& self.inner.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

        let total_len = ibuf.len();
        let mut consumed: usize = 0;
        let mut remaining = total_len;
        let mut rest = ibuf.skip(0);
        let mut values = Vec::new();

        while remaining > 0
            invariant
                self.exec_inv(),
                consumed + remaining == total_len,
                remaining == rest@.len(),
                ({
                    let prefix = values.deep_view();
                    let (n, suffix) = self.parse_rec(rest@);
                    self.parse_rec(ibuf@) == (consumed + n, prefix + suffix)
                }),
            decreases remaining,
        {
            broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

            match self.inner.parse(&rest) {
                Ok((n, v)) => {
                    // TODO: can require productive parsers to guarantee progress (and eliminate this run-time check)
                    if n == 0 {
                        return Ok((consumed, values));
                    }
                    values.push(v);
                    rest = rest.skip(n);
                    consumed += n;
                    remaining -= n;
                },
                Err(_) => return Ok((consumed, values)),
            }
        }
        Ok((consumed, values))
    }
}

impl<I, Inner, N> Parser<I> for super::RepeatN<Inner, N> where
    I: InputBuf,
    Inner: Parser<I> + SafeParser,
    N: AsLen,
 {
    type PT = Vec<Inner::PT>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

        let count = self.0.as_usize();
        let _total_len = ibuf.len();
        let mut consumed: usize = 0;
        let mut rest = ibuf.skip(0);
        let mut values = Vec::new();

        for i in 0..count
            invariant
                self.exec_inv(),
                count as nat == self.0.as_nat(),
                consumed + rest@.len() == _total_len,
                ({
                    let prefix = values.deep_view();
                    let parsed = self.parse_n_rec(count as nat, ibuf@);
                    match self.parse_n_rec((count - i) as nat, rest@) {
                        Some((n, suffix)) => parsed == Some((consumed + n, prefix + suffix)),
                        None => parsed is None,
                    }
                }),
        {
            broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

            let (n, v) = self.1.parse(&rest)?;
            values.push(v);
            rest = rest.skip(n);
            consumed += n;
        }
        Ok((consumed, values))
    }
}

pub fn serialize_slice<Inner, InnerST>(inner: &Inner, values: &[InnerST], obuf: &mut Vec<u8>) where
    Inner: Serializer<InnerST>,
    InnerST: DeepView<V = Inner::SVal> + Copy,

    requires
        inner.exec_inv(),
    ensures
        final(obuf)@ == old(obuf)@ + spec_serialize_seq(inner, values.deep_view()),
{
    let ghost old_obuf = obuf@;

    for i in 0..values.len()
        invariant
            inner.exec_inv(),
            obuf@ == old_obuf + spec_serialize_seq(inner, values.deep_view().take(i as int)),
    {
        proof {
            let vs = values.deep_view();
            assert(vs.take(i + 1) == vs.take(i as int).push(vs[i as int]));
            assert(vs.take(i as int).push(vs[i as int]).drop_last() == vs.take(i as int));
        }
        inner.ex_serialize(values[i], obuf);
    }
}

impl<Inner, InnerST> Serializer<&[InnerST]> for super::Star<Inner> where
    Inner: Serializer<InnerST>,
    InnerST: DeepView<V = Inner::SVal> + Copy,
 {
    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn ex_serialize(&self, v: &[InnerST], obuf: &mut Vec<u8>) {
        serialize_slice(&self.inner, v, obuf);
    }
}

impl<Inner, N, InnerST> Serializer<&[InnerST]> for super::RepeatN<Inner, N> where
    Inner: Serializer<InnerST>,
    InnerST: DeepView<V = Inner::SVal> + Copy,
    N: AsLen,
 {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn ex_serialize(&self, v: &[InnerST], obuf: &mut Vec<u8>) {
        serialize_slice(&self.1, v, obuf);
    }
}

} // verus!
