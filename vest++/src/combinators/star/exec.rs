use super::spec::*;
use crate::combinators::length::AsLen;
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

        for _i in 0..count
            invariant
                self.exec_inv(),
                count as nat == self.0.as_nat(),
                consumed + rest@.len() == _total_len,
                ({
                    let prefix = values.deep_view();
                    let parsed = self.parse_n_rec(count as nat, ibuf@);
                    match self.parse_n_rec((count - _i) as nat, rest@) {
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

pub assume_specification<T, const N: usize, F: FnMut(usize) -> T>[ core::array::from_fn ](
    f: F,
) -> (out: [T; N])
    requires
        forall|i: int| 0 <= i < N ==> #[trigger] call_requires(f, (i as usize,)),
    ensures
        forall|i: int| 0 <= i < N ==> call_ensures(f, (i as usize,), #[trigger] out[i]),
;

pub assume_specification<T, const N: usize, F: FnMut(T) -> U, U>[ <[T; N]>::map ](
    arr: [T; N],
    f: F,
) -> (out: [U; N])
    requires
        forall|i: int| 0 <= i < N ==> #[trigger] call_requires(f, (arr[i],)),
    ensures
        forall|i: int|
            #![trigger arr[i]]
            #![trigger out[i]]
            0 <= i < N ==> call_ensures(f, (arr[i],), out[i]),
;

#[inline(always)]
pub fn array_of_none<T, const N: usize>() -> (out: [Option<T>; N])
    ensures
        forall|j: int| 0 <= j < N ==> #[trigger] out@[j] is None,
{
    broadcast use vstd::array::lemma_array_index;

    let out = core::array::from_fn(
        |_i| -> (o: Option<T>)
            ensures
                o is None,
            { None },
    );
    out
}

#[inline(always)]
pub fn array_option_unwrap<T: DeepView, const N: usize>(arr: [Option<T>; N]) -> (out: [T; N])
    requires
        forall|j: int| 0 <= j < N ==> #[trigger] arr@[j] is Some,
    ensures
        out.deep_view() == Seq::new(N as nat, |j| arr@[j]->0.deep_view()),
{
    let out = arr.map(
        |opt| -> (o: T)
            requires
                opt is Some,
            ensures
                o == opt->0,
            { opt.unwrap() },
    );
    out
}

impl<I, Inner, const N: usize> Parser<I> for super::Array<N, Inner> where
    I: InputBuf,
    Inner: Parser<I> + SafeParser,
 {
    type PT = [Inner::PT; N];

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

        let mut consumed: usize = 0;
        let _total_len = ibuf.len();
        let mut rest = ibuf.skip(0);
        let mut arr: [Option<Inner::PT>; N] = array_of_none();

        for i in 0..N
            invariant
                self.exec_inv(),
                consumed + rest@.len() == _total_len,
                forall|j: int| 0 <= j < i ==> #[trigger] arr@[j] is Some,
                forall|j: int| i <= j < N ==> #[trigger] arr@[j] is None,
                ({
                    let prefix = Seq::new(i as nat, |j| arr@[j]->0.deep_view());
                    match super::RepeatN(N, self.0).parse_n_rec((N - i) as nat, rest@) {
                        Some((n, suffix)) => self.spec_parse(ibuf@) == Some(
                            (consumed + n, prefix + suffix),
                        ),
                        None => self.spec_parse(ibuf@) is None,
                    }
                }),
        {
            broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

            let (n, v) = self.0.parse(&rest)?;
            let elem = Some(v);
            arr.set(i, elem);
            rest = rest.skip(n);
            consumed += n;
        }

        let arr = array_option_unwrap(arr);

        Ok((consumed, arr))
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

impl<Inner, InnerST, const N: usize> Serializer<&[InnerST; N]> for super::Array<N, Inner> where
    Inner: Serializer<InnerST>,
    InnerST: DeepView<V = Inner::SVal> + Copy,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn ex_serialize(&self, v: &[InnerST; N], obuf: &mut Vec<u8>) {
        let slice = v.as_slice();
        proof {
            assert(slice.deep_view() == v.deep_view());
        }
        serialize_slice(&self.0, slice, obuf);
    }
}

} // verus!
