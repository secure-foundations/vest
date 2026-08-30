use super::spec::*;
use crate::combinators::length::AsLen;
use crate::core::exec::output::*;
use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
        serializer::{ByteLen, ComplianceErrorKind, PreSerializeError, Prepare, Serializer},
        ParseError,
    },
    proof::Productive,
    spec::{Consistency, SafeParser, SpecByteLen, SpecParser, SpecSerializer},
};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;
use OutputBuf;

verus! {

#[cfg(feature = "alloc")]
impl<I, Inner> Parser<I> for super::Star<Inner> where I: InputBuf, Inner: Parser<I> + Productive {
    type PT = Vec<Inner::PT>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.0.productive_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        reveal(<super::Star::<_> as SpecParser>::spec_parse);
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

            reveal(<super::Star::<_> as SpecParser>::spec_parse);

            match self.0.parse(&rest) {
                Ok((n, v)) => {
                    proof {
                        self.0.lemma_productive(rest@);
                        assert(n > 0);
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

#[cfg(feature = "alloc")]
impl<I, A, B> Parser<I> for super::Repeat<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser + Productive + Copy,
    B: Parser<I> + SafeParser + Copy,
 {
    type PT = (Vec<A::PT>, B::PT);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.0.productive_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        crate::combinators::Pair(super::Star(self.0), self.1).parse(ibuf)
    }
}

#[cfg(feature = "alloc")]
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

        let count = self.0.get();
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

// pub assume_specification<T, const N: usize, F: FnMut(usize) -> T>[ core::array::from_fn ](
//     f: F,
// ) -> (out: [T; N])
//     requires
//         forall|i: int| 0 <= i < N ==> #[trigger] call_requires(f, (i as usize,)),
//     ensures
//         forall|i: int| 0 <= i < N ==> call_ensures(f, (i as usize,), #[trigger] out[i]),
// ;
// pub assume_specification<T, const N: usize, F: FnMut(T) -> U, U>[ <[T; N]>::map ](
//     arr: [T; N],
//     f: F,
// ) -> (out: [U; N])
//     requires
//         forall|i: int| 0 <= i < N ==> #[trigger] call_requires(f, (arr[i],)),
//     ensures
//         forall|i: int|
//             #![trigger arr[i]]
//             #![trigger out[i]]
//             0 <= i < N ==> call_ensures(f, (arr[i],), out[i]),
// ;
#[inline(always)]
#[verifier::external_body]
pub fn array_of_none<T, const N: usize>() -> (out: [Option<T>; N])
    ensures
        forall|j: int| 0 <= j < N ==> #[trigger] out@[j] is None,
{
    core::array::from_fn(|_i| None)
}

#[inline(always)]
#[verifier::external_body]
pub fn array_option_unwrap<T: DeepView, const N: usize>(arr: [Option<T>; N]) -> (out: [T; N])
    requires
        forall|j: int| 0 <= j < N ==> #[trigger] arr@[j] is Some,
    ensures
        out.deep_view() == Seq::new(N as nat, |j| arr@[j]->0.deep_view()),
{
    arr.map(Option::<T>::unwrap)
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
            arr[i] = elem;
            rest = rest.skip(n);
            consumed += n;
        }

        let arr = array_option_unwrap(arr);

        Ok((consumed, arr))
    }
}

#[verifier::loop_isolation(false)]
pub fn serialize_slice<Output, Inner, T>(inner: &Inner, values: &[T], obuf: &mut Output) where
    Output: OutputBuf,
    T: DeepView,
    Inner: Serializer<Output, T>,

    requires
        inner.exec_inv(),
        (super::Star(*inner)).consistent(values.deep_view()),
        old(obuf).fits((super::Star(*inner)).byte_len(values.deep_view())),
    ensures
        final(obuf)@ == old(obuf)@ + spec_serialize_seq(inner, values.deep_view()),
        forall|n|
            old(obuf).fits((super::Star(*inner)).byte_len(values.deep_view()) + n)
                <==> #[trigger] final(obuf).fits(n),
        old(obuf).same_destination(final(obuf)),
{
    broadcast use crate::core::exec::output::outbuf_lemmas;

    reveal(<super::Star::<_> as SpecByteLen>::byte_len);
    reveal(<super::Star::<_> as Consistency>::consistent);

    let ghost vs = values.deep_view();
    let ghost star = super::Star(*inner);
    let ghost mut consumed: nat = 0;

    for i in 0..values.len()
        invariant
            consumed + star.byte_len(vs.skip(i as int)) == star.byte_len(vs),
            obuf@ == old(obuf)@ + spec_serialize_seq(inner, vs.take(i as int)),
            forall|n| old(obuf).fits(consumed + n) <==> #[trigger] obuf.fits(n),
            old(obuf).same_destination(obuf),
    {
        proof {
            let elem_len = inner.byte_len(vs[i as int]);
            assert(vs.skip(i as int) == seq![vs[i as int]] + vs.skip(i + 1));
            star.lemma_byte_len_cons(vs[i as int], vs.skip(i + 1));
            assert(vs.take(i + 1) == vs.take(i as int).push(vs[i as int]));
            assert(vs.take(i as int).push(vs[i as int]).drop_last() == vs.take(i as int));
            consumed = consumed + elem_len;
        }
        inner.serialize_into(&values[i], obuf);
    }
}

#[verifier::loop_isolation(false)]
pub fn length_slice<Inner, T>(fmt: &Inner, values: &[T]) -> (len: usize) where
    Inner: ByteLen<T>,
    T: DeepView,

    requires
        fmt.exec_inv(),
        (super::Star(*fmt)).byte_len(values.deep_view()) <= usize::MAX,
    ensures
        len == (super::Star(*fmt)).byte_len(values.deep_view()),
{
    reveal(<super::Star::<_> as SpecByteLen>::byte_len);
    let ghost vs = values.deep_view();
    let ghost star = super::Star(*fmt);

    let mut len = 0usize;
    for i in 0..values.len()
        invariant
            len + star.byte_len(vs.skip(i as int)) == star.byte_len(vs),
    {
        proof {
            assert(vs.skip(i as int) == seq![vs[i as int]] + vs.skip(i + 1));
            star.lemma_byte_len_cons(vs[i as int], vs.skip(i + 1));
        }
        let l = fmt.length(&values[i]);
        len += l;
    }
    len
}

#[verifier::loop_isolation(false)]
pub fn prepare_slice<Inner, T>(fmt: &Inner, values: &[T]) -> (checked: Result<
    usize,
    PreSerializeError,
>) where Inner: Prepare<T>, T: DeepView
    requires
        fmt.exec_inv(),
    ensures
        checked matches Ok(len) ==> {
            &&& (super::Star(*fmt)).consistent(values.deep_view())
            &&& len == (super::Star(*fmt)).byte_len(values.deep_view())
        },
{
    reveal(<super::Star::<_> as Consistency>::consistent);
    reveal(<super::Star::<_> as SpecByteLen>::byte_len);
    let ghost vs = values.deep_view();
    let ghost star = super::Star(*fmt);

    let mut len = 0usize;
    for i in 0..values.len()
        invariant
            forall|j: int| 0 <= j < i ==> fmt.consistent(#[trigger] vs[j]),
            len + star.byte_len(vs.skip(i as int)) == star.byte_len(vs),
    {
        proof {
            assert(vs.skip(i as int) == seq![vs[i as int]] + vs.skip(i + 1));
            star.lemma_byte_len_cons(vs[i as int], vs.skip(i + 1));
        }
        let elem_len = fmt.prepare(&values[i])?;
        match len.checked_add(elem_len) {
            Some(total) => len = total,
            None => return Err(PreSerializeError::length_too_large()),
        }
    }
    Ok(len)
}

impl<Output: OutputBuf, Inner, T> Serializer<Output, [T]> for super::Star<Inner> where
    T: DeepView,
    Inner: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &[T], obuf: &mut Output) {
        reveal(<super::Star::<_> as SpecSerializer>::spec_serialize);
        serialize_slice(&self.0, v, obuf);
    }
}

impl<Inner, T> ByteLen<[T]> for super::Star<Inner> where Inner: ByteLen<T>, T: DeepView {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &[T]) -> (len: usize) {
        length_slice(&self.0, v)
    }
}

impl<Inner, T> Prepare<[T]> for super::Star<Inner> where Inner: Prepare<T>, T: DeepView {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, v: &[T]) -> (checked: Result<usize, PreSerializeError>) {
        prepare_slice(&self.0, v)
    }
}

impl<Output: OutputBuf, A, B, TA, TB> Serializer<Output, (&[TA], TB)> for super::Repeat<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA> + Copy,
    B: Serializer<Output, TB>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn serialize_into(&self, v: &(&[TA], TB), obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        reveal(<super::Star<_> as SpecSerializer>::spec_serialize);

        super::Star(self.0).serialize_into(v.0, obuf);
        assert(obuf.fits(self.1.byte_len(v.deep_view().1)));
        self.1.serialize_into(&v.1, obuf);
    }
}

impl<A, B, TA, TB> ByteLen<(&[TA], TB)> for super::Repeat<A, B> where
    A: ByteLen<TA> + Copy,
    B: ByteLen<TB>,
    TA: DeepView,
    TB: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn length(&self, v: &(&[TA], TB)) -> (len: usize) {
        let la = super::Star(self.0).length(v.0);
        let lb = self.1.length(&v.1);
        la + lb
    }
}

impl<A, B, TA, TB> Prepare<(&[TA], TB)> for super::Repeat<A, B> where
    A: Prepare<TA> + Copy,
    B: Prepare<TB>,
    TA: DeepView,
    TB: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn prepare(&self, v: &(&[TA], TB)) -> (checked: Result<usize, PreSerializeError>) {
        let la = super::Star(self.0).prepare(v.0)?;
        let lb = self.1.prepare(&v.1)?;
        match la.checked_add(lb) {
            Some(total) => Ok(total),
            None => Err(PreSerializeError::length_too_large()),
        }
    }
}

impl<Output: OutputBuf, Inner, N, T> Serializer<Output, [T]> for super::RepeatN<Inner, N> where
    T: DeepView,
    Inner: Serializer<Output, T>,
    N: AsLen,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn serialize_into(&self, v: &[T], obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        serialize_slice(&self.1, v, obuf);
    }
}

impl<Inner, N, T> ByteLen<[T]> for super::RepeatN<Inner, N> where
    Inner: ByteLen<T>,
    T: DeepView,
    N: AsLen,
 {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn length(&self, v: &[T]) -> (len: usize) {
        length_slice(&self.1, v)
    }
}

impl<Inner, N, T> Prepare<[T]> for super::RepeatN<Inner, N> where
    Inner: Prepare<T>,
    T: DeepView,
    N: AsLen,
 {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn prepare(&self, v: &[T]) -> (checked: Result<usize, PreSerializeError>) {
        if v.len() == self.0.get() {
            prepare_slice(&self.1, v)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::LengthInconsistent))
        }
    }
}

impl<Output: OutputBuf, Inner, T, const N: usize> Serializer<Output, [T; N]> for super::Array<
    N,
    Inner,
> where T: DeepView, Inner: Serializer<Output, T> {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &[T; N], obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        serialize_slice(&self.0, v, obuf);
    }
}

impl<Inner, T, const N: usize> ByteLen<[T; N]> for super::Array<N, Inner> where
    Inner: ByteLen<T>,
    T: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &[T; N]) -> (len: usize) {
        length_slice(&self.0, v.as_slice())
    }
}

impl<Inner, T, const N: usize> Prepare<[T; N]> for super::Array<N, Inner> where
    Inner: Prepare<T>,
    T: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, v: &[T; N]) -> (checked: Result<usize, PreSerializeError>) {
        prepare_slice(&self.0, v.as_slice())
    }
}

} // verus!
