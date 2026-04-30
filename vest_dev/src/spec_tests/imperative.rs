use crate::combinators::mapped::spec::{SpecMap, SpecMapper};
use crate::combinators::refined::exec::*;
use crate::combinators::*;
use crate::core::exec::fns::{FnPred, MapRef, Pred};
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::parser::{PResult, Parser};
use crate::core::exec::ParseError;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

struct MyFmtCont;

impl SpecMap for MyFmtCont {
    type Input = u8;

    type Output = Varied;

    open spec fn spec_map(&self, i: Self::Input) -> Self::Output {
        Varied(i)
    }
}

impl MapRef<u8> for MyFmtCont {
    type O = Varied;

    fn map(&self, i: &u8) -> Self::O {
        Varied(*i)
    }
}

fn test_bind(ibuf: &[u8]) -> PResult<()> {
    #[verusfmt::skip]
    let ghost tx_segwit_fmt =
        WithPrefixTag(U8, 1u8,
        Bind(U8, |txin_count: u8|
        Pair(Varied(txin_count),
        Bind(U8, |txout_count: u8|
        Pair(Varied(txout_count),
        Pair(Varied(txin_count),
        U32Le))))));

    let ghost _ = tx_segwit_fmt.spec_parse(ibuf@);

    let tx_segwit_fmt = Bind(U8, MyFmtCont);
    // Bind(
    //     U8,
    //     (
    //         |len: &u8| -> (o: Varied)
    //             ensures
    //                 o == Varied(*len),
    //             { Varied(*len) },
    //         Ghost(|len: u8| Varied(len)),
    //     ),
    // );

    let ghost _ = tx_segwit_fmt.spec_parse(ibuf@);
    assert(Parser::exec_inv(&tx_segwit_fmt));
    let (_n, _v) = tx_segwit_fmt.parse(&ibuf)?;

    Err(ParseError::expecting_eof())
}

struct TxSegwitFmt;

impl SpecParser for TxSegwitFmt {
    type PVal = (u8, (Seq<u8>, (u8, (Seq<u8>, (Seq<u8>, u8)))));

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        #[verusfmt::skip]
        WithPrefixTag(U8, 1u8,
        Bind(U8, |txin_count: u8|
        Pair(Varied(txin_count),
        Bind(Refined(U8, |x: u8| x == txin_count), |txout_count: u8|
        Pair(Varied(txout_count),
        Pair(Varied(txin_count),
        U8)))))).spec_parse(ibuf)
    }
}

impl<'i> Parser<&'i [u8]> for TxSegwitFmt {
    type PT = (u8, (&'i [u8], (u8, (&'i [u8], (&'i [u8], u8)))));

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let (n1, _) = Const(U8, 1u8).parse(ibuf)?;
        let (n2, txin_cnt) = U8.parse(&ibuf.skip(n1))?;
        let (n3, txin) = Varied(txin_cnt).parse(&ibuf.skip(n1 + n2))?;
        let (n4, txout_cnt) = U8.parse(&ibuf.skip(n1 + n2 + n3))?;
        if txout_cnt != txin_cnt {
            return Err(ParseError::predicate_failed());
        }
        let (n5, txout) = Varied(txout_cnt).parse(&ibuf.skip(n1 + n2 + n3 + n4))?;
        let (n6, witness) = Varied(txin_cnt).parse(&ibuf.skip(n1 + n2 + n3 + n4 + n5))?;
        let (n7, locktime) = U8.parse(&ibuf.skip(n1 + n2 + n3 + n4 + n5 + n6))?;
        let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7;
        let final_v = (txin_cnt, (txin, (txout_cnt, (txout, (witness, locktime)))));
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

struct TLV;

type TLVMsgSpec = Sum<u8, Sum<Seq<u8>, Sum<(u8, Seq<u8>), (u8, Seq<u8>)>>>;

type TLVMsg<'i> = Sum<u8, Sum<&'i [u8], Sum<(u8, &'i [u8]), (u8, &'i [u8])>>>;

type PayloadFmt = Choice<
    Cond<U8>,
    Choice<Cond<Fixed<10>>, Choice<Cond<Pair<U8, Tail>>, Cond<Pair<U8, Tail>>>>,
>;

type TLVFmt = Implicit<
    U8,
    KVFormat<u8, TLVMsgSpec, Implicit<U8, KVFormat<u8, TLVMsgSpec, ExactLen<PayloadFmt>>>>,
>;

#[verifier::allow_in_spec]
pub fn payload_fmt(tag: u8) -> PayloadFmt
    returns
        Choice(
            Cond(tag == 1, U8),
            Choice(
                Cond(tag == 2, Fixed::<10>),
                Choice(Cond(tag == 3, Pair(U8, Tail)), Cond(tag == 4, Pair(U8, Tail))),
            ),
        ),
{
    Choice(
        Cond(tag == 1, U8),
        Choice(
            Cond(tag == 2, Fixed::<10>),
            Choice(Cond(tag == 3, Pair(U8, Tail)), Cond(tag == 4, Pair(U8, Tail))),
        ),
    )
}

pub open spec fn tlv_fmt() -> TLVFmt {
    let recover_tag = |msg: TLVMsgSpec| -> u8
        {
            match msg {
                Sum::Inl(_) => 1,
                Sum::Inr(Sum::Inl(_)) => 2,
                Sum::Inr(Sum::Inr(Sum::Inl(_))) => 3,
                Sum::Inr(Sum::Inr(Sum::Inr(_))) => 4,
            }
        };
    let recover_len = |msg: TLVMsgSpec| -> u8
        {
            let tag = recover_tag(msg);
            payload_fmt(tag).byte_len(msg) as u8
        };
    #[verusfmt::skip]
    let fmt = Implicit(U8,
        (|tag: u8| Implicit(U8,
        (|len: u8| ExactLen(len, payload_fmt(tag)),
        recover_len)),
        recover_tag));
    fmt
}

impl SpecParser for TLV {
    type PVal = TLVMsgSpec;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        tlv_fmt().spec_parse(ibuf)
    }
}

impl<'i> Parser<&'i [u8]> for TLV {
    type PT = TLVMsg<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let (n1, tag) = U8.parse(ibuf)?;
        let (n2, len) = U8.parse(&ibuf.skip(n1))?;
        let (n3, payload) = ExactLen(len, payload_fmt(tag)).parse(&ibuf.skip(n1 + n2))?;
        let total_n = n1 + n2 + n3;
        assert(self.spec_parse(ibuf@) == Some((total_n as int, payload.deep_view())));
        Ok((total_n, payload))
    }
}

struct MatchedFmt;

impl SpecParser for MatchedFmt {
    type PVal = (u8, TLVMsgSpec);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Bind(U8, |tag: u8| payload_fmt(tag)).spec_parse(ibuf)
    }
}

impl<'i> Parser<&'i [u8]> for MatchedFmt {
    type PT = (u8, TLVMsg<'i>);

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _total_len = ibuf.len();
        let (n1, tag) = U8.parse(ibuf)?;
        // let (n2, payload) = payload_fmt(tag).parse(&ibuf.skip(n1))?;
        let (n2, payload) = match tag {
            1 => {
                let (n2, v) = U8.parse(&ibuf.skip(n1))?;
                (n2, Sum::Inl(v))
            },
            2 => {
                let (n2, v) = Fixed::<10>.parse(&ibuf.skip(n1))?;
                (n2, Sum::Inr(Sum::Inl(v)))
            },
            3 => {
                let (n2, v) = Pair(U8, Tail).parse(&ibuf.skip(n1))?;
                (n2, Sum::Inr(Sum::Inr(Sum::Inl(v))))
            },
            4 => {
                let (n2, v) = Pair(U8, Tail).parse(&ibuf.skip(n1))?;
                (n2, Sum::Inr(Sum::Inr(Sum::Inr(v))))
            },
            _ => return Err(ParseError::invalid_tag()),
        };
        let total_n = n1 + n2;
        Ok((total_n, (tag, payload)))
    }
}

} // verus!
