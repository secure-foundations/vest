use crate::combinators::mapped::spec::*;
use crate::combinators::refined::exec::*;
use crate::combinators::*;
use crate::core::exec::fns::{FnPred, MapRef, Pred};
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::parser::{PResult, Parser};
use crate::core::exec::serializer::*;
use crate::core::exec::ParseError;
use crate::core::{proof::*, spec::*};
use crate::with_deep_view;
use vstd::prelude::*;

verus! {

/*
 * btc_tx_fmt: Data types.
 */

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct BtcTx<'i> {
    pub txin_cnt: u8,
    pub txin: &'i [u8],
    pub txout_cnt: u8,
    pub txout: &'i [u8],
    pub witness: &'i [u8],
    pub locktime: u8,
}

#[verifier::ext_equal]
pub struct BtcTxSpec {
    pub txin_cnt: u8,
    pub txin: Seq<u8>,
    pub txout_cnt: u8,
    pub txout: Seq<u8>,
    pub witness: Seq<u8>,
    pub locktime: u8,
}

type BtcTxInner = (u8, (Seq<u8>, (u8, (Seq<u8>, (Seq<u8>, u8)))));

impl<'i> DeepView for BtcTx<'i> {
    type V = BtcTxSpec;

    open spec fn deep_view(&self) -> Self::V {
        BtcTxSpec {
            txin_cnt: self.txin_cnt,
            txin: self.txin.deep_view(),
            txout_cnt: self.txout_cnt,
            txout: self.txout.deep_view(),
            witness: self.witness.deep_view(),
            locktime: self.locktime,
        }
    }
}

/*
 * btc_tx_fmt: Format specifications.
 */

pub open spec fn btc_tx_fmt() -> Named<
    Mapped<
        WithPrefixTag<
            U8,
            Bind<
                U8,
                spec_fn(txin_count: u8) -> Pair<
                    Varied,
                    Bind<
                        Refined<U8, PredFnSpec<u8>>,
                        spec_fn(txout_count: u8) -> Pair<Varied, Pair<Varied, U8>>,
                    >,
                >,
            >,
        >,
        FnSpecMapper<BtcTxInner, BtcTxSpec>,
    >,
> {
    #[verusfmt::skip]
    Named("btc_tx_fmt", Mapped{
        inner:
            WithPrefixTag(U8, 1u8,
            Bind(U8, |txin_count: u8|
            Pair(Varied(txin_count),
            Bind(Refined(U8, |x: u8| x == txin_count), |txout_count: u8|
            Pair(Varied(txout_count),
            Pair(Varied(txin_count),
            U8)))))),
        mapper: (
            |parsed: BtcTxInner| -> BtcTxSpec {
                let (txin_cnt, (txin, (txout_cnt, (txout, (witness, locktime))))) = parsed;
                BtcTxSpec { txin_cnt, txin, txout_cnt, txout, witness, locktime }
            },
            |value: BtcTxSpec| -> BtcTxInner {
                let BtcTxSpec { txin_cnt, txin, txout_cnt, txout, witness, locktime } = value;
                (txin_cnt, (txin, (txout_cnt, (txout, (witness, locktime)))))
            }
        )
    })
}

struct TxSegwitFmt;

impl SpecParser for TxSegwitFmt {
    type PVal = BtcTxSpec;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        btc_tx_fmt().spec_parse(ibuf)
    }
}

impl Consistency for TxSegwitFmt {
    type Val = BtcTxSpec;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        btc_tx_fmt().consistent(v)
    }
}

impl SpecSerializerDps for TxSegwitFmt {
    type SValue = BtcTxSpec;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        btc_tx_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for TxSegwitFmt {
    type SVal = BtcTxSpec;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        btc_tx_fmt().spec_serialize(v)
    }
}

impl SpecByteLen for TxSegwitFmt {
    type T = BtcTxSpec;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        btc_tx_fmt().byte_len(v)
    }
}

/*
 * btc_tx_fmt: Format properties.
 */

impl SafeParser for TxSegwitFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        btc_tx_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for TxSegwitFmt {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        btc_tx_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        btc_tx_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for TxSegwitFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        btc_tx_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        btc_tx_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for TxSegwitFmt {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        btc_tx_fmt().lemma_serialize_len(v);
    }
}

impl SPRoundTripDps for TxSegwitFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        btc_tx_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for TxSegwitFmt {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        btc_tx_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializers for TxSegwitFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        btc_tx_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

/*
 * btc_tx_fmt: Executable implementations.
 */

impl<'i> Parser<&'i [u8]> for TxSegwitFmt {
    type PT = BtcTx<'i>;

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
        let final_v = BtcTx { txin_cnt, txin, txout_cnt, txout, witness, locktime };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Serializer<&'i BtcTx<'i>> for TxSegwitFmt {
    fn ex_serialize(&self, v: &'i BtcTx<'i>, obuf: &mut Vec<u8>) {
        let ghost old_obuf = obuf@;
        let BtcTx { txin_cnt, txin, txout_cnt, txout, witness, locktime } = *v;
        U8.ex_serialize(1u8, obuf);
        U8.ex_serialize(txin_cnt, obuf);
        Varied(txin_cnt).ex_serialize(txin, obuf);
        U8.ex_serialize(txout_cnt, obuf);
        Varied(txout_cnt).ex_serialize(txout, obuf);
        Varied(txin_cnt).ex_serialize(witness, obuf);
        U8.ex_serialize(locktime, obuf);
        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl<'i> Prepare<&'i BtcTx<'i>> for TxSegwitFmt {
    fn prepare(&self, v: &'i BtcTx<'i>) -> Result<usize, PreSerializeError> {
        let BtcTx { txin_cnt, txin, txout_cnt, txout, witness, locktime } = *v;
        let l1 = U8.prepare(1u8)?;
        let l2 = U8.prepare(txin_cnt)?;
        let l3 = Varied(txin_cnt).prepare(txin)?;
        let l4 = U8.prepare(txout_cnt)?;
        if txout_cnt != txin_cnt {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        let l5 = Varied(txout_cnt).prepare(txout)?;
        let l6 = Varied(txin_cnt).prepare(witness)?;
        let l7 = U8.prepare(locktime)?;
        let total_len = l1
            .checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?
            .checked_add(l3).ok_or(PreSerializeError::LengthTooLarge)?
            .checked_add(l4).ok_or(PreSerializeError::LengthTooLarge)?
            .checked_add(l5).ok_or(PreSerializeError::LengthTooLarge)?
            .checked_add(l6).ok_or(PreSerializeError::LengthTooLarge)?
            .checked_add(l7).ok_or(PreSerializeError::LengthTooLarge)?;

        // let mut total_len = l1;
        // total_len = total_len.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?;
        // total_len = total_len.checked_add(l3).ok_or(PreSerializeError::LengthTooLarge)?;
        // total_len = total_len.checked_add(l4).ok_or(PreSerializeError::LengthTooLarge)?;
        // total_len = total_len.checked_add(l5).ok_or(PreSerializeError::LengthTooLarge)?;
        // total_len = total_len.checked_add(l6).ok_or(PreSerializeError::LengthTooLarge)?;
        // total_len = total_len.checked_add(l7).ok_or(PreSerializeError::LengthTooLarge)?;

        Ok(total_len)
    }
}

/*
 * tlv_msg_fmt: Data types.
 */

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TLVMsg<'i> {
    V1(u8),
    V2(&'i [u8]),
    V3(u8, &'i [u8]),
    V4(u8, &'i [u8]),
}

#[verifier::ext_equal]
pub enum TLVMsgSpec {
    V1(u8),
    V2(Seq<u8>),
    V3(u8, Seq<u8>),
    V4(u8, Seq<u8>),
}

type TLVMsgInner = Sum<u8, Sum<Seq<u8>, Sum<(u8, Seq<u8>), (u8, Seq<u8>)>>>;

impl<'i> DeepView for TLVMsg<'i> {
    type V = TLVMsgSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            TLVMsg::V1(v) => TLVMsgSpec::V1(v),
            TLVMsg::V2(v) => TLVMsgSpec::V2(v.deep_view()),
            TLVMsg::V3(v1, v2) => TLVMsgSpec::V3(v1, v2.deep_view()),
            TLVMsg::V4(v1, v2) => TLVMsgSpec::V4(v1, v2.deep_view()),
        }
    }
}

/*
 * tlv_msg_fmt: Specifications.
 */


pub struct TLVPayloadFmt {
    pub tag: u8,
}

pub struct TLVFmt;

type TLVPayloadSpec = Mapped<
    Choice<Cond<U8>, Choice<Cond<Fixed<10>>, Choice<Cond<Pair<U8, Tail>>, Cond<Pair<U8, Tail>>>>>,
    FnSpecMapper<TLVMsgInner, TLVMsgSpec>,
>;

type TLVSpec = Implicit<
    U8,
    KVFormat<u8, TLVMsgSpec, Implicit<U8, KVFormat<u8, TLVMsgSpec, ExactLen<TLVPayloadFmt>>>>,
>;

pub open spec fn payload_fmt(tag: u8) -> TLVPayloadSpec {
    Mapped {
        inner: Choice(
            Cond(tag == 1, U8),
            Choice(
                Cond(tag == 2, Fixed::<10>),
                Choice(Cond(tag == 3, Pair(U8, Tail)), Cond(tag == 4, Pair(U8, Tail))),
            ),
        ),
        mapper: (
            |parsed: TLVMsgInner| -> TLVMsgSpec
                {
                    match parsed {
                        Sum::Inl(v) => TLVMsgSpec::V1(v),
                        Sum::Inr(Sum::Inl(v)) => TLVMsgSpec::V2(v),
                        Sum::Inr(Sum::Inr(Sum::Inl((v1, v2)))) => TLVMsgSpec::V3(v1, v2),
                        Sum::Inr(Sum::Inr(Sum::Inr((v1, v2)))) => TLVMsgSpec::V4(v1, v2),
                    }
                },
            |value: TLVMsgSpec| -> TLVMsgInner
                {
                    match value {
                        TLVMsgSpec::V1(v) => Sum::Inl(v),
                        TLVMsgSpec::V2(v) => Sum::Inr(Sum::Inl(v)),
                        TLVMsgSpec::V3(v1, v2) => Sum::Inr(Sum::Inr(Sum::Inl((v1, v2)))),
                        TLVMsgSpec::V4(v1, v2) => Sum::Inr(Sum::Inr(Sum::Inr((v1, v2)))),
                    }
                },
        ),
    }
}

pub open spec fn tlv_fmt() -> TLVSpec {
    let recover_tag = |msg: TLVMsgSpec| -> u8
        {
            match msg {
                TLVMsgSpec::V1(_) => 1u8,
                TLVMsgSpec::V2(_) => 2u8,
                TLVMsgSpec::V3(_, _) => 3u8,
                TLVMsgSpec::V4(_, _) => 4u8,
            }
        };
    let recover_len = |msg: TLVMsgSpec| -> u8
        {
            let tag = recover_tag(msg);
            TLVPayloadFmt { tag }.byte_len(msg) as u8
        };
    #[verusfmt::skip]
    let fmt = Implicit(U8,
        (|tag: u8| Implicit(U8,
        (|len: u8| ExactLen(len, TLVPayloadFmt { tag }),
        recover_len)),
        recover_tag));
    fmt
}

impl SpecParser for TLVPayloadFmt {
    type PVal = TLVMsgSpec;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        payload_fmt(self.tag).spec_parse(ibuf)
    }
}

impl Consistency for TLVPayloadFmt {
    type Val = TLVMsgSpec;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        payload_fmt(self.tag).consistent(v)
    }
}

impl SpecSerializerDps for TLVPayloadFmt {
    type SValue = TLVMsgSpec;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        payload_fmt(self.tag).spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for TLVPayloadFmt {
    type SVal = TLVMsgSpec;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        payload_fmt(self.tag).spec_serialize(v)
    }
}

impl SpecByteLen for TLVPayloadFmt {
    type T = TLVMsgSpec;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        payload_fmt(self.tag).byte_len(v)
    }
}

impl SpecParser for TLVFmt {
    type PVal = TLVMsgSpec;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        tlv_fmt().spec_parse(ibuf)
    }
}

impl Consistency for TLVFmt {
    type Val = TLVMsgSpec;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        tlv_fmt().consistent(v)
    }
}

impl SpecSerializerDps for TLVFmt {
    type SValue = TLVMsgSpec;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        tlv_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for TLVFmt {
    type SVal = TLVMsgSpec;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        tlv_fmt().spec_serialize(v)
    }
}

impl SpecByteLen for TLVFmt {
    type T = TLVMsgSpec;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        tlv_fmt().byte_len(v)
    }
}

/*
 * tlv_msg_fmt: Format properties.
 */

impl SafeParser for TLVPayloadFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        payload_fmt(self.tag).lemma_parse_safe(ibuf);
    }
}

impl SoundParser for TLVPayloadFmt {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        payload_fmt(self.tag).lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        payload_fmt(self.tag).lemma_parse_sound_value(ibuf);
    }
}

// impl NonTailFmt for TLVPayloadFmt {
//     proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
//         payload_fmt(self.tag).lemma_serialize_dps_prepend(v, obuf);
//     }
//     proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
//         payload_fmt(self.tag).lemma_serialize_dps_len(v, obuf);
//     }
// }
impl GoodSerializer for TLVPayloadFmt {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        payload_fmt(self.tag).lemma_serialize_len(v);
    }
}

impl SPRoundTripDps for TLVPayloadFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        payload_fmt(self.tag).theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for TLVPayloadFmt {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        payload_fmt(self.tag).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializers for TLVPayloadFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        payload_fmt(self.tag).lemma_serialize_equiv_on_empty(v);
    }
}

impl SafeParser for TLVFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        tlv_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for TLVFmt {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        tlv_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        tlv_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for TLVFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        tlv_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        tlv_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for TLVFmt {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        tlv_fmt().lemma_serialize_len(v);
    }
}

impl SPRoundTripDps for TLVFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        tlv_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for TLVFmt {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        tlv_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializers for TLVFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        tlv_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

/*
 * tlv_msg_fmt: Executable implementations.
 */

impl<'i> Parser<&'i [u8]> for TLVPayloadFmt {
    type PT = TLVMsg<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, payload) = match self.tag {
            1 => {
                let (n, v) = U8.parse(ibuf)?;
                (n, TLVMsg::V1(v))
            },
            2 => {
                let (n, v) = Fixed::<10>.parse(ibuf)?;
                (n, TLVMsg::V2(v))
            },
            3 => {
                let (n, (v1, v2)) = Pair(U8, Tail).parse(ibuf)?;
                (n, TLVMsg::V3(v1, v2))
            },
            4 => {
                let (n, (v1, v2)) = Pair(U8, Tail).parse(ibuf)?;
                (n, TLVMsg::V4(v1, v2))
            },
            _ => return Err(ParseError::invalid_tag()),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, payload.deep_view())));
        Ok((n, payload))
    }
}

impl<'i> Serializer<&'i TLVMsg<'i>> for TLVPayloadFmt {
    fn ex_serialize(&self, v: &'i TLVMsg<'i>, obuf: &mut Vec<u8>) {
        let ghost old_obuf = obuf@;
        match v {
            TLVMsg::V1(v) => U8.ex_serialize(*v, obuf),
            TLVMsg::V2(v) => Fixed::<10>.ex_serialize(*v, obuf),
            TLVMsg::V3(v1, v2) => Pair(U8, Tail).ex_serialize((*v1, *v2), obuf),
            TLVMsg::V4(v1, v2) => Pair(U8, Tail).ex_serialize((*v1, *v2), obuf),
        }
        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl<'i> Prepare<&'i TLVMsg<'i>> for TLVPayloadFmt {
    fn prepare(&self, v: &'i TLVMsg<'i>) -> Result<usize, PreSerializeError> {
        match (self.tag, v) {
            (1, TLVMsg::V1(v)) => U8.prepare(*v),
            (2, TLVMsg::V2(v)) => Fixed::<10>.prepare(*v),
            (3, TLVMsg::V3(v1, v2)) => Pair(U8, Tail).prepare((*v1, *v2)),
            (4, TLVMsg::V4(v1, v2)) => Pair(U8, Tail).prepare((*v1, *v2)),
            _ => Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
        }
    }
}

impl<'i> Parser<&'i [u8]> for TLVFmt {
    type PT = TLVMsg<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let (n1, tag) = U8.parse(ibuf)?;
        let (n2, len) = U8.parse(&ibuf.skip(n1))?;
        let (n3, payload) = ExactLen(len, TLVPayloadFmt { tag }).parse(&ibuf.skip(n1 + n2))?;
        let total_n = n1 + n2 + n3;
        assert(self.spec_parse(ibuf@) == Some((total_n as int, payload.deep_view())));
        Ok((total_n, payload))
    }
}

impl<'i> Serializer<&'i TLVMsg<'i>> for TLVFmt {
    fn ex_serialize(&self, v: &'i TLVMsg<'i>, obuf: &mut Vec<u8>) {
        broadcast use crate::core::spec::GoodSerializer::lemma_serialize_len;

        let ghost old_obuf = obuf@;
        let tag = match v {
            TLVMsg::V1(_) => 1u8,
            TLVMsg::V2(_) => 2u8,
            TLVMsg::V3(_, _) => 3u8,
            TLVMsg::V4(_, _) => 4u8,
        };
        U8.ex_serialize(tag, obuf);
        // Strategy 0:
        // call `TLVPayloadFmt { tag }.length()` to get the length of the payload, and serialize it before serializing the payload.
        // However, this means we have to strengthen the pre-condition of `ex_serialize` to require
        // `self.byte_len(v.deep_view()) <= usize::MAX`, which is not ideal.

        // Strategy 1: in-place update
        // // record the offset of the length field in the output buffer
        // let offset = obuf.len();
        // U8.ex_serialize(0u8, obuf); // placeholder for length
        // let old_len = obuf.len();
        // TLVPayloadFmt { tag }.ex_serialize(v, obuf);
        // let new_len = obuf.len();
        // // Update the length field in the output buffer
        // let actual_len = (new_len - old_len) as u8;
        // obuf[offset] = actual_len;

        // Strategy 2: re-allocation
        let mut payload_buf = Vec::new();
        TLVPayloadFmt { tag }.ex_serialize(v, &mut payload_buf);
        let payload_len = payload_buf.len() as u8;
        U8.ex_serialize(payload_len, obuf);
        obuf.extend_from_slice(&payload_buf);
        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl<'i> Prepare<&'i TLVMsg<'i>> for TLVFmt {
    fn prepare(&self, v: &'i TLVMsg<'i>) -> Result<usize, PreSerializeError> {
        let tag = match v {
            TLVMsg::V1(_) => 1u8,
            TLVMsg::V2(_) => 2u8,
            TLVMsg::V3(_, _) => 3u8,
            TLVMsg::V4(_, _) => 4u8,
        };
        let len = TLVPayloadFmt { tag }.prepare(v)?;
        let l1 = U8.prepare(tag)?;
        if len > u8::MAX as usize {
            return Err(PreSerializeError::LengthTooLarge);
        }
        let l2 = U8.prepare(len as u8)?;
        let total_len = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(
            len,
        ).ok_or(PreSerializeError::LengthTooLarge)?;
        Ok(total_len)
    }
}

} // verus!
