use crate::combinators::mapped::spec::*;
use crate::combinators::refined::exec::*;
use crate::combinators::*;
use crate::core::exec::fns::{FnPred, MapRef, Pred};
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::parser::*;
use crate::core::exec::serializer::*;
use crate::core::exec::ParseError;
use crate::core::{proof::*, spec::*};
use crate::with_deep_view;
use vstd::prelude::*;

verus! {

/*
 *
 * ```vest
 * btc_tx = {
 *     omitted const magic: u8 = 1,
 *     @txin_cnt: u8,
 *     txin: [u8; @txin_cnt],
 *     @txout_cnt: u8 | @txout_cnt == @txin_cnt,
 *     txout: [u16; @txout_cnt],
 *     witness: [u16; @txin_cnt],
 *     locktime: u8,
 * }
 * ```
 */
/*
 * btc_tx_fmt: Data types.
 */
#[derive(Debug, PartialEq, Eq)]
pub struct BtcTx<'i> {
    pub txin_cnt: u8,
    pub txin: &'i [u8],
    pub txout_cnt: u8,
    pub txout: Vec<u16>,
    pub witness: Vec<u16>,
    pub locktime: u8,
}

#[verifier::ext_equal]
pub struct BtcTxSpec {
    pub txin_cnt: u8,
    pub txin: Seq<u8>,
    pub txout_cnt: u8,
    pub txout: Seq<u16>,
    pub witness: Seq<u16>,
    pub locktime: u8,
}

type BtcTxInner = (u8, (Seq<u8>, (u8, (Seq<u16>, (Seq<u16>, u8)))));

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
        PrefixTagged<
            U8,
            Bind<
                U8,
                spec_fn(txin_count: u8) -> Pair<
                    Varied,
                    Bind<
                        Refined<U8, PredFnSpec<u8>>,
                        spec_fn(txout_count: u8) -> Pair<RepeatN<U16Le>, Pair<RepeatN<U16Le>, U8>>,
                    >,
                >,
            >,
        >,
        FnSpecMapper<BtcTxInner, BtcTxSpec>,
    >,
> {
    #[verusfmt::skip]
    Named("btc_tx", Mapped{
        inner:
            PrefixTagged(U8, 1u8,
            Bind(U8, |txin_count: u8|
            Pair(Varied(txin_count),
            Bind(Refined(U8, |x: u8| x == txin_count), |txout_count: u8|
            Pair(RepeatN(txout_count, U16Le),
            Pair(RepeatN(txin_count, U16Le),
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

pub struct TxSegwitFmt;

impl SpecParser for TxSegwitFmt {
    type PVal = BtcTxSpec;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        btc_tx_fmt().spec_parse(ibuf)
    }
}

impl Consistency for TxSegwitFmt {
    type Val = BtcTxSpec;

    #[verifier::opaque]
    open spec fn consistent(&self, v: Self::Val) -> bool {
        btc_tx_fmt().consistent(v)
    }
}

impl SpecSerializerDps for TxSegwitFmt {
    type SValue = BtcTxSpec;

    #[verifier::opaque]
    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        btc_tx_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for TxSegwitFmt {
    type SVal = BtcTxSpec;

    #[verifier::opaque]
    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        btc_tx_fmt().spec_serialize(v)
    }
}

impl SpecByteLen for TxSegwitFmt {
    type T = BtcTxSpec;

    #[verifier::opaque]
    open spec fn byte_len(&self, v: Self::T) -> nat {
        btc_tx_fmt().byte_len(v)
    }
}

/*
 * btc_tx_fmt: Format properties.
 */

impl SafeParser for TxSegwitFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<TxSegwitFmt as SpecParser>::spec_parse);
        btc_tx_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for TxSegwitFmt {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        reveal(<TxSegwitFmt as SpecParser>::spec_parse);
        reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
        btc_tx_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        reveal(<TxSegwitFmt as SpecParser>::spec_parse);
        reveal(<TxSegwitFmt as Consistency>::consistent);
        btc_tx_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for TxSegwitFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
        btc_tx_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
        btc_tx_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for TxSegwitFmt {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
        reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
        btc_tx_fmt().lemma_serialize_len(v);
    }
}

impl SPRoundTripDps for TxSegwitFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        reveal(<TxSegwitFmt as SpecParser>::spec_parse);
        reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TxSegwitFmt as Consistency>::consistent);
        reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
        btc_tx_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for TxSegwitFmt {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        reveal(<TxSegwitFmt as SpecParser>::spec_parse);
        btc_tx_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializersGeneral for TxSegwitFmt {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
        btc_tx_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for TxSegwitFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
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

        reveal(<TxSegwitFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, _) = Const(U8, 1u8).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, txin_cnt) = U8.parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, txin) = Varied(txin_cnt).parse(&rest)?;
        let rest = rest.skip(n3);
        let (n4, txout_cnt) = U8.parse(&rest)?;
        if txout_cnt != txin_cnt {
            return Err(ParseError::predicate_failed());
        }
        let rest = rest.skip(n4);
        let (n5, txout) = RepeatN(txout_cnt, U16Le).parse(&rest)?;
        let rest = rest.skip(n5);
        let (n6, witness) = RepeatN(txin_cnt, U16Le).parse(&rest)?;
        let rest = rest.skip(n6);
        let (n7, locktime) = U8.parse(&rest)?;
        let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7;
        let final_v = BtcTx { txin_cnt, txin, txout_cnt, txout, witness, locktime };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Serializer<BtcTx<'i>> for TxSegwitFmt {
    fn serialize(&self, v: &BtcTx<'i>, obuf: &mut Vec<u8>) {
        reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
        reveal(<TxSegwitFmt as Consistency>::consistent);

        let ghost old_obuf = obuf@;
        let BtcTx { txin_cnt, txin, txout_cnt, txout, witness, locktime } = v;
        U8.serialize(&1u8, obuf);
        U8.serialize(txin_cnt, obuf);
        Varied(*txin_cnt).serialize(txin, obuf);
        U8.serialize(txout_cnt, obuf);
        RepeatN(*txout_cnt, U16Le).serialize(txout, obuf);
        RepeatN(*txin_cnt, U16Le).serialize(witness, obuf);

        U8.serialize(locktime, obuf);
        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl<'i> Prepare<BtcTx<'i>> for TxSegwitFmt {
    fn prepare(&self, v: &BtcTx<'i>) -> Result<usize, PreSerializeError> {
        reveal(<TxSegwitFmt as Consistency>::consistent);
        reveal(<TxSegwitFmt as SpecByteLen>::byte_len);

        let BtcTx { txin_cnt, txin, txout_cnt, txout, witness, locktime } = v;
        let l1 = U8.prepare(&1u8)?;
        let l2 = U8.prepare(txin_cnt)?;
        let l3 = Varied(txin_cnt).prepare(txin)?;
        let l4 = U8.prepare(txout_cnt)?;
        if txout_cnt != txin_cnt {
            return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
        }
        let l5 = RepeatN(txout_cnt, U16Le).prepare(txout)?;
        let l6 = RepeatN(txin_cnt, U16Le).prepare(witness)?;
        let l7 = U8.prepare(locktime)?;
        let total_len = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(
            l3,
        ).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(l4).ok_or(
            PreSerializeError::LengthTooLarge,
        )?.checked_add(l5).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(l6).ok_or(
            PreSerializeError::LengthTooLarge,
        )?.checked_add(l7).ok_or(PreSerializeError::LengthTooLarge)?;

        Ok(total_len)
    }
}

/*
 *
 * ```vest
 * msg_ty = enum {
 *   TYPE1 = 1,
 *   TYPE2 = 2,
 *   TYPE3 = 3,
 *   TYPE4 = 4,
 * }
 *
 * tlv = {
 *     omitted @tag: msg_ty,
 *     omitted @len: u8,
 *     payload: [u8; @len] >>= choose(@tag) {
 *         TYPE1 => u8,
 *         TYPE2 => [u8; 10],
 *         TYPE3 => btc_tx,
 *         TYPE4 => btc_tx,
 *     },
 * }
 * ```
 */

/*
  * msg_ty: Data types.
  */

#[derive(Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum MsgTy {
    TYPE1 = 1,
    TYPE2 = 2,
    TYPE3 = 3,
    TYPE4 = 4,
}

type MsgTyInner = Sum<u8, Sum<u8, Sum<u8, u8>>>;

impl DeepView for MsgTy {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

/*
 * msg_ty: Specifications.
 */

pub struct MsgTyFmt;

pub open spec fn msg_ty_fmt() -> Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<u8, MsgTy>>,
> {
    #[verusfmt::skip]
    Named("msg_ty", Mapped{
        inner: Refined(U8, |x: u8| x == 1u8 || x == 2u8 || x == 3u8 || x == 4u8),
        mapper: (
            |parsed: u8| -> MsgTy {
                match parsed {
                    1u8 => MsgTy::TYPE1,
                    2u8 => MsgTy::TYPE2,
                    3u8 => MsgTy::TYPE3,
                    4u8 => MsgTy::TYPE4,
                    _ => arbitrary(),
                }
            },
            |value: MsgTy| -> u8 {
                match value {
                    MsgTy::TYPE1 => 1u8,
                    MsgTy::TYPE2 => 2u8,
                    MsgTy::TYPE3 => 3u8,
                    MsgTy::TYPE4 => 4u8,
                }
            }
        )
    })
}

impl SpecParser for MsgTyFmt {
    type PVal = MsgTy;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        msg_ty_fmt().spec_parse(ibuf)
    }
}

impl Consistency for MsgTyFmt {
    type Val = MsgTy;

    #[verifier::opaque]
    open spec fn consistent(&self, v: Self::Val) -> bool {
        msg_ty_fmt().consistent(v)
    }
}

impl SpecSerializerDps for MsgTyFmt {
    type SValue = MsgTy;

    #[verifier::opaque]
    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        msg_ty_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for MsgTyFmt {
    type SVal = MsgTy;

    #[verifier::opaque]
    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        msg_ty_fmt().spec_serialize(v)
    }
}

impl SpecByteLen for MsgTyFmt {
    type T = MsgTy;

    #[verifier::opaque]
    open spec fn byte_len(&self, v: Self::T) -> nat {
        msg_ty_fmt().byte_len(v)
    }
}

/*
 * msg_ty: Format properties.
 */

impl SafeParser for MsgTyFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<MsgTyFmt as SpecParser>::spec_parse);
        msg_ty_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for MsgTyFmt {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        reveal(<MsgTyFmt as SpecParser>::spec_parse);
        reveal(<MsgTyFmt as SpecByteLen>::byte_len);
        msg_ty_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        reveal(<MsgTyFmt as SpecParser>::spec_parse);
        reveal(<MsgTyFmt as Consistency>::consistent);
        msg_ty_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for MsgTyFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        reveal(<MsgTyFmt as SpecSerializerDps>::spec_serialize_dps);
        msg_ty_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        reveal(<MsgTyFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<MsgTyFmt as SpecByteLen>::byte_len);
        msg_ty_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for MsgTyFmt {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        reveal(<MsgTyFmt as SpecSerializer>::spec_serialize);
        reveal(<MsgTyFmt as SpecByteLen>::byte_len);
        msg_ty_fmt().lemma_serialize_len(v);
    }
}

impl SPRoundTripDps for MsgTyFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        reveal(<MsgTyFmt as SpecParser>::spec_parse);
        reveal(<MsgTyFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<MsgTyFmt as Consistency>::consistent);
        reveal(<MsgTyFmt as SpecByteLen>::byte_len);
        msg_ty_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for MsgTyFmt {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        reveal(<MsgTyFmt as SpecParser>::spec_parse);
        msg_ty_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializersGeneral for MsgTyFmt {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        reveal(<MsgTyFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<MsgTyFmt as SpecSerializer>::spec_serialize);
        msg_ty_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for MsgTyFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        reveal(<MsgTyFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<MsgTyFmt as SpecSerializer>::spec_serialize);
        msg_ty_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

/*
 * msg_ty: Executable implementations.
 */

impl<'i> Parser<&'i [u8]> for MsgTyFmt {
    type PT = MsgTy;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(<MsgTyFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = U8.parse(&rest)?;
        let msg_ty = match v {
            1u8 => MsgTy::TYPE1,
            2u8 => MsgTy::TYPE2,
            3u8 => MsgTy::TYPE3,
            4u8 => MsgTy::TYPE4,
            _ => return Err(ParseError::invalid_tag()),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, msg_ty.deep_view())));
        Ok((n, msg_ty))
    }
}

impl<'i> Serializer<MsgTy> for MsgTyFmt {
    fn serialize(&self, v: &MsgTy, obuf: &mut Vec<u8>) {
        reveal(<MsgTyFmt as SpecSerializer>::spec_serialize);
        let ghost old_obuf = obuf@;
        let tag = match v {
            MsgTy::TYPE1 => 1u8,
            MsgTy::TYPE2 => 2u8,
            MsgTy::TYPE3 => 3u8,
            MsgTy::TYPE4 => 4u8,
        };
        U8.serialize(&tag, obuf);
        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl Prepare<MsgTy> for MsgTyFmt {
    fn prepare(&self, v: &MsgTy) -> Result<usize, PreSerializeError> {
        reveal(<MsgTyFmt as Consistency>::consistent);
        reveal(<MsgTyFmt as SpecByteLen>::byte_len);
        let tag = match v {
            MsgTy::TYPE1 => 1u8,
            MsgTy::TYPE2 => 2u8,
            MsgTy::TYPE3 => 3u8,
            MsgTy::TYPE4 => 4u8,
        };
        U8.prepare(&tag)
    }
}

// impl MsgTy {
//     pub fn parse(ibuf: &[u8]) -> (r: PResult<Self>)
//         ensures
//             parse_matches_spec(r, MsgTyFmt.spec_parse(ibuf@)),
//     {
//         Named("msg_ty", MsgTyFmt).parse(&ibuf)
//     }
//     pub fn serialize(&self, obuf: &mut Vec<u8>)
//         requires
//             MsgTyFmt.consistent(self.deep_view()),
//         ensures
//             final(obuf)@ == old(obuf)@ + MsgTyFmt.spec_serialize(self.deep_view()),
//     {
//         MsgTyFmt.serialize(self, obuf)
//     }
//     pub fn prepare(&self) -> (checked: Result<usize, PreSerializeError>)
//         ensures
//             checked matches Ok(len) ==> {
//                 &&& MsgTyFmt.consistent(self.deep_view())
//                 &&& len == MsgTyFmt.byte_len(self.deep_view())
//             },
//     {
//         Named("msg_ty", MsgTyFmt).prepare(self)
//     }
// }
/*
 * tlv_msg_fmt: Data types.
 */

#[derive(Debug, PartialEq, Eq)]
pub enum TLVMsg<'i> {
    V1(u8),
    V2(&'i [u8]),
    V3(BtcTx<'i>),
    V4(BtcTx<'i>),
}

#[verifier::ext_equal]
pub enum TLVMsgSpec {
    V1(u8),
    V2(Seq<u8>),
    V3(BtcTxSpec),
    V4(BtcTxSpec),
}

type TLVMsgInner = Sum<u8, Sum<Seq<u8>, Sum<BtcTxSpec, BtcTxSpec>>>;

impl<'i> DeepView for TLVMsg<'i> {
    type V = TLVMsgSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            TLVMsg::V1(v) => TLVMsgSpec::V1(v),
            TLVMsg::V2(v) => TLVMsgSpec::V2(v.deep_view()),
            TLVMsg::V3(v) => TLVMsgSpec::V3(v.deep_view()),
            TLVMsg::V4(v) => TLVMsgSpec::V4(v.deep_view()),
        }
    }
}

/*
 * tlv_msg_fmt: Specifications.
 */

pub struct TLVFmt;

pub struct TLVPayloadFmt {
    pub tag: MsgTy,
}

pub open spec fn tlv_fmt() -> Implicit<
    MsgTyFmt,
    KVFormat<MsgTy, TLVMsgSpec, Implicit<U8, KVFormat<u8, TLVMsgSpec, ExactLen<TLVPayloadFmt>>>>,
> {
    let recover_tag = |msg: TLVMsgSpec| -> MsgTy
        {
            match msg {
                TLVMsgSpec::V1(_) => MsgTy::TYPE1,
                TLVMsgSpec::V2(_) => MsgTy::TYPE2,
                TLVMsgSpec::V3(_) => MsgTy::TYPE3,
                TLVMsgSpec::V4(_) => MsgTy::TYPE4,
            }
        };
    let recover_len = |msg: TLVMsgSpec| -> u8
        {
            let tag = recover_tag(msg);
            TLVPayloadFmt { tag }.byte_len(msg) as u8
        };
    #[verusfmt::skip]
    let fmt = Implicit(MsgTyFmt,
        (|tag: MsgTy| Implicit(U8,
        (|len: u8| ExactLen(len, TLVPayloadFmt { tag }),
        recover_len)),
        recover_tag));
    fmt
}

// pub open spec fn payload_fmt(tag: MsgTy) -> Mapped<
//     Choice<Cond<U8>, Choice<Cond<Fixed<10>>, Choice<Cond<Pair<U8, Tail>>, Cond<Pair<U8, Tail>>>>>,
//     FnSpecMapper<TLVMsgInner, TLVMsgSpec>,
// > {
// Mapped {
// inner: Choice(
//     Cond(tag == MsgTy::TYPE1, U8),
//     Choice(
//         Cond(tag == MsgTy::TYPE2, Fixed::<10>),
//         Choice(Cond(tag == MsgTy::TYPE3, Pair(U8, Tail)), Cond(tag == MsgTy::TYPE4, Pair(U8, Tail))),
//     ),
// ),
pub open spec fn payload_fmt(tag: MsgTy) -> Mapped<
    Sum<U8, Sum<Fixed<10>, Sum<TxSegwitFmt, TxSegwitFmt>>>,
    FnSpecMapper<TLVMsgInner, TLVMsgSpec>,
> {
    Mapped {
        inner: match tag {
            MsgTy::TYPE1 => Sum::Inl(U8),
            MsgTy::TYPE2 => Sum::Inr(Sum::Inl(Fixed::<10>)),
            MsgTy::TYPE3 => Sum::Inr(Sum::Inr(Sum::Inl(TxSegwitFmt))),
            MsgTy::TYPE4 => Sum::Inr(Sum::Inr(Sum::Inr(TxSegwitFmt))),
        },
        mapper: (
            |parsed: TLVMsgInner| -> TLVMsgSpec
                {
                    match parsed {
                        Sum::Inl(v) => TLVMsgSpec::V1(v),
                        Sum::Inr(Sum::Inl(v)) => TLVMsgSpec::V2(v),
                        Sum::Inr(Sum::Inr(Sum::Inl(v))) => TLVMsgSpec::V3(v),
                        Sum::Inr(Sum::Inr(Sum::Inr((v)))) => TLVMsgSpec::V4(v),
                    }
                },
            |value: TLVMsgSpec| -> TLVMsgInner
                {
                    match value {
                        TLVMsgSpec::V1(v) => Sum::Inl(v),
                        TLVMsgSpec::V2(v) => Sum::Inr(Sum::Inl(v)),
                        TLVMsgSpec::V3(v) => Sum::Inr(Sum::Inr(Sum::Inl((v)))),
                        TLVMsgSpec::V4(v) => Sum::Inr(Sum::Inr(Sum::Inr((v)))),
                    }
                },
        ),
    }
}

impl SpecParser for TLVFmt {
    type PVal = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        tlv_fmt().spec_parse(ibuf)
    }
}

impl Consistency for TLVFmt {
    type Val = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn consistent(&self, v: Self::Val) -> bool {
        tlv_fmt().consistent(v)
    }
}

impl SpecSerializerDps for TLVFmt {
    type SValue = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        tlv_fmt().spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for TLVFmt {
    type SVal = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        tlv_fmt().spec_serialize(v)
    }
}

impl SpecByteLen for TLVFmt {
    type T = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn byte_len(&self, v: Self::T) -> nat {
        tlv_fmt().byte_len(v)
    }
}

impl SpecParser for TLVPayloadFmt {
    type PVal = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        payload_fmt(self.tag).spec_parse(ibuf)
    }
}

impl Consistency for TLVPayloadFmt {
    type Val = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn consistent(&self, v: Self::Val) -> bool {
        payload_fmt(self.tag).consistent(v)
    }
}

impl SpecSerializerDps for TLVPayloadFmt {
    type SValue = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        payload_fmt(self.tag).spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for TLVPayloadFmt {
    type SVal = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        payload_fmt(self.tag).spec_serialize(v)
    }
}

impl SpecByteLen for TLVPayloadFmt {
    type T = TLVMsgSpec;

    #[verifier::opaque]
    open spec fn byte_len(&self, v: Self::T) -> nat {
        payload_fmt(self.tag).byte_len(v)
    }
}

/*
 * tlv_msg_fmt: Format properties.
 */

impl SafeParser for TLVFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<TLVFmt as SpecParser>::spec_parse);
        tlv_fmt().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for TLVFmt {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        reveal(<TLVFmt as SpecParser>::spec_parse);
        reveal(<TLVFmt as SpecByteLen>::byte_len);
        reveal(<TLVPayloadFmt as Consistency>::consistent);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);
        tlv_fmt().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        reveal(<TLVFmt as SpecParser>::spec_parse);
        reveal(<TLVFmt as Consistency>::consistent);
        reveal(<TLVPayloadFmt as Consistency>::consistent);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);
        tlv_fmt().lemma_parse_sound_value(ibuf);
    }
}

impl NonTailFmt for TLVFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        reveal(<TLVFmt as SpecSerializerDps>::spec_serialize_dps);
        tlv_fmt().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        reveal(<TLVFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TLVFmt as SpecByteLen>::byte_len);
        tlv_fmt().lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for TLVFmt {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        reveal(<TLVFmt as SpecSerializer>::spec_serialize);
        reveal(<TLVFmt as SpecByteLen>::byte_len);
        tlv_fmt().lemma_serialize_len(v);
    }
}

impl SPRoundTripDps for TLVFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        reveal(<TLVFmt as SpecParser>::spec_parse);
        reveal(<TLVFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TLVFmt as Consistency>::consistent);
        reveal(<TLVFmt as SpecByteLen>::byte_len);
        tlv_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for TLVFmt {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        reveal(<TLVFmt as SpecParser>::spec_parse);
        reveal(<TLVPayloadFmt as Consistency>::consistent);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);
        tlv_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializersGeneral for TLVFmt {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        reveal(<TLVFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TLVFmt as SpecSerializer>::spec_serialize);
        tlv_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for TLVFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        reveal(<TLVFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TLVFmt as SpecSerializer>::spec_serialize);
        tlv_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SafeParser for TLVPayloadFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<TLVPayloadFmt as SpecParser>::spec_parse);
        payload_fmt(self.tag).lemma_parse_safe(ibuf);
    }
}

impl SoundParser for TLVPayloadFmt {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        reveal(<TLVPayloadFmt as SpecParser>::spec_parse);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);
        payload_fmt(self.tag).lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        reveal(<TLVPayloadFmt as SpecParser>::spec_parse);
        reveal(<TLVPayloadFmt as Consistency>::consistent);
        payload_fmt(self.tag).lemma_parse_sound_value(ibuf);
    }
}

impl GoodSerializer for TLVPayloadFmt {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        reveal(<TLVPayloadFmt as SpecSerializer>::spec_serialize);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);
        payload_fmt(self.tag).lemma_serialize_len(v);
    }
}

impl SPRoundTripDps for TLVPayloadFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        reveal(<TLVPayloadFmt as SpecParser>::spec_parse);
        reveal(<TLVPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TLVPayloadFmt as Consistency>::consistent);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);
        payload_fmt(self.tag).theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for TLVPayloadFmt {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        reveal(<TLVPayloadFmt as SpecParser>::spec_parse);
        payload_fmt(self.tag).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializers for TLVPayloadFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        reveal(<TLVPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
        reveal(<TLVPayloadFmt as SpecSerializer>::spec_serialize);
        payload_fmt(self.tag).lemma_serialize_equiv_on_empty(v);
    }
}

/*
 * tlv_msg_fmt: Executable implementations.
 */

impl<'i> Parser<&'i [u8]> for TLVFmt {
    type PT = TLVMsg<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TLVFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, tag) = Named("msg_ty", MsgTyFmt).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, len) = U8.parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, payload) = ExactLen(len, TLVPayloadFmt { tag }).parse(&rest)?;
        let total_n = n1 + n2 + n3;
        assert(self.spec_parse(ibuf@) == Some((total_n as int, payload.deep_view())));
        Ok((total_n, payload))
    }
}

impl<'i> Serializer<TLVMsg<'i>> for TLVFmt {
    fn serialize(&self, v: &TLVMsg<'i>, obuf: &mut Vec<u8>) {
        reveal(<TLVFmt as SpecSerializer>::spec_serialize);
        reveal(<TLVFmt as Consistency>::consistent);
        reveal(<MsgTyFmt as SpecSerializer>::spec_serialize);
        reveal(<MsgTyFmt as Consistency>::consistent);
        reveal(<TLVPayloadFmt as SpecSerializer>::spec_serialize);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);
        reveal(<TLVPayloadFmt as Consistency>::consistent);
        let ghost old_obuf = obuf@;
        let tag = match v {
            TLVMsg::V1(_) => MsgTy::TYPE1,
            TLVMsg::V2(_) => MsgTy::TYPE2,
            TLVMsg::V3(_) => MsgTy::TYPE3,
            TLVMsg::V4(_) => MsgTy::TYPE4,
        };
        MsgTyFmt.serialize(&tag, obuf);
        // Strategy 0:
        // call `TLVPayloadFmt { tag }.length()` to get the length of the payload, and serialize it before serializing the payload.
        // However, this means we have to strengthen the pre-condition of `serialize` to require
        // `self.byte_len(v.deep_view()) <= usize::MAX`, which is not ideal.

        // Strategy 1: in-place update
        // // record the offset of the length field in the output buffer
        // let offset = obuf.len();
        // U8.serialize(0u8, obuf); // placeholder for length
        // let old_len = obuf.len();
        // TLVPayloadFmt { tag }.serialize(v, obuf);
        // let new_len = obuf.len();
        // // Update the length field in the output buffer
        // let actual_len = (new_len - old_len) as u8;
        // obuf[offset] = actual_len;

        // Strategy 2: re-allocation
        let mut payload_buf = Vec::new();
        TLVPayloadFmt { tag }.serialize(v, &mut payload_buf);
        proof {
            TLVPayloadFmt { tag }.lemma_serialize_len(v.deep_view());
        }
        let payload_len = payload_buf.len() as u8;
        U8.serialize(&payload_len, obuf);
        obuf.extend_from_slice(&payload_buf);
        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl<'i> Prepare<TLVMsg<'i>> for TLVFmt {
    fn prepare(&self, v: &TLVMsg<'i>) -> Result<usize, PreSerializeError> {
        reveal(<TLVFmt as Consistency>::consistent);
        reveal(<TLVFmt as SpecByteLen>::byte_len);
        reveal(<TLVPayloadFmt as Consistency>::consistent);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);
        let tag = match v {
            TLVMsg::V1(_) => MsgTy::TYPE1,
            TLVMsg::V2(_) => MsgTy::TYPE2,
            TLVMsg::V3(_) => MsgTy::TYPE3,
            TLVMsg::V4(_) => MsgTy::TYPE4,
        };
        let l1 = Named("msg_ty", MsgTyFmt).prepare(&tag)?;
        let l3 = TLVPayloadFmt { tag }.prepare(v)?;
        if l3 > u8::MAX as usize {
            return Err(PreSerializeError::LengthTooLarge);
        }
        let l2 = U8.prepare(&(l3 as u8))?;
        let total_len = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(
            l3,
        ).ok_or(PreSerializeError::LengthTooLarge)?;
        Ok(total_len)
    }
}

impl<'i> Parser<&'i [u8]> for TLVPayloadFmt {
    type PT = TLVMsg<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TLVPayloadFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, payload) = match self.tag {
            MsgTy::TYPE1 => {
                let (n, v) = U8.parse(&rest)?;
                (n, TLVMsg::V1(v))
            },
            MsgTy::TYPE2 => {
                let (n, v) = Fixed::<10>.parse(&rest)?;
                (n, TLVMsg::V2(v))
            },
            MsgTy::TYPE3 => {
                let (n, v) = Named("btc_tx", TxSegwitFmt).parse(&rest)?;
                (n, TLVMsg::V3(v))
            },
            MsgTy::TYPE4 => {
                let (n, v) = Named("btc_tx", TxSegwitFmt).parse(&rest)?;
                (n, TLVMsg::V4(v))
            },
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, payload.deep_view())));
        Ok((n, payload))
    }
}

impl<'i> Serializer<TLVMsg<'i>> for TLVPayloadFmt {
    fn serialize(&self, v: &TLVMsg<'i>, obuf: &mut Vec<u8>) {
        reveal(<TLVPayloadFmt as SpecSerializer>::spec_serialize);
        reveal(<TLVPayloadFmt as Consistency>::consistent);

        let ghost old_obuf = obuf@;
        match (self.tag, v) {
            (MsgTy::TYPE1, TLVMsg::V1(v)) => U8.serialize(v, obuf),
            (MsgTy::TYPE2, TLVMsg::V2(v)) => Fixed::<10>.serialize(*v, obuf),
            (MsgTy::TYPE3, TLVMsg::V3(v)) => TxSegwitFmt.serialize(v, obuf),
            (MsgTy::TYPE4, TLVMsg::V4(v)) => TxSegwitFmt.serialize(v, obuf),
            _ => {},
        }
        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl<'i> Prepare<TLVMsg<'i>> for TLVPayloadFmt {
    fn prepare(&self, v: &TLVMsg<'i>) -> Result<usize, PreSerializeError> {
        reveal(<TLVPayloadFmt as Consistency>::consistent);
        reveal(<TLVPayloadFmt as SpecByteLen>::byte_len);

        match (self.tag, v) {
            (MsgTy::TYPE1, TLVMsg::V1(v)) => U8.prepare(v),
            (MsgTy::TYPE2, TLVMsg::V2(v)) => Fixed::<10>.prepare(v),
            (MsgTy::TYPE3, TLVMsg::V3(v)) => TxSegwitFmt.prepare(v),
            (MsgTy::TYPE4, TLVMsg::V4(v)) => TxSegwitFmt.prepare(v),
            _ => Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
        }
    }
}

} // verus!
