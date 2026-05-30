#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::*;
use vest_lib2::core::exec::input::{InputBuf, InputSlice};
use vest_lib2::core::exec::parser::*;
use vest_lib2::core::exec::serializer::*;
use vest_lib2::core::exec::ParseError;
use vest_lib2::core::exec::{DeepEq, SelfView};
use vest_lib2::core::{proof::*, spec::*};
use vest_lib2::macros::impl_self_view_for;
use vest_lib2::primitives::btcvarint::VarInt;
use vest_lib2::primitives::leb128::ULeb128;
use vstd::prelude::*;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `script`."]
# [derive (Debug , PartialEq , Eq)]
pub struct Script<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier :: ext_equal]
pub struct ScriptSpec {
    pub l: u64,
    pub data: Seq<u8>,
}

pub type ScriptInner = (u64, Seq<u8>);

impl<'i> DeepView for Script<'i> {
    type V = ScriptSpec;

    open spec fn deep_view(&self) -> Self::V {
        ScriptSpec { l: self.l.deep_view(), data: self.data.deep_view() }
    }
}

# [doc = "data type for `txout`."]
# [derive (Debug , PartialEq , Eq)]
pub struct Txout<'i> {
    pub value: u64,
    pub script_pubkey: Script<'i>,
}

# [verifier :: ext_equal]
pub struct TxoutSpec {
    pub value: u64,
    pub script_pubkey: ScriptSpec,
}

pub type TxoutInner = (u64, ScriptSpec);

impl<'i> DeepView for Txout<'i> {
    type V = TxoutSpec;

    open spec fn deep_view(&self) -> Self::V {
        TxoutSpec { value: self.value.deep_view(), script_pubkey: self.script_pubkey.deep_view() }
    }
}

# [doc = "data type for `outpoint`."]
# [derive (Debug , PartialEq , Eq)]
pub struct Outpoint<'i> {
    pub hash: &'i [u8],
    pub index: u32,
}

# [verifier :: ext_equal]
pub struct OutpointSpec {
    pub hash: Seq<u8>,
    pub index: u32,
}

pub type OutpointInner = (Seq<u8>, u32);

impl<'i> DeepView for Outpoint<'i> {
    type V = OutpointSpec;

    open spec fn deep_view(&self) -> Self::V {
        OutpointSpec { hash: self.hash.deep_view(), index: self.index.deep_view() }
    }
}

# [doc = "data type for `script_sig`."]
# [derive (Debug , PartialEq , Eq)]
pub struct ScriptSig<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier :: ext_equal]
pub struct ScriptSigSpec {
    pub l: u64,
    pub data: Seq<u8>,
}

pub type ScriptSigInner = (u64, Seq<u8>);

impl<'i> DeepView for ScriptSig<'i> {
    type V = ScriptSigSpec;

    open spec fn deep_view(&self) -> Self::V {
        ScriptSigSpec { l: self.l.deep_view(), data: self.data.deep_view() }
    }
}

# [doc = "data type for `witness_component`."]
# [derive (Debug , PartialEq , Eq)]
pub struct WitnessComponent<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier :: ext_equal]
pub struct WitnessComponentSpec {
    pub l: u64,
    pub data: Seq<u8>,
}

pub type WitnessComponentInner = (u64, Seq<u8>);

impl<'i> DeepView for WitnessComponent<'i> {
    type V = WitnessComponentSpec;

    open spec fn deep_view(&self) -> Self::V {
        WitnessComponentSpec { l: self.l.deep_view(), data: self.data.deep_view() }
    }
}

# [doc = "data type for `witness`."]
# [derive (Debug , PartialEq , Eq)]
pub struct Witness<'i> {
    pub count: u64,
    pub data: Vec<WitnessComponent<'i>>,
}

# [verifier :: ext_equal]
pub struct WitnessSpec {
    pub count: u64,
    pub data: Seq<WitnessComponentSpec>,
}

pub type WitnessInner = (u64, Seq<WitnessComponentSpec>);

impl<'i> DeepView for Witness<'i> {
    type V = WitnessSpec;

    open spec fn deep_view(&self) -> Self::V {
        WitnessSpec { count: self.count.deep_view(), data: self.data.deep_view() }
    }
}

# [doc = "data type for `txin`."]
# [derive (Debug , PartialEq , Eq)]
pub struct Txin<'i> {
    pub previous_output: Outpoint<'i>,
    pub script_sig: ScriptSig<'i>,
    pub sequence: u32,
}

# [verifier :: ext_equal]
pub struct TxinSpec {
    pub previous_output: OutpointSpec,
    pub script_sig: ScriptSigSpec,
    pub sequence: u32,
}

pub type TxinInner = (OutpointSpec, (ScriptSigSpec, u32));

impl<'i> DeepView for Txin<'i> {
    type V = TxinSpec;

    open spec fn deep_view(&self) -> Self::V {
        TxinSpec {
            previous_output: self.previous_output.deep_view(),
            script_sig: self.script_sig.deep_view(),
            sequence: self.sequence.deep_view(),
        }
    }
}

# [doc = "data type for `lock_time`."]
# [derive (Debug , PartialEq , Eq)]
pub enum LockTime {
    BlockNo(u32),
    Timestamp(u32),
}

# [verifier :: ext_equal]
pub enum LockTimeSpec {
    BlockNo(u32),
    Timestamp(u32),
}

pub type LockTimeInner = Sum<u32, u32>;

impl DeepView for LockTime {
    type V = LockTimeSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            LockTime::BlockNo(v) => LockTimeSpec::BlockNo(v.deep_view()),
            LockTime::Timestamp(v) => LockTimeSpec::Timestamp(v.deep_view()),
        }
    }
}

# [doc = "data type for `tx_nonsegwit`."]
# [derive (Debug , PartialEq , Eq)]
pub struct TxNonsegwit<'i> {
    pub txins: Vec<Txin<'i>>,
    pub txout_count: u64,
    pub txouts: Vec<Txout<'i>>,
    pub lock_time: LockTime,
}

# [verifier :: ext_equal]
pub struct TxNonsegwitSpec {
    pub txins: Seq<TxinSpec>,
    pub txout_count: u64,
    pub txouts: Seq<TxoutSpec>,
    pub lock_time: LockTimeSpec,
}

pub type TxNonsegwitInner = (Seq<TxinSpec>, (u64, (Seq<TxoutSpec>, LockTimeSpec)));

impl<'i> DeepView for TxNonsegwit<'i> {
    type V = TxNonsegwitSpec;

    open spec fn deep_view(&self) -> Self::V {
        TxNonsegwitSpec {
            txins: self.txins.deep_view(),
            txout_count: self.txout_count.deep_view(),
            txouts: self.txouts.deep_view(),
            lock_time: self.lock_time.deep_view(),
        }
    }
}

# [doc = "data type for `tx_segwit`."]
# [derive (Debug , PartialEq , Eq)]
pub struct TxSegwit<'i> {
    pub flag: u8,
    pub txin_count: u64,
    pub txins: Vec<Txin<'i>>,
    pub txout_count: u64,
    pub txouts: Vec<Txout<'i>>,
    pub witness: Vec<Witness<'i>>,
    pub lock_time: LockTime,
}

# [verifier :: ext_equal]
pub struct TxSegwitSpec {
    pub flag: u8,
    pub txin_count: u64,
    pub txins: Seq<TxinSpec>,
    pub txout_count: u64,
    pub txouts: Seq<TxoutSpec>,
    pub witness: Seq<WitnessSpec>,
    pub lock_time: LockTimeSpec,
}

pub type TxSegwitInner = (
    u8,
    (u64, (Seq<TxinSpec>, (u64, (Seq<TxoutSpec>, (Seq<WitnessSpec>, LockTimeSpec))))),
);

impl<'i> DeepView for TxSegwit<'i> {
    type V = TxSegwitSpec;

    open spec fn deep_view(&self) -> Self::V {
        TxSegwitSpec {
            flag: self.flag.deep_view(),
            txin_count: self.txin_count.deep_view(),
            txins: self.txins.deep_view(),
            txout_count: self.txout_count.deep_view(),
            txouts: self.txouts.deep_view(),
            witness: self.witness.deep_view(),
            lock_time: self.lock_time.deep_view(),
        }
    }
}

# [doc = "data type for `tx_rem`."]
# [derive (Debug , PartialEq , Eq)]
pub enum TxRem<'i> {
    Variant1(TxSegwit<'i>),
    Default(TxNonsegwit<'i>),
}

# [verifier :: ext_equal]
pub enum TxRemSpec {
    Variant1(TxSegwitSpec),
    Default(TxNonsegwitSpec),
}

pub type TxRemInner = Sum<TxSegwitSpec, TxNonsegwitSpec>;

impl<'i> DeepView for TxRem<'i> {
    type V = TxRemSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            TxRem::Variant1(v) => TxRemSpec::Variant1(v.deep_view()),
            TxRem::Default(v) => TxRemSpec::Default(v.deep_view()),
        }
    }
}

# [doc = "data type for `tx`."]
# [derive (Debug , PartialEq , Eq)]
pub struct Tx<'i> {
    pub version: u32,
    pub txin_count: u64,
    pub rem: TxRem<'i>,
}

# [verifier :: ext_equal]
pub struct TxSpec {
    pub version: u32,
    pub txin_count: u64,
    pub rem: TxRemSpec,
}

pub type TxInner = (u32, (u64, TxRemSpec));

impl<'i> DeepView for Tx<'i> {
    type V = TxSpec;

    open spec fn deep_view(&self) -> Self::V {
        TxSpec {
            version: self.version.deep_view(),
            txin_count: self.txin_count.deep_view(),
            rem: self.rem.deep_view(),
        }
    }
}

# [doc = "data type for `block`."]
# [derive (Debug , PartialEq , Eq)]
pub struct Block<'i> {
    pub version: u32,
    pub prev_block: &'i [u8],
    pub merkle_root: &'i [u8],
    pub timestamp: u32,
    pub bits: u32,
    pub nonce: u32,
    pub tx_count: u64,
    pub txs: Vec<Tx<'i>>,
}

# [verifier :: ext_equal]
pub struct BlockSpec {
    pub version: u32,
    pub prev_block: Seq<u8>,
    pub merkle_root: Seq<u8>,
    pub timestamp: u32,
    pub bits: u32,
    pub nonce: u32,
    pub tx_count: u64,
    pub txs: Seq<TxSpec>,
}

pub type BlockInner = (u32, (Seq<u8>, (Seq<u8>, (u32, (u32, (u32, (u64, Seq<TxSpec>)))))));

impl<'i> DeepView for Block<'i> {
    type V = BlockSpec;

    open spec fn deep_view(&self) -> Self::V {
        BlockSpec {
            version: self.version.deep_view(),
            prev_block: self.prev_block.deep_view(),
            merkle_root: self.merkle_root.deep_view(),
            timestamp: self.timestamp.deep_view(),
            bits: self.bits.deep_view(),
            nonce: self.nonce.deep_view(),
            tx_count: self.tx_count.deep_view(),
            txs: self.txs.deep_view(),
        }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `script`."]
pub struct ScriptFmt;

pub type ScriptFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> Varied<usize>>,
        FnSpecMapper<ScriptInner, ScriptSpec>,
    >,
>;

# [doc = "specification constructor for `script`."]
pub open spec fn script_fmt() -> ScriptFmtSpec {
    Named(
        "script",
        Mapped {
            inner: Bind(VarInt::<true>, |l: u64| Varied((l as usize))),
            mapper: (
                |parsed: ScriptInner| -> ScriptSpec
                    {
                        let (l, data) = parsed;
                        ScriptSpec { l, data }
                    },
                |value: ScriptSpec| -> ScriptInner
                    {
                        let ScriptSpec { l, data } = value;
                        (l, data)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `txout`."]
pub struct TxoutFmt;

pub type TxoutFmtSpec = Named<Mapped<Pair<U64Le, ScriptFmt>, FnSpecMapper<TxoutInner, TxoutSpec>>>;

# [doc = "specification constructor for `txout`."]
pub open spec fn txout_fmt() -> TxoutFmtSpec {
    Named(
        "txout",
        Mapped {
            inner: Pair(U64Le, ScriptFmt),
            mapper: (
                |parsed: TxoutInner| -> TxoutSpec
                    {
                        let (value, script_pubkey) = parsed;
                        TxoutSpec { value, script_pubkey }
                    },
                |value: TxoutSpec| -> TxoutInner
                    {
                        let TxoutSpec { value, script_pubkey } = value;
                        (value, script_pubkey)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `outpoint`."]
pub struct OutpointFmt;

pub type OutpointFmtSpec = Named<
    Mapped<Pair<Fixed<32>, U32Le>, FnSpecMapper<OutpointInner, OutpointSpec>>,
>;

# [doc = "specification constructor for `outpoint`."]
pub open spec fn outpoint_fmt() -> OutpointFmtSpec {
    Named(
        "outpoint",
        Mapped {
            inner: Pair(Fixed::<32>, U32Le),
            mapper: (
                |parsed: OutpointInner| -> OutpointSpec
                    {
                        let (hash, index) = parsed;
                        OutpointSpec { hash, index }
                    },
                |value: OutpointSpec| -> OutpointInner
                    {
                        let OutpointSpec { hash, index } = value;
                        (hash, index)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `script_sig`."]
pub struct ScriptSigFmt;

pub type ScriptSigFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> Varied<usize>>,
        FnSpecMapper<ScriptSigInner, ScriptSigSpec>,
    >,
>;

# [doc = "specification constructor for `script_sig`."]
pub open spec fn script_sig_fmt() -> ScriptSigFmtSpec {
    Named(
        "script_sig",
        Mapped {
            inner: Bind(VarInt::<true>, |l: u64| Varied((l as usize))),
            mapper: (
                |parsed: ScriptSigInner| -> ScriptSigSpec
                    {
                        let (l, data) = parsed;
                        ScriptSigSpec { l, data }
                    },
                |value: ScriptSigSpec| -> ScriptSigInner
                    {
                        let ScriptSigSpec { l, data } = value;
                        (l, data)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `witness_component`."]
pub struct WitnessComponentFmt;

pub type WitnessComponentFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> Varied<usize>>,
        FnSpecMapper<WitnessComponentInner, WitnessComponentSpec>,
    >,
>;

# [doc = "specification constructor for `witness_component`."]
pub open spec fn witness_component_fmt() -> WitnessComponentFmtSpec {
    Named(
        "witness_component",
        Mapped {
            inner: Bind(VarInt::<true>, |l: u64| Varied((l as usize))),
            mapper: (
                |parsed: WitnessComponentInner| -> WitnessComponentSpec
                    {
                        let (l, data) = parsed;
                        WitnessComponentSpec { l, data }
                    },
                |value: WitnessComponentSpec| -> WitnessComponentInner
                    {
                        let WitnessComponentSpec { l, data } = value;
                        (l, data)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `witness`."]
pub struct WitnessFmt;

pub type WitnessFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> RepeatN<WitnessComponentFmt, usize>>,
        FnSpecMapper<WitnessInner, WitnessSpec>,
    >,
>;

# [doc = "specification constructor for `witness`."]
pub open spec fn witness_fmt() -> WitnessFmtSpec {
    Named(
        "witness",
        Mapped {
            inner: Bind(
                VarInt::<true>,
                |count: u64| RepeatN((count as usize), WitnessComponentFmt),
            ),
            mapper: (
                |parsed: WitnessInner| -> WitnessSpec
                    {
                        let (count, data) = parsed;
                        WitnessSpec { count, data }
                    },
                |value: WitnessSpec| -> WitnessInner
                    {
                        let WitnessSpec { count, data } = value;
                        (count, data)
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `txin`."]
pub struct TxinFmt;

pub type TxinFmtSpec = Named<
    Mapped<Pair<OutpointFmt, Pair<ScriptSigFmt, U32Le>>, FnSpecMapper<TxinInner, TxinSpec>>,
>;

# [doc = "specification constructor for `txin`."]
pub open spec fn txin_fmt() -> TxinFmtSpec {
    Named(
        "txin",
        Mapped {
            inner: Pair(OutpointFmt, Pair(ScriptSigFmt, U32Le)),
            mapper: (
                |parsed: TxinInner| -> TxinSpec
                    {
                        let (previous_output, (script_sig, sequence)) = parsed;
                        TxinSpec { previous_output, script_sig, sequence }
                    },
                |value: TxinSpec| -> TxinInner
                    {
                        let TxinSpec { previous_output, script_sig, sequence } = value;
                        (previous_output, (script_sig, sequence))
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `lock_time`."]
pub struct LockTimeFmt;

pub type LockTimeFmtSpec = Named<
    Mapped<
        Choice<Refined<U32Le, PredFnSpec<u32>>, Refined<U32Le, PredFnSpec<u32>>>,
        FnSpecMapper<LockTimeInner, LockTimeSpec>,
    >,
>;

# [doc = "specification constructor for `lock_time`."]
pub open spec fn lock_time_fmt() -> LockTimeFmtSpec {
    Named(
        "lock_time",
        Mapped {
            inner: Choice(
                Refined(U32Le, |x: u32| x >= 0 && x <= 499999999),
                Refined(U32Le, |x: u32| x >= 500000000),
            ),
            mapper: (
                |parsed: LockTimeInner| -> LockTimeSpec
                    {
                        match parsed {
                            Sum::Inl(v) => LockTimeSpec::BlockNo(v),
                            Sum::Inr(v) => LockTimeSpec::Timestamp(v),
                        }
                    },
                |value: LockTimeSpec| -> LockTimeInner
                    {
                        match value {
                            LockTimeSpec::BlockNo(v) => Sum::Inl(v),
                            LockTimeSpec::Timestamp(v) => Sum::Inr(v),
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `tx_nonsegwit`."]
pub struct TxNonsegwitFmt {
    pub txin_count: u64,
}

pub type TxNonsegwitFmtSpec = Named<
    Mapped<
        Pair<
            RepeatN<TxinFmt, usize>,
            Bind<VarInt<true>, spec_fn(u64) -> Pair<RepeatN<TxoutFmt, usize>, LockTimeFmt>>,
        >,
        FnSpecMapper<TxNonsegwitInner, TxNonsegwitSpec>,
    >,
>;

# [doc = "specification constructor for `tx_nonsegwit`."]
pub open spec fn tx_nonsegwit_fmt(txin_count: u64) -> TxNonsegwitFmtSpec {
    Named(
        "tx_nonsegwit",
        Mapped {
            inner: Pair(
                RepeatN((txin_count as usize), TxinFmt),
                Bind(
                    VarInt::<true>,
                    |txout_count: u64| Pair(RepeatN((txout_count as usize), TxoutFmt), LockTimeFmt),
                ),
            ),
            mapper: (
                |parsed: TxNonsegwitInner| -> TxNonsegwitSpec
                    {
                        let (txins, (txout_count, (txouts, lock_time))) = parsed;
                        TxNonsegwitSpec { txins, txout_count, txouts, lock_time }
                    },
                |value: TxNonsegwitSpec| -> TxNonsegwitInner
                    {
                        let TxNonsegwitSpec { txins, txout_count, txouts, lock_time } = value;
                        (txins, (txout_count, (txouts, lock_time)))
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `tx_segwit`."]
pub struct TxSegwitFmt;

pub type TxSegwitFmtSpec = Named<
    Mapped<
        Pair<
            Const<U8, u8>,
            Bind<
                VarInt<true>,
                spec_fn(u64) -> Pair<
                    RepeatN<TxinFmt, usize>,
                    Bind<
                        VarInt<true>,
                        spec_fn(u64) -> Pair<
                            RepeatN<TxoutFmt, usize>,
                            Pair<RepeatN<WitnessFmt, usize>, LockTimeFmt>,
                        >,
                    >,
                >,
            >,
        >,
        FnSpecMapper<TxSegwitInner, TxSegwitSpec>,
    >,
>;

# [doc = "specification constructor for `tx_segwit`."]
pub open spec fn tx_segwit_fmt() -> TxSegwitFmtSpec {
    Named(
        "tx_segwit",
        Mapped {
            inner: Pair(
                Const(U8, 1),
                Bind(
                    VarInt::<true>,
                    |txin_count: u64|
                        Pair(
                            RepeatN((txin_count as usize), TxinFmt),
                            Bind(
                                VarInt::<true>,
                                |txout_count: u64|
                                    Pair(
                                        RepeatN((txout_count as usize), TxoutFmt),
                                        Pair(
                                            RepeatN((txin_count as usize), WitnessFmt),
                                            LockTimeFmt,
                                        ),
                                    ),
                            ),
                        ),
                ),
            ),
            mapper: (
                |parsed: TxSegwitInner| -> TxSegwitSpec
                    {
                        let (
                            flag,
                            (txin_count, (txins, (txout_count, (txouts, (witness, lock_time))))),
                        ) = parsed;
                        TxSegwitSpec {
                            flag,
                            txin_count,
                            txins,
                            txout_count,
                            txouts,
                            witness,
                            lock_time,
                        }
                    },
                |value: TxSegwitSpec| -> TxSegwitInner
                    {
                        let TxSegwitSpec {
                            flag,
                            txin_count,
                            txins,
                            txout_count,
                            txouts,
                            witness,
                            lock_time,
                        } = value;
                        (flag, (txin_count, (txins, (txout_count, (txouts, (witness, lock_time))))))
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `tx_rem`."]
pub struct TxRemFmt {
    pub txin_count: u64,
}

pub type TxRemFmtSpec = Named<
    Mapped<Sum<TxSegwitFmt, TxNonsegwitFmt>, FnSpecMapper<TxRemInner, TxRemSpec>>,
>;

# [doc = "specification constructor for `tx_rem`."]
pub open spec fn tx_rem_fmt(txin_count: u64) -> TxRemFmtSpec {
    Named(
        "tx_rem",
        Mapped {
            inner: match txin_count {
                0 => Sum::Inl(TxSegwitFmt),
                _ => Sum::Inr(TxNonsegwitFmt { txin_count }),
            },
            mapper: (
                |parsed: TxRemInner| -> TxRemSpec
                    {
                        match parsed {
                            Sum::Inl(v) => TxRemSpec::Variant1(v),
                            Sum::Inr(v) => TxRemSpec::Default(v),
                        }
                    },
                |value: TxRemSpec| -> TxRemInner
                    {
                        match value {
                            TxRemSpec::Variant1(v) => Sum::Inl(v),
                            TxRemSpec::Default(v) => Sum::Inr(v),
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `tx`."]
pub struct TxFmt;

pub type TxFmtSpec = Named<
    Mapped<
        Pair<U32Le, Bind<VarInt<true>, spec_fn(u64) -> TxRemFmt>>,
        FnSpecMapper<TxInner, TxSpec>,
    >,
>;

# [doc = "specification constructor for `tx`."]
pub open spec fn tx_fmt() -> TxFmtSpec {
    Named(
        "tx",
        Mapped {
            inner: Pair(U32Le, Bind(VarInt::<true>, |txin_count: u64| TxRemFmt { txin_count })),
            mapper: (
                |parsed: TxInner| -> TxSpec
                    {
                        let (version, (txin_count, rem)) = parsed;
                        TxSpec { version, txin_count, rem }
                    },
                |value: TxSpec| -> TxInner
                    {
                        let TxSpec { version, txin_count, rem } = value;
                        (version, (txin_count, rem))
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `block`."]
pub struct BlockFmt;

pub type BlockFmtSpec = Named<
    Mapped<
        Pair<
            U32Le,
            Pair<
                Fixed<32>,
                Pair<
                    Fixed<32>,
                    Pair<
                        U32Le,
                        Pair<
                            U32Le,
                            Pair<U32Le, Bind<VarInt<true>, spec_fn(u64) -> RepeatN<TxFmt, usize>>>,
                        >,
                    >,
                >,
            >,
        >,
        FnSpecMapper<BlockInner, BlockSpec>,
    >,
>;

# [doc = "specification constructor for `block`."]
pub open spec fn block_fmt() -> BlockFmtSpec {
    Named(
        "block",
        Mapped {
            inner: Pair(
                U32Le,
                Pair(
                    Fixed::<32>,
                    Pair(
                        Fixed::<32>,
                        Pair(
                            U32Le,
                            Pair(
                                U32Le,
                                Pair(
                                    U32Le,
                                    Bind(
                                        VarInt::<true>,
                                        |tx_count: u64| RepeatN((tx_count as usize), TxFmt),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            mapper: (
                |parsed: BlockInner| -> BlockSpec
                    {
                        let (
                            version,
                            (
                                prev_block,
                                (merkle_root, (timestamp, (bits, (nonce, (tx_count, txs))))),
                            ),
                        ) = parsed;
                        BlockSpec {
                            version,
                            prev_block,
                            merkle_root,
                            timestamp,
                            bits,
                            nonce,
                            tx_count,
                            txs,
                        }
                    },
                |value: BlockSpec| -> BlockInner
                    {
                        let BlockSpec {
                            version,
                            prev_block,
                            merkle_root,
                            timestamp,
                            bits,
                            nonce,
                            tx_count,
                            txs,
                        } = value;
                        (
                            version,
                            (
                                prev_block,
                                (merkle_root, (timestamp, (bits, (nonce, (tx_count, txs))))),
                            ),
                        )
                    },
            ),
        },
    )
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ScriptFmt {
        type PVal = ScriptSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            script_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for ScriptFmt {
        type Val = ScriptSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            script_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for ScriptFmt {
        type SValue = ScriptSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            script_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ScriptFmt {
        type SVal = ScriptSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            script_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for ScriptFmt {
        type T = ScriptSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            script_fmt().byte_len(v)
        }
    }

    impl SpecParser for TxoutFmt {
        type PVal = TxoutSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            txout_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for TxoutFmt {
        type Val = TxoutSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            txout_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for TxoutFmt {
        type SValue = TxoutSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            txout_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxoutFmt {
        type SVal = TxoutSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            txout_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxoutFmt {
        type T = TxoutSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            txout_fmt().byte_len(v)
        }
    }

    impl SpecParser for OutpointFmt {
        type PVal = OutpointSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            outpoint_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for OutpointFmt {
        type Val = OutpointSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            outpoint_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for OutpointFmt {
        type SValue = OutpointSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            outpoint_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OutpointFmt {
        type SVal = OutpointSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            outpoint_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for OutpointFmt {
        type T = OutpointSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            outpoint_fmt().byte_len(v)
        }
    }

    impl SpecParser for ScriptSigFmt {
        type PVal = ScriptSigSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            script_sig_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for ScriptSigFmt {
        type Val = ScriptSigSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            script_sig_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for ScriptSigFmt {
        type SValue = ScriptSigSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            script_sig_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ScriptSigFmt {
        type SVal = ScriptSigSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            script_sig_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for ScriptSigFmt {
        type T = ScriptSigSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            script_sig_fmt().byte_len(v)
        }
    }

    impl SpecParser for WitnessComponentFmt {
        type PVal = WitnessComponentSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            witness_component_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for WitnessComponentFmt {
        type Val = WitnessComponentSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            witness_component_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for WitnessComponentFmt {
        type SValue = WitnessComponentSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            witness_component_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for WitnessComponentFmt {
        type SVal = WitnessComponentSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            witness_component_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for WitnessComponentFmt {
        type T = WitnessComponentSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            witness_component_fmt().byte_len(v)
        }
    }

    impl SpecParser for WitnessFmt {
        type PVal = WitnessSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            witness_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for WitnessFmt {
        type Val = WitnessSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            witness_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for WitnessFmt {
        type SValue = WitnessSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            witness_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for WitnessFmt {
        type SVal = WitnessSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            witness_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for WitnessFmt {
        type T = WitnessSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            witness_fmt().byte_len(v)
        }
    }

    impl SpecParser for TxinFmt {
        type PVal = TxinSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            txin_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for TxinFmt {
        type Val = TxinSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            txin_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for TxinFmt {
        type SValue = TxinSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            txin_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxinFmt {
        type SVal = TxinSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            txin_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxinFmt {
        type T = TxinSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            txin_fmt().byte_len(v)
        }
    }

    impl SpecParser for LockTimeFmt {
        type PVal = LockTimeSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            lock_time_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for LockTimeFmt {
        type Val = LockTimeSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            lock_time_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for LockTimeFmt {
        type SValue = LockTimeSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            lock_time_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for LockTimeFmt {
        type SVal = LockTimeSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            lock_time_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for LockTimeFmt {
        type T = LockTimeSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            lock_time_fmt().byte_len(v)
        }
    }

    impl SpecParser for TxNonsegwitFmt {
        type PVal = TxNonsegwitSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            tx_nonsegwit_fmt(self.txin_count.deep_view()).spec_parse(ibuf)
        }
    }

    impl Consistency for TxNonsegwitFmt {
        type Val = TxNonsegwitSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            tx_nonsegwit_fmt(self.txin_count.deep_view()).consistent(v)
        }
    }

    impl SpecSerializerDps for TxNonsegwitFmt {
        type SValue = TxNonsegwitSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            tx_nonsegwit_fmt(self.txin_count.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxNonsegwitFmt {
        type SVal = TxNonsegwitSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            tx_nonsegwit_fmt(self.txin_count.deep_view()).spec_serialize(v)
        }
    }

    impl SpecByteLen for TxNonsegwitFmt {
        type T = TxNonsegwitSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            tx_nonsegwit_fmt(self.txin_count.deep_view()).byte_len(v)
        }
    }

    impl SpecParser for TxSegwitFmt {
        type PVal = TxSegwitSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            tx_segwit_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for TxSegwitFmt {
        type Val = TxSegwitSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            tx_segwit_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for TxSegwitFmt {
        type SValue = TxSegwitSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            tx_segwit_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxSegwitFmt {
        type SVal = TxSegwitSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            tx_segwit_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxSegwitFmt {
        type T = TxSegwitSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            tx_segwit_fmt().byte_len(v)
        }
    }

    impl SpecParser for TxRemFmt {
        type PVal = TxRemSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            tx_rem_fmt(self.txin_count.deep_view()).spec_parse(ibuf)
        }
    }

    impl Consistency for TxRemFmt {
        type Val = TxRemSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            tx_rem_fmt(self.txin_count.deep_view()).consistent(v)
        }
    }

    impl SpecSerializerDps for TxRemFmt {
        type SValue = TxRemSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            tx_rem_fmt(self.txin_count.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxRemFmt {
        type SVal = TxRemSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            tx_rem_fmt(self.txin_count.deep_view()).spec_serialize(v)
        }
    }

    impl SpecByteLen for TxRemFmt {
        type T = TxRemSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            tx_rem_fmt(self.txin_count.deep_view()).byte_len(v)
        }
    }

    impl SpecParser for TxFmt {
        type PVal = TxSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            tx_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for TxFmt {
        type Val = TxSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            tx_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for TxFmt {
        type SValue = TxSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            tx_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxFmt {
        type SVal = TxSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            tx_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxFmt {
        type T = TxSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            tx_fmt().byte_len(v)
        }
    }

    impl SpecParser for BlockFmt {
        type PVal = BlockSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            block_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for BlockFmt {
        type Val = BlockSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            block_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for BlockFmt {
        type SValue = BlockSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            block_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for BlockFmt {
        type SVal = BlockSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            block_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for BlockFmt {
        type T = BlockSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            block_fmt().byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for ScriptFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            script_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ScriptFmt {
        open spec fn productive_inv(&self) -> bool {
            script_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            let fmt = script_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ScriptFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            let fmt = script_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            reveal(<ScriptFmt as Consistency>::consistent);
            let fmt = script_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ScriptFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = script_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            let fmt = script_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ScriptFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ScriptFmt as SpecSerializer>::spec_serialize);
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            let fmt = script_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ScriptFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptFmt as Consistency>::consistent);
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            let fmt = script_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ScriptFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            let fmt = script_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ScriptFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptFmt as SpecSerializer>::spec_serialize);
            let fmt = script_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ScriptFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptFmt as SpecSerializer>::spec_serialize);
            let fmt = script_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxoutFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            txout_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxoutFmt {
        open spec fn productive_inv(&self) -> bool {
            txout_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            let fmt = txout_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxoutFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            let fmt = txout_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            reveal(<TxoutFmt as Consistency>::consistent);
            let fmt = txout_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxoutFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = txout_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            let fmt = txout_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxoutFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxoutFmt as SpecSerializer>::spec_serialize);
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            let fmt = txout_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxoutFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxoutFmt as Consistency>::consistent);
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            let fmt = txout_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxoutFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            let fmt = txout_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxoutFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxoutFmt as SpecSerializer>::spec_serialize);
            let fmt = txout_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxoutFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxoutFmt as SpecSerializer>::spec_serialize);
            let fmt = txout_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for OutpointFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            outpoint_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for OutpointFmt {
        open spec fn productive_inv(&self) -> bool {
            outpoint_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            let fmt = outpoint_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for OutpointFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            let fmt = outpoint_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<OutpointFmt as Consistency>::consistent);
            let fmt = outpoint_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for OutpointFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = outpoint_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            let fmt = outpoint_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for OutpointFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<OutpointFmt as SpecSerializer>::spec_serialize);
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            let fmt = outpoint_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for OutpointFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OutpointFmt as Consistency>::consistent);
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            let fmt = outpoint_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OutpointFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            let fmt = outpoint_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for OutpointFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OutpointFmt as SpecSerializer>::spec_serialize);
            let fmt = outpoint_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for OutpointFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OutpointFmt as SpecSerializer>::spec_serialize);
            let fmt = outpoint_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ScriptSigFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            script_sig_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ScriptSigFmt {
        open spec fn productive_inv(&self) -> bool {
            script_sig_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            let fmt = script_sig_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ScriptSigFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            let fmt = script_sig_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            reveal(<ScriptSigFmt as Consistency>::consistent);
            let fmt = script_sig_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ScriptSigFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = script_sig_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            let fmt = script_sig_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ScriptSigFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ScriptSigFmt as SpecSerializer>::spec_serialize);
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            let fmt = script_sig_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ScriptSigFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptSigFmt as Consistency>::consistent);
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            let fmt = script_sig_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ScriptSigFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            let fmt = script_sig_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ScriptSigFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptSigFmt as SpecSerializer>::spec_serialize);
            let fmt = script_sig_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ScriptSigFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptSigFmt as SpecSerializer>::spec_serialize);
            let fmt = script_sig_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for WitnessComponentFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            witness_component_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for WitnessComponentFmt {
        open spec fn productive_inv(&self) -> bool {
            witness_component_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            let fmt = witness_component_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for WitnessComponentFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            let fmt = witness_component_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            reveal(<WitnessComponentFmt as Consistency>::consistent);
            let fmt = witness_component_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for WitnessComponentFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = witness_component_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            let fmt = witness_component_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for WitnessComponentFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<WitnessComponentFmt as SpecSerializer>::spec_serialize);
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            let fmt = witness_component_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for WitnessComponentFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessComponentFmt as Consistency>::consistent);
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            let fmt = witness_component_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for WitnessComponentFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            let fmt = witness_component_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for WitnessComponentFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessComponentFmt as SpecSerializer>::spec_serialize);
            let fmt = witness_component_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for WitnessComponentFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessComponentFmt as SpecSerializer>::spec_serialize);
            let fmt = witness_component_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for WitnessFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            witness_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for WitnessFmt {
        open spec fn productive_inv(&self) -> bool {
            witness_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            let fmt = witness_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for WitnessFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            let fmt = witness_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            reveal(<WitnessFmt as Consistency>::consistent);
            let fmt = witness_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for WitnessFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = witness_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            let fmt = witness_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for WitnessFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<WitnessFmt as SpecSerializer>::spec_serialize);
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            let fmt = witness_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for WitnessFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessFmt as Consistency>::consistent);
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            let fmt = witness_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for WitnessFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            let fmt = witness_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for WitnessFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessFmt as SpecSerializer>::spec_serialize);
            let fmt = witness_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for WitnessFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessFmt as SpecSerializer>::spec_serialize);
            let fmt = witness_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxinFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            txin_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxinFmt {
        open spec fn productive_inv(&self) -> bool {
            txin_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            let fmt = txin_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxinFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            let fmt = txin_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            reveal(<TxinFmt as Consistency>::consistent);
            let fmt = txin_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxinFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = txin_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            let fmt = txin_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxinFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxinFmt as SpecSerializer>::spec_serialize);
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            let fmt = txin_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxinFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxinFmt as Consistency>::consistent);
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            let fmt = txin_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxinFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            let fmt = txin_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxinFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxinFmt as SpecSerializer>::spec_serialize);
            let fmt = txin_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxinFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxinFmt as SpecSerializer>::spec_serialize);
            let fmt = txin_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for LockTimeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            lock_time_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for LockTimeFmt {
        open spec fn productive_inv(&self) -> bool {
            lock_time_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            let fmt = lock_time_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for LockTimeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            let fmt = lock_time_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            reveal(<LockTimeFmt as Consistency>::consistent);
            let fmt = lock_time_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for LockTimeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = lock_time_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            let fmt = lock_time_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for LockTimeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<LockTimeFmt as SpecSerializer>::spec_serialize);
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            let fmt = lock_time_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for LockTimeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LockTimeFmt as Consistency>::consistent);
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            let fmt = lock_time_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for LockTimeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            let fmt = lock_time_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for LockTimeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LockTimeFmt as SpecSerializer>::spec_serialize);
            let fmt = lock_time_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for LockTimeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LockTimeFmt as SpecSerializer>::spec_serialize);
            let fmt = lock_time_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxNonsegwitFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            tx_nonsegwit_fmt(self.txin_count.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxNonsegwitFmt {
        open spec fn productive_inv(&self) -> bool {
            tx_nonsegwit_fmt(self.txin_count.deep_view()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxNonsegwitFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            reveal(<TxNonsegwitFmt as Consistency>::consistent);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxNonsegwitFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxNonsegwitFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxNonsegwitFmt as SpecSerializer>::spec_serialize);
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxNonsegwitFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxNonsegwitFmt as Consistency>::consistent);
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxNonsegwitFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxNonsegwitFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxNonsegwitFmt as SpecSerializer>::spec_serialize);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxNonsegwitFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxNonsegwitFmt as SpecSerializer>::spec_serialize);
            let fmt = tx_nonsegwit_fmt(self.txin_count.deep_view());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxSegwitFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            tx_segwit_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxSegwitFmt {
        open spec fn productive_inv(&self) -> bool {
            tx_segwit_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            let fmt = tx_segwit_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxSegwitFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            let fmt = tx_segwit_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            reveal(<TxSegwitFmt as Consistency>::consistent);
            let fmt = tx_segwit_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxSegwitFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = tx_segwit_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            let fmt = tx_segwit_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxSegwitFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            let fmt = tx_segwit_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxSegwitFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxSegwitFmt as Consistency>::consistent);
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            let fmt = tx_segwit_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxSegwitFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            let fmt = tx_segwit_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxSegwitFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
            let fmt = tx_segwit_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxSegwitFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
            let fmt = tx_segwit_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxRemFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            tx_rem_fmt(self.txin_count.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxRemFmt {
        open spec fn productive_inv(&self) -> bool {
            tx_rem_fmt(self.txin_count.deep_view()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxRemFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            reveal(<TxRemFmt as Consistency>::consistent);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxRemFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxRemFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxRemFmt as SpecSerializer>::spec_serialize);
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxRemFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxRemFmt as Consistency>::consistent);
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxRemFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxRemFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxRemFmt as SpecSerializer>::spec_serialize);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxRemFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxRemFmt as SpecSerializer>::spec_serialize);
            let fmt = tx_rem_fmt(self.txin_count.deep_view());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            tx_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxFmt {
        open spec fn productive_inv(&self) -> bool {
            tx_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            let fmt = tx_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            reveal(<TxFmt as SpecByteLen>::byte_len);
            let fmt = tx_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            reveal(<TxFmt as Consistency>::consistent);
            let fmt = tx_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = tx_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxFmt as SpecByteLen>::byte_len);
            let fmt = tx_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxFmt as SpecSerializer>::spec_serialize);
            reveal(<TxFmt as SpecByteLen>::byte_len);
            let fmt = tx_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxFmt as Consistency>::consistent);
            reveal(<TxFmt as SpecByteLen>::byte_len);
            let fmt = tx_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            let fmt = tx_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxFmt as SpecSerializer>::spec_serialize);
            let fmt = tx_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxFmt as SpecSerializer>::spec_serialize);
            let fmt = tx_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for BlockFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            block_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for BlockFmt {
        open spec fn productive_inv(&self) -> bool {
            block_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            let fmt = block_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for BlockFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            let fmt = block_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            reveal(<BlockFmt as Consistency>::consistent);
            let fmt = block_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for BlockFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = block_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            let fmt = block_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for BlockFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<BlockFmt as SpecSerializer>::spec_serialize);
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            let fmt = block_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for BlockFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockFmt as Consistency>::consistent);
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            let fmt = block_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for BlockFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            let fmt = block_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for BlockFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockFmt as SpecSerializer>::spec_serialize);
            let fmt = block_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for BlockFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockFmt as SpecSerializer>::spec_serialize);
            let fmt = block_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
impl<'i> Parser<&'i [u8]> for ScriptFmt {
    type PT = Script<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<ScriptFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, l) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, data) = (Varied((l as usize))).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = Script { l, data };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for TxoutFmt {
    type PT = Txout<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TxoutFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, value) = (U64Le).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, script_pubkey) = (ScriptFmt).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = Txout { value, script_pubkey };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for OutpointFmt {
    type PT = Outpoint<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<OutpointFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, hash) = (Fixed::<32>).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, index) = (U32Le).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = Outpoint { hash, index };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for ScriptSigFmt {
    type PT = ScriptSig<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<ScriptSigFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, l) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, data) = (Varied((l as usize))).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = ScriptSig { l, data };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for WitnessComponentFmt {
    type PT = WitnessComponent<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, l) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, data) = (Varied((l as usize))).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = WitnessComponent { l, data };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for WitnessFmt {
    type PT = Witness<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<WitnessFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, count) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, data) = (RepeatN((count as usize), WitnessComponentFmt)).parse(&rest)?;
        let rest = rest.skip(n2);
        let total_n = n1 + n2;
        let final_v = Witness { count, data };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for TxinFmt {
    type PT = Txin<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TxinFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, previous_output) = (OutpointFmt).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, script_sig) = (ScriptSigFmt).parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, sequence) = (U32Le).parse(&rest)?;
        let rest = rest.skip(n3);
        let total_n = n1 + n2 + n3;
        let final_v = Txin { previous_output, script_sig, sequence };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for LockTimeFmt {
    type PT = LockTime;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<LockTimeFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = match (U32Le).parse(&rest) {
            Ok((n, va)) if va >= 0 && va <= 499999999 => Ok((n, LockTime::BlockNo(va))),
            _ => match (U32Le).parse(&rest) {
                Ok((n, va)) if va >= 500000000 => Ok((n, LockTime::Timestamp(va))),
                _ => Err(ParseError::invalid_tag()),
            },
        }?;
        assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
        Ok((n, v))
    }
}

impl<'i> Parser<&'i [u8]> for TxNonsegwitFmt {
    type PT = TxNonsegwit<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, txins) = (RepeatN((self.txin_count as usize), TxinFmt)).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, txout_count) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, txouts) = (RepeatN((txout_count as usize), TxoutFmt)).parse(&rest)?;
        let rest = rest.skip(n3);
        let (n4, lock_time) = (LockTimeFmt).parse(&rest)?;
        let rest = rest.skip(n4);
        let total_n = n1 + n2 + n3 + n4;
        let final_v = TxNonsegwit { txins, txout_count, txouts, lock_time };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for TxSegwitFmt {
    type PT = TxSegwit<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TxSegwitFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, flag) = (Const(U8, 1)).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, txin_count) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, txins) = (RepeatN((txin_count as usize), TxinFmt)).parse(&rest)?;
        let rest = rest.skip(n3);
        let (n4, txout_count) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n4);
        let (n5, txouts) = (RepeatN((txout_count as usize), TxoutFmt)).parse(&rest)?;
        let rest = rest.skip(n5);
        let (n6, witness) = (RepeatN((txin_count as usize), WitnessFmt)).parse(&rest)?;
        let rest = rest.skip(n6);
        let (n7, lock_time) = (LockTimeFmt).parse(&rest)?;
        let rest = rest.skip(n7);
        let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7;
        let final_v = TxSegwit { flag, txin_count, txins, txout_count, txouts, witness, lock_time };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for TxRemFmt {
    type PT = TxRem<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TxRemFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = match self.txin_count {
            0 => {
                let (n, v) = (TxSegwitFmt).parse(&rest)?;
                (n, TxRem::Variant1(v))
            },
            _ => {
                let (n, v) = (TxNonsegwitFmt { txin_count: self.txin_count }).parse(&rest)?;
                (n, TxRem::Default(v))
            },
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
        Ok((n, v))
    }
}

impl<'i> Parser<&'i [u8]> for TxFmt {
    type PT = Tx<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TxFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, version) = (U32Le).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, txin_count) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, rem) = (TxRemFmt { txin_count: txin_count }).parse(&rest)?;
        let rest = rest.skip(n3);
        let total_n = n1 + n2 + n3;
        let final_v = Tx { version, txin_count, rem };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for BlockFmt {
    type PT = Block<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<BlockFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, version) = (U32Le).parse(&rest)?;
        let rest = rest.skip(n1);
        let (n2, prev_block) = (Fixed::<32>).parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, merkle_root) = (Fixed::<32>).parse(&rest)?;
        let rest = rest.skip(n3);
        let (n4, timestamp) = (U32Le).parse(&rest)?;
        let rest = rest.skip(n4);
        let (n5, bits) = (U32Le).parse(&rest)?;
        let rest = rest.skip(n5);
        let (n6, nonce) = (U32Le).parse(&rest)?;
        let rest = rest.skip(n6);
        let (n7, tx_count) = (VarInt::<true>).parse(&rest)?;
        let rest = rest.skip(n7);
        let (n8, txs) = (RepeatN((tx_count as usize), TxFmt)).parse(&rest)?;
        let rest = rest.skip(n8);
        let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8;
        let final_v = Block {
            version,
            prev_block,
            merkle_root,
            timestamp,
            bits,
            nonce,
            tx_count,
            txs,
        };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

} // verus!
