#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::recursive::*;
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
use vest_lib2::Never;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `block`."]
# [derive (Debug, PartialEq, Eq, Clone)]
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

# [verifier::ext_equal]
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

# [doc = "data type for `tx`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct Tx<'i> {
    pub version: u32,
    pub txin_count: u64,
    pub rem: TxRem<'i>,
}

# [verifier::ext_equal]
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

# [doc = "data type for `tx_segwit`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct TxSegwit<'i> {
    pub flag: u8,
    pub txin_count: u64,
    pub txins: Vec<Txin<'i>>,
    pub txout_count: u64,
    pub txouts: Vec<Txout<'i>>,
    pub witness: Vec<Witness<'i>>,
    pub lock_time: LockTime,
}

# [verifier::ext_equal]
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

# [doc = "data type for `witness`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct Witness<'i> {
    pub count: u64,
    pub data: Vec<WitnessComponent<'i>>,
}

# [verifier::ext_equal]
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

# [doc = "data type for `witness_component`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct WitnessComponent<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
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

# [doc = "data type for `tx_nonsegwit`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct TxNonsegwit<'i> {
    pub txins: Vec<Txin<'i>>,
    pub txout_count: u64,
    pub txouts: Vec<Txout<'i>>,
    pub lock_time: LockTime,
}

# [verifier::ext_equal]
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

# [doc = "data type for `lock_time`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum LockTime {
    BlockNo(u32),
    Timestamp(u32),
}

pub type LockTimeSpec = LockTime;

pub type LockTimeInner = Sum<u32, u32>;

impl DeepView for LockTime {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `txout`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Txout<'i> {
    pub value: u64,
    pub script_pubkey: Script<'i>,
}

# [verifier::ext_equal]
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

# [doc = "data type for `script`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Script<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
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

# [doc = "data type for `txin`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Txin<'i> {
    pub previous_output: Outpoint<'i>,
    pub script_sig: ScriptSig<'i>,
    pub sequence: u32,
}

# [verifier::ext_equal]
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

# [doc = "data type for `outpoint`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Outpoint<'i> {
    pub hash: &'i [u8],
    pub index: u32,
}

# [verifier::ext_equal]
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
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct ScriptSig<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
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

# [doc = "data type for `tx_rem`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub enum TxRem<'i> {
    Variant1(TxSegwit<'i>),
    Default(TxNonsegwit<'i>),
}

# [verifier::ext_equal]
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

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `block`."]
# [derive (Clone, Copy)]
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
                            Pair<U32Le, Bind<VarInt<true>, spec_fn(u64) -> RepeatN<TxFmt, u64>>>,
                        >,
                    >,
                >,
            >,
        >,
        FnSpecMapper<BlockInner, BlockSpec>,
    >,
>;

impl BlockFmt {
    # [doc = "specification constructor for `block`."]
    pub open spec fn spec_inner() -> BlockFmtSpec {
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
                                            |tx_count: u64| RepeatN(tx_count, TxFmt),
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
}

# [doc = "named format combinator for `tx`."]
# [derive (Clone, Copy)]
pub struct TxFmt;

pub type TxFmtSpec = Named<
    Mapped<
        Pair<U32Le, Bind<VarInt<true>, spec_fn(u64) -> TxRemFmt>>,
        FnSpecMapper<TxInner, TxSpec>,
    >,
>;

impl TxFmt {
    # [doc = "specification constructor for `tx`."]
    pub open spec fn spec_inner() -> TxFmtSpec {
        Named(
            "tx",
            Mapped {
                inner: Pair(
                    U32Le,
                    Bind(VarInt::<true>, |txin_count: u64| TxRemFmt::spec(txin_count)),
                ),
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
}

# [doc = "named format combinator for `tx_segwit`."]
# [derive (Clone, Copy)]
pub struct TxSegwitFmt;

pub type TxSegwitFmtSpec = Named<
    Mapped<
        Pair<
            Const<U8, u8>,
            Bind<
                VarInt<true>,
                spec_fn(u64) -> Pair<
                    RepeatN<TxinFmt, u64>,
                    Bind<
                        VarInt<true>,
                        spec_fn(u64) -> Pair<
                            RepeatN<TxoutFmt, u64>,
                            Pair<RepeatN<WitnessFmt, u64>, LockTimeFmt>,
                        >,
                    >,
                >,
            >,
        >,
        FnSpecMapper<TxSegwitInner, TxSegwitSpec>,
    >,
>;

impl TxSegwitFmt {
    # [doc = "specification constructor for `tx_segwit`."]
    pub open spec fn spec_inner() -> TxSegwitFmtSpec {
        Named(
            "tx_segwit",
            Mapped {
                inner: Pair(
                    Const(U8, 1),
                    Bind(
                        VarInt::<true>,
                        |txin_count: u64|
                            Pair(
                                RepeatN(txin_count, TxinFmt),
                                Bind(
                                    VarInt::<true>,
                                    |txout_count: u64|
                                        Pair(
                                            RepeatN(txout_count, TxoutFmt),
                                            Pair(RepeatN(txin_count, WitnessFmt), LockTimeFmt),
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
                                (
                                    txin_count,
                                    (txins, (txout_count, (txouts, (witness, lock_time)))),
                                ),
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
                            (
                                flag,
                                (
                                    txin_count,
                                    (txins, (txout_count, (txouts, (witness, lock_time)))),
                                ),
                            )
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `witness`."]
# [derive (Clone, Copy)]
pub struct WitnessFmt;

pub type WitnessFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> RepeatN<WitnessComponentFmt, u64>>,
        FnSpecMapper<WitnessInner, WitnessSpec>,
    >,
>;

impl WitnessFmt {
    # [doc = "specification constructor for `witness`."]
    pub open spec fn spec_inner() -> WitnessFmtSpec {
        Named(
            "witness",
            Mapped {
                inner: Bind(VarInt::<true>, |count: u64| RepeatN(count, WitnessComponentFmt)),
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
}

# [doc = "named format combinator for `witness_component`."]
# [derive (Clone, Copy)]
pub struct WitnessComponentFmt;

pub type WitnessComponentFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> Varied<u64>>,
        FnSpecMapper<WitnessComponentInner, WitnessComponentSpec>,
    >,
>;

impl WitnessComponentFmt {
    # [doc = "specification constructor for `witness_component`."]
    pub open spec fn spec_inner() -> WitnessComponentFmtSpec {
        Named(
            "witness_component",
            Mapped {
                inner: Bind(VarInt::<true>, |l: u64| Varied(l)),
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
}

# [doc = "named format combinator for `tx_nonsegwit`."]
# [derive (Clone, Copy)]
pub struct TxNonsegwitFmt {
    txin_count: u64,
}

impl TxNonsegwitFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn txin_count_spec(&self) -> u64 {
        self.txin_count.deep_view()
    }

    pub closed spec fn spec(txin_count: u64) -> Self {
        TxNonsegwitFmt { txin_count }
    }
}

pub type TxNonsegwitFmtSpec = Named<
    Mapped<
        Pair<
            RepeatN<TxinFmt, u64>,
            Bind<VarInt<true>, spec_fn(u64) -> Pair<RepeatN<TxoutFmt, u64>, LockTimeFmt>>,
        >,
        FnSpecMapper<TxNonsegwitInner, TxNonsegwitSpec>,
    >,
>;

impl TxNonsegwitFmt {
    # [doc = "specification constructor for `tx_nonsegwit`."]
    pub open spec fn spec_inner(txin_count: u64) -> TxNonsegwitFmtSpec {
        Named(
            "tx_nonsegwit",
            Mapped {
                inner: Pair(
                    RepeatN(txin_count, TxinFmt),
                    Bind(
                        VarInt::<true>,
                        |txout_count: u64| Pair(RepeatN(txout_count, TxoutFmt), LockTimeFmt),
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
}

# [doc = "named format combinator for `lock_time`."]
# [derive (Clone, Copy)]
pub struct LockTimeFmt;

pub type LockTimeFmtSpec = Named<
    Mapped<
        Choice<Refined<U32Le, PredFnSpec<u32>>, Refined<U32Le, PredFnSpec<u32>>>,
        FnSpecMapper<LockTimeInner, LockTimeSpec>,
    >,
>;

impl LockTimeFmt {
    # [doc = "specification constructor for `lock_time`."]
    pub open spec fn spec_inner() -> LockTimeFmtSpec {
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
                                L(v) => LockTimeSpec::BlockNo(v),
                                R(v) => LockTimeSpec::Timestamp(v),
                            }
                        },
                    |value: LockTimeSpec| -> LockTimeInner
                        {
                            match value {
                                LockTimeSpec::BlockNo(v) => L(v),
                                LockTimeSpec::Timestamp(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `txout`."]
# [derive (Clone, Copy)]
pub struct TxoutFmt;

pub type TxoutFmtSpec = Named<Mapped<Pair<U64Le, ScriptFmt>, FnSpecMapper<TxoutInner, TxoutSpec>>>;

impl TxoutFmt {
    # [doc = "specification constructor for `txout`."]
    pub open spec fn spec_inner() -> TxoutFmtSpec {
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
}

# [doc = "named format combinator for `script`."]
# [derive (Clone, Copy)]
pub struct ScriptFmt;

pub type ScriptFmtSpec = Named<
    Mapped<Bind<VarInt<true>, spec_fn(u64) -> Varied<u64>>, FnSpecMapper<ScriptInner, ScriptSpec>>,
>;

impl ScriptFmt {
    # [doc = "specification constructor for `script`."]
    pub open spec fn spec_inner() -> ScriptFmtSpec {
        Named(
            "script",
            Mapped {
                inner: Bind(VarInt::<true>, |l: u64| Varied(l)),
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
}

# [doc = "named format combinator for `txin`."]
# [derive (Clone, Copy)]
pub struct TxinFmt;

pub type TxinFmtSpec = Named<
    Mapped<Pair<OutpointFmt, Pair<ScriptSigFmt, U32Le>>, FnSpecMapper<TxinInner, TxinSpec>>,
>;

impl TxinFmt {
    # [doc = "specification constructor for `txin`."]
    pub open spec fn spec_inner() -> TxinFmtSpec {
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
}

# [doc = "named format combinator for `outpoint`."]
# [derive (Clone, Copy)]
pub struct OutpointFmt;

pub type OutpointFmtSpec = Named<
    Mapped<Pair<Fixed<32>, U32Le>, FnSpecMapper<OutpointInner, OutpointSpec>>,
>;

impl OutpointFmt {
    # [doc = "specification constructor for `outpoint`."]
    pub open spec fn spec_inner() -> OutpointFmtSpec {
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
}

# [doc = "named format combinator for `script_sig`."]
# [derive (Clone, Copy)]
pub struct ScriptSigFmt;

pub type ScriptSigFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> Varied<u64>>,
        FnSpecMapper<ScriptSigInner, ScriptSigSpec>,
    >,
>;

impl ScriptSigFmt {
    # [doc = "specification constructor for `script_sig`."]
    pub open spec fn spec_inner() -> ScriptSigFmtSpec {
        Named(
            "script_sig",
            Mapped {
                inner: Bind(VarInt::<true>, |l: u64| Varied(l)),
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
}

# [doc = "named format combinator for `tx_rem`."]
# [derive (Clone, Copy)]
pub struct TxRemFmt {
    txin_count: u64,
}

impl TxRemFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn txin_count_spec(&self) -> u64 {
        self.txin_count.deep_view()
    }

    pub closed spec fn spec(txin_count: u64) -> Self {
        TxRemFmt { txin_count }
    }
}

pub type TxRemFmtSpec = Named<
    Mapped<Sum<TxSegwitFmt, TxNonsegwitFmt>, FnSpecMapper<TxRemInner, TxRemSpec>>,
>;

impl TxRemFmt {
    # [doc = "specification constructor for `tx_rem`."]
    pub open spec fn spec_inner(txin_count: u64) -> TxRemFmtSpec {
        Named(
            "tx_rem",
            Mapped {
                inner: match txin_count {
                    0 => L(TxSegwitFmt),
                    _ => R(TxNonsegwitFmt::spec(txin_count)),
                },
                mapper: (
                    |parsed: TxRemInner| -> TxRemSpec
                        {
                            match parsed {
                                L(v) => TxRemSpec::Variant1(v),
                                R(v) => TxRemSpec::Default(v),
                            }
                        },
                    |value: TxRemSpec| -> TxRemInner
                        {
                            match value {
                                TxRemSpec::Variant1(v) => L(v),
                                TxRemSpec::Default(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for BlockFmt {
        type PVal = BlockSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for BlockFmt {
        type Val = BlockSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for BlockFmt {
        type SValue = BlockSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for BlockFmt {
        type SVal = BlockSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for BlockFmt {
        type T = BlockSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxFmt {
        type PVal = TxSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TxFmt {
        type Val = TxSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TxFmt {
        type SValue = TxSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxFmt {
        type SVal = TxSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxFmt {
        type T = TxSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxSegwitFmt {
        type PVal = TxSegwitSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TxSegwitFmt {
        type Val = TxSegwitSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TxSegwitFmt {
        type SValue = TxSegwitSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxSegwitFmt {
        type SVal = TxSegwitSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxSegwitFmt {
        type T = TxSegwitSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for WitnessFmt {
        type PVal = WitnessSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for WitnessFmt {
        type Val = WitnessSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for WitnessFmt {
        type SValue = WitnessSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for WitnessFmt {
        type SVal = WitnessSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for WitnessFmt {
        type T = WitnessSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for WitnessComponentFmt {
        type PVal = WitnessComponentSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for WitnessComponentFmt {
        type Val = WitnessComponentSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for WitnessComponentFmt {
        type SValue = WitnessComponentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for WitnessComponentFmt {
        type SVal = WitnessComponentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for WitnessComponentFmt {
        type T = WitnessComponentSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxNonsegwitFmt {
        type PVal = TxNonsegwitSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.txin_count_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for TxNonsegwitFmt {
        type Val = TxNonsegwitSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.txin_count_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for TxNonsegwitFmt {
        type SValue = TxNonsegwitSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.txin_count_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxNonsegwitFmt {
        type SVal = TxNonsegwitSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.txin_count_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for TxNonsegwitFmt {
        type T = TxNonsegwitSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.txin_count_spec()).byte_len(v)
        }
    }

    impl SpecParser for LockTimeFmt {
        type PVal = LockTimeSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for LockTimeFmt {
        type Val = LockTimeSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for LockTimeFmt {
        type SValue = LockTimeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for LockTimeFmt {
        type SVal = LockTimeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for LockTimeFmt {
        type T = LockTimeSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxoutFmt {
        type PVal = TxoutSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TxoutFmt {
        type Val = TxoutSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TxoutFmt {
        type SValue = TxoutSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxoutFmt {
        type SVal = TxoutSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxoutFmt {
        type T = TxoutSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ScriptFmt {
        type PVal = ScriptSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ScriptFmt {
        type Val = ScriptSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ScriptFmt {
        type SValue = ScriptSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ScriptFmt {
        type SVal = ScriptSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ScriptFmt {
        type T = ScriptSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxinFmt {
        type PVal = TxinSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TxinFmt {
        type Val = TxinSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TxinFmt {
        type SValue = TxinSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxinFmt {
        type SVal = TxinSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxinFmt {
        type T = TxinSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for OutpointFmt {
        type PVal = OutpointSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for OutpointFmt {
        type Val = OutpointSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for OutpointFmt {
        type SValue = OutpointSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OutpointFmt {
        type SVal = OutpointSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for OutpointFmt {
        type T = OutpointSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ScriptSigFmt {
        type PVal = ScriptSigSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ScriptSigFmt {
        type Val = ScriptSigSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ScriptSigFmt {
        type SValue = ScriptSigSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ScriptSigFmt {
        type SVal = ScriptSigSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ScriptSigFmt {
        type T = ScriptSigSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxRemFmt {
        type PVal = TxRemSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.txin_count_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for TxRemFmt {
        type Val = TxRemSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.txin_count_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for TxRemFmt {
        type SValue = TxRemSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.txin_count_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxRemFmt {
        type SVal = TxRemSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.txin_count_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for TxRemFmt {
        type T = TxRemSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.txin_count_spec()).byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for BlockFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for BlockFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for BlockFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            reveal(<BlockFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for BlockFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for BlockFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<BlockFmt as SpecSerializer>::spec_serialize);
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for BlockFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for BlockFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for BlockFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<BlockFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            reveal(<TxFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            reveal(<TxFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxFmt as SpecSerializer>::spec_serialize);
            reveal(<TxFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxSegwitFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxSegwitFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxSegwitFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            reveal(<TxSegwitFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxSegwitFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxSegwitFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxSegwitFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxSegwitFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxSegwitFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxSegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for WitnessFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for WitnessFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for WitnessFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            reveal(<WitnessFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for WitnessFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for WitnessFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<WitnessFmt as SpecSerializer>::spec_serialize);
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for WitnessFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for WitnessFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for WitnessFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<WitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for WitnessComponentFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for WitnessComponentFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for WitnessComponentFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            reveal(<WitnessComponentFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for WitnessComponentFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for WitnessComponentFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<WitnessComponentFmt as SpecSerializer>::spec_serialize);
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for WitnessComponentFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for WitnessComponentFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessComponentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for WitnessComponentFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<WitnessComponentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessComponentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxNonsegwitFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.txin_count_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxNonsegwitFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.txin_count_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxNonsegwitFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            reveal(<TxNonsegwitFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxNonsegwitFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxNonsegwitFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxNonsegwitFmt as SpecSerializer>::spec_serialize);
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.txin_count_spec());
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
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxNonsegwitFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxNonsegwitFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxNonsegwitFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxNonsegwitFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxNonsegwitFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxNonsegwitFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for LockTimeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for LockTimeFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for LockTimeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            reveal(<LockTimeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for LockTimeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for LockTimeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<LockTimeFmt as SpecSerializer>::spec_serialize);
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for LockTimeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for LockTimeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LockTimeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for LockTimeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<LockTimeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LockTimeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxoutFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxoutFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxoutFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            reveal(<TxoutFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxoutFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxoutFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxoutFmt as SpecSerializer>::spec_serialize);
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxoutFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxoutFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxoutFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxoutFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxoutFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxoutFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ScriptFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ScriptFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ScriptFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            reveal(<ScriptFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ScriptFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ScriptFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ScriptFmt as SpecSerializer>::spec_serialize);
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ScriptFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ScriptFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ScriptFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ScriptFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxinFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxinFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxinFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            reveal(<TxinFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxinFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxinFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxinFmt as SpecSerializer>::spec_serialize);
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxinFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxinFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxinFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxinFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxinFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxinFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for OutpointFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for OutpointFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for OutpointFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<OutpointFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for OutpointFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for OutpointFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<OutpointFmt as SpecSerializer>::spec_serialize);
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OutpointFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for OutpointFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OutpointFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for OutpointFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<OutpointFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OutpointFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ScriptSigFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ScriptSigFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ScriptSigFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            reveal(<ScriptSigFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ScriptSigFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ScriptSigFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ScriptSigFmt as SpecSerializer>::spec_serialize);
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ScriptSigFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ScriptSigFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptSigFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ScriptSigFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ScriptSigFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ScriptSigFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxRemFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.txin_count_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxRemFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.txin_count_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxRemFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            reveal(<TxRemFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxRemFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxRemFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxRemFmt as SpecSerializer>::spec_serialize);
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.txin_count_spec());
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
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxRemFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxRemFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxRemFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxRemFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxRemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxRemFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for BlockFmt {
        type PT = Block<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

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
            let (n8, txs) = (RepeatN(tx_count, TxFmt)).parse(&rest)?;
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

    impl<'i> Serializer<Block<'i>> for BlockFmt {
        fn serialize(&self, v: &Block<'i>, obuf: &mut Vec<u8>) {
            reveal(<BlockFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Block { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs } =
                v;
            U32Le.serialize(version, obuf);
            Fixed::<32>.serialize(prev_block, obuf);
            Fixed::<32>.serialize(merkle_root, obuf);
            U32Le.serialize(timestamp, obuf);
            U32Le.serialize(bits, obuf);
            U32Le.serialize(nonce, obuf);
            VarInt::<true>.serialize(tx_count, obuf);
            RepeatN(tx_count, TxFmt).serialize(txs, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Block<'i>> for BlockFmt {
        fn prepare(&self, v: &Block<'i>) -> Result<usize, PreSerializeError> {
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            let Block { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs } =
                v;
            let l1 = (U32Le).prepare(version)?;
            let l2 = (Fixed::<32>).prepare(prev_block)?;
            let l3 = (Fixed::<32>).prepare(merkle_root)?;
            let l4 = (U32Le).prepare(timestamp)?;
            let l5 = (U32Le).prepare(bits)?;
            let l6 = (U32Le).prepare(nonce)?;
            let l7 = (VarInt::<true>).prepare(tx_count)?;
            let l8 = (RepeatN(tx_count, TxFmt)).prepare(txs)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?.checked_add(l4).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l5).ok_or(PreSerializeError::length_too_large())?.checked_add(l6).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l7).ok_or(PreSerializeError::length_too_large())?.checked_add(l8).ok_or(
                PreSerializeError::length_too_large(),
            )?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxFmt {
        type PT = Tx<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, version) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, txin_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, rem) = (Named("tx_rem", TxRemFmt { txin_count: txin_count })).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Tx { version, txin_count, rem };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Tx<'i>> for TxFmt {
        fn serialize(&self, v: &Tx<'i>, obuf: &mut Vec<u8>) {
            reveal(<TxFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Tx { version, txin_count, rem } = v;
            U32Le.serialize(version, obuf);
            VarInt::<true>.serialize(txin_count, obuf);
            TxRemFmt { txin_count: *txin_count }.serialize(rem, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Tx<'i>> for TxFmt {
        fn prepare(&self, v: &Tx<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxFmt as SpecByteLen>::byte_len);
            let Tx { version, txin_count, rem } = v;
            let l1 = (U32Le).prepare(version)?;
            let l2 = (VarInt::<true>).prepare(txin_count)?;
            let l3 = (Named("tx_rem", TxRemFmt { txin_count: *txin_count })).prepare(rem)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxSegwitFmt {
        type PT = TxSegwit<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, flag) = Const(U8, 1).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, txin_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, txins) = (RepeatN(txin_count, TxinFmt)).parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, txout_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n4);
            let (n5, txouts) = (RepeatN(txout_count, TxoutFmt)).parse(&rest)?;
            let rest = rest.skip(n5);
            let (n6, witness) = (RepeatN(txin_count, WitnessFmt)).parse(&rest)?;
            let rest = rest.skip(n6);
            let (n7, lock_time) = (Named("lock_time", LockTimeFmt)).parse(&rest)?;
            let rest = rest.skip(n7);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7;
            let final_v = TxSegwit {
                flag,
                txin_count,
                txins,
                txout_count,
                txouts,
                witness,
                lock_time,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<TxSegwit<'i>> for TxSegwitFmt {
        fn serialize(&self, v: &TxSegwit<'i>, obuf: &mut Vec<u8>) {
            reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let TxSegwit { flag, txin_count, txins, txout_count, txouts, witness, lock_time } = v;
            Const(U8, 1).serialize(flag, obuf);
            VarInt::<true>.serialize(txin_count, obuf);
            RepeatN(txin_count, TxinFmt).serialize(txins, obuf);
            VarInt::<true>.serialize(txout_count, obuf);
            RepeatN(txout_count, TxoutFmt).serialize(txouts, obuf);
            RepeatN(txin_count, WitnessFmt).serialize(witness, obuf);
            LockTimeFmt.serialize(lock_time, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxSegwit<'i>> for TxSegwitFmt {
        fn prepare(&self, v: &TxSegwit<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            let TxSegwit { flag, txin_count, txins, txout_count, txouts, witness, lock_time } = v;
            let l1 = (Const(U8, 1)).prepare(flag)?;
            let l2 = (VarInt::<true>).prepare(txin_count)?;
            let l3 = (RepeatN(txin_count, TxinFmt)).prepare(txins)?;
            let l4 = (VarInt::<true>).prepare(txout_count)?;
            let l5 = (RepeatN(txout_count, TxoutFmt)).prepare(txouts)?;
            let l6 = (RepeatN(txin_count, WitnessFmt)).prepare(witness)?;
            let l7 = (Named("lock_time", LockTimeFmt)).prepare(lock_time)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?.checked_add(l4).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l5).ok_or(PreSerializeError::length_too_large())?.checked_add(l6).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l7).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for WitnessFmt {
        type PT = Witness<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<WitnessFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, data) = (RepeatN(count, WitnessComponentFmt)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Witness { count, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Witness<'i>> for WitnessFmt {
        fn serialize(&self, v: &Witness<'i>, obuf: &mut Vec<u8>) {
            reveal(<WitnessFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Witness { count, data } = v;
            VarInt::<true>.serialize(count, obuf);
            RepeatN(count, WitnessComponentFmt).serialize(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Witness<'i>> for WitnessFmt {
        fn prepare(&self, v: &Witness<'i>) -> Result<usize, PreSerializeError> {
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            let Witness { count, data } = v;
            let l1 = (VarInt::<true>).prepare(count)?;
            let l2 = (RepeatN(count, WitnessComponentFmt)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for WitnessComponentFmt {
        type PT = WitnessComponent<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, l) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, data) = (Varied(l)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = WitnessComponent { l, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<WitnessComponent<'i>> for WitnessComponentFmt {
        fn serialize(&self, v: &WitnessComponent<'i>, obuf: &mut Vec<u8>) {
            reveal(<WitnessComponentFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let WitnessComponent { l, data } = v;
            VarInt::<true>.serialize(l, obuf);
            Varied(l).serialize(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<WitnessComponent<'i>> for WitnessComponentFmt {
        fn prepare(&self, v: &WitnessComponent<'i>) -> Result<usize, PreSerializeError> {
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            let WitnessComponent { l, data } = v;
            let l1 = (VarInt::<true>).prepare(l)?;
            let l2 = (Varied(l)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxNonsegwitFmt {
        type PT = TxNonsegwit<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, txins) = (RepeatN(self.txin_count, TxinFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, txout_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, txouts) = (RepeatN(txout_count, TxoutFmt)).parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, lock_time) = (Named("lock_time", LockTimeFmt)).parse(&rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = TxNonsegwit { txins, txout_count, txouts, lock_time };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<TxNonsegwit<'i>> for TxNonsegwitFmt {
        fn serialize(&self, v: &TxNonsegwit<'i>, obuf: &mut Vec<u8>) {
            reveal(<TxNonsegwitFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let TxNonsegwit { txins, txout_count, txouts, lock_time } = v;
            RepeatN(self.txin_count, TxinFmt).serialize(txins, obuf);
            VarInt::<true>.serialize(txout_count, obuf);
            RepeatN(txout_count, TxoutFmt).serialize(txouts, obuf);
            LockTimeFmt.serialize(lock_time, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxNonsegwit<'i>> for TxNonsegwitFmt {
        fn prepare(&self, v: &TxNonsegwit<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let TxNonsegwit { txins, txout_count, txouts, lock_time } = v;
            let l1 = (RepeatN(self.txin_count, TxinFmt)).prepare(txins)?;
            let l2 = (VarInt::<true>).prepare(txout_count)?;
            let l3 = (RepeatN(txout_count, TxoutFmt)).prepare(txouts)?;
            let l4 = (Named("lock_time", LockTimeFmt)).prepare(lock_time)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?.checked_add(l4).ok_or(
                PreSerializeError::length_too_large(),
            )?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for LockTimeFmt {
        type PT = LockTime;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U32Le).parse(&rest) {
                Ok((n, va)) if va >= 0 && va <= 499999999 => { Ok((n, LockTime::BlockNo(va))) },
                _ => match (U32Le).parse(&rest) {
                    Ok((n, va)) if va >= 500000000 => { Ok((n, LockTime::Timestamp(va))) },
                    _ => Err(ParseError::invalid_choice()),
                },
            }?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<LockTime> for LockTimeFmt {
        fn serialize(&self, v: &LockTime, obuf: &mut Vec<u8>) {
            reveal(<LockTimeFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            match v {
                LockTime::BlockNo(v) => {
                    (U32Le).serialize(v, obuf);
                },
                LockTime::Timestamp(v) => {
                    (U32Le).serialize(v, obuf);
                },
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<LockTime> for LockTimeFmt {
        fn prepare(&self, v: &LockTime) -> Result<usize, PreSerializeError> {
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            match v {
                LockTime::BlockNo(v) => {
                    if !(*v >= 0 && *v <= 499999999) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U32Le).prepare(v)
                    }
                },
                LockTime::Timestamp(v) => {
                    if !(*v >= 500000000) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U32Le).prepare(v)
                    }
                },
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for TxoutFmt {
        type PT = Txout<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxoutFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (U64Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, script_pubkey) = (Named("script", ScriptFmt)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Txout { value, script_pubkey };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Txout<'i>> for TxoutFmt {
        fn serialize(&self, v: &Txout<'i>, obuf: &mut Vec<u8>) {
            reveal(<TxoutFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Txout { value, script_pubkey } = v;
            U64Le.serialize(value, obuf);
            ScriptFmt.serialize(script_pubkey, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Txout<'i>> for TxoutFmt {
        fn prepare(&self, v: &Txout<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            let Txout { value, script_pubkey } = v;
            let l1 = (U64Le).prepare(value)?;
            let l2 = (Named("script", ScriptFmt)).prepare(script_pubkey)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for ScriptFmt {
        type PT = Script<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ScriptFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, l) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, data) = (Varied(l)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Script { l, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Script<'i>> for ScriptFmt {
        fn serialize(&self, v: &Script<'i>, obuf: &mut Vec<u8>) {
            reveal(<ScriptFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Script { l, data } = v;
            VarInt::<true>.serialize(l, obuf);
            Varied(l).serialize(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Script<'i>> for ScriptFmt {
        fn prepare(&self, v: &Script<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            let Script { l, data } = v;
            let l1 = (VarInt::<true>).prepare(l)?;
            let l2 = (Varied(l)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxinFmt {
        type PT = Txin<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxinFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, previous_output) = (Named("outpoint", OutpointFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, script_sig) = (Named("script_sig", ScriptSigFmt)).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, sequence) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Txin { previous_output, script_sig, sequence };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Txin<'i>> for TxinFmt {
        fn serialize(&self, v: &Txin<'i>, obuf: &mut Vec<u8>) {
            reveal(<TxinFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Txin { previous_output, script_sig, sequence } = v;
            OutpointFmt.serialize(previous_output, obuf);
            ScriptSigFmt.serialize(script_sig, obuf);
            U32Le.serialize(sequence, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Txin<'i>> for TxinFmt {
        fn prepare(&self, v: &Txin<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            let Txin { previous_output, script_sig, sequence } = v;
            let l1 = (Named("outpoint", OutpointFmt)).prepare(previous_output)?;
            let l2 = (Named("script_sig", ScriptSigFmt)).prepare(script_sig)?;
            let l3 = (U32Le).prepare(sequence)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for OutpointFmt {
        type PT = Outpoint<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

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

    impl<'i> Serializer<Outpoint<'i>> for OutpointFmt {
        fn serialize(&self, v: &Outpoint<'i>, obuf: &mut Vec<u8>) {
            reveal(<OutpointFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Outpoint { hash, index } = v;
            Fixed::<32>.serialize(hash, obuf);
            U32Le.serialize(index, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Outpoint<'i>> for OutpointFmt {
        fn prepare(&self, v: &Outpoint<'i>) -> Result<usize, PreSerializeError> {
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            let Outpoint { hash, index } = v;
            let l1 = (Fixed::<32>).prepare(hash)?;
            let l2 = (U32Le).prepare(index)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for ScriptSigFmt {
        type PT = ScriptSig<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, l) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, data) = (Varied(l)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = ScriptSig { l, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<ScriptSig<'i>> for ScriptSigFmt {
        fn serialize(&self, v: &ScriptSig<'i>, obuf: &mut Vec<u8>) {
            reveal(<ScriptSigFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let ScriptSig { l, data } = v;
            VarInt::<true>.serialize(l, obuf);
            Varied(l).serialize(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ScriptSig<'i>> for ScriptSigFmt {
        fn prepare(&self, v: &ScriptSig<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            let ScriptSig { l, data } = v;
            let l1 = (VarInt::<true>).prepare(l)?;
            let l2 = (Varied(l)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxRemFmt {
        type PT = TxRem<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.txin_count {
                0 => {
                    let (n, v) = (Named("tx_segwit", TxSegwitFmt)).parse(&rest)?;
                    (n, TxRem::Variant1(v))
                },
                _ => {
                    let (n, v) = (Named(
                        "tx_nonsegwit",
                        TxNonsegwitFmt { txin_count: self.txin_count },
                    )).parse(&rest)?;
                    (n, TxRem::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<TxRem<'i>> for TxRemFmt {
        fn serialize(&self, v: &TxRem<'i>, obuf: &mut Vec<u8>) {
            reveal(<TxRemFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.txin_count, v) {
                (0, TxRem::Variant1(v)) => {
                    (TxSegwitFmt).serialize(v, obuf);
                },
                (_, TxRem::Default(v)) => {
                    (TxNonsegwitFmt { txin_count: self.txin_count }).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxRem<'i>> for TxRemFmt {
        fn prepare(&self, v: &TxRem<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.txin_count, v) {
                (0, TxRem::Variant1(v)) => (Named("tx_segwit", TxSegwitFmt)).prepare(v),
                (x, TxRem::Default(v)) if !(x == 0) => (Named(
                    "tx_nonsegwit",
                    TxNonsegwitFmt { txin_count: self.txin_count },
                )).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

} // verus!
