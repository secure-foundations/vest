#![allow(warnings)]
use vest_lib::combinators::mapped::spec::*;
use vest_lib::combinators::recursive::*;
use vest_lib::combinators::*;
use vest_lib::core::exec::bytes_eq;
use vest_lib::core::exec::input::{InputBuf, InputSlice};
use vest_lib::core::exec::output::OutputBuf;
use vest_lib::core::exec::parser::*;
use vest_lib::core::exec::serializer::*;
use vest_lib::core::exec::ParseError;
use vest_lib::core::{proof::*, spec::*};
use vest_lib::primitives::btcvarint::VarInt;
use vest_lib::primitives::leb128::ULeb128;
use vest_lib::Never;
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
pub struct BlockSpec<
    T0 = u32,
    T1 = Seq<u8>,
    T2 = Seq<u8>,
    T3 = u32,
    T4 = u32,
    T5 = u32,
    T6 = u64,
    T7 = Seq<TxSpec>,
> {
    pub version: T0,
    pub prev_block: T1,
    pub merkle_root: T2,
    pub timestamp: T3,
    pub bits: T4,
    pub nonce: T5,
    pub tx_count: T6,
    pub txs: T7,
}

pub type BlockInner = (u32, (Seq<u8>, (Seq<u8>, (u32, (u32, (u32, (u64, Seq<TxSpec>)))))));

impl<'i> DeepView for Block<'i> {
    type V = BlockSpec;

    # [verifier::opaque]
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

impl<'i> Block<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().version == self.version.deep_view(),
            self.deep_view().prev_block == self.prev_block.deep_view(),
            self.deep_view().merkle_root == self.merkle_root.deep_view(),
            self.deep_view().timestamp == self.timestamp.deep_view(),
            self.deep_view().bits == self.bits.deep_view(),
            self.deep_view().nonce == self.nonce.deep_view(),
            self.deep_view().tx_count == self.tx_count.deep_view(),
            self.deep_view().txs == self.txs.deep_view(),
    {
        reveal(<Block as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> BlockSpec<T0, T1, T2, T3, T4, T5, T6, T7> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, (T3, (T4, (T5, (T6, T7)))))))) -> Self {
        let (version, (prev_block, (merkle_root, (timestamp, (bits, (nonce, (tx_count, txs))))))) =
            input;
        Self { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, (T3, (T4, (T5, (T6, T7))))))) {
        let Self { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs } = self;
        (version, (prev_block, (merkle_root, (timestamp, (bits, (nonce, (tx_count, txs)))))))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(BlockSpec::from_structural);
        reveal(BlockSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, (T3, (T4, (T5, (T6, T7))))))))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(BlockSpec::from_structural);
        reveal(BlockSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self {
                    version,
                    prev_block,
                    merkle_root,
                    timestamp,
                    bits,
                    nonce,
                    tx_count,
                    txs,
                } => (
                    version,
                    (prev_block, (merkle_root, (timestamp, (bits, (nonce, (tx_count, txs)))))),
                ),
            },
    {
        reveal(BlockSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BlockForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BlockReverse;

impl SpecMap for BlockForward {
    type Input = BlockInner;

    type Output = BlockSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        BlockSpec::from_structural(input)
    }
}

impl SpecMap for BlockReverse {
    type Input = BlockSpec;

    type Output = BlockInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
pub struct TxSpec<T0 = u32, T1 = u64, T2 = TxRemSpec> {
    pub version: T0,
    pub txin_count: T1,
    pub rem: T2,
}

pub type TxInner = (u32, (u64, TxRemSpec));

impl<'i> DeepView for Tx<'i> {
    type V = TxSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TxSpec {
            version: self.version.deep_view(),
            txin_count: self.txin_count.deep_view(),
            rem: self.rem.deep_view(),
        }
    }
}

impl<'i> Tx<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().version == self.version.deep_view(),
            self.deep_view().txin_count == self.txin_count.deep_view(),
            self.deep_view().rem == self.rem.deep_view(),
    {
        reveal(<Tx as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> TxSpec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (version, (txin_count, rem)) = input;
        Self { version, txin_count, rem }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { version, txin_count, rem } = self;
        (version, (txin_count, rem))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxSpec::from_structural);
        reveal(TxSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxSpec::from_structural);
        reveal(TxSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { version, txin_count, rem } => (version, (txin_count, rem)),
            },
    {
        reveal(TxSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxReverse;

impl SpecMap for TxForward {
    type Input = TxInner;

    type Output = TxSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxSpec::from_structural(input)
    }
}

impl SpecMap for TxReverse {
    type Input = TxSpec;

    type Output = TxInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
pub struct TxSegwitSpec<
    T0 = u8,
    T1 = u64,
    T2 = Seq<TxinSpec>,
    T3 = u64,
    T4 = Seq<TxoutSpec>,
    T5 = Seq<WitnessSpec>,
    T6 = LockTimeSpec,
> {
    pub flag: T0,
    pub txin_count: T1,
    pub txins: T2,
    pub txout_count: T3,
    pub txouts: T4,
    pub witness: T5,
    pub lock_time: T6,
}

pub type TxSegwitInner = (
    u8,
    (u64, (Seq<TxinSpec>, (u64, (Seq<TxoutSpec>, (Seq<WitnessSpec>, LockTimeSpec))))),
);

impl<'i> DeepView for TxSegwit<'i> {
    type V = TxSegwitSpec;

    # [verifier::opaque]
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

impl<'i> TxSegwit<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().flag == self.flag.deep_view(),
            self.deep_view().txin_count == self.txin_count.deep_view(),
            self.deep_view().txins == self.txins.deep_view(),
            self.deep_view().txout_count == self.txout_count.deep_view(),
            self.deep_view().txouts == self.txouts.deep_view(),
            self.deep_view().witness == self.witness.deep_view(),
            self.deep_view().lock_time == self.lock_time.deep_view(),
    {
        reveal(<TxSegwit as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3, T4, T5, T6> TxSegwitSpec<T0, T1, T2, T3, T4, T5, T6> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, (T3, (T4, (T5, T6))))))) -> Self {
        let (flag, (txin_count, (txins, (txout_count, (txouts, (witness, lock_time)))))) = input;
        Self { flag, txin_count, txins, txout_count, txouts, witness, lock_time }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, (T3, (T4, (T5, T6)))))) {
        let Self { flag, txin_count, txins, txout_count, txouts, witness, lock_time } = self;
        (flag, (txin_count, (txins, (txout_count, (txouts, (witness, lock_time))))))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxSegwitSpec::from_structural);
        reveal(TxSegwitSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, (T3, (T4, (T5, T6)))))))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxSegwitSpec::from_structural);
        reveal(TxSegwitSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { flag, txin_count, txins, txout_count, txouts, witness, lock_time } => (
                    flag,
                    (txin_count, (txins, (txout_count, (txouts, (witness, lock_time))))),
                ),
            },
    {
        reveal(TxSegwitSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxSegwitForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxSegwitReverse;

impl SpecMap for TxSegwitForward {
    type Input = TxSegwitInner;

    type Output = TxSegwitSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxSegwitSpec::from_structural(input)
    }
}

impl SpecMap for TxSegwitReverse {
    type Input = TxSegwitSpec;

    type Output = TxSegwitInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `witness`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct Witness<'i> {
    pub count: u64,
    pub data: Vec<WitnessComponent<'i>>,
}

# [verifier::ext_equal]
pub struct WitnessSpec<T0 = u64, T1 = Seq<WitnessComponentSpec>> {
    pub count: T0,
    pub data: T1,
}

pub type WitnessInner = (u64, Seq<WitnessComponentSpec>);

impl<'i> DeepView for Witness<'i> {
    type V = WitnessSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        WitnessSpec { count: self.count.deep_view(), data: self.data.deep_view() }
    }
}

impl<'i> Witness<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().count == self.count.deep_view(),
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<Witness as DeepView>::deep_view);
    }
}

impl<T0, T1> WitnessSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (count, data) = input;
        Self { count, data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { count, data } = self;
        (count, data)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(WitnessSpec::from_structural);
        reveal(WitnessSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(WitnessSpec::from_structural);
        reveal(WitnessSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { count, data } => (count, data),
            },
    {
        reveal(WitnessSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct WitnessForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct WitnessReverse;

impl SpecMap for WitnessForward {
    type Input = WitnessInner;

    type Output = WitnessSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        WitnessSpec::from_structural(input)
    }
}

impl SpecMap for WitnessReverse {
    type Input = WitnessSpec;

    type Output = WitnessInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `witness_component`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct WitnessComponent<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct WitnessComponentSpec<T0 = u64, T1 = Seq<u8>> {
    pub l: T0,
    pub data: T1,
}

pub type WitnessComponentInner = (u64, Seq<u8>);

impl<'i> DeepView for WitnessComponent<'i> {
    type V = WitnessComponentSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        WitnessComponentSpec { l: self.l.deep_view(), data: self.data.deep_view() }
    }
}

impl<'i> WitnessComponent<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().l == self.l.deep_view(),
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<WitnessComponent as DeepView>::deep_view);
    }
}

impl<T0, T1> WitnessComponentSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (l, data) = input;
        Self { l, data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { l, data } = self;
        (l, data)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(WitnessComponentSpec::from_structural);
        reveal(WitnessComponentSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(WitnessComponentSpec::from_structural);
        reveal(WitnessComponentSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { l, data } => (l, data),
            },
    {
        reveal(WitnessComponentSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct WitnessComponentForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct WitnessComponentReverse;

impl SpecMap for WitnessComponentForward {
    type Input = WitnessComponentInner;

    type Output = WitnessComponentSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        WitnessComponentSpec::from_structural(input)
    }
}

impl SpecMap for WitnessComponentReverse {
    type Input = WitnessComponentSpec;

    type Output = WitnessComponentInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
pub struct TxNonsegwitSpec<T0 = Seq<TxinSpec>, T1 = u64, T2 = Seq<TxoutSpec>, T3 = LockTimeSpec> {
    pub txins: T0,
    pub txout_count: T1,
    pub txouts: T2,
    pub lock_time: T3,
}

pub type TxNonsegwitInner = (Seq<TxinSpec>, (u64, (Seq<TxoutSpec>, LockTimeSpec)));

impl<'i> DeepView for TxNonsegwit<'i> {
    type V = TxNonsegwitSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TxNonsegwitSpec {
            txins: self.txins.deep_view(),
            txout_count: self.txout_count.deep_view(),
            txouts: self.txouts.deep_view(),
            lock_time: self.lock_time.deep_view(),
        }
    }
}

impl<'i> TxNonsegwit<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().txins == self.txins.deep_view(),
            self.deep_view().txout_count == self.txout_count.deep_view(),
            self.deep_view().txouts == self.txouts.deep_view(),
            self.deep_view().lock_time == self.lock_time.deep_view(),
    {
        reveal(<TxNonsegwit as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3> TxNonsegwitSpec<T0, T1, T2, T3> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, T3)))) -> Self {
        let (txins, (txout_count, (txouts, lock_time))) = input;
        Self { txins, txout_count, txouts, lock_time }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, T3))) {
        let Self { txins, txout_count, txouts, lock_time } = self;
        (txins, (txout_count, (txouts, lock_time)))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxNonsegwitSpec::from_structural);
        reveal(TxNonsegwitSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, T3))))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxNonsegwitSpec::from_structural);
        reveal(TxNonsegwitSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { txins, txout_count, txouts, lock_time } => (
                    txins,
                    (txout_count, (txouts, lock_time)),
                ),
            },
    {
        reveal(TxNonsegwitSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxNonsegwitForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxNonsegwitReverse;

impl SpecMap for TxNonsegwitForward {
    type Input = TxNonsegwitInner;

    type Output = TxNonsegwitSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxNonsegwitSpec::from_structural(input)
    }
}

impl SpecMap for TxNonsegwitReverse {
    type Input = TxNonsegwitSpec;

    type Output = TxNonsegwitInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `lock_time`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum LockTime {
    BlockNo(u32),
    Timestamp(u32),
}

# [verifier::ext_equal]
pub enum LockTimeSpec<T0 = u32, T1 = u32> {
    BlockNo(T0),
    Timestamp(T1),
}

pub type LockTimeInner = Sum<u32, u32>;

impl DeepView for LockTime {
    type V = LockTimeSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            LockTime::BlockNo(v) => LockTimeSpec::BlockNo(v.deep_view()),
            LockTime::Timestamp(v) => LockTimeSpec::Timestamp(v.deep_view()),
        }
    }
}

impl LockTime {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                LockTime::BlockNo(v) => LockTimeSpec::BlockNo(v.deep_view()),
                LockTime::Timestamp(v) => LockTimeSpec::Timestamp(v.deep_view()),
            },
    {
        reveal(<LockTime as DeepView>::deep_view);
    }
}

impl<T0, T1> LockTimeSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::BlockNo(value),
            R(value) => Self::Timestamp(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::BlockNo(value) => L(value),
            Self::Timestamp(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(LockTimeSpec::from_structural);
        reveal(LockTimeSpec::into_structural);
        match self {
            Self::BlockNo(_) => {},
            Self::Timestamp(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(LockTimeSpec::from_structural);
        reveal(LockTimeSpec::into_structural);
        match input {
            L(_) => {},
            R(_) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::BlockNo(value) => L(value),
                Self::Timestamp(value) => R(value),
            },
    {
        reveal(LockTimeSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct LockTimeForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct LockTimeReverse;

impl SpecMap for LockTimeForward {
    type Input = LockTimeInner;

    type Output = LockTimeSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        LockTimeSpec::from_structural(input)
    }
}

impl SpecMap for LockTimeReverse {
    type Input = LockTimeSpec;

    type Output = LockTimeInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `txout`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Txout<'i> {
    pub value: u64,
    pub script_pubkey: Script<'i>,
}

# [verifier::ext_equal]
pub struct TxoutSpec<T0 = u64, T1 = ScriptSpec> {
    pub value: T0,
    pub script_pubkey: T1,
}

pub type TxoutInner = (u64, ScriptSpec);

impl<'i> DeepView for Txout<'i> {
    type V = TxoutSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TxoutSpec { value: self.value.deep_view(), script_pubkey: self.script_pubkey.deep_view() }
    }
}

impl<'i> Txout<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().value == self.value.deep_view(),
            self.deep_view().script_pubkey == self.script_pubkey.deep_view(),
    {
        reveal(<Txout as DeepView>::deep_view);
    }
}

impl<T0, T1> TxoutSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (value, script_pubkey) = input;
        Self { value, script_pubkey }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { value, script_pubkey } = self;
        (value, script_pubkey)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxoutSpec::from_structural);
        reveal(TxoutSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxoutSpec::from_structural);
        reveal(TxoutSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { value, script_pubkey } => (value, script_pubkey),
            },
    {
        reveal(TxoutSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxoutForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxoutReverse;

impl SpecMap for TxoutForward {
    type Input = TxoutInner;

    type Output = TxoutSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxoutSpec::from_structural(input)
    }
}

impl SpecMap for TxoutReverse {
    type Input = TxoutSpec;

    type Output = TxoutInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `script`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Script<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct ScriptSpec<T0 = u64, T1 = Seq<u8>> {
    pub l: T0,
    pub data: T1,
}

pub type ScriptInner = (u64, Seq<u8>);

impl<'i> DeepView for Script<'i> {
    type V = ScriptSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        ScriptSpec { l: self.l.deep_view(), data: self.data.deep_view() }
    }
}

impl<'i> Script<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().l == self.l.deep_view(),
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<Script as DeepView>::deep_view);
    }
}

impl<T0, T1> ScriptSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (l, data) = input;
        Self { l, data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { l, data } = self;
        (l, data)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ScriptSpec::from_structural);
        reveal(ScriptSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ScriptSpec::from_structural);
        reveal(ScriptSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { l, data } => (l, data),
            },
    {
        reveal(ScriptSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ScriptForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ScriptReverse;

impl SpecMap for ScriptForward {
    type Input = ScriptInner;

    type Output = ScriptSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ScriptSpec::from_structural(input)
    }
}

impl SpecMap for ScriptReverse {
    type Input = ScriptSpec;

    type Output = ScriptInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
pub struct TxinSpec<T0 = OutpointSpec, T1 = ScriptSigSpec, T2 = u32> {
    pub previous_output: T0,
    pub script_sig: T1,
    pub sequence: T2,
}

pub type TxinInner = (OutpointSpec, (ScriptSigSpec, u32));

impl<'i> DeepView for Txin<'i> {
    type V = TxinSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TxinSpec {
            previous_output: self.previous_output.deep_view(),
            script_sig: self.script_sig.deep_view(),
            sequence: self.sequence.deep_view(),
        }
    }
}

impl<'i> Txin<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().previous_output == self.previous_output.deep_view(),
            self.deep_view().script_sig == self.script_sig.deep_view(),
            self.deep_view().sequence == self.sequence.deep_view(),
    {
        reveal(<Txin as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> TxinSpec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (previous_output, (script_sig, sequence)) = input;
        Self { previous_output, script_sig, sequence }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { previous_output, script_sig, sequence } = self;
        (previous_output, (script_sig, sequence))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxinSpec::from_structural);
        reveal(TxinSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxinSpec::from_structural);
        reveal(TxinSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { previous_output, script_sig, sequence } => (
                    previous_output,
                    (script_sig, sequence),
                ),
            },
    {
        reveal(TxinSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxinForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxinReverse;

impl SpecMap for TxinForward {
    type Input = TxinInner;

    type Output = TxinSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxinSpec::from_structural(input)
    }
}

impl SpecMap for TxinReverse {
    type Input = TxinSpec;

    type Output = TxinInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `outpoint`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Outpoint<'i> {
    pub hash: &'i [u8],
    pub index: u32,
}

# [verifier::ext_equal]
pub struct OutpointSpec<T0 = Seq<u8>, T1 = u32> {
    pub hash: T0,
    pub index: T1,
}

pub type OutpointInner = (Seq<u8>, u32);

impl<'i> DeepView for Outpoint<'i> {
    type V = OutpointSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        OutpointSpec { hash: self.hash.deep_view(), index: self.index.deep_view() }
    }
}

impl<'i> Outpoint<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().hash == self.hash.deep_view(),
            self.deep_view().index == self.index.deep_view(),
    {
        reveal(<Outpoint as DeepView>::deep_view);
    }
}

impl<T0, T1> OutpointSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (hash, index) = input;
        Self { hash, index }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { hash, index } = self;
        (hash, index)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(OutpointSpec::from_structural);
        reveal(OutpointSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(OutpointSpec::from_structural);
        reveal(OutpointSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { hash, index } => (hash, index),
            },
    {
        reveal(OutpointSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct OutpointForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct OutpointReverse;

impl SpecMap for OutpointForward {
    type Input = OutpointInner;

    type Output = OutpointSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        OutpointSpec::from_structural(input)
    }
}

impl SpecMap for OutpointReverse {
    type Input = OutpointSpec;

    type Output = OutpointInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `script_sig`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct ScriptSig<'i> {
    pub l: u64,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct ScriptSigSpec<T0 = u64, T1 = Seq<u8>> {
    pub l: T0,
    pub data: T1,
}

pub type ScriptSigInner = (u64, Seq<u8>);

impl<'i> DeepView for ScriptSig<'i> {
    type V = ScriptSigSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        ScriptSigSpec { l: self.l.deep_view(), data: self.data.deep_view() }
    }
}

impl<'i> ScriptSig<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().l == self.l.deep_view(),
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<ScriptSig as DeepView>::deep_view);
    }
}

impl<T0, T1> ScriptSigSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (l, data) = input;
        Self { l, data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { l, data } = self;
        (l, data)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ScriptSigSpec::from_structural);
        reveal(ScriptSigSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ScriptSigSpec::from_structural);
        reveal(ScriptSigSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { l, data } => (l, data),
            },
    {
        reveal(ScriptSigSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ScriptSigForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ScriptSigReverse;

impl SpecMap for ScriptSigForward {
    type Input = ScriptSigInner;

    type Output = ScriptSigSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ScriptSigSpec::from_structural(input)
    }
}

impl SpecMap for ScriptSigReverse {
    type Input = ScriptSigSpec;

    type Output = ScriptSigInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tx_rem`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub enum TxRem<'i> {
    Variant1(TxSegwit<'i>),
    Default(TxNonsegwit<'i>),
}

# [verifier::ext_equal]
pub enum TxRemSpec<T0 = TxSegwitSpec, T1 = TxNonsegwitSpec> {
    Variant1(T0),
    Default(T1),
}

pub type TxRemInner = Sum<TxSegwitSpec, TxNonsegwitSpec>;

impl<'i> DeepView for TxRem<'i> {
    type V = TxRemSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            TxRem::Variant1(v) => TxRemSpec::Variant1(v.deep_view()),
            TxRem::Default(v) => TxRemSpec::Default(v.deep_view()),
        }
    }
}

impl<'i> TxRem<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                TxRem::Variant1(v) => TxRemSpec::Variant1(v.deep_view()),
                TxRem::Default(v) => TxRemSpec::Default(v.deep_view()),
            },
    {
        reveal(<TxRem as DeepView>::deep_view);
    }
}

impl<T0, T1> TxRemSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::Variant1(value),
            R(value) => Self::Default(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::Variant1(value) => L(value),
            Self::Default(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxRemSpec::from_structural);
        reveal(TxRemSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxRemSpec::from_structural);
        reveal(TxRemSpec::into_structural);
        match input {
            L(_) => {},
            R(_) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::Variant1(value) => L(value),
                Self::Default(value) => R(value),
            },
    {
        reveal(TxRemSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxRemForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TxRemReverse;

impl SpecMap for TxRemForward {
    type Input = TxRemInner;

    type Output = TxRemSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxRemSpec::from_structural(input)
    }
}

impl SpecMap for TxRemReverse {
    type Input = TxRemSpec;

    type Output = TxRemInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
        BiMap<BlockForward, BlockReverse>,
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
                mapper: BiMap(BlockForward, BlockReverse),
            },
        )
    }
}

# [doc = "named format combinator for `tx`."]
# [derive (Clone, Copy)]
pub struct TxFmt;

pub type TxFmtSpec = Named<
    Mapped<Pair<U32Le, Bind<VarInt<true>, spec_fn(u64) -> TxRemFmt>>, BiMap<TxForward, TxReverse>>,
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
                mapper: BiMap(TxForward, TxReverse),
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
        BiMap<TxSegwitForward, TxSegwitReverse>,
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
                mapper: BiMap(TxSegwitForward, TxSegwitReverse),
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
        BiMap<WitnessForward, WitnessReverse>,
    >,
>;

impl WitnessFmt {
    # [doc = "specification constructor for `witness`."]
    pub open spec fn spec_inner() -> WitnessFmtSpec {
        Named(
            "witness",
            Mapped {
                inner: Bind(VarInt::<true>, |count: u64| RepeatN(count, WitnessComponentFmt)),
                mapper: BiMap(WitnessForward, WitnessReverse),
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
        BiMap<WitnessComponentForward, WitnessComponentReverse>,
    >,
>;

impl WitnessComponentFmt {
    # [doc = "specification constructor for `witness_component`."]
    pub open spec fn spec_inner() -> WitnessComponentFmtSpec {
        Named(
            "witness_component",
            Mapped {
                inner: Bind(VarInt::<true>, |l: u64| Varied(l)),
                mapper: BiMap(WitnessComponentForward, WitnessComponentReverse),
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
        BiMap<TxNonsegwitForward, TxNonsegwitReverse>,
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
                mapper: BiMap(TxNonsegwitForward, TxNonsegwitReverse),
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
        BiMap<LockTimeForward, LockTimeReverse>,
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
                mapper: BiMap(LockTimeForward, LockTimeReverse),
            },
        )
    }
}

# [doc = "named format combinator for `txout`."]
# [derive (Clone, Copy)]
pub struct TxoutFmt;

pub type TxoutFmtSpec = Named<Mapped<Pair<U64Le, ScriptFmt>, BiMap<TxoutForward, TxoutReverse>>>;

impl TxoutFmt {
    # [doc = "specification constructor for `txout`."]
    pub open spec fn spec_inner() -> TxoutFmtSpec {
        Named(
            "txout",
            Mapped { inner: Pair(U64Le, ScriptFmt), mapper: BiMap(TxoutForward, TxoutReverse) },
        )
    }
}

# [doc = "named format combinator for `script`."]
# [derive (Clone, Copy)]
pub struct ScriptFmt;

pub type ScriptFmtSpec = Named<
    Mapped<Bind<VarInt<true>, spec_fn(u64) -> Varied<u64>>, BiMap<ScriptForward, ScriptReverse>>,
>;

impl ScriptFmt {
    # [doc = "specification constructor for `script`."]
    pub open spec fn spec_inner() -> ScriptFmtSpec {
        Named(
            "script",
            Mapped {
                inner: Bind(VarInt::<true>, |l: u64| Varied(l)),
                mapper: BiMap(ScriptForward, ScriptReverse),
            },
        )
    }
}

# [doc = "named format combinator for `txin`."]
# [derive (Clone, Copy)]
pub struct TxinFmt;

pub type TxinFmtSpec = Named<
    Mapped<Pair<OutpointFmt, Pair<ScriptSigFmt, U32Le>>, BiMap<TxinForward, TxinReverse>>,
>;

impl TxinFmt {
    # [doc = "specification constructor for `txin`."]
    pub open spec fn spec_inner() -> TxinFmtSpec {
        Named(
            "txin",
            Mapped {
                inner: Pair(OutpointFmt, Pair(ScriptSigFmt, U32Le)),
                mapper: BiMap(TxinForward, TxinReverse),
            },
        )
    }
}

# [doc = "named format combinator for `outpoint`."]
# [derive (Clone, Copy)]
pub struct OutpointFmt;

pub type OutpointFmtSpec = Named<
    Mapped<Pair<Fixed<32>, U32Le>, BiMap<OutpointForward, OutpointReverse>>,
>;

impl OutpointFmt {
    # [doc = "specification constructor for `outpoint`."]
    pub open spec fn spec_inner() -> OutpointFmtSpec {
        Named(
            "outpoint",
            Mapped {
                inner: Pair(Fixed::<32>, U32Le),
                mapper: BiMap(OutpointForward, OutpointReverse),
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
        BiMap<ScriptSigForward, ScriptSigReverse>,
    >,
>;

impl ScriptSigFmt {
    # [doc = "specification constructor for `script_sig`."]
    pub open spec fn spec_inner() -> ScriptSigFmtSpec {
        Named(
            "script_sig",
            Mapped {
                inner: Bind(VarInt::<true>, |l: u64| Varied(l)),
                mapper: BiMap(ScriptSigForward, ScriptSigReverse),
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
    Mapped<Sum<TxSegwitFmt, TxNonsegwitFmt>, BiMap<TxRemForward, TxRemReverse>>,
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
                mapper: BiMap(TxRemForward, TxRemReverse),
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

    broadcast use {
        vest_lib::combinators::disjoint::disjointness_lemmas,
        BlockSpec::lemma_from_into,
        BlockSpec::lemma_into_from,
        TxSpec::lemma_from_into,
        TxSpec::lemma_into_from,
        TxSegwitSpec::lemma_from_into,
        TxSegwitSpec::lemma_into_from,
        WitnessSpec::lemma_from_into,
        WitnessSpec::lemma_into_from,
        WitnessComponentSpec::lemma_from_into,
        WitnessComponentSpec::lemma_into_from,
        TxNonsegwitSpec::lemma_from_into,
        TxNonsegwitSpec::lemma_into_from,
        LockTimeSpec::lemma_from_into,
        LockTimeSpec::lemma_into_from,
        TxoutSpec::lemma_from_into,
        TxoutSpec::lemma_into_from,
        ScriptSpec::lemma_from_into,
        ScriptSpec::lemma_into_from,
        TxinSpec::lemma_from_into,
        TxinSpec::lemma_into_from,
        OutpointSpec::lemma_from_into,
        OutpointSpec::lemma_into_from,
        ScriptSigSpec::lemma_from_into,
        ScriptSigSpec::lemma_into_from,
        TxRemSpec::lemma_from_into,
        TxRemSpec::lemma_into_from,
    };

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
            assert forall|input: BlockInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BlockSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            reveal(<BlockFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: BlockInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BlockSpec::lemma_into_from(input);
            }
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
            assert forall|output: BlockSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                BlockSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for BlockFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: BlockInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BlockSpec::lemma_into_from(input);
            }
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
            assert forall|input: TxInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            reveal(<TxFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TxInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxSpec::lemma_into_from(input);
            }
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
            assert forall|output: TxSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TxInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxSpec::lemma_into_from(input);
            }
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
            assert forall|input: TxSegwitInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxSegwitSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            reveal(<TxSegwitFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TxSegwitInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxSegwitSpec::lemma_into_from(input);
            }
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
            assert forall|output: TxSegwitSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxSegwitSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxSegwitFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TxSegwitInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxSegwitSpec::lemma_into_from(input);
            }
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
            assert forall|input: WitnessInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            reveal(<WitnessFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: WitnessInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessSpec::lemma_into_from(input);
            }
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
            assert forall|output: WitnessSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                WitnessSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for WitnessFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: WitnessInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessSpec::lemma_into_from(input);
            }
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
            assert forall|input: WitnessComponentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessComponentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            reveal(<WitnessComponentFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: WitnessComponentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessComponentSpec::lemma_into_from(input);
            }
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
            assert forall|output: WitnessComponentSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                WitnessComponentSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for WitnessComponentFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: WitnessComponentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessComponentSpec::lemma_into_from(input);
            }
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
            assert forall|input: TxNonsegwitInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxNonsegwitSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            reveal(<TxNonsegwitFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert forall|input: TxNonsegwitInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxNonsegwitSpec::lemma_into_from(input);
            }
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
            assert forall|output: TxNonsegwitSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxNonsegwitSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxNonsegwitFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert forall|input: TxNonsegwitInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxNonsegwitSpec::lemma_into_from(input);
            }
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
            assert forall|input: LockTimeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                LockTimeSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            reveal(<LockTimeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: LockTimeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                LockTimeSpec::lemma_into_from(input);
            }
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
            assert forall|output: LockTimeSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                LockTimeSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for LockTimeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: LockTimeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                LockTimeSpec::lemma_into_from(input);
            }
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
            assert forall|input: TxoutInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxoutSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            reveal(<TxoutFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TxoutInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxoutSpec::lemma_into_from(input);
            }
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
            assert forall|output: TxoutSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxoutSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxoutFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TxoutInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxoutSpec::lemma_into_from(input);
            }
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
            assert forall|input: ScriptInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ScriptSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            reveal(<ScriptFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ScriptInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ScriptSpec::lemma_into_from(input);
            }
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
            assert forall|output: ScriptSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ScriptSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ScriptFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: ScriptInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ScriptSpec::lemma_into_from(input);
            }
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
            assert forall|input: TxinInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxinSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            reveal(<TxinFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TxinInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxinSpec::lemma_into_from(input);
            }
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
            assert forall|output: TxinSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxinSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxinFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TxinInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxinSpec::lemma_into_from(input);
            }
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
            assert forall|input: OutpointInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OutpointSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<OutpointFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: OutpointInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OutpointSpec::lemma_into_from(input);
            }
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
            assert forall|output: OutpointSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                OutpointSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OutpointFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: OutpointInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OutpointSpec::lemma_into_from(input);
            }
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
            assert forall|input: ScriptSigInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ScriptSigSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            reveal(<ScriptSigFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ScriptSigInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ScriptSigSpec::lemma_into_from(input);
            }
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
            assert forall|output: ScriptSigSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ScriptSigSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ScriptSigFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: ScriptSigInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ScriptSigSpec::lemma_into_from(input);
            }
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
            assert forall|input: TxRemInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxRemSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            reveal(<TxRemFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert forall|input: TxRemInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxRemSpec::lemma_into_from(input);
            }
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
            assert forall|output: TxRemSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxRemSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxRemFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.txin_count_spec());
            assert forall|input: TxRemInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxRemSpec::lemma_into_from(input);
            }
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
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<BlockFmt as SpecParser>::spec_parse);
            reveal(<Block as DeepView>::deep_view);
            reveal(BlockSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, Block<'i>> for BlockFmt {
        fn serialize_into(&self, v: &Block<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<BlockFmt as SpecSerializer>::spec_serialize);
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            reveal(<Block as DeepView>::deep_view);
            reveal(BlockSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Block { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs } =
                v;
            U32Le.serialize_into(version, obuf);
            Fixed::<32>.serialize_into(*prev_block, obuf);
            Fixed::<32>.serialize_into(*merkle_root, obuf);
            U32Le.serialize_into(timestamp, obuf);
            U32Le.serialize_into(bits, obuf);
            U32Le.serialize_into(nonce, obuf);
            VarInt::<true>.serialize_into(tx_count, obuf);
            RepeatN(*tx_count, TxFmt).serialize_into(txs, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Block<'i>> for BlockFmt {
        fn prepare(&self, v: &Block<'i>) -> Result<usize, PreSerializeError> {
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            reveal(<Block as DeepView>::deep_view);
            reveal(BlockSpec::into_structural);
            let Block { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs } =
                v;
            let l1 = (U32Le).prepare(version)?;
            let l2 = (Fixed::<32>).prepare(prev_block)?;
            let l3 = (Fixed::<32>).prepare(merkle_root)?;
            let l4 = (U32Le).prepare(timestamp)?;
            let l5 = (U32Le).prepare(bits)?;
            let l6 = (U32Le).prepare(nonce)?;
            let l7 = (VarInt::<true>).prepare(tx_count)?;
            let l8 = (RepeatN(*tx_count, TxFmt)).prepare(txs)?;
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
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxFmt as SpecParser>::spec_parse);
            reveal(<Tx as DeepView>::deep_view);
            reveal(TxSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, Tx<'i>> for TxFmt {
        fn serialize_into(&self, v: &Tx<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<TxFmt as SpecSerializer>::spec_serialize);
            reveal(<TxFmt as SpecByteLen>::byte_len);
            reveal(<Tx as DeepView>::deep_view);
            reveal(TxSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Tx { version, txin_count, rem } = v;
            U32Le.serialize_into(version, obuf);
            VarInt::<true>.serialize_into(txin_count, obuf);
            TxRemFmt { txin_count: *txin_count }.serialize_into(rem, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Tx<'i>> for TxFmt {
        fn prepare(&self, v: &Tx<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxFmt as SpecByteLen>::byte_len);
            reveal(<Tx as DeepView>::deep_view);
            reveal(TxSpec::into_structural);
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
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxSegwitFmt as SpecParser>::spec_parse);
            reveal(<TxSegwit as DeepView>::deep_view);
            reveal(TxSegwitSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, TxSegwit<'i>> for TxSegwitFmt {
        fn serialize_into(&self, v: &TxSegwit<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<TxSegwitFmt as SpecSerializer>::spec_serialize);
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            reveal(<TxSegwit as DeepView>::deep_view);
            reveal(TxSegwitSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TxSegwit { flag, txin_count, txins, txout_count, txouts, witness, lock_time } = v;
            U8.serialize_into(flag, obuf);
            VarInt::<true>.serialize_into(txin_count, obuf);
            RepeatN(*txin_count, TxinFmt).serialize_into(txins, obuf);
            VarInt::<true>.serialize_into(txout_count, obuf);
            RepeatN(*txout_count, TxoutFmt).serialize_into(txouts, obuf);
            RepeatN(*txin_count, WitnessFmt).serialize_into(witness, obuf);
            LockTimeFmt.serialize_into(lock_time, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxSegwit<'i>> for TxSegwitFmt {
        fn prepare(&self, v: &TxSegwit<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxSegwitFmt as SpecByteLen>::byte_len);
            reveal(<TxSegwit as DeepView>::deep_view);
            reveal(TxSegwitSpec::into_structural);
            let TxSegwit { flag, txin_count, txins, txout_count, txouts, witness, lock_time } = v;
            let l1 = (Const(U8, 1)).prepare(flag)?;
            let l2 = (VarInt::<true>).prepare(txin_count)?;
            let l3 = (RepeatN(*txin_count, TxinFmt)).prepare(txins)?;
            let l4 = (VarInt::<true>).prepare(txout_count)?;
            let l5 = (RepeatN(*txout_count, TxoutFmt)).prepare(txouts)?;
            let l6 = (RepeatN(*txin_count, WitnessFmt)).prepare(witness)?;
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
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<WitnessFmt as SpecParser>::spec_parse);
            reveal(<Witness as DeepView>::deep_view);
            reveal(WitnessSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, Witness<'i>> for WitnessFmt {
        fn serialize_into(&self, v: &Witness<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<WitnessFmt as SpecSerializer>::spec_serialize);
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            reveal(<Witness as DeepView>::deep_view);
            reveal(WitnessSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Witness { count, data } = v;
            VarInt::<true>.serialize_into(count, obuf);
            RepeatN(*count, WitnessComponentFmt).serialize_into(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Witness<'i>> for WitnessFmt {
        fn prepare(&self, v: &Witness<'i>) -> Result<usize, PreSerializeError> {
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            reveal(<Witness as DeepView>::deep_view);
            reveal(WitnessSpec::into_structural);
            let Witness { count, data } = v;
            let l1 = (VarInt::<true>).prepare(count)?;
            let l2 = (RepeatN(*count, WitnessComponentFmt)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for WitnessComponentFmt {
        type PT = WitnessComponent<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<WitnessComponentFmt as SpecParser>::spec_parse);
            reveal(<WitnessComponent as DeepView>::deep_view);
            reveal(WitnessComponentSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, WitnessComponent<'i>> for WitnessComponentFmt {
        fn serialize_into(&self, v: &WitnessComponent<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<WitnessComponentFmt as SpecSerializer>::spec_serialize);
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            reveal(<WitnessComponent as DeepView>::deep_view);
            reveal(WitnessComponentSpec::into_structural);
            let ghost old_obuf = obuf@;

            let WitnessComponent { l, data } = v;
            VarInt::<true>.serialize_into(l, obuf);
            Varied(*l).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<WitnessComponent<'i>> for WitnessComponentFmt {
        fn prepare(&self, v: &WitnessComponent<'i>) -> Result<usize, PreSerializeError> {
            reveal(<WitnessComponentFmt as SpecByteLen>::byte_len);
            reveal(<WitnessComponent as DeepView>::deep_view);
            reveal(WitnessComponentSpec::into_structural);
            let WitnessComponent { l, data } = v;
            let l1 = (VarInt::<true>).prepare(l)?;
            let l2 = (Varied(*l)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxNonsegwitFmt {
        type PT = TxNonsegwit<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxNonsegwitFmt as SpecParser>::spec_parse);
            reveal(<TxNonsegwit as DeepView>::deep_view);
            reveal(TxNonsegwitSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, TxNonsegwit<'i>> for TxNonsegwitFmt {
        fn serialize_into(&self, v: &TxNonsegwit<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<TxNonsegwitFmt as SpecSerializer>::spec_serialize);
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            reveal(<TxNonsegwit as DeepView>::deep_view);
            reveal(TxNonsegwitSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let TxNonsegwit { txins, txout_count, txouts, lock_time } = v;
            RepeatN(self.txin_count, TxinFmt).serialize_into(txins, obuf);
            VarInt::<true>.serialize_into(txout_count, obuf);
            RepeatN(*txout_count, TxoutFmt).serialize_into(txouts, obuf);
            LockTimeFmt.serialize_into(lock_time, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxNonsegwit<'i>> for TxNonsegwitFmt {
        fn prepare(&self, v: &TxNonsegwit<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxNonsegwitFmt as SpecByteLen>::byte_len);
            reveal(<TxNonsegwit as DeepView>::deep_view);
            reveal(TxNonsegwitSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let TxNonsegwit { txins, txout_count, txouts, lock_time } = v;
            let l1 = (RepeatN(self.txin_count, TxinFmt)).prepare(txins)?;
            let l2 = (VarInt::<true>).prepare(txout_count)?;
            let l3 = (RepeatN(*txout_count, TxoutFmt)).prepare(txouts)?;
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
            reveal(<LockTime as DeepView>::deep_view);
            reveal(LockTimeSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, LockTime> for LockTimeFmt {
        fn serialize_into(&self, v: &LockTime, obuf: &mut Output) {
            reveal(<LockTimeFmt as SpecSerializer>::spec_serialize);
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            reveal(<LockTime as DeepView>::deep_view);
            reveal(LockTimeSpec::into_structural);
            let ghost old_obuf = obuf@;

            match v {
                LockTime::BlockNo(v) => {
                    (U32Le).serialize_into(v, obuf);
                },
                LockTime::Timestamp(v) => {
                    (U32Le).serialize_into(v, obuf);
                },
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<LockTime> for LockTimeFmt {
        fn prepare(&self, v: &LockTime) -> Result<usize, PreSerializeError> {
            reveal(<LockTimeFmt as SpecByteLen>::byte_len);
            reveal(<LockTime as DeepView>::deep_view);
            reveal(LockTimeSpec::into_structural);
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
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxoutFmt as SpecParser>::spec_parse);
            reveal(<Txout as DeepView>::deep_view);
            reveal(TxoutSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, Txout<'i>> for TxoutFmt {
        fn serialize_into(&self, v: &Txout<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<TxoutFmt as SpecSerializer>::spec_serialize);
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            reveal(<Txout as DeepView>::deep_view);
            reveal(TxoutSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Txout { value, script_pubkey } = v;
            U64Le.serialize_into(value, obuf);
            ScriptFmt.serialize_into(script_pubkey, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Txout<'i>> for TxoutFmt {
        fn prepare(&self, v: &Txout<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxoutFmt as SpecByteLen>::byte_len);
            reveal(<Txout as DeepView>::deep_view);
            reveal(TxoutSpec::into_structural);
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
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ScriptFmt as SpecParser>::spec_parse);
            reveal(<Script as DeepView>::deep_view);
            reveal(ScriptSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, Script<'i>> for ScriptFmt {
        fn serialize_into(&self, v: &Script<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<ScriptFmt as SpecSerializer>::spec_serialize);
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            reveal(<Script as DeepView>::deep_view);
            reveal(ScriptSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Script { l, data } = v;
            VarInt::<true>.serialize_into(l, obuf);
            Varied(*l).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Script<'i>> for ScriptFmt {
        fn prepare(&self, v: &Script<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            reveal(<Script as DeepView>::deep_view);
            reveal(ScriptSpec::into_structural);
            let Script { l, data } = v;
            let l1 = (VarInt::<true>).prepare(l)?;
            let l2 = (Varied(*l)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxinFmt {
        type PT = Txin<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxinFmt as SpecParser>::spec_parse);
            reveal(<Txin as DeepView>::deep_view);
            reveal(TxinSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, Txin<'i>> for TxinFmt {
        fn serialize_into(&self, v: &Txin<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<TxinFmt as SpecSerializer>::spec_serialize);
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            reveal(<Txin as DeepView>::deep_view);
            reveal(TxinSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Txin { previous_output, script_sig, sequence } = v;
            OutpointFmt.serialize_into(previous_output, obuf);
            ScriptSigFmt.serialize_into(script_sig, obuf);
            U32Le.serialize_into(sequence, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Txin<'i>> for TxinFmt {
        fn prepare(&self, v: &Txin<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxinFmt as SpecByteLen>::byte_len);
            reveal(<Txin as DeepView>::deep_view);
            reveal(TxinSpec::into_structural);
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
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<Outpoint as DeepView>::deep_view);
            reveal(OutpointSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, Outpoint<'i>> for OutpointFmt {
        fn serialize_into(&self, v: &Outpoint<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<OutpointFmt as SpecSerializer>::spec_serialize);
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            reveal(<Outpoint as DeepView>::deep_view);
            reveal(OutpointSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Outpoint { hash, index } = v;
            Fixed::<32>.serialize_into(*hash, obuf);
            U32Le.serialize_into(index, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Outpoint<'i>> for OutpointFmt {
        fn prepare(&self, v: &Outpoint<'i>) -> Result<usize, PreSerializeError> {
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            reveal(<Outpoint as DeepView>::deep_view);
            reveal(OutpointSpec::into_structural);
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
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ScriptSigFmt as SpecParser>::spec_parse);
            reveal(<ScriptSig as DeepView>::deep_view);
            reveal(ScriptSigSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, ScriptSig<'i>> for ScriptSigFmt {
        fn serialize_into(&self, v: &ScriptSig<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<ScriptSigFmt as SpecSerializer>::spec_serialize);
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            reveal(<ScriptSig as DeepView>::deep_view);
            reveal(ScriptSigSpec::into_structural);
            let ghost old_obuf = obuf@;

            let ScriptSig { l, data } = v;
            VarInt::<true>.serialize_into(l, obuf);
            Varied(*l).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ScriptSig<'i>> for ScriptSigFmt {
        fn prepare(&self, v: &ScriptSig<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ScriptSigFmt as SpecByteLen>::byte_len);
            reveal(<ScriptSig as DeepView>::deep_view);
            reveal(ScriptSigSpec::into_structural);
            let ScriptSig { l, data } = v;
            let l1 = (VarInt::<true>).prepare(l)?;
            let l2 = (Varied(*l)).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxRemFmt {
        type PT = TxRem<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TxRemFmt as SpecParser>::spec_parse);
            reveal(<TxRem as DeepView>::deep_view);
            reveal(TxRemSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, TxRem<'i>> for TxRemFmt {
        fn serialize_into(&self, v: &TxRem<'i>, obuf: &mut Output) {
            reveal(<TxRemFmt as SpecSerializer>::spec_serialize);
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            reveal(<TxRem as DeepView>::deep_view);
            reveal(TxRemSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.txin_count, v) {
                (0, TxRem::Variant1(v)) => {
                    (TxSegwitFmt).serialize_into(v, obuf);
                },
                (_, TxRem::Default(v)) => {
                    (TxNonsegwitFmt { txin_count: self.txin_count }).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxRem<'i>> for TxRemFmt {
        fn prepare(&self, v: &TxRem<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxRemFmt as SpecByteLen>::byte_len);
            reveal(<TxRem as DeepView>::deep_view);
            reveal(TxRemSpec::into_structural);
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
