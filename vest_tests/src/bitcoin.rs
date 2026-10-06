#![allow(warnings)]
use vest_lib::combinators::mapped::spec::*;
use vest_lib::combinators::*;
use vest_lib::combinators::recursive::*;
use Sum::Inl as L;
use Sum::Inr as R;
use vest_lib::Never;
use vest_lib::core::exec::input::{InputBuf, InputSlice};
use vest_lib::core::exec::output::OutputBuf;
use vest_lib::core::exec::parser::*;
use vest_lib::core::exec::serializer::*;
use vest_lib::core::exec::ParseError;
use vest_lib::core::exec::bytes_eq;
use vest_lib::core::{proof::*, spec::*};
use vest_lib::primitives::btcvarint::VarInt;
use vest_lib::primitives::leb128::ULeb128;
use vstd::prelude::*;
verus! {
// ============================================================
// Data Types
// ============================================================
/// data type for `block_header`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct BlockHeader<'i> {
    pub version: u32,
    pub previous_block_hash: &'i [u8],
    pub merkle_root_hash: &'i [u8],
    pub timestamp: u32,
    pub bits: u32,
    pub nonce: u32,
}

#[verifier::ext_equal]
pub struct BlockHeaderSpec<T0 = u32, T1 = Seq<u8>, T2 = Seq<u8>, T3 = u32, T4 = u32, T5 = u32> {
    pub version: T0,
    pub previous_block_hash: T1,
    pub merkle_root_hash: T2,
    pub timestamp: T3,
    pub bits: T4,
    pub nonce: T5,
}

pub type BlockHeaderInner = (u32, (Seq<u8>, (Seq<u8>, (u32, (u32, u32)))));

impl<'i> DeepView for BlockHeader<'i> {
    type V = BlockHeaderSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        BlockHeaderSpec {
            version: self.version.deep_view(),
            previous_block_hash: self.previous_block_hash.deep_view(),
            merkle_root_hash: self.merkle_root_hash.deep_view(),
            timestamp: self.timestamp.deep_view(),
            bits: self.bits.deep_view(),
            nonce: self.nonce.deep_view(),
        }
    }
}

impl<'i> BlockHeader<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().version == self.version.deep_view(),
            self.deep_view().previous_block_hash == self.previous_block_hash.deep_view(),
            self.deep_view().merkle_root_hash == self.merkle_root_hash.deep_view(),
            self.deep_view().timestamp == self.timestamp.deep_view(),
            self.deep_view().bits == self.bits.deep_view(),
            self.deep_view().nonce == self.nonce.deep_view(),
    {
        reveal(<BlockHeader as DeepView>::deep_view);
    }
}

/// data type for `block`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Block<'i> {
    pub header: BlockHeader<'i>,
    pub transaction_count: u64,
    pub transactions: Vec<Tx<'i>>,
}

#[verifier::ext_equal]
pub struct BlockSpec<T0 = BlockHeaderSpec, T1 = u64, T2 = Seq<TxSpec>> {
    pub header: T0,
    pub transaction_count: T1,
    pub transactions: T2,
}

pub type BlockInner = (BlockHeaderSpec, (u64, Seq<TxSpec>));

impl<'i> DeepView for Block<'i> {
    type V = BlockSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        BlockSpec {
            header: self.header.deep_view(),
            transaction_count: self.transaction_count.deep_view(),
            transactions: self.transactions.deep_view(),
        }
    }
}

impl<'i> Block<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().header == self.header.deep_view(),
            self.deep_view().transaction_count == self.transaction_count.deep_view(),
            self.deep_view().transactions == self.transactions.deep_view(),
    {
        reveal(<Block as DeepView>::deep_view);
    }
}

/// data type for `tx`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Tx<'i> {
    pub version: u32,
    pub marker_or_input_count: u64,
    pub payload: TxPayload<'i>,
}

#[verifier::ext_equal]
pub struct TxSpec<T0 = u32, T1 = u64, T2 = TxPayloadSpec> {
    pub version: T0,
    pub marker_or_input_count: T1,
    pub payload: T2,
}

pub type TxInner = (u32, (u64, TxPayloadSpec));

impl<'i> DeepView for Tx<'i> {
    type V = TxSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TxSpec {
            version: self.version.deep_view(),
            marker_or_input_count: self.marker_or_input_count.deep_view(),
            payload: self.payload.deep_view(),
        }
    }
}

impl<'i> Tx<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().version == self.version.deep_view(),
            self.deep_view().marker_or_input_count == self.marker_or_input_count.deep_view(),
            self.deep_view().payload == self.payload.deep_view(),
    {
        reveal(<Tx as DeepView>::deep_view);
    }
}

/// data type for `tx_with_witness`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TxWithWitness<'i> {
    pub flag: u8,
    pub input_count: u64,
    pub inputs: Vec<Txin<'i>>,
    pub output_count: u64,
    pub outputs: Vec<Txout<'i>>,
    pub witnesses: Vec<Witness<'i>>,
    pub lock_time: LockTime,
}

#[verifier::ext_equal]
pub struct TxWithWitnessSpec<
    T0 = u8,
    T1 = u64,
    T2 = Seq<TxinSpec>,
    T3 = u64,
    T4 = Seq<TxoutSpec>,
    T5 = Seq<WitnessSpec>,
    T6 = LockTimeSpec,
> {
    pub flag: T0,
    pub input_count: T1,
    pub inputs: T2,
    pub output_count: T3,
    pub outputs: T4,
    pub witnesses: T5,
    pub lock_time: T6,
}

pub type TxWithWitnessInner = (u8, (u64, (Seq<TxinSpec>, (u64, (Seq<TxoutSpec>,
    (Seq<WitnessSpec>, LockTimeSpec))))));

impl<'i> DeepView for TxWithWitness<'i> {
    type V = TxWithWitnessSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TxWithWitnessSpec {
            flag: self.flag.deep_view(),
            input_count: self.input_count.deep_view(),
            inputs: self.inputs.deep_view(),
            output_count: self.output_count.deep_view(),
            outputs: self.outputs.deep_view(),
            witnesses: self.witnesses.deep_view(),
            lock_time: self.lock_time.deep_view(),
        }
    }
}

impl<'i> TxWithWitness<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().flag == self.flag.deep_view(),
            self.deep_view().input_count == self.input_count.deep_view(),
            self.deep_view().inputs == self.inputs.deep_view(),
            self.deep_view().output_count == self.output_count.deep_view(),
            self.deep_view().outputs == self.outputs.deep_view(),
            self.deep_view().witnesses == self.witnesses.deep_view(),
            self.deep_view().lock_time == self.lock_time.deep_view(),
    {
        reveal(<TxWithWitness as DeepView>::deep_view);
    }
}

/// data type for `tx_without_witness`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TxWithoutWitness<'i> {
    pub inputs: Vec<Txin<'i>>,
    pub output_count: u64,
    pub outputs: Vec<Txout<'i>>,
    pub lock_time: LockTime,
}

#[verifier::ext_equal]
pub struct TxWithoutWitnessSpec<
    T0 = Seq<TxinSpec>,
    T1 = u64,
    T2 = Seq<TxoutSpec>,
    T3 = LockTimeSpec,
> {
    pub inputs: T0,
    pub output_count: T1,
    pub outputs: T2,
    pub lock_time: T3,
}

pub type TxWithoutWitnessInner = (Seq<TxinSpec>, (u64, (Seq<TxoutSpec>, LockTimeSpec)));

impl<'i> DeepView for TxWithoutWitness<'i> {
    type V = TxWithoutWitnessSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TxWithoutWitnessSpec {
            inputs: self.inputs.deep_view(),
            output_count: self.output_count.deep_view(),
            outputs: self.outputs.deep_view(),
            lock_time: self.lock_time.deep_view(),
        }
    }
}

impl<'i> TxWithoutWitness<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().inputs == self.inputs.deep_view(),
            self.deep_view().output_count == self.output_count.deep_view(),
            self.deep_view().outputs == self.outputs.deep_view(),
            self.deep_view().lock_time == self.lock_time.deep_view(),
    {
        reveal(<TxWithoutWitness as DeepView>::deep_view);
    }
}

/// data type for `lock_time`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LockTime {
    BlockHeight(u32),
    Timestamp(u32),
}

#[verifier::ext_equal]
pub enum LockTimeSpec<T0 = u32, T1 = u32> {
    BlockHeight(T0),
    Timestamp(T1),
}

pub type LockTimeInner = Sum<u32, u32>;

impl DeepView for LockTime {
    type V = LockTimeSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            LockTime::BlockHeight(v) => LockTimeSpec::BlockHeight(v.deep_view()),
            LockTime::Timestamp(v) => LockTimeSpec::Timestamp(v.deep_view()),
        }
    }
}

impl LockTime {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view()
                == match self {
                    LockTime::BlockHeight(v) => LockTimeSpec::BlockHeight(v.deep_view()),
                    LockTime::Timestamp(v) => LockTimeSpec::Timestamp(v.deep_view()),
                },
    {
        reveal(<LockTime as DeepView>::deep_view);
    }
}

/// data type for `txin`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Txin<'i> {
    pub previous_output: Outpoint<'i>,
    pub script_sig: Script<'i>,
    pub sequence: u32,
}

#[verifier::ext_equal]
pub struct TxinSpec<T0 = OutpointSpec, T1 = ScriptSpec, T2 = u32> {
    pub previous_output: T0,
    pub script_sig: T1,
    pub sequence: T2,
}

pub type TxinInner = (OutpointSpec, (ScriptSpec, u32));

impl<'i> DeepView for Txin<'i> {
    type V = TxinSpec;

    #[verifier::opaque]
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

/// data type for `outpoint`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Outpoint<'i> {
    pub transaction_hash: &'i [u8],
    pub output_index: u32,
}

#[verifier::ext_equal]
pub struct OutpointSpec<T0 = Seq<u8>, T1 = u32> {
    pub transaction_hash: T0,
    pub output_index: T1,
}

pub type OutpointInner = (Seq<u8>, u32);

impl<'i> DeepView for Outpoint<'i> {
    type V = OutpointSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        OutpointSpec {
            transaction_hash: self.transaction_hash.deep_view(),
            output_index: self.output_index.deep_view(),
        }
    }
}

impl<'i> Outpoint<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().transaction_hash == self.transaction_hash.deep_view(),
            self.deep_view().output_index == self.output_index.deep_view(),
    {
        reveal(<Outpoint as DeepView>::deep_view);
    }
}

/// data type for `txout`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Txout<'i> {
    pub value: u64,
    pub script_pubkey: Script<'i>,
}

#[verifier::ext_equal]
pub struct TxoutSpec<T0 = u64, T1 = ScriptSpec> {
    pub value: T0,
    pub script_pubkey: T1,
}

pub type TxoutInner = (u64, ScriptSpec);

impl<'i> DeepView for Txout<'i> {
    type V = TxoutSpec;

    #[verifier::opaque]
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

/// data type for `script`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Script<'i> {
    pub length: u64,
    pub bytes: &'i [u8],
}

#[verifier::ext_equal]
pub struct ScriptSpec<T0 = u64, T1 = Seq<u8>> {
    pub length: T0,
    pub bytes: T1,
}

pub type ScriptInner = (u64, Seq<u8>);

impl<'i> DeepView for Script<'i> {
    type V = ScriptSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        ScriptSpec { length: self.length.deep_view(), bytes: self.bytes.deep_view() }
    }
}

impl<'i> Script<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().length == self.length.deep_view(),
            self.deep_view().bytes == self.bytes.deep_view(),
    {
        reveal(<Script as DeepView>::deep_view);
    }
}

/// data type for `witness`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Witness<'i> {
    pub item_count: u64,
    pub items: Vec<WitnessItem<'i>>,
}

#[verifier::ext_equal]
pub struct WitnessSpec<T0 = u64, T1 = Seq<WitnessItemSpec>> {
    pub item_count: T0,
    pub items: T1,
}

pub type WitnessInner = (u64, Seq<WitnessItemSpec>);

impl<'i> DeepView for Witness<'i> {
    type V = WitnessSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        WitnessSpec { item_count: self.item_count.deep_view(), items: self.items.deep_view() }
    }
}

impl<'i> Witness<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().item_count == self.item_count.deep_view(),
            self.deep_view().items == self.items.deep_view(),
    {
        reveal(<Witness as DeepView>::deep_view);
    }
}

/// data type for `witness_item`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct WitnessItem<'i> {
    pub length: u64,
    pub bytes: &'i [u8],
}

#[verifier::ext_equal]
pub struct WitnessItemSpec<T0 = u64, T1 = Seq<u8>> {
    pub length: T0,
    pub bytes: T1,
}

pub type WitnessItemInner = (u64, Seq<u8>);

impl<'i> DeepView for WitnessItem<'i> {
    type V = WitnessItemSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        WitnessItemSpec { length: self.length.deep_view(), bytes: self.bytes.deep_view() }
    }
}

impl<'i> WitnessItem<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().length == self.length.deep_view(),
            self.deep_view().bytes == self.bytes.deep_view(),
    {
        reveal(<WitnessItem as DeepView>::deep_view);
    }
}

/// data type for `tx_payload`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TxPayload<'i> {
    TxWithWitness(TxWithWitness<'i>),
    TxWithoutWitness(TxWithoutWitness<'i>),
}

#[verifier::ext_equal]
pub enum TxPayloadSpec<T0 = TxWithWitnessSpec, T1 = TxWithoutWitnessSpec> {
    TxWithWitness(T0),
    TxWithoutWitness(T1),
}

pub type TxPayloadInner = Sum<TxWithWitnessSpec, TxWithoutWitnessSpec>;

impl<'i> DeepView for TxPayload<'i> {
    type V = TxPayloadSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            TxPayload::TxWithWitness(v) => TxPayloadSpec::TxWithWitness(v.deep_view()),
            TxPayload::TxWithoutWitness(v) => TxPayloadSpec::TxWithoutWitness(v.deep_view()),
        }
    }
}

impl<'i> TxPayload<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view()
                == match self {
                    TxPayload::TxWithWitness(v) => TxPayloadSpec::TxWithWitness(v.deep_view()),
                    TxPayload::TxWithoutWitness(v) =>
                        TxPayloadSpec::TxWithoutWitness(v.deep_view()),
                },
    {
        reveal(<TxPayload as DeepView>::deep_view);
    }
}

// ============================================================
// Structural Mappers
// ============================================================
impl<T0, T1, T2, T3, T4, T5> BlockHeaderSpec<T0, T1, T2, T3, T4, T5> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, (T3, (T4, T5)))))) -> Self {
        let (version, (previous_block_hash, (merkle_root_hash, (timestamp,
            (bits, nonce))))) = input;
        Self { version, previous_block_hash, merkle_root_hash, timestamp, bits, nonce }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, (T3, (T4, T5))))) {
        let Self { version, previous_block_hash, merkle_root_hash, timestamp, bits, nonce } = self;
        (version, (previous_block_hash, (merkle_root_hash, (timestamp, (bits, nonce)))))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(BlockHeaderSpec::from_structural);
        reveal(BlockHeaderSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, (T3, (T4, T5))))))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(BlockHeaderSpec::from_structural);
        reveal(BlockHeaderSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self {
                        version,
                        previous_block_hash,
                        merkle_root_hash,
                        timestamp,
                        bits,
                        nonce,
                    } =>
                        (version, (previous_block_hash, (merkle_root_hash, (timestamp,
                            (bits, nonce))))),
                },
    {
        reveal(BlockHeaderSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct BlockHeaderForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct BlockHeaderReverse;

impl SpecMap for BlockHeaderForward {
    type Input = BlockHeaderInner;
    type Output = BlockHeaderSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        BlockHeaderSpec::from_structural(input)
    }
}

impl SpecMap for BlockHeaderReverse {
    type Input = BlockHeaderSpec;
    type Output = BlockHeaderInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0, T1, T2> BlockSpec<T0, T1, T2> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (header, (transaction_count, transactions)) = input;
        Self { header, transaction_count, transactions }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { header, transaction_count, transactions } = self;
        (header, (transaction_count, transactions))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(BlockSpec::from_structural);
        reveal(BlockSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(BlockSpec::from_structural);
        reveal(BlockSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { header, transaction_count, transactions } =>
                        (header, (transaction_count, transactions)),
                },
    {
        reveal(BlockSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct BlockForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
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

impl<T0, T1, T2> TxSpec<T0, T1, T2> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (version, (marker_or_input_count, payload)) = input;
        Self { version, marker_or_input_count, payload }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { version, marker_or_input_count, payload } = self;
        (version, (marker_or_input_count, payload))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxSpec::from_structural);
        reveal(TxSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxSpec::from_structural);
        reveal(TxSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { version, marker_or_input_count, payload } =>
                        (version, (marker_or_input_count, payload)),
                },
    {
        reveal(TxSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
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

impl<T0, T1, T2, T3, T4, T5, T6> TxWithWitnessSpec<T0, T1, T2, T3, T4, T5, T6> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, (T3, (T4, (T5, T6))))))) -> Self {
        let (flag, (input_count, (inputs, (output_count, (outputs,
            (witnesses, lock_time)))))) = input;
        Self { flag, input_count, inputs, output_count, outputs, witnesses, lock_time }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, (T3, (T4, (T5, T6)))))) {
        let Self { flag, input_count, inputs, output_count, outputs, witnesses, lock_time } = self;
        (flag, (input_count, (inputs, (output_count, (outputs, (witnesses, lock_time))))))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxWithWitnessSpec::from_structural);
        reveal(TxWithWitnessSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, (T3, (T4, (T5, T6)))))))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxWithWitnessSpec::from_structural);
        reveal(TxWithWitnessSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self {
                        flag,
                        input_count,
                        inputs,
                        output_count,
                        outputs,
                        witnesses,
                        lock_time,
                    } =>
                        (flag, (input_count, (inputs, (output_count, (outputs,
                            (witnesses, lock_time)))))),
                },
    {
        reveal(TxWithWitnessSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxWithWitnessForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxWithWitnessReverse;

impl SpecMap for TxWithWitnessForward {
    type Input = TxWithWitnessInner;
    type Output = TxWithWitnessSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxWithWitnessSpec::from_structural(input)
    }
}

impl SpecMap for TxWithWitnessReverse {
    type Input = TxWithWitnessSpec;
    type Output = TxWithWitnessInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0, T1, T2, T3> TxWithoutWitnessSpec<T0, T1, T2, T3> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, T3)))) -> Self {
        let (inputs, (output_count, (outputs, lock_time))) = input;
        Self { inputs, output_count, outputs, lock_time }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, T3))) {
        let Self { inputs, output_count, outputs, lock_time } = self;
        (inputs, (output_count, (outputs, lock_time)))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxWithoutWitnessSpec::from_structural);
        reveal(TxWithoutWitnessSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, T3))))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxWithoutWitnessSpec::from_structural);
        reveal(TxWithoutWitnessSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { inputs, output_count, outputs, lock_time } =>
                        (inputs, (output_count, (outputs, lock_time))),
                },
    {
        reveal(TxWithoutWitnessSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxWithoutWitnessForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxWithoutWitnessReverse;

impl SpecMap for TxWithoutWitnessForward {
    type Input = TxWithoutWitnessInner;
    type Output = TxWithoutWitnessSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxWithoutWitnessSpec::from_structural(input)
    }
}

impl SpecMap for TxWithoutWitnessReverse {
    type Input = TxWithoutWitnessSpec;
    type Output = TxWithoutWitnessInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0, T1> LockTimeSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::BlockHeight(value),
            R(value) => Self::Timestamp(value),
        }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::BlockHeight(value) => L(value),
            Self::Timestamp(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(LockTimeSpec::from_structural);
        reveal(LockTimeSpec::into_structural);
        match self {
            Self::BlockHeight(_) => {}
            Self::Timestamp(_) => {}
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(LockTimeSpec::from_structural);
        reveal(LockTimeSpec::into_structural);
        match input {
            L(_) => {}
            R(_) => {}
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self::BlockHeight(value) => L(value),
                    Self::Timestamp(value) => R(value),
                },
    {
        reveal(LockTimeSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct LockTimeForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
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

impl<T0, T1, T2> TxinSpec<T0, T1, T2> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (previous_output, (script_sig, sequence)) = input;
        Self { previous_output, script_sig, sequence }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { previous_output, script_sig, sequence } = self;
        (previous_output, (script_sig, sequence))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxinSpec::from_structural);
        reveal(TxinSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxinSpec::from_structural);
        reveal(TxinSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { previous_output, script_sig, sequence } =>
                        (previous_output, (script_sig, sequence)),
                },
    {
        reveal(TxinSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxinForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
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

impl<T0, T1> OutpointSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (transaction_hash, output_index) = input;
        Self { transaction_hash, output_index }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { transaction_hash, output_index } = self;
        (transaction_hash, output_index)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(OutpointSpec::from_structural);
        reveal(OutpointSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(OutpointSpec::from_structural);
        reveal(OutpointSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { transaction_hash, output_index } => (transaction_hash, output_index),
                },
    {
        reveal(OutpointSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct OutpointForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
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

impl<T0, T1> TxoutSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (value, script_pubkey) = input;
        Self { value, script_pubkey }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { value, script_pubkey } = self;
        (value, script_pubkey)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxoutSpec::from_structural);
        reveal(TxoutSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxoutSpec::from_structural);
        reveal(TxoutSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { value, script_pubkey } => (value, script_pubkey),
                },
    {
        reveal(TxoutSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxoutForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
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

impl<T0, T1> ScriptSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (length, bytes) = input;
        Self { length, bytes }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { length, bytes } = self;
        (length, bytes)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ScriptSpec::from_structural);
        reveal(ScriptSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ScriptSpec::from_structural);
        reveal(ScriptSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { length, bytes } => (length, bytes),
                },
    {
        reveal(ScriptSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct ScriptForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
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

impl<T0, T1> WitnessSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (item_count, items) = input;
        Self { item_count, items }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { item_count, items } = self;
        (item_count, items)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(WitnessSpec::from_structural);
        reveal(WitnessSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(WitnessSpec::from_structural);
        reveal(WitnessSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { item_count, items } => (item_count, items),
                },
    {
        reveal(WitnessSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct WitnessForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
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

impl<T0, T1> WitnessItemSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (length, bytes) = input;
        Self { length, bytes }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { length, bytes } = self;
        (length, bytes)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(WitnessItemSpec::from_structural);
        reveal(WitnessItemSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(WitnessItemSpec::from_structural);
        reveal(WitnessItemSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { length, bytes } => (length, bytes),
                },
    {
        reveal(WitnessItemSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct WitnessItemForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct WitnessItemReverse;

impl SpecMap for WitnessItemForward {
    type Input = WitnessItemInner;
    type Output = WitnessItemSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        WitnessItemSpec::from_structural(input)
    }
}

impl SpecMap for WitnessItemReverse {
    type Input = WitnessItemSpec;
    type Output = WitnessItemInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0, T1> TxPayloadSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::TxWithWitness(value),
            R(value) => Self::TxWithoutWitness(value),
        }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::TxWithWitness(value) => L(value),
            Self::TxWithoutWitness(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TxPayloadSpec::from_structural);
        reveal(TxPayloadSpec::into_structural);
        match self {
            Self::TxWithWitness(_) => {}
            Self::TxWithoutWitness(_) => {}
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TxPayloadSpec::from_structural);
        reveal(TxPayloadSpec::into_structural);
        match input {
            L(_) => {}
            R(_) => {}
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self::TxWithWitness(value) => L(value),
                    Self::TxWithoutWitness(value) => R(value),
                },
    {
        reveal(TxPayloadSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxPayloadForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct TxPayloadReverse;

impl SpecMap for TxPayloadForward {
    type Input = TxPayloadInner;
    type Output = TxPayloadSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TxPayloadSpec::from_structural(input)
    }
}

impl SpecMap for TxPayloadReverse {
    type Input = TxPayloadSpec;
    type Output = TxPayloadInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
/// named format combinator for `block_header`.
#[derive(Clone, Copy)]
pub struct BlockHeaderFmt;

pub type BlockHeaderFmtSpec = Named<
    Mapped<
        Pair<U32Le, Pair<Fixed<32>, Pair<Fixed<32>, Pair<U32Le, Pair<U32Le, U32Le>>>>>,
        BiMap<BlockHeaderForward, BlockHeaderReverse>,
    >,
>;

impl BlockHeaderFmt {
    /// specification constructor for `block_header`.
    pub open spec fn spec_inner() -> BlockHeaderFmtSpec {
        Named(
            "block_header",
            Mapped {
                inner: Pair(
                    U32Le,
                    Pair(Fixed::<32>, Pair(Fixed::<32>, Pair(U32Le, Pair(U32Le, U32Le)))),
                ),
                mapper: BiMap(BlockHeaderForward, BlockHeaderReverse),
            },
        )
    }
}

/// named format combinator for `block`.
#[derive(Clone, Copy)]
pub struct BlockFmt;

pub type BlockFmtSpec = Named<
    Mapped<
        Pair<BlockHeaderFmt, Bind<VarInt<true>, spec_fn(u64) -> RepeatN<TxFmt, u64>>>,
        BiMap<BlockForward, BlockReverse>,
    >,
>;

impl BlockFmt {
    /// specification constructor for `block`.
    pub open spec fn spec_inner() -> BlockFmtSpec {
        Named(
            "block",
            Mapped {
                inner: Pair(
                    BlockHeaderFmt,
                    Bind(
                        VarInt::<true>,
                        |transaction_count: u64| RepeatN(transaction_count, TxFmt),
                    ),
                ),
                mapper: BiMap(BlockForward, BlockReverse),
            },
        )
    }
}

/// named format combinator for `tx`.
#[derive(Clone, Copy)]
pub struct TxFmt;

pub type TxFmtSpec = Named<
    Mapped<
        Pair<U32Le, Bind<VarInt<true>, spec_fn(u64) -> TxPayloadFmt>>,
        BiMap<TxForward, TxReverse>,
    >,
>;

impl TxFmt {
    /// specification constructor for `tx`.
    pub open spec fn spec_inner() -> TxFmtSpec {
        Named(
            "tx",
            Mapped {
                inner: Pair(
                    U32Le,
                    Bind(
                        VarInt::<true>,
                        |marker_or_input_count: u64| TxPayloadFmt::spec(marker_or_input_count),
                    ),
                ),
                mapper: BiMap(TxForward, TxReverse),
            },
        )
    }
}

/// named format combinator for `tx_with_witness`.
#[derive(Clone, Copy)]
pub struct TxWithWitnessFmt;

pub type TxWithWitnessFmtSpec = Named<
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
        BiMap<TxWithWitnessForward, TxWithWitnessReverse>,
    >,
>;

impl TxWithWitnessFmt {
    /// specification constructor for `tx_with_witness`.
    pub open spec fn spec_inner() -> TxWithWitnessFmtSpec {
        Named(
            "tx_with_witness",
            Mapped {
                inner: Pair(
                    Const(U8, 1),
                    Bind(
                        VarInt::<true>,
                        |input_count: u64| Pair(
                            RepeatN(input_count, TxinFmt),
                            Bind(
                                VarInt::<true>,
                                |output_count: u64| Pair(
                                    RepeatN(output_count, TxoutFmt),
                                    Pair(RepeatN(input_count, WitnessFmt), LockTimeFmt),
                                ),
                            ),
                        ),
                    ),
                ),
                mapper: BiMap(TxWithWitnessForward, TxWithWitnessReverse),
            },
        )
    }
}

/// named format combinator for `tx_without_witness`.
#[derive(Clone, Copy)]
pub struct TxWithoutWitnessFmt {
    input_count: u64,
}

impl TxWithoutWitnessFmt {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn input_count_spec(&self) -> u64 {
        self.input_count.deep_view()
    }

    pub closed spec fn spec(input_count: u64) -> Self {
        TxWithoutWitnessFmt { input_count }
    }
}

pub type TxWithoutWitnessFmtSpec = Named<
    Mapped<
        Pair<
            RepeatN<TxinFmt, u64>,
            Bind<VarInt<true>, spec_fn(u64) -> Pair<RepeatN<TxoutFmt, u64>, LockTimeFmt>>,
        >,
        BiMap<TxWithoutWitnessForward, TxWithoutWitnessReverse>,
    >,
>;

impl TxWithoutWitnessFmt {
    /// specification constructor for `tx_without_witness`.
    pub open spec fn spec_inner(input_count: u64) -> TxWithoutWitnessFmtSpec {
        Named(
            "tx_without_witness",
            Mapped {
                inner: Pair(
                    RepeatN(input_count, TxinFmt),
                    Bind(
                        VarInt::<true>,
                        |output_count: u64| Pair(RepeatN(output_count, TxoutFmt), LockTimeFmt),
                    ),
                ),
                mapper: BiMap(TxWithoutWitnessForward, TxWithoutWitnessReverse),
            },
        )
    }
}

/// named format combinator for `lock_time`.
#[derive(Clone, Copy)]
pub struct LockTimeFmt;

pub type LockTimeFmtSpec = Named<
    Mapped<
        Choice<Refined<U32Le, PredFnSpec<u32>>, Refined<U32Le, PredFnSpec<u32>>>,
        BiMap<LockTimeForward, LockTimeReverse>,
    >,
>;

impl LockTimeFmt {
    /// specification constructor for `lock_time`.
    pub open spec fn spec_inner() -> LockTimeFmtSpec {
        Named(
            "lock_time",
            Mapped {
                inner: Choice(
                    Refined(U32Le, |x: u32| x >= 0 &&x <= 499999999),
                    Refined(U32Le, |x: u32| x >= 500000000),
                ),
                mapper: BiMap(LockTimeForward, LockTimeReverse),
            },
        )
    }
}

/// named format combinator for `txin`.
#[derive(Clone, Copy)]
pub struct TxinFmt;

pub type TxinFmtSpec = Named<
    Mapped<Pair<OutpointFmt, Pair<ScriptFmt, U32Le>>, BiMap<TxinForward, TxinReverse>>,
>;

impl TxinFmt {
    /// specification constructor for `txin`.
    pub open spec fn spec_inner() -> TxinFmtSpec {
        Named(
            "txin",
            Mapped {
                inner: Pair(OutpointFmt, Pair(ScriptFmt, U32Le)),
                mapper: BiMap(TxinForward, TxinReverse),
            },
        )
    }
}

/// named format combinator for `outpoint`.
#[derive(Clone, Copy)]
pub struct OutpointFmt;

pub type OutpointFmtSpec = Named<
    Mapped<Pair<Fixed<32>, U32Le>, BiMap<OutpointForward, OutpointReverse>>,
>;

impl OutpointFmt {
    /// specification constructor for `outpoint`.
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

/// named format combinator for `txout`.
#[derive(Clone, Copy)]
pub struct TxoutFmt;

pub type TxoutFmtSpec = Named<Mapped<Pair<U64Le, ScriptFmt>, BiMap<TxoutForward, TxoutReverse>>>;

impl TxoutFmt {
    /// specification constructor for `txout`.
    pub open spec fn spec_inner() -> TxoutFmtSpec {
        Named(
            "txout",
            Mapped { inner: Pair(U64Le, ScriptFmt), mapper: BiMap(TxoutForward, TxoutReverse) },
        )
    }
}

/// named format combinator for `script`.
#[derive(Clone, Copy)]
pub struct ScriptFmt;

pub type ScriptFmtSpec = Named<
    Mapped<Bind<VarInt<true>, spec_fn(u64) -> Varied<u64>>, BiMap<ScriptForward, ScriptReverse>>,
>;

impl ScriptFmt {
    /// specification constructor for `script`.
    pub open spec fn spec_inner() -> ScriptFmtSpec {
        Named(
            "script",
            Mapped {
                inner: Bind(VarInt::<true>, |length: u64| Varied(length)),
                mapper: BiMap(ScriptForward, ScriptReverse),
            },
        )
    }
}

/// named format combinator for `witness`.
#[derive(Clone, Copy)]
pub struct WitnessFmt;

pub type WitnessFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> RepeatN<WitnessItemFmt, u64>>,
        BiMap<WitnessForward, WitnessReverse>,
    >,
>;

impl WitnessFmt {
    /// specification constructor for `witness`.
    pub open spec fn spec_inner() -> WitnessFmtSpec {
        Named(
            "witness",
            Mapped {
                inner: Bind(VarInt::<true>, |item_count: u64| RepeatN(item_count, WitnessItemFmt)),
                mapper: BiMap(WitnessForward, WitnessReverse),
            },
        )
    }
}

/// named format combinator for `witness_item`.
#[derive(Clone, Copy)]
pub struct WitnessItemFmt;

pub type WitnessItemFmtSpec = Named<
    Mapped<
        Bind<VarInt<true>, spec_fn(u64) -> Varied<u64>>,
        BiMap<WitnessItemForward, WitnessItemReverse>,
    >,
>;

impl WitnessItemFmt {
    /// specification constructor for `witness_item`.
    pub open spec fn spec_inner() -> WitnessItemFmtSpec {
        Named(
            "witness_item",
            Mapped {
                inner: Bind(VarInt::<true>, |length: u64| Varied(length)),
                mapper: BiMap(WitnessItemForward, WitnessItemReverse),
            },
        )
    }
}

/// named format combinator for `tx_payload`.
#[derive(Clone, Copy)]
pub struct TxPayloadFmt {
    marker_or_input_count: u64,
}

impl TxPayloadFmt {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn marker_or_input_count_spec(&self) -> u64 {
        self.marker_or_input_count.deep_view()
    }

    pub closed spec fn spec(marker_or_input_count: u64) -> Self {
        TxPayloadFmt { marker_or_input_count }
    }
}

pub type TxPayloadFmtSpec = Named<
    Mapped<Sum<TxWithWitnessFmt, TxWithoutWitnessFmt>, BiMap<TxPayloadForward, TxPayloadReverse>>,
>;

impl TxPayloadFmt {
    /// specification constructor for `tx_payload`.
    pub open spec fn spec_inner(marker_or_input_count: u64) -> TxPayloadFmtSpec {
        Named(
            "tx_payload",
            Mapped {
                inner: match marker_or_input_count {
                    0 => L(TxWithWitnessFmt),
                    _ => R(TxWithoutWitnessFmt::spec(marker_or_input_count)),
                },
                mapper: BiMap(TxPayloadForward, TxPayloadReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for BlockHeaderFmt {
        type PVal = BlockHeaderSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for BlockHeaderFmt {
        type Val = BlockHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for BlockHeaderFmt {
        type SValue = BlockHeaderSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for BlockHeaderFmt {
        type SVal = BlockHeaderSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for BlockHeaderFmt {
        type T = BlockHeaderSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for BlockFmt {
        type PVal = BlockSpec;

        #[verifier::opaque]
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

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for BlockFmt {
        type SVal = BlockSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for BlockFmt {
        type T = BlockSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxFmt {
        type PVal = TxSpec;

        #[verifier::opaque]
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

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxFmt {
        type SVal = TxSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxFmt {
        type T = TxSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxWithWitnessFmt {
        type PVal = TxWithWitnessSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TxWithWitnessFmt {
        type Val = TxWithWitnessSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TxWithWitnessFmt {
        type SValue = TxWithWitnessSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxWithWitnessFmt {
        type SVal = TxWithWitnessSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxWithWitnessFmt {
        type T = TxWithWitnessSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxWithoutWitnessFmt {
        type PVal = TxWithoutWitnessSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.input_count_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for TxWithoutWitnessFmt {
        type Val = TxWithoutWitnessSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.input_count_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for TxWithoutWitnessFmt {
        type SValue = TxWithoutWitnessSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.input_count_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxWithoutWitnessFmt {
        type SVal = TxWithoutWitnessSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.input_count_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for TxWithoutWitnessFmt {
        type T = TxWithoutWitnessSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.input_count_spec()).byte_len(v)
        }
    }

    impl SpecParser for LockTimeFmt {
        type PVal = LockTimeSpec;

        #[verifier::opaque]
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

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for LockTimeFmt {
        type SVal = LockTimeSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for LockTimeFmt {
        type T = LockTimeSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxinFmt {
        type PVal = TxinSpec;

        #[verifier::opaque]
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

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxinFmt {
        type SVal = TxinSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxinFmt {
        type T = TxinSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for OutpointFmt {
        type PVal = OutpointSpec;

        #[verifier::opaque]
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

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OutpointFmt {
        type SVal = OutpointSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for OutpointFmt {
        type T = OutpointSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxoutFmt {
        type PVal = TxoutSpec;

        #[verifier::opaque]
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

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxoutFmt {
        type SVal = TxoutSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TxoutFmt {
        type T = TxoutSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ScriptFmt {
        type PVal = ScriptSpec;

        #[verifier::opaque]
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

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ScriptFmt {
        type SVal = ScriptSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ScriptFmt {
        type T = ScriptSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for WitnessFmt {
        type PVal = WitnessSpec;

        #[verifier::opaque]
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

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for WitnessFmt {
        type SVal = WitnessSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for WitnessFmt {
        type T = WitnessSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for WitnessItemFmt {
        type PVal = WitnessItemSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for WitnessItemFmt {
        type Val = WitnessItemSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for WitnessItemFmt {
        type SValue = WitnessItemSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for WitnessItemFmt {
        type SVal = WitnessItemSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for WitnessItemFmt {
        type T = WitnessItemSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TxPayloadFmt {
        type PVal = TxPayloadSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.marker_or_input_count_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for TxPayloadFmt {
        type Val = TxPayloadSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.marker_or_input_count_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for TxPayloadFmt {
        type SValue = TxPayloadSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.marker_or_input_count_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TxPayloadFmt {
        type SVal = TxPayloadSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.marker_or_input_count_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for TxPayloadFmt {
        type T = TxPayloadSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.marker_or_input_count_spec()).byte_len(v)
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
        BlockHeaderSpec::lemma_from_into,
        BlockHeaderSpec::lemma_into_from,
        BlockSpec::lemma_from_into,
        BlockSpec::lemma_into_from,
        TxSpec::lemma_from_into,
        TxSpec::lemma_into_from,
        TxWithWitnessSpec::lemma_from_into,
        TxWithWitnessSpec::lemma_into_from,
        TxWithoutWitnessSpec::lemma_from_into,
        TxWithoutWitnessSpec::lemma_into_from,
        LockTimeSpec::lemma_from_into,
        LockTimeSpec::lemma_into_from,
        TxinSpec::lemma_from_into,
        TxinSpec::lemma_into_from,
        OutpointSpec::lemma_from_into,
        OutpointSpec::lemma_into_from,
        TxoutSpec::lemma_from_into,
        TxoutSpec::lemma_into_from,
        ScriptSpec::lemma_from_into,
        ScriptSpec::lemma_into_from,
        WitnessSpec::lemma_from_into,
        WitnessSpec::lemma_into_from,
        WitnessItemSpec::lemma_from_into,
        WitnessItemSpec::lemma_into_from,
        TxPayloadSpec::lemma_from_into,
        TxPayloadSpec::lemma_into_from,
    };

    impl SafeParser for BlockHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for BlockHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for BlockHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecParser>::spec_parse);
            reveal(<BlockHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: BlockHeaderInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BlockHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecParser>::spec_parse);
            reveal(<BlockHeaderFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: BlockHeaderInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BlockHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for BlockHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for BlockHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<BlockHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<BlockHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for BlockHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecParser>::spec_parse);
            reveal(<BlockHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockHeaderFmt as Consistency>::consistent);
            reveal(<BlockHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: BlockHeaderSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                BlockHeaderSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for BlockHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: BlockHeaderInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BlockHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for BlockHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<BlockHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for BlockHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<BlockHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BlockHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

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
            assert forall|input: BlockInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BlockSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<BlockFmt as SpecParser>::spec_parse);
            reveal(<BlockFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: BlockInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|output: BlockSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
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
            assert forall|input: BlockInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|input: TxInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxFmt as SpecParser>::spec_parse);
            reveal(<TxFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TxInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|output: TxSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
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
            assert forall|input: TxInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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

    impl SafeParser for TxWithWitnessFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxWithWitnessFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxWithWitnessFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecParser>::spec_parse);
            reveal(<TxWithWitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: TxWithWitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxWithWitnessSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecParser>::spec_parse);
            reveal(<TxWithWitnessFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TxWithWitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxWithWitnessSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxWithWitnessFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxWithWitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxWithWitnessFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxWithWitnessFmt as SpecSerializer>::spec_serialize);
            reveal(<TxWithWitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxWithWitnessFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecParser>::spec_parse);
            reveal(<TxWithWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxWithWitnessFmt as Consistency>::consistent);
            reveal(<TxWithWitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: TxWithWitnessSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxWithWitnessSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxWithWitnessFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TxWithWitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxWithWitnessSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxWithWitnessFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxWithWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxWithWitnessFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxWithWitnessFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxWithWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxWithWitnessFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxWithoutWitnessFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.input_count_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxWithoutWitnessFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.input_count_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxWithoutWitnessFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecParser>::spec_parse);
            reveal(<TxWithoutWitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert forall|input: TxWithoutWitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxWithoutWitnessSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecParser>::spec_parse);
            reveal(<TxWithoutWitnessFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert forall|input: TxWithoutWitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxWithoutWitnessSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxWithoutWitnessFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxWithoutWitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxWithoutWitnessFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxWithoutWitnessFmt as SpecSerializer>::spec_serialize);
            reveal(<TxWithoutWitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxWithoutWitnessFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecParser>::spec_parse);
            reveal(<TxWithoutWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxWithoutWitnessFmt as Consistency>::consistent);
            reveal(<TxWithoutWitnessFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert forall|output: TxWithoutWitnessSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxWithoutWitnessSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxWithoutWitnessFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert forall|input: TxWithoutWitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxWithoutWitnessSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxWithoutWitnessFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxWithoutWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxWithoutWitnessFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.input_count_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxWithoutWitnessFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxWithoutWitnessFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxWithoutWitnessFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.input_count_spec());
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
            assert forall|input: LockTimeInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                LockTimeSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            reveal(<LockTimeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: LockTimeInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|output: LockTimeSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
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
            assert forall|input: LockTimeInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|input: TxinInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxinSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxinFmt as SpecParser>::spec_parse);
            reveal(<TxinFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TxinInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|output: TxinSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
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
            assert forall|input: TxinInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|input: OutpointInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OutpointSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<OutpointFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: OutpointInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|output: OutpointSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
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
            assert forall|input: OutpointInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|input: TxoutInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxoutSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxoutFmt as SpecParser>::spec_parse);
            reveal(<TxoutFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TxoutInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|output: TxoutSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
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
            assert forall|input: TxoutInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|input: ScriptInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ScriptSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ScriptFmt as SpecParser>::spec_parse);
            reveal(<ScriptFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ScriptInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|output: ScriptSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
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
            assert forall|input: ScriptInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|input: WitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WitnessFmt as SpecParser>::spec_parse);
            reveal(<WitnessFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: WitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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
            assert forall|output: WitnessSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
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
            assert forall|input: WitnessInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
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

    impl SafeParser for WitnessItemFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for WitnessItemFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for WitnessItemFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecParser>::spec_parse);
            reveal(<WitnessItemFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: WitnessItemInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessItemSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecParser>::spec_parse);
            reveal(<WitnessItemFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: WitnessItemInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessItemSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for WitnessItemFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessItemFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for WitnessItemFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<WitnessItemFmt as SpecSerializer>::spec_serialize);
            reveal(<WitnessItemFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for WitnessItemFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecParser>::spec_parse);
            reveal(<WitnessItemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessItemFmt as Consistency>::consistent);
            reveal(<WitnessItemFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: WitnessItemSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                WitnessItemSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for WitnessItemFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: WitnessItemInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WitnessItemSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for WitnessItemFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<WitnessItemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessItemFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for WitnessItemFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<WitnessItemFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WitnessItemFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TxPayloadFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.marker_or_input_count_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TxPayloadFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.marker_or_input_count_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TxPayloadFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecParser>::spec_parse);
            reveal(<TxPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert forall|input: TxPayloadInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxPayloadSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecParser>::spec_parse);
            reveal(<TxPayloadFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert forall|input: TxPayloadInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxPayloadSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TxPayloadFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TxPayloadFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TxPayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<TxPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TxPayloadFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecParser>::spec_parse);
            reveal(<TxPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxPayloadFmt as Consistency>::consistent);
            reveal(<TxPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert forall|output: TxPayloadSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TxPayloadSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TxPayloadFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert forall|input: TxPayloadInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TxPayloadSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TxPayloadFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TxPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TxPayloadFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TxPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TxPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.marker_or_input_count_spec());
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

    impl<'i> Parser<&'i [u8]> for BlockHeaderFmt {
        type PT = BlockHeader<'i>;

        fn min_byte_len(&self) -> usize {
            80
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<BlockHeaderFmt as SpecParser>::spec_parse);
            reveal(<BlockHeader as DeepView>::deep_view);
            reveal(BlockHeaderSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, version) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, previous_block_hash) = (Fixed::<32>).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, merkle_root_hash) = (Fixed::<32>).parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, timestamp) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n4);
            let (n5, bits) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n5);
            let (n6, nonce) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n6);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6;

            let final_v = BlockHeader {
                version,
                previous_block_hash,
                merkle_root_hash,
                timestamp,
                bits,
                nonce,
            };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, BlockHeader<'i>> for BlockHeaderFmt {
        fn serialize_into(&self, v: &BlockHeader<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<BlockHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<BlockHeaderFmt as SpecByteLen>::byte_len);
            reveal(<BlockHeader as DeepView>::deep_view);
            reveal(BlockHeaderSpec::into_structural);
            let ghost old_obuf = obuf@;

            let BlockHeader {
                version,
                previous_block_hash,
                merkle_root_hash,
                timestamp,
                bits,
                nonce,
            } = v;

            U32Le.serialize_into(version, obuf);
            Fixed::<32>.serialize_into(*previous_block_hash, obuf);
            Fixed::<32>.serialize_into(*merkle_root_hash, obuf);
            U32Le.serialize_into(timestamp, obuf);
            U32Le.serialize_into(bits, obuf);
            U32Le.serialize_into(nonce, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<BlockHeader<'i>> for BlockHeaderFmt {
        fn prepare(&self, v: &BlockHeader<'i>) -> Result<usize, PreSerializeError> {
            reveal(<BlockHeaderFmt as SpecByteLen>::byte_len);
            reveal(<BlockHeader as DeepView>::deep_view);
            reveal(BlockHeaderSpec::into_structural);
            let BlockHeader {
                version,
                previous_block_hash,
                merkle_root_hash,
                timestamp,
                bits,
                nonce,
            } = v;
            let l1 = (U32Le).prepare(version)?;
            let l2 = (Fixed::<32>).prepare(previous_block_hash)?;
            let l3 = (Fixed::<32>).prepare(merkle_root_hash)?;
            let l4 = (U32Le).prepare(timestamp)?;
            let l5 = (U32Le).prepare(bits)?;
            let l6 = (U32Le).prepare(nonce)?;
            let total_len = l1
                .checked_add(l2)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l3)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l4)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l5)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l6)
                .ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

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

            let (n1, header) = (Named("block_header", BlockHeaderFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, transaction_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, transactions) = (RepeatN(transaction_count, TxFmt)).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;

            let final_v = Block { header, transaction_count, transactions };

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

            let Block { header, transaction_count, transactions } = v;

            BlockHeaderFmt.serialize_into(header, obuf);
            VarInt::<true>.serialize_into(transaction_count, obuf);
            RepeatN(*transaction_count, TxFmt).serialize_into(transactions, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Block<'i>> for BlockFmt {
        fn prepare(&self, v: &Block<'i>) -> Result<usize, PreSerializeError> {
            reveal(<BlockFmt as SpecByteLen>::byte_len);
            reveal(<Block as DeepView>::deep_view);
            reveal(BlockSpec::into_structural);
            let Block { header, transaction_count, transactions } = v;
            let l1 = (Named("block_header", BlockHeaderFmt)).prepare(header)?;
            let l2 = (VarInt::<true>).prepare(transaction_count)?;
            let l3 = (RepeatN(*transaction_count, TxFmt)).prepare(transactions)?;
            let total_len = l1
                .checked_add(l2)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l3)
                .ok_or(PreSerializeError::length_too_large())?;
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
            let (n2, marker_or_input_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, payload) = (
                Named("tx_payload", TxPayloadFmt { marker_or_input_count: marker_or_input_count })
            ).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;

            let final_v = Tx { version, marker_or_input_count, payload };

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

            let Tx { version, marker_or_input_count, payload } = v;

            U32Le.serialize_into(version, obuf);
            VarInt::<true>.serialize_into(marker_or_input_count, obuf);

            TxPayloadFmt { marker_or_input_count: *marker_or_input_count }.serialize_into(
                payload,
                obuf,
            );

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Tx<'i>> for TxFmt {
        fn prepare(&self, v: &Tx<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxFmt as SpecByteLen>::byte_len);
            reveal(<Tx as DeepView>::deep_view);
            reveal(TxSpec::into_structural);
            let Tx { version, marker_or_input_count, payload } = v;
            let l1 = (U32Le).prepare(version)?;
            let l2 = (VarInt::<true>).prepare(marker_or_input_count)?;
            let l3 = (
                Named("tx_payload", TxPayloadFmt { marker_or_input_count: *marker_or_input_count })
            ).prepare(payload)?;
            let total_len = l1
                .checked_add(l2)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l3)
                .ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxWithWitnessFmt {
        type PT = TxWithWitness<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxWithWitnessFmt as SpecParser>::spec_parse);
            reveal(<TxWithWitness as DeepView>::deep_view);
            reveal(TxWithWitnessSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, flag) = Const(U8, 1).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, input_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, inputs) = (RepeatN(input_count, TxinFmt)).parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, output_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n4);
            let (n5, outputs) = (RepeatN(output_count, TxoutFmt)).parse(&rest)?;
            let rest = rest.skip(n5);
            let (n6, witnesses) = (RepeatN(input_count, WitnessFmt)).parse(&rest)?;
            let rest = rest.skip(n6);
            let (n7, lock_time) = (Named("lock_time", LockTimeFmt)).parse(&rest)?;
            let rest = rest.skip(n7);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7;

            let final_v = TxWithWitness {
                flag,
                input_count,
                inputs,
                output_count,
                outputs,
                witnesses,
                lock_time,
            };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TxWithWitness<'i>> for TxWithWitnessFmt {
        fn serialize_into(&self, v: &TxWithWitness<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TxWithWitnessFmt as SpecSerializer>::spec_serialize);
            reveal(<TxWithWitnessFmt as SpecByteLen>::byte_len);
            reveal(<TxWithWitness as DeepView>::deep_view);
            reveal(TxWithWitnessSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TxWithWitness {
                flag,
                input_count,
                inputs,
                output_count,
                outputs,
                witnesses,
                lock_time,
            } = v;

            U8.serialize_into(flag, obuf);
            VarInt::<true>.serialize_into(input_count, obuf);
            RepeatN(*input_count, TxinFmt).serialize_into(inputs, obuf);
            VarInt::<true>.serialize_into(output_count, obuf);
            RepeatN(*output_count, TxoutFmt).serialize_into(outputs, obuf);
            RepeatN(*input_count, WitnessFmt).serialize_into(witnesses, obuf);
            LockTimeFmt.serialize_into(lock_time, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxWithWitness<'i>> for TxWithWitnessFmt {
        fn prepare(&self, v: &TxWithWitness<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxWithWitnessFmt as SpecByteLen>::byte_len);
            reveal(<TxWithWitness as DeepView>::deep_view);
            reveal(TxWithWitnessSpec::into_structural);
            let TxWithWitness {
                flag,
                input_count,
                inputs,
                output_count,
                outputs,
                witnesses,
                lock_time,
            } = v;
            let l1 = (Const(U8, 1)).prepare(flag)?;
            let l2 = (VarInt::<true>).prepare(input_count)?;
            let l3 = (RepeatN(*input_count, TxinFmt)).prepare(inputs)?;
            let l4 = (VarInt::<true>).prepare(output_count)?;
            let l5 = (RepeatN(*output_count, TxoutFmt)).prepare(outputs)?;
            let l6 = (RepeatN(*input_count, WitnessFmt)).prepare(witnesses)?;
            let l7 = (Named("lock_time", LockTimeFmt)).prepare(lock_time)?;
            let total_len = l1
                .checked_add(l2)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l3)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l4)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l5)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l6)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l7)
                .ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxWithoutWitnessFmt {
        type PT = TxWithoutWitness<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TxWithoutWitnessFmt as SpecParser>::spec_parse);
            reveal(<TxWithoutWitness as DeepView>::deep_view);
            reveal(TxWithoutWitnessSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, inputs) = (RepeatN(self.input_count, TxinFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, output_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, outputs) = (RepeatN(output_count, TxoutFmt)).parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, lock_time) = (Named("lock_time", LockTimeFmt)).parse(&rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;

            let final_v = TxWithoutWitness { inputs, output_count, outputs, lock_time };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TxWithoutWitness<'i>> for TxWithoutWitnessFmt {
        fn serialize_into(&self, v: &TxWithoutWitness<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TxWithoutWitnessFmt as SpecSerializer>::spec_serialize);
            reveal(<TxWithoutWitnessFmt as SpecByteLen>::byte_len);
            reveal(<TxWithoutWitness as DeepView>::deep_view);
            reveal(TxWithoutWitnessSpec::into_structural);

            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let TxWithoutWitness { inputs, output_count, outputs, lock_time } = v;

            RepeatN(self.input_count, TxinFmt).serialize_into(inputs, obuf);
            VarInt::<true>.serialize_into(output_count, obuf);
            RepeatN(*output_count, TxoutFmt).serialize_into(outputs, obuf);
            LockTimeFmt.serialize_into(lock_time, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxWithoutWitness<'i>> for TxWithoutWitnessFmt {
        fn prepare(&self, v: &TxWithoutWitness<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxWithoutWitnessFmt as SpecByteLen>::byte_len);
            reveal(<TxWithoutWitness as DeepView>::deep_view);
            reveal(TxWithoutWitnessSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let TxWithoutWitness { inputs, output_count, outputs, lock_time } = v;
            let l1 = (RepeatN(self.input_count, TxinFmt)).prepare(inputs)?;
            let l2 = (VarInt::<true>).prepare(output_count)?;
            let l3 = (RepeatN(*output_count, TxoutFmt)).prepare(outputs)?;
            let l4 = (Named("lock_time", LockTimeFmt)).prepare(lock_time)?;
            let total_len = l1
                .checked_add(l2)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l3)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l4)
                .ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for LockTimeFmt {
        type PT = LockTime;

        fn min_byte_len(&self) -> usize {
            4
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<LockTimeFmt as SpecParser>::spec_parse);
            reveal(<LockTime as DeepView>::deep_view);
            reveal(LockTimeSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U32Le).parse(&rest) {
                Ok((n, va)) if va >= 0 &&va <= 499999999 => {
                    Ok((n, LockTime::BlockHeight(va)))
                }
                _ =>
                    match (U32Le).parse(&rest) {
                        Ok((n, va)) if va >= 500000000 => {
                            Ok((n, LockTime::Timestamp(va)))
                        }
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
                LockTime::BlockHeight(v) => {
                    (U32Le).serialize_into(v, obuf);
                }
                LockTime::Timestamp(v) => {
                    (U32Le).serialize_into(v, obuf);
                }
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
                LockTime::BlockHeight(v) => {
                    if !(*v >= 0 &&*v <= 499999999) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U32Le).prepare(v)
                    }
                }
                LockTime::Timestamp(v) => {
                    if !(*v >= 500000000) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U32Le).prepare(v)
                    }
                }
            }
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
            let (n2, script_sig) = (Named("script", ScriptFmt)).parse(&rest)?;
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
            ScriptFmt.serialize_into(script_sig, obuf);
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
            let l2 = (Named("script", ScriptFmt)).prepare(script_sig)?;
            let l3 = (U32Le).prepare(sequence)?;
            let total_len = l1
                .checked_add(l2)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l3)
                .ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for OutpointFmt {
        type PT = Outpoint<'i>;

        fn min_byte_len(&self) -> usize {
            36
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<OutpointFmt as SpecParser>::spec_parse);
            reveal(<Outpoint as DeepView>::deep_view);
            reveal(OutpointSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, transaction_hash) = (Fixed::<32>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, output_index) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;

            let final_v = Outpoint { transaction_hash, output_index };

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

            let Outpoint { transaction_hash, output_index } = v;

            Fixed::<32>.serialize_into(*transaction_hash, obuf);
            U32Le.serialize_into(output_index, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Outpoint<'i>> for OutpointFmt {
        fn prepare(&self, v: &Outpoint<'i>) -> Result<usize, PreSerializeError> {
            reveal(<OutpointFmt as SpecByteLen>::byte_len);
            reveal(<Outpoint as DeepView>::deep_view);
            reveal(OutpointSpec::into_structural);
            let Outpoint { transaction_hash, output_index } = v;
            let l1 = (Fixed::<32>).prepare(transaction_hash)?;
            let l2 = (U32Le).prepare(output_index)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
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

            let (n1, length) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, bytes) = (Varied(length)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;

            let final_v = Script { length, bytes };

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

            let Script { length, bytes } = v;

            VarInt::<true>.serialize_into(length, obuf);
            Varied(*length).serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Script<'i>> for ScriptFmt {
        fn prepare(&self, v: &Script<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ScriptFmt as SpecByteLen>::byte_len);
            reveal(<Script as DeepView>::deep_view);
            reveal(ScriptSpec::into_structural);
            let Script { length, bytes } = v;
            let l1 = (VarInt::<true>).prepare(length)?;
            let l2 = (Varied(*length)).prepare(bytes)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
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

            let (n1, item_count) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, items) = (RepeatN(item_count, WitnessItemFmt)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;

            let final_v = Witness { item_count, items };

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

            let Witness { item_count, items } = v;

            VarInt::<true>.serialize_into(item_count, obuf);
            RepeatN(*item_count, WitnessItemFmt).serialize_into(items, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Witness<'i>> for WitnessFmt {
        fn prepare(&self, v: &Witness<'i>) -> Result<usize, PreSerializeError> {
            reveal(<WitnessFmt as SpecByteLen>::byte_len);
            reveal(<Witness as DeepView>::deep_view);
            reveal(WitnessSpec::into_structural);
            let Witness { item_count, items } = v;
            let l1 = (VarInt::<true>).prepare(item_count)?;
            let l2 = (RepeatN(*item_count, WitnessItemFmt)).prepare(items)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for WitnessItemFmt {
        type PT = WitnessItem<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<WitnessItemFmt as SpecParser>::spec_parse);
            reveal(<WitnessItem as DeepView>::deep_view);
            reveal(WitnessItemSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, length) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, bytes) = (Varied(length)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;

            let final_v = WitnessItem { length, bytes };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, WitnessItem<'i>> for WitnessItemFmt {
        fn serialize_into(&self, v: &WitnessItem<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<WitnessItemFmt as SpecSerializer>::spec_serialize);
            reveal(<WitnessItemFmt as SpecByteLen>::byte_len);
            reveal(<WitnessItem as DeepView>::deep_view);
            reveal(WitnessItemSpec::into_structural);
            let ghost old_obuf = obuf@;

            let WitnessItem { length, bytes } = v;

            VarInt::<true>.serialize_into(length, obuf);
            Varied(*length).serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<WitnessItem<'i>> for WitnessItemFmt {
        fn prepare(&self, v: &WitnessItem<'i>) -> Result<usize, PreSerializeError> {
            reveal(<WitnessItemFmt as SpecByteLen>::byte_len);
            reveal(<WitnessItem as DeepView>::deep_view);
            reveal(WitnessItemSpec::into_structural);
            let WitnessItem { length, bytes } = v;
            let l1 = (VarInt::<true>).prepare(length)?;
            let l2 = (Varied(*length)).prepare(bytes)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TxPayloadFmt {
        type PT = TxPayload<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TxPayloadFmt as SpecParser>::spec_parse);
            reveal(<TxPayload as DeepView>::deep_view);
            reveal(TxPayloadSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.marker_or_input_count {
                0 => {
                    let (n, v) = (Named("tx_with_witness", TxWithWitnessFmt)).parse(&rest)?;
                    (n, TxPayload::TxWithWitness(v))
                }
                _ => {
                    let (n, v) = (
                        Named(
                            "tx_without_witness",
                            TxWithoutWitnessFmt { input_count: self.marker_or_input_count },
                        )
                    ).parse(&rest)?;
                    (n, TxPayload::TxWithoutWitness(v))
                }
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TxPayload<'i>> for TxPayloadFmt {
        fn serialize_into(&self, v: &TxPayload<'i>, obuf: &mut Output) {
            reveal(<TxPayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<TxPayloadFmt as SpecByteLen>::byte_len);
            reveal(<TxPayload as DeepView>::deep_view);
            reveal(TxPayloadSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.marker_or_input_count, v) {
                (0, TxPayload::TxWithWitness(v)) => {
                    (TxWithWitnessFmt).serialize_into(v, obuf);
                }
                (_, TxPayload::TxWithoutWitness(v)) => {
                    (
                        TxWithoutWitnessFmt { input_count: self.marker_or_input_count }
                    ).serialize_into(v, obuf);
                }
                _ => {}
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TxPayload<'i>> for TxPayloadFmt {
        fn prepare(&self, v: &TxPayload<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TxPayloadFmt as SpecByteLen>::byte_len);
            reveal(<TxPayload as DeepView>::deep_view);
            reveal(TxPayloadSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            match (self.marker_or_input_count, v) {
                (0, TxPayload::TxWithWitness(v)) =>
                    (Named("tx_with_witness", TxWithWitnessFmt)).prepare(v),
                (x, TxPayload::TxWithoutWitness(v)) if !(x == 0) =>
                    (
                        Named(
                            "tx_without_witness",
                            TxWithoutWitnessFmt { input_count: self.marker_or_input_count },
                        )
                    ).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }
}
}
