//! Bounded fixpoint combinator for recursive formats.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::proof::LeafNonMalleable;
use crate::core::proof::StrictCombinator;
use vstd::prelude::*;

pub use exec::{ParserRecBody, PrepareRecBody, SerializerRecBody};
pub use proof::{
    EquivSerializersGeneralRecBody, NoLookAheadRecBody, NonMalleableRecBody, SPRoundTripDpsRecBody,
    StrictRecBody,
};
pub use spec::{
    BundledSpecs, GoodSerializerRecBody, NonTailFmtRecBody, ParamRecSpecs, SafeParserRecBody,
    SoundParserRecBody, SpecRecBody,
};

verus! {

/// Bounded fixpoint combinator for parameterized recursive formats.
///
/// `Param` is the starting parameter for the recursive `Body`.
/// Context-free recursive formats use `Param = ()`.
pub struct FixWith<const LIMIT: usize, Body, Param>(pub Body, pub Param);

impl<const N: usize, Body, Param> LeafNonMalleable for FixWith<N, Body, Param> where
    Param: DeepView<V = Body::Param>,
    Body: StrictRecBody,
    Body::Body: StrictCombinator,
 {
    proof fn nonmal_leaf_inv(&self) {
    }
}

} // verus!
