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
    BundledSpecs, GoodSerializerRecBody, NonTailFmtRecBody, ParamRecSpecs, ProductiveRecBody,
    SafeParserRecBody, SoundParserRecBody, SpecRecBody,
};

verus! {

/// Bounded fixpoint combinator for parameterized recursive formats.
///
/// `Param` is the starting parameter for the recursive `Body`.
/// Context-free recursive formats use `Param = ()`.
#[derive(Copy)]
pub struct FixWith<const LIMIT: usize, Body, Param>(pub Body, pub Param);

impl<const LIMIT: usize, Body: Clone, Param: Clone> Clone for FixWith<LIMIT, Body, Param> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Body::clone, (&self.0,), cloned.0),
            call_ensures(Param::clone, (&self.1,), cloned.1),
    {
        FixWith(self.0.clone(), self.1.clone())
    }
}

impl<const N: usize, Body, Param> LeafNonMalleable for FixWith<N, Body, Param> where
    Param: DeepView<V = Body::Param>,
    Body: StrictRecBody,
    Body::Body: StrictCombinator,
 {
    proof fn nonmal_leaf_inv(&self) {
    }
}

} // verus!
