//! Bounded fixpoint combinator for recursive and mutually recursive formats.
//!
//! Body proof traits state preservation of
//! each invariant under the inductive hypothesis.
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

use crate::core::{proof::*, spec::*};

verus! {

/// Bounded fixpoint combinator for parameterized recursive formats.
///
/// `Param` is the starting parameter for the recursive `Body`.
/// Context-free recursive formats use `Param = ()`.
#[derive(Copy)]
pub struct FixWith<const LIMIT: usize, Body, Param>(pub Body, pub Param);

// spec fn fix_<T>(r: spec_fn(ParserFnSpec<T>) -> impl SpecParser<PVal = T>, input: Seq<u8>) -> impl SpecParser<PVal = T>
spec fn fix_<T>(r: spec_fn(ParserFnSpec<T>) -> impl SpecParser<PVal = T>, input: Seq<u8>) -> Option<
    (int, T),
>
    decreases input.len(),
{
    let f = r;
    let call_back = |buf: Seq<u8>|
        if buf.len() < input.len() {
            fix_(r, buf)
        } else {
            None
        };
    f(call_back).spec_parse(input)
}

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
