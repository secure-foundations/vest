pub mod spec;

use vstd::prelude::*;

use crate::combinators::choice::Alt;
use crate::combinators::mapped::spec::{IsoMapper, Mapper};
use crate::combinators::Mapped;
use crate::core::spec::SpecType;
use core::marker::PhantomData;

verus! {

/// Mapper that swaps a pair (B, A) to (A, B)
pub struct Swap2Mapper<A, B>(pub PhantomData<(A, B)>);

impl<A: SpecType, B: SpecType> Mapper for Swap2Mapper<A, B> {
    type In = (B, A);

    type Out = (A, B);

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        (i.1, i.0)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o.1, o.0)
    }
}

impl<A: SpecType, B: SpecType> IsoMapper for Swap2Mapper<A, B> {
    proof fn lemma_map_wf(&self, v: Self::In) {
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
    }

    proof fn lemma_map_iso(&self, i: Self::In) {
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

/// Mapper for Permute3: (B, (A, C)) -> (A, (B, C))
pub struct Swap3Mapper1<A, B, C>(pub PhantomData<(A, B, C)>);

impl<A: SpecType, B: SpecType, C: SpecType> Mapper for Swap3Mapper1<A, B, C> {
    type In = (B, (A, C));

    type Out = (A, (B, C));

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        (i.1.0, (i.0, i.1.1))
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o.1.0, (o.0, o.1.1))
    }
}

impl<A: SpecType, B: SpecType, C: SpecType> IsoMapper for Swap3Mapper1<A, B, C> {
    proof fn lemma_map_wf(&self, v: Self::In) {
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
    }

    proof fn lemma_map_iso(&self, i: Self::In) {
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

/// Mapper for Permute3: (C, (A, B)) -> (A, (B, C))
pub struct Swap3Mapper2<A, B, C>(pub PhantomData<(A, B, C)>);

impl<A: SpecType, B: SpecType, C: SpecType> Mapper for Swap3Mapper2<A, B, C> {
    type In = (C, (A, B));

    type Out = (A, (B, C));

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        (i.1.0, (i.1.1, i.0))
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o.1.1, (o.0, o.1.0))
    }
}

impl<A: SpecType, B: SpecType, C: SpecType> IsoMapper for Swap3Mapper2<A, B, C> {
    proof fn lemma_map_wf(&self, v: Self::In) {
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
    }

    proof fn lemma_map_iso(&self, i: Self::In) {
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

/// Mapper for Permute4: (B, (A, (C, D))) -> (A, (B, (C, D)))
pub struct Swap4Mapper1<A, B, C, D>(pub PhantomData<(A, B, C, D)>);

impl<A: SpecType, B: SpecType, C: SpecType, D: SpecType> Mapper for Swap4Mapper1<A, B, C, D> {
    type In = (B, (A, (C, D)));

    type Out = (A, (B, (C, D)));

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        (i.1.0, (i.0, i.1.1))
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o.1.0, (o.0, o.1.1))
    }
}

impl<A: SpecType, B: SpecType, C: SpecType, D: SpecType> IsoMapper for Swap4Mapper1<A, B, C, D> {
    proof fn lemma_map_wf(&self, v: Self::In) {
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
    }

    proof fn lemma_map_iso(&self, i: Self::In) {
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

/// Mapper for Permute4: (C, (A, (B, D))) -> (A, (B, (C, D)))
pub struct Swap4Mapper2<A, B, C, D>(pub PhantomData<(A, B, C, D)>);

impl<A: SpecType, B: SpecType, C: SpecType, D: SpecType> Mapper for Swap4Mapper2<A, B, C, D> {
    type In = (C, (A, (B, D)));

    type Out = (A, (B, (C, D)));

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        (i.1.0, (i.1.1.0, (i.0, i.1.1.1)))
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o.1.1.0, (o.0, (o.1.0, o.1.1.1)))
    }
}

impl<A: SpecType, B: SpecType, C: SpecType, D: SpecType> IsoMapper for Swap4Mapper2<A, B, C, D> {
    proof fn lemma_map_wf(&self, v: Self::In) {
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
    }

    proof fn lemma_map_iso(&self, i: Self::In) {
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

/// Mapper for Permute4: (D, (A, (B, C))) -> (A, (B, (C, D)))
pub struct Swap4Mapper3<A, B, C, D>(pub PhantomData<(A, B, C, D)>);

impl<A: SpecType, B: SpecType, C: SpecType, D: SpecType> Mapper for Swap4Mapper3<A, B, C, D> {
    type In = (D, (A, (B, C)));

    type Out = (A, (B, (C, D)));

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        (i.1.0, (i.1.1.0, (i.1.1.1, i.0)))
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        (o.1.1.1, (o.0, (o.1.0, o.1.1.0)))
    }
}

impl<A: SpecType, B: SpecType, C: SpecType, D: SpecType> IsoMapper for Swap4Mapper3<A, B, C, D> {
    proof fn lemma_map_wf(&self, v: Self::In) {
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
    }

    proof fn lemma_map_iso(&self, i: Self::In) {
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

/// Permute2<P1, P2> parses either (P1, P2) or (P2, P1) and produces (P1::PVal, P2::PVal)
/// Permute2 ::= Alt((P1, P2), Mapped((P2, P1), swap))
pub struct Permute2<P1, P2>(pub P1, pub P2);

/// Permute3<A, B, C> parses any permutation of A, B, C and produces (A::PVal, (B::PVal, C::PVal))
/// Permute3(A, B, C) ::= Alt(
///     (A, Permute2(B, C)),
///     Alt(
///         Mapped((B, Permute2(A, C)), swap2),
///         Mapped((C, Permute2(A, B)), swap3),
///     )
/// )
pub struct Permute3<A, B, C>(pub A, pub B, pub C);

/// Permute4<A, B, C, D> parses any permutation and produces (A::PVal, (B::PVal, (C::PVal, D::PVal)))
/// Permute4(A, B, C, D) ::= Alt(
///     (A, Permute3(B, C, D)),
///     Alt(
///         Mapped((B, Permute3(A, C, D)), swap4_1),
///         Alt(
///             Mapped((C, Permute3(A, B, D)), swap4_2),
///             Mapped((D, Permute3(A, B, C)), swap4_3),
///         )
///     )
/// )
pub struct Permute4<A, B, C, D>(pub A, pub B, pub C, pub D);

} // verus!
