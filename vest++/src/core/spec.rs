use vstd::prelude::*;

verus! {

pub trait SpecCombinator {
    type Type;

    /// Well-formedness predicate for values of [`Self::Type`].
    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }

    /// Serializability constraint for values of [`Self::Type`] and output buffer.
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        true
    }

    /// Parser specification for values of [`Self::Type`].
    /// 
    /// Returns `Some((n, v))` if parsing succeeds, where `n` is the number of bytes consumed
    /// from the input buffer `ibuf`, and `v` is the parsed value.
    /// Returns `None` if parsing fails.
    spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)>;

    /// Serializer specification for values of [`Self::Type`].
    /// 
    /// Takes a value `v` and an output buffer `obuf`, and returns the new output buffer
    /// after serializing `v` into it.
    spec fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8>;
}

} // verus!
