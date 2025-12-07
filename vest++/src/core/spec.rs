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

    /// Destination passing style serializer specification for values of [`Self::Type`].
    ///
    /// Takes a value `v` and an output buffer `obuf`, and returns the new output buffer
    /// after serializing `v` into it.
    spec fn spec_serialize_dps(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8>;

    /// Serializer specification for values of [`Self::Type`].
    ///
    /// Takes a value `v` and returns the serialized bytes.
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.spec_serialize_dps(v, Seq::empty())
    }

    /// Lemma: parser returns valid buffer positions
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
    ;

    /// Lemma: serializer *prepends* to the output buffer
    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>)
        requires
            self.serializable(v, obuf),
        ensures
            self.wf(v) ==> exists|new_buf: Seq<u8>|
                self.spec_serialize_dps(v, obuf) == new_buf + obuf,
    ;

    /// Lemma: parser returns well-formed values
    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.wf(v),
    ;
}

} // verus!
