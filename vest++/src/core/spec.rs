//! Core specification traits for Vest++ combinators.
use vstd::prelude::*;

verus! {

/// Parser specification.
pub trait SpecParser {
    /// The type of parsed values.
    type PVal;

    /// Attempts to parse a value from `ibuf`.
    ///
    /// Returns `Some((n, v))` on success, where `n` bytes were consumed and `v` is
    /// the parsed value, or `None` on failure.
    spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)>;
}

/// Two parsers have disjoint domains if no input can be successfully parsed by both.
///
/// This is the key condition for establishing [`Unambiguity`] in combinator compositions.
/// See also [`crate::combinators::disjoint`] for broadcast lemmas establishing
/// disjointness for common compositions.
pub open spec fn disjoint_domains<P1: SpecParser, P2: SpecParser>(p1: P1, p2: P2) -> bool {
    forall|input: Seq<u8>| p1.spec_parse(input) is Some && p2.spec_parse(input) is Some ==> false
}

/// Combinator denotations that admit disjoint (mutually exclusive) sets of consistent values.
///
/// Used by [`crate::combinators::Alt`] for non-malleability.
pub trait DisjointFrom<Other: Consistency<Val = Self::Val>>: Consistency {
    /// No value is simultaneously consistent with both `Self` and `Other`.
    proof fn lemma_disjoint(&self, other: &Other, v: Self::Val)
        ensures
            self.consistent(v) && other.consistent(v) ==> false,
    ;
}

/// Returns `true` when parser `p` fails on input `ibuf`.
pub open spec fn parser_fails_on<P: SpecParser>(p: P, ibuf: Seq<u8>) -> bool {
    p.spec_parse(ibuf) is None
}

/// Parser soundness.
///
/// This trait specifies basic properties that a parser must satisfy to be considered sound w.r.t.
/// its format spec.
pub trait SoundParser: SpecByteLen + SpecParser<PVal = Self::T> + Consistency<Val = Self::T> {
    /// Optional invariant (used by spec-function combinators; struct-based combinators
    /// typically leave this as `true`).
    open spec fn sound_inv(&self) -> bool {
        true
    }

    /// For any successful parse `Some((n, _))`, `0 <= n <= ibuf.len()`.
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>)
        requires
            self.sound_inv(),
        ensures
            self.spec_parse(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
    ;

    /// For any successful parse `Some((n, v))`, `n == self.byte_len(v)`.
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>)
        requires
            self.sound_inv(),
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> n == self.byte_len(v),
    ;

    /// For any successful parse `Some((_, v))`, `v` is consistent with the format's spec.
    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>)
        requires
            self.sound_inv(),
        ensures
            self.spec_parse(ibuf) matches Some((_, v)) ==> self.consistent(v),
    ;
}

/// Value well-formedness in relation to a combinator's denotation (format).
///
/// ## Examples
///
/// - [`crate::combinators::Refined`] requires the refinement predicate;
/// - [`crate::combinators::Varied`]/[`crate::combinators::Repeat`] requires matching length/count;
/// - [`crate::combinators::U8`] imposes trivial consistency condition (all `u8` values are consistent with the format);
/// - [`crate::combinators::Void`] is uninhabited and thus has no consistent values.
pub trait Consistency {
    /// The type of values whose consistency is being checked.
    type Val;

    /// Returns `true` if `v` is well-formed w.r.t. this combinator.
    spec fn consistent(&self, v: Self::Val) -> bool;
}

/// Combinators whose consistency admits at most one value.
///
/// Used by e.g., [`crate::combinators::Preceded`] and [`crate::combinators::Terminated`] to
/// recover non-malleability.
pub trait AdmitsUniqueVal: Consistency {
    /// Any two consistent values must be equal.
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val)
        ensures
            self.consistent(v1) && self.consistent(v2) ==> v1 == v2,
    ;
}

/// Spec-level predicate abstraction.
pub trait SpecPred<T> {
    /// Applies the predicate to a value.
    spec fn apply(&self, value: T) -> bool;
}

/// A spec-level predicate function type alias.
pub type PredFnSpec<T> = spec_fn(T) -> bool;

impl<T> SpecPred<T> for PredFnSpec<T> {
    open spec fn apply(&self, value: T) -> bool {
        self(value)
    }
}

/// Destination-passing style (DPS) serializer specification.
///
/// See [`crate::core::proof::EquivSerializers`] for its relationship to [`SpecSerializer`].
pub trait SpecSerializerDps {
    /// The type of values to be serialized.
    type ST;

    /// Serializes `v` by prepending its encoding onto `obuf`.
    spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8>;
}

/// Byte length of serialized values.
pub trait SpecByteLen {
    /// The type of values whose byte length is being computed.
    type T;

    /// Returns the number of bytes `v` occupies when serialized.
    spec fn byte_len(&self, v: Self::T) -> nat;
}

/// Marker for combinators whose corresponding values are raw bytes (`Seq<u8>`).
pub trait BytesCombinator: SpecByteLen<T = Seq<u8>> {
    /// Byte length equals buffer length.
    proof fn lemma_byte_len_is_buf_len(&self, buf: Seq<u8>)
        ensures
            self.byte_len(buf) == buf.len(),
    ;
}

/// Serializer specification.
///
/// See [`crate::core::proof::EquivSerializers`] for its relationship to [`SpecSerializerDps`].
pub trait SpecSerializer {
    /// The type of values to be serialized.
    type SVal;

    /// Serializes `v` into a fresh byte sequence.
    spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8>;
}

/// Conditions for unambiguous format composition.
pub trait Unambiguity: SpecParser {
    /// Returns the condition for this parser (combinator) to be unambiguous.
    open spec fn unambiguous(&self) -> bool {
        true
    }
}

/// A non-tail format combinator would allow for things to be serialized after itself.
///
/// ## Notable formats that are *not* non-tail (i.e., tail formats)
///
/// - [`crate::combinators::Tail`]
/// - [`crate::combinators::Eof`]
/// - [`crate::combinators::OptionalEnd`]
/// - [`crate::combinators::RepeatTillEnd`]
pub trait NonTailFmt: SpecByteLen + SpecSerializerDps<ST = Self::T> {
    /// Optional invariant for DPS serializer proofs.
    open spec fn serialize_dps_inv(&self) -> bool {
        true
    }

    /// The serializer prepends to `obuf` (so it will leave `obuf` intact, no truncation, corruption, etc.).
    ///
    /// Another way to think about this is that the format allows for trailing bytes after itself, whereas a tail format
    /// would only allow for leading bytes before itself.
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>)
        requires
            self.serialize_dps_inv(),
        ensures
            exists|new_buf: Seq<u8>| self.spec_serialize_dps(v, obuf) == new_buf + obuf,
    ;

    /// number of bytes prepended equals `byte_len(v)`.
    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>)
        requires
            self.serialize_dps_inv(),
        ensures
            self.spec_serialize_dps(v, obuf).len() - obuf.len() == self.byte_len(v),
    ;
}

/// A well-behaved serializer.
pub trait GoodSerializer: SpecByteLen + SpecSerializer<SVal = Self::T> {
    /// Optional invariant for serializer-length proofs.
    open spec fn serialize_inv(&self) -> bool {
        true
    }

    /// serialized byte sequence has the expected length.
    proof fn lemma_serialize_len(&self, v: Self::SVal)
        requires
            self.serialize_inv(),
        ensures
            self.spec_serialize(v).len() == self.byte_len(v),
    ;
}

/// Blanket super-trait combining parser, both serializers, and byte-length.
pub trait SpecCombinator: SpecByteLen + Consistency<Val = Self::T> + Unambiguity + SpecParser<
    PVal = Self::T,
> + SpecSerializer<SVal = Self::T> + SpecSerializerDps<ST = Self::T> {

}

impl<T> SpecCombinator for T where
    T: SpecByteLen + Consistency<Val = Self::T> + Unambiguity + SpecParser<
        PVal = Self::T,
    > + SpecSerializer<SVal = Self::T> + SpecSerializerDps<ST = Self::T>,
 {

}

} // verus!
pub use crate::core::fns::{
    ByteLenFnSpec, ParserFnSpec, SerializerDPSFnSpec, SerializerFnSpec, UnambiguityFnSpec,
};
