use crate::combinators::{Fixed, Preceded, Refined, Terminated};
use crate::combinators::refined::Tag;
use crate::core::{
    proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{SpecCombinator, SpecParser, SpecSerializer, SpecType},
};
use vstd::prelude::*;

verus! {

// Malleability Examples

// Helper functions that impose trait bounds to test malleability
proof fn requires_ps_roundtrip<T: PSRoundTrip>(parser: T, ibuf: Seq<u8>, obuf: Seq<u8>) {
    parser.theorem_parse_serialize_roundtrip(ibuf, obuf);
}

proof fn requires_non_malleable<T: NonMalleable>(parser: T, buf1: Seq<u8>, buf2: Seq<u8>) {
    parser.lemma_parse_non_malleable(buf1, buf2);
}

proof fn requires_deterministic<T: Deterministic>(combinator: T, v: T::Type, obuf: Seq<u8>)
    requires
        combinator.serializable(v, obuf),
{
    combinator.lemma_serialize_equiv(v, obuf);
}

// These compositions fail to implement `PSRoundTrip`, `NonMalleable`, or `Deterministic`
// traits because they involve `Preceded` or `Terminated` with combinators that lack
// `UniqueWfValue`.
proof fn test_preceded_non_unique_prefix_ps(ibuf: Seq<u8>, obuf: Seq<u8>)
{
    let parser = Preceded(Fixed::<2>, Fixed::<3>);
    // requires_ps_roundtrip(parser, ibuf, obuf); // Should fail: A does not have UniqueWfValue
}
proof fn test_preceded_non_unique_prefix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>)
{
    let parser = Preceded(Fixed::<2>, Fixed::<3>);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: A does not have UniqueWfValue
}
proof fn test_preceded_non_unique_prefix_deterministic(v: Seq<u8>, obuf: Seq<u8>)
{
    let combinator = Preceded(Fixed::<2>, Fixed::<3>);
    // requires_deterministic(combinator, v, obuf); // Should fail: A does not have UniqueWfValue
}
proof fn test_terminated_non_unique_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>)
{
    let parser = Terminated(Fixed::<3>, Fixed::<2>);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: B does not have UniqueWfValue
}
proof fn test_terminated_refined_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>)
{
    let refined = Refined { inner: Fixed::<2>, pred: |v: Seq<u8>| v.len() > 0 ==> v[0] == 0 };
    let parser = Terminated(Fixed::<3>, refined);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: Refined does not have UniqueWfValue
}
proof fn test_preceded_terminated_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>)
{
    let inner = Terminated(Fixed::<2>, Fixed::<1>);
    let outer = Preceded(Fixed::<1>, inner);
    // requires_non_malleable(outer, buf1, buf2); // Should fail: multiple sources of non-uniqueness
}

// Unlike Fixed and Refined, Tag has UniqueWfValue because it restricts
// its well-formed values to exactly one value (the tag).

proof fn test_preceded_tag_prefix_ps(ibuf: Seq<u8>, obuf: Seq<u8>)
{
    let tag = Tag { inner: Fixed::<2>, tag: seq![0u8, 1u8] };
    let combinator = Preceded(tag, Fixed::<3>);
    requires_ps_roundtrip(combinator, ibuf, obuf); // Should pass: Tag has UniqueWfValue
}

proof fn test_preceded_tag_prefix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>)
{
    let tag = Tag { inner: Fixed::<2>, tag: seq![0u8, 1u8] };
    let parser = Preceded(tag, Fixed::<3>);
    requires_non_malleable(parser, buf1, buf2); // Should pass: Tag has UniqueWfValue
}

proof fn test_preceded_tag_prefix_deterministic(v: Seq<u8>, obuf: Seq<u8>)
    requires
        v.len() == 3,
{
    let val = seq![0u8, 1u8];
    let tag = Tag { inner: Fixed::<2>, tag: val };
    let serializer = Preceded(tag, Fixed::<3>);
    
    let witness_va = val;
    // Use serializer.0 to match the trigger pattern exactly
    assert(serializer.0.wf(witness_va));
    assert(serializer.serializable(v, obuf));
    
    requires_deterministic(serializer, v, obuf); // Should pass: Tag has UniqueWfValue
}

proof fn test_terminated_tag_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>)
{
    let tag = Tag { inner: Fixed::<2>, tag: seq![0xFFu8, 0xFFu8] };
    let parser = Terminated(Fixed::<3>, tag);
    requires_non_malleable(parser, buf1, buf2); // Should pass: Tag has UniqueWfValue
}

proof fn test_mixed_preceded_terminated_with_tag_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>)
{
    let tag1 = Tag { inner: Fixed::<1>, tag: seq![0x01u8] };
    let tag2 = Tag { inner: Fixed::<1>, tag: seq![0x02u8] };
    let inner = Terminated(Fixed::<2>, tag1);
    let outer = Preceded(tag2, inner);
    requires_non_malleable(outer, buf1, buf2); // Should pass: both Tags have UniqueWfValue
}

proof fn test_double_terminated_tag_deterministic(v: Seq<u8>)
    requires
        v.len() == 2,
{
    let val1 = seq![0x00u8];
    let val2 = seq![0xFFu8];
    let obuf = Seq::empty();
    let tag1 = Tag { inner: Fixed::<1>, tag: val1 };
    let tag2 = Tag { inner: Fixed::<1>, tag: val2 };
    let inner = Terminated(Fixed::<2>, tag1);
    let outer = Terminated(inner, tag2);
    
    assert(inner.1.wf(val1));
    assert(outer.1.wf(val2));
    requires_deterministic(outer, v, obuf); // Should pass: both Tags have UniqueWfValue
}

} // verus!
