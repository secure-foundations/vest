use crate::combinators::refined::Tag;
use crate::combinators::{BerBool, Fixed, Preceded, Refined, Terminated};
use crate::core::{
    proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{SpecCombinator, SpecParser, SpecSerializer, SpecSerializerDps, SpecType},
};
use vstd::prelude::*;

verus! {

// (Non)-malleability Examples
// Helper functions that impose certain trait bounds
proof fn requires_sp_roundtrip<T: SPRoundTrip>(serializer: T, v: T::Type, obuf: Seq<u8>)
    requires
        serializer.serializable(v, obuf),
{
    serializer.theorem_serialize_parse_roundtrip(v, obuf);
}

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
proof fn test_preceded_non_unique_prefix_ps(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let val = seq![0u8, 1u8];
    let parser = Preceded(Fixed::<2>, Fixed::<3>);
    assert(parser.0.wf(val));
    requires_sp_roundtrip(parser, val, obuf);
    // requires_ps_roundtrip(parser, ibuf, obuf); // Should fail: A does not have UniqueWfValue
}

proof fn test_preceded_non_unique_prefix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = Preceded(Fixed::<2>, Fixed::<3>);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: A does not have UniqueWfValue
}

proof fn test_preceded_non_unique_prefix_deterministic(v: Seq<u8>, obuf: Seq<u8>) {
    let combinator = Preceded(Fixed::<2>, Fixed::<3>);
    // requires_deterministic(combinator, v, obuf); // Should fail: A does not have UniqueWfValue
}

proof fn test_terminated_non_unique_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = Terminated(Fixed::<3>, Fixed::<2>);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: B does not have UniqueWfValue
}

proof fn test_terminated_refined_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let refined = Refined { inner: Fixed::<2>, pred: |v: Seq<u8>| v.len() > 0 ==> v[0] == 0 };
    let parser = Terminated(Fixed::<3>, refined);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: Refined does not have UniqueWfValue
}

proof fn test_preceded_terminated_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let inner = Terminated(Fixed::<2>, Fixed::<1>);
    let outer = Preceded(Fixed::<1>, inner);
    // requires_non_malleable(outer, buf1, buf2); // Should fail: multiple sources of non-uniqueness
    let val1 = seq![0u8];
    let val2 = seq![0u8];
    assert(outer.0.wf(val1));
    assert(inner.1.wf(val2));
    let obuf = Seq::empty();
    let v = seq![0u8, 0u8, 0u8, 0u8];
    requires_sp_roundtrip(outer, v, obuf);
}

// Unlike Fixed and Refined, Tag has UniqueWfValue because it restricts
// its well-formed values to exactly one value (the tag).
proof fn test_preceded_tag_prefix_ps(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let tag = Tag { inner: Fixed::<2>, tag: seq![0u8, 1u8] };
    let combinator = Preceded(tag, Fixed::<3>);
    requires_ps_roundtrip(combinator, ibuf, obuf);  // Should pass: Tag has UniqueWfValue
}

proof fn test_preceded_tag_prefix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag = Tag { inner: Fixed::<2>, tag: seq![0u8, 1u8] };
    let parser = Preceded(tag, Fixed::<3>);
    requires_non_malleable(parser, buf1, buf2);  // Should pass: Tag has UniqueWfValue
}

proof fn test_preceded_tag_prefix_deterministic(v: Seq<u8>, obuf: Seq<u8>)
    requires
        v.len() == 3,
{
    let val = seq![0u8, 1u8];
    let tag = Tag { inner: Fixed::<2>, tag: val };
    let serializer = Preceded(tag, Fixed::<3>);

    // Use serializer.0 to match the trigger pattern exactly
    assert(serializer.0.wf(()));
    assert(serializer.serializable(v, obuf));

    requires_deterministic(serializer, v, obuf);  // Should pass: Tag has UniqueWfValue
}

proof fn test_terminated_tag_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag = Tag { inner: Fixed::<2>, tag: seq![0xFFu8, 0xFFu8] };
    let parser = Terminated(Fixed::<3>, tag);
    requires_non_malleable(parser, buf1, buf2);  // Should pass: Tag has UniqueWfValue
}

proof fn test_mixed_preceded_terminated_with_tag_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag1 = Tag { inner: Fixed::<1>, tag: seq![0x01u8] };
    let tag2 = Tag { inner: Fixed::<1>, tag: seq![0x02u8] };
    let inner = Terminated(Fixed::<2>, tag1);
    let outer = Preceded(tag2, inner);
    requires_non_malleable(outer, buf1, buf2);  // Should pass: both Tags have UniqueWfValue
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

    assert(inner.1.wf(()));
    assert(outer.1.wf(()));
    requires_deterministic(outer, v, obuf);  // Should pass: both Tags have UniqueWfValue
}

// BerBool: Malleable Boolean Combinator Tests
proof fn test_berbool_sp_roundtrip(v: bool, obuf: Seq<u8>) {
    let combinator = BerBool;
    requires_sp_roundtrip(combinator, v, obuf);  // Should pass: BerBool implements SPRoundTrip
}

proof fn test_berbool_fails_ps_roundtrip(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let parser = BerBool;
    // requires_ps_roundtrip(parser, ibuf, obuf); // Would fail: BerBool does not implement PSRoundTrip
}

proof fn test_berbool_fails_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = BerBool;
    // requires_non_malleable(parser, buf1, buf2); // Would fail: BerBool does not implement NonMalleable
}

proof fn test_large_format_with_berbools() {
    // Format: [Header 0xAA] [(BerBool, BerBool, Fixed::<2>)] [Footer 0xFF]
    let format = Terminated(
        Preceded(Tag { inner: Fixed::<1>, tag: seq![0xAAu8] }, ((BerBool, BerBool), Fixed::<2>)),
        Tag { inner: Fixed::<1>, tag: seq![0xFFu8] },
    );

    let v = ((true, false), seq![0x11u8, 0x22u8]);
    let obuf = Seq::empty();

    // establish well-formedness of header and footer (for serializability)
    let header_val = seq![0xAAu8];
    let footer_val = seq![0xFFu8];
    assert(format.0.0.wf(()));
    assert(format.1.wf(()));

    // serialize-parse roundtrip should still hold
    requires_sp_roundtrip(format, v, obuf);
    // requires_non_malleable(format, header_val, footer_val); // Should fail: BerBool is malleable

    // But multiple different buffers parse to the same value
    // [0xAA] [0x01] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0x01
    // [0xAA] [0xFF] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0xFF
    // [0xAA] [0x42] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0x42

    let buf1 = seq![0xAAu8, 0x01u8, 0x00u8, 0x11u8, 0x22u8, 0xFFu8];
    let buf2 = seq![0xAAu8, 0xFFu8, 0x00u8, 0x11u8, 0x22u8, 0xFFu8];
    let buf3 = seq![0xAAu8, 0x42u8, 0x00u8, 0x11u8, 0x22u8, 0xFFu8];

    if let Some((n1, v1)) = format.spec_parse(buf1) {
        if let Some((n2, v2)) = format.spec_parse(buf2) {
            if let Some((n3, v3)) = format.spec_parse(buf3) {
                assert(v1 == v);
                assert(v2 == v);
                assert(v3 == v);
                assert(n1 == n2 == n3);

                // But all byte prefixes are different
                assert(buf1.take(n1)[1] == 0x01u8);
                assert(buf2.take(n2)[1] == 0xFFu8);
                assert(buf3.take(n3)[1] == 0x42u8);
            }
        }
    }
}

} // verus!
