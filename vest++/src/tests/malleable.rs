use crate::combinators::fixed::spec::axiom_array_from_seq;
use crate::combinators::refined::Tag;
use crate::combinators::{BerBool, Fixed, Preceded, Refined, Terminated, U16Le, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

// (Non)-malleability Examples
// Helper functions that impose certain trait bounds
proof fn requires_sp_roundtrip<T: SPRoundTrip>(serializer: T, v: T::ST, obuf: Seq<u8>)
    requires
        serializer.unambiguous(),
{
    serializer.theorem_serialize_parse_roundtrip(v, obuf);
}

proof fn requires_ps_roundtrip<T: PSRoundTrip>(parser: T, ibuf: Seq<u8>)
    requires
        parser.unambiguous(),
{
    parser.theorem_parse_serialize_roundtrip(ibuf);
}

proof fn requires_non_malleable<T: NonMalleable>(parser: T, buf1: Seq<u8>, buf2: Seq<u8>) {
    parser.lemma_parse_non_malleable(buf1, buf2);
}

proof fn requires_deterministic<T: Deterministic>(
    combinator: T,
    v: <T as SpecSerializer>::ST,
    obuf: Seq<u8>,
) {
    combinator.lemma_serialize_equiv(v, obuf);
}

// These compositions fail to implement `PSRoundTrip`, `NonMalleable`, or `Deterministic`
// traits because they involve `Preceded` or `Terminated` with combinators that lack
// `UniqueWfValue`.
proof fn test_preceded_non_unique_prefix_ps(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let val0 = 0u8;
    let val1 = 0u8;
    let parser = Preceded(U8, U8);
    assert(val0.wf());
    requires_sp_roundtrip(parser, val1, obuf);
    // requires_ps_roundtrip(parser, ibuf, obuf); // Should fail: A does not have UniqueWfValue
}

proof fn test_preceded_non_unique_prefix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = Preceded(U8, U8);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: A does not have UniqueWfValue
}

proof fn test_preceded_non_unique_prefix_deterministic(v: Seq<u8>, obuf: Seq<u8>) {
    let combinator = Preceded(U8, U8);
    // requires_deterministic(combinator, v, obuf); // Should fail: A does not have UniqueWfValue
}

proof fn test_terminated_non_unique_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = Terminated(U8, U8);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: B does not have UniqueWfValue
}

proof fn test_terminated_refined_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let refined = Refined { inner: U8, pred: |v: u8| v == 0 };
    let parser = Terminated(U8, refined);
    // requires_non_malleable(parser, buf1, buf2); // Should fail: Refined does not have UniqueWfValue
}

proof fn test_preceded_terminated_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let inner = Terminated(U8, U8);
    let outer = Preceded(U8, inner);
    // requires_non_malleable(outer, buf1, buf2); // Should fail: multiple sources of non-uniqueness
    let val1 = 0u8;
    let val2 = 0u8;
    assert(val1.wf());
    assert(val2.wf());
    let obuf = Seq::empty();
    let v = 0u8;
    requires_sp_roundtrip(outer, v, obuf);
}

// Unlike Fixed and Refined, Tag has UniqueWfValue because it restricts
// its well-formed values to exactly one value (the tag).
proof fn test_preceded_tag_prefix_ps(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let tag = Tag { inner: Fixed::<2>, tag: [0u8, 0u8] };
    let combinator = Preceded(tag, U8);
    assert(().wf());
    assert(combinator.unambiguous());
    requires_ps_roundtrip(combinator, ibuf);  // Should pass: Tag has UniqueWfValue
}

proof fn test_preceded_tag_prefix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag = Tag { inner: U8, tag: 0u8 };
    let parser = Preceded(tag, U8);
    requires_non_malleable(parser, buf1, buf2);  // Should pass: Tag has UniqueWfValue
}

proof fn test_preceded_tag_prefix_deterministic(v: u8, obuf: Seq<u8>) {
    let val = 0u8;
    let tag = Tag { inner: U8, tag: val };
    let serializer = Preceded(tag, U8);

    assert(().wf());
    assert(serializer.unambiguous()) by {
        unambiguous_pair((tag, U8));
    }
    requires_deterministic(serializer, v, obuf);  // Should pass: Tag has UniqueWfValue
}

proof fn test_terminated_tag_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag = Tag { inner: U8, tag: 0xFFu8 };
    let parser = Terminated(U8, tag);
    requires_non_malleable(parser, buf1, buf2);  // Should pass: Tag has UniqueWfValue
}

proof fn test_mixed_preceded_terminated_with_tag_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag1 = Tag { inner: U8, tag: 0x01u8 };
    let tag2 = Tag { inner: U8, tag: 0x02u8 };
    let inner = Terminated(U8, tag1);
    let outer = Preceded(tag2, inner);
    requires_non_malleable(outer, buf1, buf2);  // Should pass: both Tags have UniqueWfValue
}

proof fn test_double_terminated_tag_deterministic(v: u8)
// requires
//     v.len() == 2,
{
    let val1 = 0x00u8;
    let val2 = 0xFFu8;
    let obuf = Seq::empty();
    let tag1 = Tag { inner: Fixed::<2>, tag: [val1, val1] };
    let tag2 = Tag { inner: Fixed::<2>, tag: [val2, val2] };
    let inner = Terminated(U8, tag1);
    let outer = Terminated(inner, tag2);

    let footer_buf = tag2.spec_serialize_dps((), obuf);
    let inner_buf = tag1.spec_serialize_dps((), footer_buf);

    assert(().wf());
    assert(inner.unambiguous());
    assert(outer.unambiguous());
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

proof fn unambiguous_pair<A: Unambiguity, B: Unambiguity>(pair: (A, B))
    requires
        pair.0.unambiguous(),
        pair.1.unambiguous(),
    ensures
        pair.unambiguous(),
{
}

proof fn test_large_format_with_berbools() {
    // Format: [Header 0xAA] [(BerBool, BerBool, Fixed::<2>)] [Footer 0xFF]
    let val1 = 0x00u8;
    let format_inner = ((BerBool, BerBool), Fixed::<2>);
    let format = Terminated(
        Preceded(Tag { inner: Fixed::<2>, tag: [val1, val1] }, format_inner),
        Tag { inner: U8, tag: 0xFFu8 },
    );

    let v = ((true, false), [0x11u8, 0x22u8]);
    let obuf = Seq::empty();

    // establish well-formedness of header and footer (for serializability)
    let header_val = 0xAAu8;
    let footer_val = 0xFFu8;
    assert(().wf());

    assert(format_inner.unambiguous());

    assert(format.0.0.unambiguous());
    assert(format.0.1.unambiguous());

    assert(format.0.unambiguous()) by {
        unambiguous_pair((format.0.0, format.0.1));
    }
    assert(format.unambiguous()) by {
        unambiguous_pair((format.0, format.1));
    }
    requires_sp_roundtrip(format, v, obuf);
    // requires_non_malleable(format, header_val, footer_val); // Should fail: BerBool is malleable

    // But multiple different buffers parse to the same value
    // [0xAA] [0x01] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0x01
    // [0xAA] [0xFF] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0xFF
    // [0xAA] [0x42] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0x42

    let buf1 = seq![0xAAu8, 0x01u8, 0x00u8, 0x11u8, 0xFFu8];
    let buf2 = seq![0xAAu8, 0xFFu8, 0x00u8, 0x11u8, 0xFFu8];
    let buf3 = seq![0xAAu8, 0x42u8, 0x00u8, 0x11u8, 0xFFu8];

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
