//! ASN.1 OBJECT IDENTIFIER contents.
//!
//! The first two arcs are represented on the wire by the single subidentifier
//! `40 * first + second`.  Importantly, that subidentifier is itself encoded using
//! the same minimal base-128 form as every later arc; it is not restricted to one
//! octet.
use crate::combinators::{
    mapped::spec::{LosslessMapper, LossyMapper, SpecMapper}, Mapped, Pair, RepeatTillEnd,
};
use crate::core::exec::output::OutputBuf;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::{proof::*, spec::*};
use crate::primitives::base128::{Base128Fmt, UInt};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;

use super::ObjectIdentifierFmt;

verus! {

pub type ObjectIdentifierInnerFmt = Pair<Base128Fmt<true>, RepeatTillEnd<Base128Fmt<true>>>;

#[verifier::allow_in_spec]
pub fn object_identifier_inner() -> (inner: ObjectIdentifierInnerFmt)
    returns
        Pair(Base128Fmt::<true>, RepeatTillEnd(Base128Fmt::<true>)),
{
    Pair(Base128Fmt::<true>, RepeatTillEnd(Base128Fmt::<true>))
}

/// Exact semantic representation of an OBJECT IDENTIFIER.
#[verifier::ext_equal]
pub struct ObjectIdentifierSpec {
    pub first: UInt,
    pub second: UInt,
    pub rest: Seq<UInt>,
}

impl ObjectIdentifierSpec {
    /// Structural restrictions imposed by X.690 §8.19, plus the finite `UInt` backend bound
    /// on the combined first subidentifier.
    pub open spec fn wf(&self) -> bool {
        &&& self.first <= 2
        &&& (self.first < 2 ==> self.second < 40)
        &&& (self.first == 2 ==> self.second <= UInt::MAX - 80)
    }
}

pub open spec fn oid_first_subidentifier(v: ObjectIdentifierSpec) -> UInt {
    if !v.wf() {
        0
    } else if v.first < 2 {
        (v.first * 40 + v.second) as UInt
    } else {
        (80 + v.second) as UInt
    }
}

pub open spec fn oid_to_subidentifiers(v: ObjectIdentifierSpec) -> (UInt, Seq<UInt>) {
    (oid_first_subidentifier(v), v.rest)
}

pub open spec fn oid_from_subidentifiers(
    first_subidentifier: UInt,
    rest: Seq<UInt>,
) -> ObjectIdentifierSpec {
    if first_subidentifier < 40 {
        ObjectIdentifierSpec { first: 0, second: first_subidentifier, rest }
    } else if first_subidentifier < 80 {
        ObjectIdentifierSpec { first: 1, second: (first_subidentifier - 40u64) as UInt, rest }
    } else {
        ObjectIdentifierSpec { first: 2, second: (first_subidentifier - 80u64) as UInt, rest }
    }
}

pub proof fn lemma_oid_from_subidentifiers_wf(first: UInt, rest: Seq<UInt>)
    ensures
        oid_from_subidentifiers(first, rest).wf(),
{
}

pub proof fn lemma_oid_subidentifier_roundtrip(first: UInt, rest: Seq<UInt>)
    ensures
        oid_to_subidentifiers(oid_from_subidentifiers(first, rest)) == (first, rest),
{
    lemma_oid_from_subidentifiers_wf(first, rest);
}

pub proof fn lemma_oid_arcs_roundtrip(v: ObjectIdentifierSpec)
    requires
        v.wf(),
    ensures
        oid_from_subidentifiers(oid_first_subidentifier(v), v.rest) == v,
{
}

#[doc(hidden)]
pub struct ObjectIdentifierMapper;

impl SpecMapper for ObjectIdentifierMapper {
    type In = (UInt, Seq<UInt>);
    type Out = ObjectIdentifierSpec;

    open spec fn spec_map(&self, wire: Self::In) -> Self::Out {
        oid_from_subidentifiers(wire.0, wire.1)
    }

    open spec fn spec_map_rev(&self, value: Self::Out) -> Self::In {
        oid_to_subidentifiers(value)
    }

    open spec fn wf_out(&self, value: Self::Out) -> bool {
        value.wf()
    }
}

impl LossyMapper for ObjectIdentifierMapper {
    proof fn lemma_sound_mapper(&self, value: Self::Out) {
        lemma_oid_arcs_roundtrip(value);
    }

    proof fn lemma_mapper_wf_out_in(&self, value: Self::Out) {
    }
}

impl LosslessMapper for ObjectIdentifierMapper {
    proof fn lemma_lossless_mapper(&self, wire: Self::In) {
        lemma_oid_subidentifier_roundtrip(wire.0, wire.1);
    }

    proof fn lemma_mapper_wf_in_out(&self, wire: Self::In) {
        lemma_oid_from_subidentifiers_wf(wire.0, wire.1);
    }
}

#[doc(hidden)]
pub open spec fn object_identifier_fmt() -> Mapped<ObjectIdentifierInnerFmt, ObjectIdentifierMapper> {
    Mapped { inner: object_identifier_inner(), mapper: ObjectIdentifierMapper }
}

proof fn lemma_oid_parser_invariants()
    ensures
        object_identifier_fmt().sound_inv(),
        object_identifier_fmt().strict_inv(),
{
    let fmt = object_identifier_fmt();
    assert forall|wire: (UInt, Seq<UInt>)| #[trigger]
        fmt.inner.consistent(wire) implies {
            &&& fmt.consistent(fmt.mapper.spec_map(wire))
            &&& fmt.mapper.spec_map_rev(fmt.mapper.spec_map(wire)) == wire
        } by {
        fmt.mapper.lemma_lossless_mapper(wire);
        fmt.mapper.lemma_mapper_wf_in_out(wire);
    }
}

mod derived_specs {
    use super::*;

    impl SpecParser for ObjectIdentifierFmt {
        type PVal = ObjectIdentifierSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            object_identifier_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for ObjectIdentifierFmt {
        type Val = ObjectIdentifierSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            object_identifier_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for ObjectIdentifierFmt {
        type SValue = ObjectIdentifierSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            object_identifier_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ObjectIdentifierFmt {
        type SVal = ObjectIdentifierSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            object_identifier_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for ObjectIdentifierFmt {
        type T = ObjectIdentifierSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            object_identifier_fmt().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl SafeParser for ObjectIdentifierFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            object_identifier_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ObjectIdentifierFmt {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            object_identifier_fmt().lemma_productive(ibuf);
        }
    }

    impl SoundParser for ObjectIdentifierFmt {
        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_oid_parser_invariants();
            object_identifier_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl StrictParser for ObjectIdentifierFmt {
        proof fn lemma_parse_strict_consumption(&self, ibuf: Seq<u8>) {
            lemma_oid_parser_invariants();
            object_identifier_fmt().lemma_parse_strict_consumption(ibuf);
        }
    }

    impl GoodSerializer for ObjectIdentifierFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            object_identifier_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ObjectIdentifierFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            object_identifier_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ObjectIdentifierFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            object_identifier_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for ObjectIdentifierFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            object_identifier_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

}

/// Executable OBJECT IDENTIFIER value.
///
/// Keeping the first two arcs separate avoids a second allocation when parsing: the
/// remaining subidentifiers are already produced as one `Vec` by `RepeatTillEnd`.
#[cfg(feature = "alloc")]
pub struct ObjectIdentifier {
    first: UInt,
    second: UInt,
    rest: Vec<UInt>,
}

#[cfg(feature = "alloc")]
impl DeepView for ObjectIdentifier {
    type V = ObjectIdentifierSpec;

    closed spec fn deep_view(&self) -> Self::V {
        ObjectIdentifierSpec { first: self.first, second: self.second, rest: self.rest.deep_view() }
    }
}

#[cfg(feature = "alloc")]
impl ObjectIdentifier {
    pub fn new(first: UInt, second: UInt, rest: Vec<UInt>) -> Self {
        Self { first, second, rest }
    }

    pub fn first(&self) -> (first: UInt)
        ensures
            first == self.deep_view().first,
    {
        self.first
    }

    pub fn second(&self) -> (second: UInt)
        ensures
            second == self.deep_view().second,
    {
        self.second
    }

    pub fn rest(&self) -> &[UInt] {
        self.rest.as_slice()
    }

    pub(crate) fn rest_vec(&self) -> (rest: &Vec<UInt>)
        ensures
            rest.deep_view() == self.deep_view().rest,
    {
        &self.rest
    }

    pub(crate) fn combined_first_subidentifier(&self) -> (combined: UInt)
        ensures
            combined == oid_first_subidentifier(self.deep_view()),
    {
        oid_first_subidentifier_exec(self.first, self.second)
    }
}

pub(crate) fn oid_first_subidentifier_exec(first: UInt, second: UInt) -> (combined: UInt)
    ensures
        combined == oid_first_subidentifier(
            ObjectIdentifierSpec { first, second, rest: Seq::empty() },
        ),
{
    if first > 2 || (first < 2 && second >= 40) || (first == 2 && second > UInt::MAX - 80) {
        0
    } else if first < 2 {
        first * 40 + second
    } else {
        80 + second
    }
}

#[cfg(feature = "alloc")]
impl Parser<&[u8]> for ObjectIdentifierFmt {
    type PT = ObjectIdentifier;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        let (n, (first_subidentifier, rest)) = object_identifier_inner().parse(ibuf)?;
        let (first, second) = if first_subidentifier < 40 {
            (0, first_subidentifier)
        } else if first_subidentifier < 80 {
            (1, first_subidentifier - 40)
        } else {
            (2, first_subidentifier - 80)
        };
        proof {
            lemma_oid_from_subidentifiers_wf(first_subidentifier, rest.deep_view());
        }
        Ok((n, ObjectIdentifier { first, second, rest }))
    }
}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf> Serializer<Output, ObjectIdentifier> for ObjectIdentifierFmt {
    fn serialize_into(&self, v: &ObjectIdentifier, obuf: &mut Output) {
        let ghost vv = v.deep_view();
        let combined = oid_first_subidentifier_exec(v.first, v.second);
        let rest = v.rest.as_slice();
        let pair = (combined, rest);
        object_identifier_inner().serialize_into(&pair, obuf);
    }
}

#[cfg(feature = "alloc")]
impl Prepare<ObjectIdentifier> for ObjectIdentifierFmt {
    fn prepare(&self, v: &ObjectIdentifier) -> Result<usize, PreSerializeError> {
        if v.first > 2 {
            return Err(PreSerializeError::custom("OBJECT IDENTIFIER first arc exceeds 2"));
        }
        if v.first < 2 && v.second >= 40 {
            return Err(
                PreSerializeError::custom(
                    "OBJECT IDENTIFIER second arc exceeds 39 for first arc 0 or 1",
                ),
            );
        }
        if v.first == 2 && v.second > UInt::MAX - 80 {
            return Err(PreSerializeError::length_too_large());
        }
        let combined = oid_first_subidentifier_exec(v.first, v.second);
        let rest = v.rest.as_slice();
        let pair = (combined, rest);
        let len = object_identifier_inner().prepare(&pair)?;
        Ok(len)
    }
}

#[cfg(feature = "alloc")]
impl ByteLen<ObjectIdentifier> for ObjectIdentifierFmt {
    fn length(&self, v: &ObjectIdentifier) -> usize {
        let combined = oid_first_subidentifier_exec(v.first, v.second);
        let rest = v.rest.as_slice();
        let pair = (combined, rest);
        object_identifier_inner().length(&pair)
    }
}

} // verus!
#[cfg(all(test, feature = "alloc"))]
mod tests {
    use super::*;
    use crate::asn1::der::OBJECT_IDENTIFIER;
    use crate::core::exec::{Parser, Prepare, SerializerExt};

    #[test]
    fn oid_roundtrips_multibyte_first_subidentifier() {
        let input = [0x06, 0x03, 0x88, 0x37, 0x03]; // 2.999.3
        let (_, value) = OBJECT_IDENTIFIER.parse(&&input[..]).unwrap();
        assert_eq!(value.first(), 2);
        assert_eq!(value.second(), 999);
        assert_eq!(value.rest(), &[3]);

        let mut output = vec![0; OBJECT_IDENTIFIER.prepare(&value).unwrap()];
        OBJECT_IDENTIFIER.serialize(&value, &mut output);
        assert_eq!(output, input);
    }

    #[test]
    fn oid_rejects_nonminimal_subidentifier() {
        let input = [0x06, 0x02, 0x80, 0x2a];
        assert!(OBJECT_IDENTIFIER.parse(&&input[..]).is_err());
    }
}
