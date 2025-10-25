use super::*;
use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;

verus! {

/// If it's expected that an INTEGER field is larger than the Int type,
/// then use this combinator to read it as an octet string (with
/// some minimality constraints).
#[derive(Debug, View)]
pub struct BigInt;

asn1_tagged!(BigInt, tag_of!(INTEGER));

/// BigInt represents the integer with a sequence of bytes in big-endian order
/// (same as ASN.1) and the most significant bit of the first byte is the sign bit.
pub type SpecBigIntValue = Seq<u8>;
pub struct BigIntValue<'a>(&'a [u8]);

#[allow(dead_code)]
pub struct BigIntOwned(Vec<u8>);

impl<'a> View for BigIntValue<'a> {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl<'a> PolyfillEq for BigIntValue<'a> {
    #[inline(always)]
    fn polyfill_eq(&self, other: &Self) -> bool {
        self.0.polyfill_eq(&other.0)
    }
}

impl View for BigIntOwned {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl<'a> PolyfillClone for BigIntValue<'a> {
    #[inline(always)]
    fn clone(&self) -> Self {
        proof {
            use_type_invariant(self);
        }
        BigIntValue(&self.0)
    }
}

impl<'a> BigIntValue<'a> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        Self::spec_wf(self@)
    }

    /// `bytes` should be the minimal encoding
    /// i.e. the first byte should not be 0 unless
    ///   1. bytes.len() == 1
    ///   2. bytes[1] >= 0x80
    pub open spec fn spec_wf(bytes: Seq<u8>) -> bool {
        &&& bytes.len() != 0
        &&& bytes[0] == 0 ==> {
            ||| bytes.len() == 1
            // the first byte cannot be removed, otherwise it will turn into a negative number
            ||| bytes[1] >= 0x80
        }
    }

    #[inline(always)]
    pub fn wf(bytes: &'a [u8]) -> (res: bool)
        ensures res == BigIntValue::spec_wf(bytes@)
    {
        bytes.len() != 0 &&
        (bytes[0] != 0 || bytes.len() == 1 || bytes[1] >= 0x80)
    }

    pub open spec fn spec_byte_len(&self) -> usize {
        (self@.len() - 1) as usize
    }

    /// The minimum number of bytes to represent the integer
    #[inline(always)]
    pub fn byte_len(&self) -> (res: usize)
        ensures res == self.spec_byte_len()
    {
        proof {
            use_type_invariant(self);
        }
        self.0.len() - 1
    }

    #[inline(always)]
    pub fn bytes(&self) -> (res: &[u8])
        ensures res@ == self@
    {
        self.0
    }

    // TODO: add more methods to interpret BigIntValue as an integer
}

impl SpecCombinator for BigInt {
    type SpecResult = Seq<u8>;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        new_spec_big_int_inner().spec_parse(s)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        new_spec_big_int_inner().spec_parse_wf(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        new_spec_big_int_inner().spec_serialize(v)
    }
}

impl SecureSpecCombinator for BigInt {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        new_spec_big_int_inner().theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_big_int_inner().theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_big_int_inner().lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for BigInt {
    type Result<'a> = BigIntValue<'a>;
    type Owned = BigIntOwned;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (len, v) = new_big_int_inner().parse(s)?;
        Ok((len, BigIntValue(v)))
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        new_big_int_inner().serialize(v.0, data, pos)
    }
}

/// A condition that the minimal encoding is used
#[derive(View)]
pub struct MinimalBigIntPred;

impl SpecPred for MinimalBigIntPred {
    type Input = Seq<u8>;

    closed spec fn spec_apply(&self, i: &Self::Input) -> bool {
        BigIntValue::spec_wf(*i)
    }
}

impl Pred for MinimalBigIntPred {
    type Input<'a> = &'a [u8];
    type InputOwned = Vec<u8>;

    fn apply(&self, i: &Self::Input<'_>) -> (res: bool)
    {
        BigIntValue::wf(i)
    }
}

type BigIntInner = Refined<OctetString, MinimalBigIntPred>;

pub closed spec fn new_spec_big_int_inner() -> BigIntInner
{
    Refined {
        inner: OctetString,
        predicate: MinimalBigIntPred,
    }
}

#[inline(always)]
fn new_big_int_inner() -> (res: BigIntInner)
    ensures res@ == new_spec_big_int_inner()
{
    Refined {
        inner: OctetString,
        predicate: MinimalBigIntPred,
    }
}

}

impl<'a> Debug for BigIntValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Print self.0 as a big-endian big integer
        write!(f, "BigIntValue(0x")?;
        for b in self.0 {
            write!(f, "{:02x}", b)?;
        }
        write!(f, ")")
    }
}
