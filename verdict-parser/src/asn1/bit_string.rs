use super::*;
use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;

verus! {

/// Combainator for BIT STRING in ASN.1
/// Essentially a refined version of OctetString
/// where we require that the first bit correctly
/// specifies the trailing zeros
#[derive(Debug, View)]
pub struct BitString;

asn1_tagged!(BitString, tag_of!(BIT_STRING));

// #[derive(View, PolyfillClone)]
// pub struct BitStringValuePoly<T>(pub T);

pub type SpecBitStringValue = Seq<u8>;

pub struct BitStringValue<'a>(&'a [u8]);
#[allow(dead_code)]
pub struct BitStringValueOwned(Vec<u8>);

impl<'a> PolyfillClone for BitStringValue<'a> {
    #[inline(always)]
    fn clone(&self) -> Self {
        proof {
            use_type_invariant(self);
        }
        BitStringValue(&self.0)
    }
}

impl<'a> View for BitStringValue<'a> {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl View for BitStringValueOwned {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl<'a> BitStringValue<'a> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        Self::spec_wf(self@)
    }

    pub open spec fn spec_wf(s: SpecBitStringValue) -> bool {
        // Empty string
        ||| s.len() == 1 && s[0] == 0

        // Otherwise, check that all trailing bits (as declared in bytes[0]) are zeros
        ||| s.len() > 1 && s[0] <= s.last().trailing_zeros()
    }

    #[inline(always)]
    pub fn wf(s: &'a [u8]) -> (res: bool)
        ensures res == Self::spec_wf(s@)
    {
        s.len() == 1 && s[0] == 0
        || s.len() > 1 && s[0] as u32 <= s[s.len() - 1].trailing_zeros()
    }

    /// Create a BitString from raw bytes
    /// The first byte of the slice should indicate the number of trailing zeros
    #[inline(always)]
    pub fn new_raw(s: &'a [u8]) -> (res: Option<BitStringValue<'a>>)
        ensures
            res matches Some(res) ==> res@ == s@ && Self::spec_wf(res@),
            res.is_none() ==> !Self::spec_wf(s@)
    {
        if Self::wf(s) {
            Some(BitStringValue(s))
        } else {
            None
        }
    }

    /// Get the number of padded zeros at the end
    #[inline(always)]
    pub fn trailing_zeros(&self) -> u8
    {
        proof {
            use_type_invariant(self);
        }
        self.0[self.0.len() - 1]
    }

    pub closed spec fn spec_bytes(s: SpecBitStringValue) -> SpecBitStringValue {
        s.drop_first()
    }

    /// Get the actual (zero-padded) bit string
    #[inline(always)]
    pub fn bytes(&self) -> (res: &[u8])
        ensures res@ == Self::spec_bytes(self@)
    {
        proof {
            use_type_invariant(self);
        }
        slice_drop_first(self.0)
    }

    /// Check if the n-th bit is set (counting from 0)
    /// e.g. the 0-th bit is the most significant bit of the first byte
    /// the 8-th bit is the most significant bit of the second byte
    pub closed spec fn spec_has_bit(s: SpecBitStringValue, n: int) -> bool {
        &&& n >= 0
        &&& s.len() > 1 + n / 8
        &&& s[1 + n / 8] & (1u8 << (7 - n % 8)) != 0
    }

    #[inline(always)]
    pub fn has_bit(&self, n: usize) -> (res: bool)
        ensures res == Self::spec_has_bit(self@, n as int)
    {
        proof {
            use_type_invariant(self);
        }
        self.0.len() > 1 + n / 8 && self.0[1 + n / 8] & (1u8 << (7 - n as usize % 8)) != 0
    }
}

impl SpecCombinator for BitString {
    type SpecResult = SpecBitStringValue;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match OctetString.spec_parse(s) {
            Ok((len, bytes)) =>
                if BitStringValue::spec_wf(bytes) {
                    Ok((len, bytes))
                } else {
                    Err(())
                }

            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        OctetString.spec_parse_wf(s);
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if BitStringValue::spec_wf(v) {
            OctetString.spec_serialize(v)
        } else {
            Err(())
        }
    }
}

impl SecureSpecCombinator for BitString {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        OctetString.theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        OctetString.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        OctetString.lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for BitString {
    type Result<'a> = BitStringValue<'a>;
    type Owned = BitStringValueOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (len, v) = OctetString.parse(s)?;

        if let Some(s) = BitStringValue::new_raw(v) {
            Ok((len, s))
        } else {
            Err(ParseError::Other("Ill-formed bit string".to_string()))
        }
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        proof {
            use_type_invariant(&v);
        }
        OctetString.serialize(v.0, data, pos)
    }
}

}

impl<'a> Debug for BitStringValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BitStringValue([{}] ",
            (self.0.len() - 1) * 8 - self.0[0] as usize
        )?;

        // Print the hex values
        for i in 1..self.0.len() {
            write!(f, "{:02x}", self.0[i])?;
        }

        write!(f, ")")
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use der::Encode;

    fn serialize_bit_string(v: BitStringValue) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; v.bytes().len() + 10];
        data[0] = 0x03; // Prepend the tag byte
        let len = BitString.serialize(v, &mut data, 1)?;
        data.truncate(len + 1);
        Ok(data)
    }

    #[test]
    fn diff_with_der() {
        // The first byte of raw should denote the number of trailing zeros
        let diff = |raw: &[u8]| {
            let res1 = serialize_bit_string(BitStringValue::new_raw(raw).unwrap()).map_err(|_| ());
            let res2 = der::asn1::BitString::new(raw[0], &raw[1..])
                .unwrap()
                .to_der()
                .map_err(|_| ());
            assert_eq!(res1, res2);
        };

        diff(&[0]);
        diff(&[5, 0b11100000]);
        diff(&[4, 0b11100000]);
    }

    #[test]
    fn has_bit() {
        let (_, s) = BitString.parse(&[0x02, 0x01, 0x86]).unwrap();
        assert_eq!(s.has_bit(0), true);
        assert_eq!(s.has_bit(1), false);
        assert_eq!(s.has_bit(2), false);
        assert_eq!(s.has_bit(3), false);
        assert_eq!(s.has_bit(4), false);
        assert_eq!(s.has_bit(5), true);
        assert_eq!(s.has_bit(6), true);
        assert_eq!(s.has_bit(7), false);
        assert_eq!(s.has_bit(100), false);
    }
}
