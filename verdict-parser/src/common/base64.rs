use super::*;
use vstd::prelude::*;

verus! {

/// Base64 combinator (RFC 4648)
#[derive(Debug, View)]
pub struct Base64;

impl Base64 {
    /// Some() => valid 6 bits
    /// None => padding byte
    closed spec fn spec_char_to_bits(b: u8) -> Result<Option<u8>, ()> {
        let c = b as char;
        if c >= 'A' && c <= 'Z' {
            Ok(Some((b - 'A' as u8) as u8))
        } else if c >= 'a' && c <= 'z' {
            Ok(Some((b - 'a' as u8 + 26) as u8))
        } else if c >= '0' && c <= '9' {
            Ok(Some((b - '0' as u8 + 52) as u8))
        } else if c == '+' {
            Ok(Some(62))
        } else if c == '/' {
            Ok(Some(63))
        } else if c == '=' {
            Ok(None)
        } else {
            Err(())
        }
    }

    closed spec fn spec_bits_to_char(b: u8) -> u8 {
        if b < 26 {
            (b + 'A' as u8) as u8
        } else if b < 52 {
            (b - 26 + 'a' as u8) as u8
        } else if b < 62 {
            (b - 52 + '0' as u8) as u8
        } else if b == 62 {
            '+' as u8
        } else {
            '/' as u8
        }
    }

    /// Convert a quadruple of 6-bit bytes to a 3-byte sequence
    closed spec fn spec_decode_6_bit_bytes(b1: u8, b2: u8, b3: u8, b4: u8) -> (u8, u8, u8) {
        let v1 = (b1 << 2) | (b2 >> 4);
        let v2 = (b2 << 4) | (b3 >> 2);
        let v3 = (b3 << 6) | b4;
        (v1, v2, v3)
    }

    /// Convert a byte sequence [v1, v2, v3] to a quadruple of 6-bit bytes
    closed spec fn spec_encode_6_bit_bytes(v1: u8, v2: u8, v3: u8) -> (u8, u8, u8, u8) {
        let b1 = v1 >> 2;
        let b2 = ((v1 & 0b11) << 4) | (v2 >> 4);
        let b3 = ((v2 & 0b1111) << 2) | (v3 >> 6);
        let b4 = v3 & 0b111111;
        (b1, b2, b3, b4)
    }

    closed spec fn spec_parse_helper(s: Seq<u8>) -> Result<(usize, Seq<u8>), ()>
        decreases s.len()
    {
        if s.len() == 0 {
            Ok((0, seq![]))
        } else if s.len() < 4 {
            Err(())
        } else {
            let b1 = Self::spec_char_to_bits(s[0]);
            let b2 = Self::spec_char_to_bits(s[1]);
            let b3 = Self::spec_char_to_bits(s[2]);
            let b4 = Self::spec_char_to_bits(s[3]);

            match (b1, b2, b3, b4, Self::spec_parse_helper(s.skip(4))) {
                (Ok(Some(b1)), Ok(Some(b2)), Ok(Some(b3)), Ok(Some(b4)), Ok((len, rest))) => {
                    let (v1, v2, v3) = Self::spec_decode_6_bit_bytes(b1, b2, b3, b4);
                    Ok((s.len() as usize, seq![ v1, v2, v3 ] + rest))
                }

                // Final 4-byte block with 1 padding `=`
                (Ok(Some(b1)), Ok(Some(b2)), Ok(Some(b3)), Ok(None), _) => {
                    let (v1, v2, v3) = Self::spec_decode_6_bit_bytes(b1, b2, b3, 0);
                    if s.len() == 4 && v3 == 0 {
                        Ok((4 as usize, seq![ v1, v2 ]))
                    } else {
                        Err(())
                    }
                }

                // Final 4-byte block with 2 padding `=`s
                (Ok(Some(b1)), Ok(Some(b2)), Ok(None), Ok(None), _) => {
                    let (v1, v2, v3) = Self::spec_decode_6_bit_bytes(b1, b2, 0, 0);
                    if s.len() == 4 && v2 == v3 == 0 {
                        Ok((4 as usize, seq![ v1 ]))
                    } else {
                        Err(())
                    }
                }

                _ => Err(()),
            }
        }
    }

    closed spec fn spec_serialize_helper(v: Seq<u8>) -> Result<Seq<u8>, ()>
        decreases v.len()
    {
        if v.len() == 0 {
            Ok(seq![])
        } else {
            let v1 = v[0];
            let v2 = if v.len() > 1 { v[1] } else { 0 };
            let v3 = if v.len() > 2 { v[2] } else { 0 };

            let (b1, b2, b3, b4) = Self::spec_encode_6_bit_bytes(v1, v2, v3);

            let b1 = Self::spec_bits_to_char(b1);
            let b2 = Self::spec_bits_to_char(b2);
            let b3 = if v.len() > 1 { Self::spec_bits_to_char(b3) } else { '=' as u8 };
            let b4 = if v.len() > 2 { Self::spec_bits_to_char(b4) } else { '=' as u8 };

            if v.len() <= 3 {
                Ok(seq![ b1, b2, b3, b4 ])
            } else {
                match Self::spec_serialize_helper(v.skip(3)) {
                    Ok(rest) => Ok(seq![ b1, b2, b3, b4 ] + rest),
                    Err(()) => Err(())
                }
            }
        }
    }
}

impl SpecCombinator for Base64 {
    type SpecResult = Seq<u8>;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        Self::spec_parse_helper(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        match Self::spec_serialize_helper(v) {
            Ok(s) =>
                if s.len() <= usize::MAX {
                    Ok(s)
                } else {
                    Err(())
                }

            Err(()) => Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}
}

/// Some lemmas
impl Base64 {
    broadcast proof fn encode_spec_decode_6_bit_bytes(v1: u8, v2: u8, v3: u8)
        ensures ({
            let (b1, b2, b3, b4) = #[trigger] Self::spec_encode_6_bit_bytes(v1, v2, v3);
            (v1, v2, v3) == Self::spec_decode_6_bit_bytes(b1, b2, b3, b4)
        })
    {
        // Essentially everything unfolded
        assert(
            v1 == ((v1 >> 2) << 2) | ((((v1 & 0b11) << 4) | (v2 >> 4)) >> 4) &&
            v2 == ((((v1 & 0b11) << 4) | (v2 >> 4)) << 4) | ((((v2 & 0b1111) << 2) | (v3 >> 6)) >> 2) &&
            v3 == ((((v2 & 0b1111) << 2) | (v3 >> 6)) << 6) | (v3 & 0b111111)
        ) by (bit_vector);
    }

    broadcast proof fn spec_encode_6_bit_bytes_range(v1: u8, v2: u8, v3: u8)
        ensures ({
            let (b1, b2, b3, b4) = #[trigger] Self::spec_encode_6_bit_bytes(v1, v2, v3);
            b1 <= 0b111111 &&
            b2 <= 0b111111 &&
            b3 <= 0b111111 &&
            b4 <= 0b111111 &&
            (v3 == 0 ==> b4 == 0) &&
            (v2 == v3 == 0 ==> b3 == b4 == 0)
        })
    {
        assert(
            (v1 >> 2) <= 0b111111 &&
            ((v1 & 0b11) << 4) | (v2 >> 4) <= 0b111111 &&
            ((v2 & 0b1111) << 2) | (v3 >> 6) <= 0b111111 &&
            (v3 & 0b111111) <= 0b111111 &&
            (v3 == 0 ==> (v3 & 0b111111) == 0) &&
            (v2 == v3 == 0 ==> ((v2 & 0b1111) << 2) | (v3 >> 6) == (v3 & 0b111111) == 0)
        ) by (bit_vector);
    }

    broadcast proof fn decode_spec_encode_6_bit_bytes(b1: u8, b2: u8, b3: u8, b4: u8)
        requires b1 <= 0b111111 && b2 <= 0b111111 && b3 <= 0b111111 && b4 <= 0b111111
        ensures ({
            let (v1, v2, v3) = #[trigger] Self::spec_decode_6_bit_bytes(b1, b2, b3, b4);
            (b1, b2, b3, b4) == Self::spec_encode_6_bit_bytes(v1, v2, v3)
        })
    {
        assert(
            b1 <= 0b111111 && b2 <= 0b111111 && b3 <= 0b111111 && b4 <= 0b111111 ==>
            b1 == (((b1 << 2) | (b2 >> 4)) >> 2) &&
            b2 == ((((b1 << 2) | (b2 >> 4)) & 0b11) << 4) | (((b2 << 4) | (b3 >> 2)) >> 4) &&
            b3 == ((((b2 << 4) | (b3 >> 2)) & 0b1111) << 2) | (((b3 << 6) | b4) >> 6) &&
            b4 == ((b3 << 6) | b4) & 0b111111
        ) by (bit_vector);
    }
}

impl SecureSpecCombinator for Base64 {
    open spec fn is_prefix_secure() -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
        decreases v.len()
    {
        let empty: Seq<u8> = seq![];

        if v.len() == 0 {
            assert(self.spec_serialize(v).unwrap() == empty);
            assert(self.spec_parse(empty).unwrap() == (0usize, v));
        } else {
            if let Ok(s) = self.spec_serialize(v) {
                broadcast use
                    Base64::encode_spec_decode_6_bit_bytes,
                    Base64::spec_encode_6_bit_bytes_range,
                    Base64::decode_spec_encode_6_bit_bytes;

                if v.len() < 3 {
                    assert(s.skip(4) == empty);
                } else {
                    self.theorem_serialize_parse_roundtrip(v.skip(3));
                    let s_rest = self.spec_serialize(v.skip(3)).unwrap();
                    assert(s.skip(4) =~= s_rest);
                    assert(s =~= seq![ s[0], s[1], s[2], s[3] ] + s.skip(4));
                }

                assert(self.spec_parse(s).unwrap().1 =~= v);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>)
        decreases s.len()
    {
        let empty: Seq<u8> = seq![];

        if s.len() == 0 {
            assert(self.spec_parse(s).unwrap().1 == empty);
            assert(self.spec_serialize(empty).unwrap() == s);
            assert(empty.subrange(0, 0) == empty);
        } else {
            if let Ok((len, v)) = self.spec_parse(s) {
                broadcast use
                    Base64::encode_spec_decode_6_bit_bytes,
                    Base64::spec_encode_6_bit_bytes_range,
                    Base64::decode_spec_encode_6_bit_bytes;

                if s.len() >= 4 {
                    self.theorem_parse_serialize_roundtrip(s.skip(4));

                    let (len_rest, v_rest) = self.spec_parse(s.skip(4)).unwrap();
                    let s_rest = self.spec_serialize(v_rest).unwrap();
                    assert(s.skip(4) =~= s_rest);

                    if v.len() >= 3 {
                        assert(v_rest =~= v.skip(3));
                    } else if v.len() == 1 || v.len() == 2 {
                        assert(s.len() == 4);
                    }

                    let s2 = self.spec_serialize(v).unwrap();
                    assert(s2 =~= s);
                    assert(s2.subrange(0, s2.len() as int) =~= s);
                }
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

/// Exec versions of some of the spec functions above
impl Base64 {
    #[inline(always)]
    fn char_to_bits(b: u8) -> (res: Result<Option<u8>, ()>)
        ensures res == Self::spec_char_to_bits(b)
    {
        let c = b as char;
        if c >= 'A' && c <= 'Z' {
            Ok(Some((b - 'A' as u8) as u8))
        } else if c >= 'a' && c <= 'z' {
            Ok(Some((b - 'a' as u8 + 26) as u8))
        } else if c >= '0' && c <= '9' {
            Ok(Some((b - '0' as u8 + 52) as u8))
        } else if c == '+' {
            Ok(Some(62))
        } else if c == '/' {
            Ok(Some(63))
        } else if c == '=' {
            Ok(None)
        } else {
            Err(())
        }
    }

    #[inline(always)]
    fn bits_to_char(b: u8) -> (res: u8)
        ensures res == Self::spec_bits_to_char(b)
    {
        if b < 26 {
            (b + 'A' as u8) as u8
        } else if b < 52 {
            (b - 26 + 'a' as u8) as u8
        } else if b < 62 {
            (b - 52 + '0' as u8) as u8
        } else if b == 62 {
            '+' as u8
        } else {
            '/' as u8
        }
    }

    /// Exec version of spec_decode_6_bit_bytes
    #[inline(always)]
    fn decode_6_bit_bytes(b1: u8, b2: u8, b3: u8, b4: u8) -> (res: (u8, u8, u8))
        ensures res == Self::spec_decode_6_bit_bytes(b1, b2, b3, b4)
    {
        let v1 = (b1 << 2) | (b2 >> 4);
        let v2 = (b2 << 4) | (b3 >> 2);
        let v3 = (b3 << 6) | b4;
        (v1, v2, v3)
    }

    /// Exec version of spec_encode_6_bit_bytes
    #[inline(always)]
    fn encode_6_bit_bytes(v1: u8, v2: u8, v3: u8) -> (res: (u8, u8, u8, u8))
        ensures res == Self::spec_encode_6_bit_bytes(v1, v2, v3)
    {
        let b1 = v1 >> 2;
        let b2 = ((v1 & 0b11) << 4) | (v2 >> 4);
        let b3 = ((v2 & 0b1111) << 2) | (v3 >> 6);
        let b4 = v3 & 0b111111;
        (b1, b2, b3, b4)
    }
}

impl Combinator for Base64 {
    type Result<'a> = Vec<u8>;
    type Owned = Vec<u8>;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let mut out = Vec::with_capacity(s.len() / 4 * 3);
        let mut i = 0;
        let len = s.len();

        assert(s@.skip(0) == s@);

        while i < len
            invariant
                0 <= i <= len,
                len == s@.len(),

                Self::spec_parse_helper(s@.skip(i as int)) matches Ok((_, rest)) ==> {
                    &&& Self::spec_parse_helper(s@) matches Ok((_, final_out))
                    &&& final_out =~= out@ + rest
                },

                Self::spec_parse_helper(s@.skip(i as int)) is Err ==>
                    Self::spec_parse_helper(s@) is Err,
            decreases len - i
        {
            assert(len - i == s@.skip(i as int).len());

            if len - i < 4 {
                return Err(ParseError::Other("invalid base64".to_string()));
            }

            let b1 = Self::char_to_bits(s[i]);
            let b2 = Self::char_to_bits(s[i + 1]);
            let b3 = Self::char_to_bits(s[i + 2]);
            let b4 = Self::char_to_bits(s[i + 3]);

            match (b1, b2, b3, b4) {
                // No padding, continue parsing
                (Ok(Some(b1)), Ok(Some(b2)), Ok(Some(b3)), Ok(Some(b4))) => {
                    let (v1, v2, v3) = Self::decode_6_bit_bytes(b1, b2, b3, b4);
                    out.push(v1);
                    out.push(v2);
                    out.push(v3);
                    assert(s@.skip(i as int).skip(4) =~= s@.skip(i + 4));
                }

                // Padding of 1/2 bytes, stop parsing
                (Ok(Some(b1)), Ok(Some(b2)), Ok(Some(b3)), Ok(None)) => {
                    let (v1, v2, v3) = Self::decode_6_bit_bytes(b1, b2, b3, 0);
                    if len - i == 4 && v3 == 0 {
                        out.push(v1);
                        out.push(v2);
                    } else {
                        return Err(ParseError::Other("invalid base64 padding".to_string()));
                    }
                }

                (Ok(Some(b1)), Ok(Some(b2)), Ok(None), Ok(None)) => {
                    let (v1, v2, v3) = Self::decode_6_bit_bytes(b1, b2, 0, 0);
                    if len - i == 4 && v2 == 0 && v3 == 0 {
                        out.push(v1);
                    } else {
                        return Err(ParseError::Other("invalid base64 padding".to_string()));
                    }
                }

                _ => return Err(ParseError::Other("invalid base64".to_string())),
            }

            i += 4;
        }

        Ok((s.len(), out))
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let mut i = 0;
        let mut written = 0;
        let len = v.len();

        if pos >= data.len() {
            return Err(SerializeError::InsufficientBuffer);
        }

        assert(v@.skip(0) == v@);

        while i < len
            invariant
                0 <= i <= len,
                len == v@.len(),

                data@.len() == old(data)@.len(),
                data@ =~= seq_splice(old(data)@, pos, data@.subrange(pos as int, pos + written)),

                Self::spec_serialize_helper(v@.skip(i as int)) matches Ok(rest) ==> {
                    &&& Self::spec_serialize_helper(v@) matches Ok(final_out)
                    &&& final_out =~= data@.subrange(pos as int, pos + written) + rest
                    &&& final_out.len() == written + rest.len()
                },

                // Self::spec_serialize_helper(v@.skip(i as int)) is Err ==>
                //     Self::spec_serialize_helper(v@) is Err,
            decreases len - i
        {
            let v1 = v[i];
            let v2 = if len - i > 1 { v[i + 1] } else { 0 };
            let v3 = if len - i > 2 { v[i + 2] } else { 0 };

            let (b1, b2, b3, b4) = Self::encode_6_bit_bytes(v1, v2, v3);

            let b1 = Self::bits_to_char(b1);
            let b2 = Self::bits_to_char(b2);
            let b3 = if len - i > 1 { Self::bits_to_char(b3) } else { '=' as u8 };
            let b4 = if len - i > 2 { Self::bits_to_char(b4) } else { '=' as u8 };

            if pos < data.len() && data.len() - pos >= written && data.len() - pos - written >= 4 {
                data.set(pos + written, b1);
                data.set(pos + written + 1, b2);
                data.set(pos + written + 2, b3);
                data.set(pos + written + 3, b4);
            } else {
                return Err(SerializeError::InsufficientBuffer);
            }

            if len - i < 3 {
                let ghost empty: Seq<u8> = seq![];
                assert(v@.skip(len as int) =~= empty);
                i = len;
            } else {
                assert(v@.skip(i + 3) =~= v@.skip(i as int).skip(3));
                i += 3;
            }

            written += 4;
        }

        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));

        Ok(written)
    }
}

}

#[cfg(test)]
mod test {
    use super::*;

    fn assert_parses_to(s: &[u8], expected: &[u8]) {
        let (len, out) = Base64.parse(s).unwrap();
        assert_eq!(len, s.len());
        assert_eq!(out, expected);
    }

    #[test]
    fn basic() {
        assert_parses_to(b"aGVsbG8=", b"hello");
        assert_parses_to(b"aGVsbA==", b"hell");
        assert_parses_to(b"aGVs", b"hel");

        assert!(Base64.parse(b"aGVsbG8").is_err());
        assert!(Base64.parse(b"aGVsbA=").is_err());
    }
}
