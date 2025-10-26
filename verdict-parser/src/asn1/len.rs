use super::*;
use vstd::prelude::*;

verus! {

/// Combinator for the length field in a TLV tuple
#[derive(Debug, View)]
pub struct Length;

/// NOTE: this should fit into a VarUIntResult
pub type LengthValue = usize;

impl SpecCombinator for Length {
    type Type = LengthValue;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    {
        if s.len() == 0 {
            None
        } else if s[0] < 0x80 {
            // One-byte length
            Some((1, s[0] as LengthValue))
        } else {
            // Multi-byte length
            let bytes = (s[0] - 0x80) as LengthValue;
            match VarUInt(bytes as usize).spec_parse(s.drop_first()) {
                Some((n, v)) => {
                    // Need to check for minimal encoding for non-malleability
                    // For 1-byte length, v > 0x7f
                    // For (2+)-byte length, v can not be represented by fewer bytes
                    if bytes > 0 && !fits_n_bytes_unsigned!(v, bytes - 1) && v > 0x7f && v <= LengthValue::MAX {
                        Some((n + 1, v as LengthValue))
                    } else {
                        None
                    }
                }
                None => None,
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    {
        if v < 0x80 {
            seq![v as u8]
        } else {
            // Find the minimum number of bytes required to represent v
            let bytes = min_num_bytes_unsigned(v as VarUIntResult);
            let buf = VarUInt(bytes as usize).spec_serialize(v as VarUIntResult);
            seq![(0x80 + bytes) as u8] + buf
        }
    }
}

impl SecureSpecCombinator for Length {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        let buf = self.spec_serialize(v);
        if v >= 0x80 {
            let bytes = min_num_bytes_unsigned(v as VarUIntResult);
            let var_uint = VarUInt(bytes as usize);

            lemma_min_num_bytes_unsigned(v as VarUIntResult);

            var_uint.theorem_serialize_parse_roundtrip(v as VarUIntResult);

            let buf2 = var_uint.spec_serialize(v as VarUIntResult);
            assert(buf.drop_first() == buf2);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(buf) {
            if buf[0] < 0x80 {
                assert(seq![ buf[0] ] == buf.subrange(0, 1));
            } else {
                let bytes = (buf[0] - 0x80) as UInt;
                let var_uint = VarUInt(bytes as usize);

                // Base lemmas from VarUInt
                var_uint.theorem_parse_serialize_roundtrip(buf.drop_first());

                // Parse the inner VarUInt
                if let Some((len, v2)) = var_uint.spec_parse(buf.drop_first()) {
                    assert(is_min_num_bytes_unsigned(v2, bytes));
                    lemma_min_num_bytes_unsigned(v2);

                    // Some sequence facts
                    let buf2 = var_uint.spec_serialize(v as VarUIntResult);
                    assert(seq![(0x80 + bytes) as u8] + buf2 == buf.subrange(0, 1 + bytes));
                }
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if s1.len() > 0 {
            let bytes = (s1[0] - 0x80) as UInt;
            if bytes as usize <= uint_size!() {
                VarUInt(bytes as usize).lemma_prefix_secure(s1.drop_first(), s2);
            }
            assert((s1 + s2).drop_first() =~= s1.drop_first() + s2);
        }
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Length {
    type Type = LengthValue;
    type SType = LengthValue;

    fn length(&self, v: Self::SType) -> usize {
        if v < 0x80 {
            let res = 1usize;
            proof {
                assert(self@.spec_serialize(v).len() == 1)
                    by {
                        assert(self@.spec_serialize(v) == seq![v as u8]);
                    };
            }
            res
        } else {
            let bytes = min_num_bytes_unsigned_exec(v as VarUIntResult);
            let res = (1 + bytes) as usize;
            proof {
                lemma_min_num_bytes_unsigned(v as VarUIntResult);

                assert(0 < bytes <= uint_size!()) by {
                    assert(is_min_num_bytes_unsigned(v as VarUIntResult, bytes));
                };

                let var_uint = VarUInt(bytes as usize);
                assert(var_uint.wf()) by {
                    assert(bytes as usize <= uint_size!());
                };
                assert(var_uint.in_bound(v as VarUIntResult)) by {
                    assert(is_min_num_bytes_unsigned(v as VarUIntResult, bytes));
                };

                var_uint.lemma_serialize_ok_len(v as VarUIntResult);
                let buf = var_uint.spec_serialize(v as VarUIntResult);
                assert(buf.len() == bytes as int);

                assert(self@.spec_serialize(v).len() == (1 + bytes) as int)
                    by {
                        assert(self@.spec_serialize(v) == seq![(0x80 + bytes) as u8] + buf);
                    };
            }
            res
        }
    }

    #[inline]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        if s.len() == 0 {
            return Err(ParseError::UnexpectedEndOfInput);
        }

        if s[0] < 0x80 {
            // One-byte length
            return Ok((1, s[0] as LengthValue));
        }

        let bytes = (s[0] - 0x80) as UInt;

        if bytes as usize > uint_size!() {
            return Err(ParseError::Other("Invalid length encoding".to_string()));
        }

        let (len, v) = VarUInt(bytes as usize).parse(slice_drop_first(s))?;

        if bytes > 0 && !fits_n_bytes_unsigned!(v, bytes - 1) && v > 0x7f && v <= LengthValue::MAX as VarUIntResult {
            Ok(((len + 1) as usize, v as LengthValue))
        } else {
            Err(ParseError::Other("Invalid length encoding".to_string()))
        }
    }

    #[inline]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        if v < 0x80 {
            if pos < data.len() {
                data.set(pos, v as u8);
                assert(data@ =~= seq_splice(old(data)@, pos, seq![v as u8]));
                return Ok(1);
            } else {
                return Err(SerializeError::InsufficientBuffer);
            }
        }

        let bytes = min_num_bytes_unsigned_exec(v as VarUIntResult);

        // Check if out of bound
        if pos >= data.len() || pos > usize::MAX - 1 {
            return Err(SerializeError::InsufficientBuffer);
        }

        data.set(pos, (0x80 + bytes) as u8);
        let len = VarUInt(bytes as usize).serialize(v as VarUIntResult, data, pos + 1)?;

        proof {
            lemma_min_num_bytes_unsigned(v as VarUIntResult);
            assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v)));
        }

        Ok(len + 1)
    }
}

}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse() {
        assert_eq!(Length.parse(&[0x0]).unwrap(), (1, 0));
        assert_eq!(Length.parse(&[0x7f]).unwrap(), (1, 0x7f));
        assert_eq!(Length.parse(&[0x81, 0x80]).unwrap(), (2, 0x80));
        assert_eq!(Length.parse(&[0x82, 0x0f, 0xff]).unwrap(), (3, 0x0fff));

        assert!(Length.parse(&[0x80]).is_err());
        assert!(Length.parse(&[0x81, 0x7f]).is_err());
        assert!(Length.parse(&[0x82, 0x00, 0xff]).is_err());
    }
}
