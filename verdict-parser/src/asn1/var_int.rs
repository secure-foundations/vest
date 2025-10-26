use super::*;
use vstd::prelude::*;

verus! {

/// Combinator for variable-length integers in big-endian
/// The length is assumed to be <= uint_size!()
#[derive(Debug, View)]
pub struct VarUInt(pub usize);

pub type VarUIntResult = UInt;
pub type VarIntResult = Int;

impl VarUInt {
    pub open spec fn wf(&self) -> bool
    {
        self.0 <= uint_size!()
    }

    pub open spec fn in_bound(&self, v: VarUIntResult) -> bool
    {
        fits_n_bytes_unsigned!(v, self.0)
    }
}

impl SpecCombinator for VarUInt {
    type Type = VarUIntResult;
    
    open spec fn wf(&self, v: Self::Type) -> bool {
        self.in_bound(v)
    }
    
    open spec fn requires(&self) -> bool {
        self.wf()
    }

    /// Parse the first `self.0` bytes of `s` as an unsigned integer in big-endian
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, VarUIntResult)>
        decreases self.0
    {
        if !self.wf() || self.0 > s.len() {
            None
        } else if self.0 == 0 {
            Some((0, 0))
        } else {
            let byte = s[0];
            match Self((self.0 - 1) as usize).spec_parse(s.drop_first()) {
                None => None,
                Some((_, rest)) => Some((self.0 as int, prepend_byte!(rest, byte, self.0 - 1))),
            }
        }
    }

    /// Serialize `v` as a big-endian integer with `self.0` bytes
    open spec fn spec_serialize(&self, v: VarUIntResult) -> Seq<u8>
        decreases self.0
    {
        if !self.wf() || !self.in_bound(v) {
            seq![]
        } else if self.0 == 0 {
            seq![]
        } else {
            // Encode the least significant (self.0 - 1) bytes of v
            // then prepend the self.0-th byte
            let rest = Self((self.0 - 1) as usize).spec_serialize(v & n_byte_max_unsigned!(self.0 - 1));
            seq![ get_nth_byte!(v, self.0 - 1) ] + rest
        }
    }
}

/// Some lemmas about VarUInt::spec_parse and VarUInt::spec_serialize
impl VarUInt {
    pub proof fn lemma_parse_ok(&self, s: Seq<u8>)
        ensures self.spec_parse(s).is_some() <==> self.wf() && self.0 <= s.len()
        decreases self.0
    {
        if self.0 > 0 {
            Self((self.0 - 1) as usize).lemma_parse_ok(s.drop_first());
        }
    }

    /// Parsed results should fit in self.0 bytes
    pub proof fn lemma_parse_ok_bound(&self, s: Seq<u8>)
        requires self.spec_parse(s).is_some()
        ensures self.in_bound(self.spec_parse(s).unwrap().1)
        decreases self.0
    {
        if self.0 > 0 {
            let rest = Self((self.0 - 1) as usize);

            rest.lemma_parse_ok_bound(s.drop_first());

            let s_0 = s[0];
            let (_, rest_parsed) = rest.spec_parse(s.drop_first()).unwrap();
            let self_len = self.0;

            // If rest_parsed is in_bound (wrt self.0 - 1)
            // so does prepend_byte!(rest_parsed, s_0, self_len - 1) (wrt self.0)
            assert(
                0 < self_len <= uint_size!() ==>
                fits_n_bytes_unsigned!(rest_parsed, self_len - 1) ==>
                fits_n_bytes_unsigned!(
                    prepend_byte!(rest_parsed, s_0, self_len - 1),
                    self_len
                )
            ) by (bit_vector);
        }
    }

    pub proof fn lemma_serialize_ok(&self, v: VarUIntResult)
        ensures (self.wf() && self.in_bound(v))
        decreases self.0
    {
        if 0 < self.0 <= uint_size!() && self.in_bound(v) {
            let self_len = self.0;
            Self((self.0 - 1) as usize).lemma_serialize_ok(v & n_byte_max_unsigned!(self_len - 1));
            assert(fits_n_bytes_unsigned!(v & n_byte_max_unsigned!(self_len - 1), self_len - 1)) by (bit_vector);
        }
    }

    pub proof fn lemma_serialize_ok_len(&self, v: VarUIntResult)
        requires self.wf() && self.in_bound(v)
        ensures self.spec_serialize(v).len() == self.0
        decreases self.0
    {
        if self.0 > 0 {
            Self((self.0 - 1) as usize).lemma_serialize_ok_len(v & n_byte_max_unsigned!(self.0 - 1));
        }
    }
}

impl SecureSpecCombinator for VarUInt {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: VarUIntResult)
        decreases self.0
    {
        if self.in_bound(v) {
            if 0 < self.0 <= uint_size!() {
                let rest = Self((self.0 - 1) as usize);

                rest.theorem_serialize_parse_roundtrip(v & n_byte_max_unsigned!(self.0 - 1));

                self.lemma_serialize_ok(v);
                self.lemma_serialize_ok_len(v);

                let b = self.spec_serialize(v);
                self.lemma_parse_ok(b);

                if let Some((len, v2)) = self.spec_parse(b) {
                    // By definition of spec_parse
                    let b_0 = b[0];
                    assert(v2 == prepend_byte!(rest.spec_parse(b.drop_first()).unwrap().1, b_0, self.0 - 1));

                    // By definition of spec_serialize
                    assert(b[0] == get_nth_byte!(v, self.0 - 1));
                    assert(b.drop_first() == rest.spec_serialize(v & n_byte_max_unsigned!(self.0 - 1)));

                    // Expand out everything purely in BV
                    // NOTE: this depends on the size of VarUIntResult
                    let self_len = self.0;
                    assert(
                        0 < self_len <= uint_size!() ==>
                        fits_n_bytes_unsigned!(v, self_len) ==>
                        v == prepend_byte!(
                            v & n_byte_max_unsigned!(self_len - 1),
                            get_nth_byte!(v, self_len - 1),
                            self_len - 1
                        )
                    ) by (bit_vector);
                }
            } else if self.0 == 0 {
                assert(n_byte_max_unsigned!(0) == 0) by (bit_vector);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        decreases self.0
    {
        if 0 < self.0 <= uint_size!() && self.0 <= buf.len() {
            self.lemma_parse_ok(buf);
            self.lemma_parse_ok_bound(buf);

            if let Some((len, v)) = self.spec_parse(buf) {
                self.lemma_serialize_ok(v);
                self.lemma_serialize_ok_len(v);

                let buf2 = self.spec_serialize(v);

                assert(buf2.len() == len);

                let rest = Self((self.0 - 1) as usize);
                if let Some((_, rest_parsed)) = rest.spec_parse(buf.drop_first()) {
                    rest.theorem_parse_serialize_roundtrip(buf.drop_first());

                    rest.lemma_parse_ok(buf.drop_first());

                    let self_len = self.0;
                    let buf_0 = buf[0];
                    let buf2_0 = buf2[0];

                    // First prove that buf2[0] == buf[0]
                    assert(buf2[0] == buf[0]) by {
                        // By definition of spec_parse
                        assert(
                            0 < self_len <= uint_size!() ==>
                            fits_n_bytes_unsigned!(rest_parsed, self_len - 1) ==>
                            get_nth_byte!(prepend_byte!(rest_parsed, buf_0, self_len - 1), self_len - 1) == buf_0
                        ) by (bit_vector);
                    }

                    // Then we prove that the rest of buf2 and buf are the same

                    // By definition of self.spec_parse(buf)
                    assert(v == prepend_byte!(rest_parsed, buf_0, self_len - 1));

                    // By some BV reasoning
                    assert(rest_parsed == v & n_byte_max_unsigned!(self_len - 1)) by {
                        assert(
                            fits_n_bytes_unsigned!(rest_parsed, self_len - 1) ==>
                            v == prepend_byte!(rest_parsed, buf_0, self_len - 1) ==>
                            rest_parsed == v & n_byte_max_unsigned!(self_len - 1)
                        ) by (bit_vector);
                    }
                }
            }
        } else if self.0 == 0 {
            assert(buf.subrange(0, 0) =~= seq![]);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        decreases self.0
    {
        if self.0 > 0 {
            Self((self.0 - 1) as usize).lemma_prefix_secure(s1.drop_first(), s2);
        }
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for VarUInt {
    type Type = VarUIntResult;
    type SType = VarUIntResult;

    fn length(&self, _v: Self::SType) -> usize {
        self.0
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        if self.0 > s.len() || self.0 > uint_size!() {
            return Err(ParseError::Other("Size overflow".to_string()));
        }

        proof {
            self.lemma_parse_ok(s@);
        }

        let len = self.0;
        let mut res = 0;
        let mut i = len;

        // TODO: Unroll this for better performance?
        while i > 0
            invariant
                0 <= i <= len,
                len <= uint_size!(),
                len <= s.len(),

                fits_n_bytes_unsigned!(res, (uint_size!() - i)),

                // At each iteration, res is the parse result of a suffix of s
                res == Self((len - i) as usize).spec_parse(s@.skip(i as int)).unwrap().1,
            decreases i
        {
            let byte = s[i - 1];

            // Prove some bounds for ruling out arithmetic overflow
            assert(
                // Some context not captured by BV solver
                0 < i <= len ==>
                len <= uint_size!() ==>
                fits_n_bytes_unsigned!(res, (uint_size!() - i)) ==>
                {
                    &&& fits_n_bytes_unsigned!(
                        prepend_byte!(res, byte, len - i),
                        (uint_size!() - (i - 1))
                    )

                    // No overflow
                    &&& n_byte_max_unsigned!(uint_size!() - i) as int + prepend_byte!(0, byte, len - i) as int <= VarUIntResult::MAX as int
                }
            ) by (bit_vector);

            let ghost old_res = res;
            let ghost old_i = i;

            res = prepend_byte!(res, byte, len - i);
            i = i - 1;

            proof {
                let suffix = s@.skip(i as int);
                assert(suffix.drop_first() =~= s@.skip(old_i as int));
                Self((len - i) as usize).lemma_parse_ok(suffix);
                Self((len - old_i) as usize).lemma_parse_ok(suffix.drop_first());
            }
        }

        assert(s@ == s@.skip(0));
        Ok((len, res))
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let len = self.0;

        if len > uint_size!() {
            return Err(SerializeError::Other("Size overflow".to_string()));
        }

        // Size overflow or not enough space to store results
        if pos > usize::MAX - uint_size!() || data.len() < pos + len {
            return Err(SerializeError::InsufficientBuffer);
        }

        // v is too large (phrased this way to avoid shift underflow)
        if (len > 0 && v > n_byte_max_unsigned!(len)) || (len == 0 && v != 0) {
            return Err(SerializeError::Other("Size overflow".to_string()));
        }

        let ghost original_data = data@;

        let mut i = len;

        assert(v & n_byte_max_unsigned!(0) == 0) by (bit_vector);
        // assert(data@.subrange(pos + i, pos + len) =~= seq![]);

        while i > 0
            invariant
                0 <= i <= len,
                len <= uint_size!(),

                pos <= usize::MAX - uint_size!(),
                data.len() >= pos + len,

                data.len() == original_data.len(),

                // At each iteration i, data@.subrange(pos + i, pos + len) is the
                // serialization of the (len - i)-th least significant bytes of v
                data@ =~= seq_splice(
                    original_data,
                    (pos + i) as usize,
                    Self((len - i) as usize).spec_serialize(v & n_byte_max_unsigned!(len - i)),
                ),
            decreases i
        {
            let byte = get_nth_byte!(v, len - i);

            let ghost old_data = data@;
            let ghost old_i = i;

            data.set(pos + i - 1, byte);
            i = i - 1;

            proof {
                // LI:
                // assert(old_data == seq_splice(
                //     original_data,
                //     (pos + old_i) as usize,
                //     Self((len - old_i) as usize).spec_serialize(v & n_byte_max_unsigned!(len - old_i)).unwrap(),
                // ));

                assert(v & n_byte_max_unsigned!(len - old_i) <= n_byte_max_unsigned!(len - old_i)) by (bit_vector);
                assert(v & n_byte_max_unsigned!(len - i) <= n_byte_max_unsigned!(len - i)) by (bit_vector);

                Self((len - old_i) as usize).lemma_serialize_ok(v & n_byte_max_unsigned!(len - old_i));
                Self((len - old_i) as usize).lemma_serialize_ok_len(v & n_byte_max_unsigned!(len - old_i));
                Self((len - i) as usize).lemma_serialize_ok(v & n_byte_max_unsigned!(len - i));
                Self((len - i) as usize).lemma_serialize_ok_len(v & n_byte_max_unsigned!(len - i));

                let old_suffix = Self((len - old_i) as usize).spec_serialize(v & n_byte_max_unsigned!(len - old_i));
                let suffix = Self((len - i) as usize).spec_serialize(v & n_byte_max_unsigned!(len - i));

                assert(suffix.drop_first() =~= old_suffix) by {
                    assert(
                        0 <= i < old_i <= len ==>
                        len <= uint_size!() ==>
                        (v & n_byte_max_unsigned!(len - i)) & n_byte_max_unsigned!(len - old_i) == v & n_byte_max_unsigned!(len - old_i)
                    ) by (bit_vector);
                }

                assert(byte == suffix[0]) by {
                    assert(
                        0 <= i <= len ==>
                        len <= uint_size!() ==>
                        get_nth_byte!(v & n_byte_max_unsigned!(len - i), len - i - 1)
                            == get_nth_byte!(v, len - (i + 1)) as u8
                    ) by (bit_vector);
                }

                assert(data@[pos + i] == suffix[0]);
            }
        }

        proof {
            self.lemma_serialize_ok(v);
            self.lemma_serialize_ok_len(v);
            assert(v <= n_byte_max_unsigned!(len) ==> v & n_byte_max_unsigned!(len) == v) by (bit_vector);
        }
        // assert(data@.subrange(pos as int, pos + len) == self.spec_serialize(v).unwrap());
        // assert(data@ =~= seq_splice(old(data)@, pos, self.spec_serialize(v).unwrap()));

        Ok(len)
    }
}

// Implement VarInt combinator through using VarUInt
// NOTE: Not using Mapped combinator here since the mapping
// is not a direct bijection from u64 -> i64
// the mapping actually depends on the length of the integer
// e.g. (00 ff) -> 255, but (ff) -> -1
// but both of them are 255 when parsed with VarUInt

pub struct VarInt(pub usize);

impl View for VarInt {
    type V = VarInt;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl VarInt {
    pub open spec fn to_var_uint(&self) -> VarUInt {
        VarUInt(self.0)
    }
}

impl SpecCombinator for VarInt {
    type Type = VarIntResult;

    open spec fn wf(&self, v: Self::Type) -> bool {
        n_byte_min_signed!(self.0) <= v && v <= n_byte_max_signed!(self.0)
    }
    
    open spec fn requires(&self) -> bool {
        self.to_var_uint().wf()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, VarIntResult)>
    {
        match self.to_var_uint().spec_parse(s) {
            None => None,
            Some((n, v)) => Some((n, sign_extend!(v, self.0))),
        }
    }

    open spec fn spec_serialize(&self, v: VarIntResult) -> Seq<u8>
    {
        // Test if v can be fit into a self.0-byte signed integer
        if n_byte_min_signed!(self.0) <= v && v <= n_byte_max_signed!(self.0) {
            self.to_var_uint().spec_serialize((v as VarUIntResult) & n_byte_max_unsigned!(self.0))
        } else {
            seq![]
        }
    }
}

impl SecureSpecCombinator for VarInt {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: VarIntResult)
    {
        self.to_var_uint().theorem_serialize_parse_roundtrip((v as VarUIntResult) & n_byte_max_unsigned!(self.0));

        // For v within bound, sign_extend(truncate(v)) == v
        let self_len = self.0;
        assert(
            0 <= self_len <= uint_size!() ==>
            n_byte_min_signed!(self_len) <= v && v <= n_byte_max_signed!(self_len) ==>
            sign_extend!((v as VarUIntResult) & n_byte_max_unsigned!(self_len), self_len) == v
        ) by (bit_vector);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {
        if let Some((len, v)) = self.to_var_uint().spec_parse(buf) {
            self.to_var_uint().theorem_parse_serialize_roundtrip(buf);

            let self_len = self.0;
            assert(
                0 <= self_len <= uint_size!() ==>
                fits_n_bytes_unsigned!(v, self_len) ==> {
                    // sign extended value should fit in the bound
                    &&& n_byte_min_signed!(self_len) <= sign_extend!(v, self_len) && sign_extend!(v, self_len) <= n_byte_max_signed!(self_len)

                    // truncate(sign_extend(v)) == v
                    &&& (sign_extend!(v, self_len) as VarUIntResult) & n_byte_max_unsigned!(self_len) == v
                }
            ) by (bit_vector);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {
        self.to_var_uint().lemma_prefix_secure(s1, s2);
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for VarInt {
    type Type = VarIntResult;
    type SType = VarIntResult;

    fn length(&self, _v: Self::SType) -> usize {
        self.0
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        if self.0 > uint_size!() {
            return Err(ParseError::Other("Size overflow".to_string()));
        }

        if self.0 > 0 {
            let (_, v) = VarUInt(self.0).parse(s)?;

            proof {
                VarUInt(self.0).lemma_parse_ok_bound(s@);

                // Prove no overflow
                let self_len = self.0;
                assert(
                    0 < self_len <= uint_size!() ==>
                    fits_n_bytes_unsigned!(v, self_len) ==>
                    v as int + !n_byte_max_unsigned!(self_len) as int <= (VarUIntResult::MAX as int)
                ) by (bit_vector);
            }

            Ok((self.0, sign_extend!(v, self.0)))
        } else {
            assert(sign_extend!(0, 0) == 0) by (bit_vector);
            Ok((0, 0))
        }
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        if self.0 > uint_size!() {
            return Err(SerializeError::Other("Size overflow".to_string()));
        }

        if pos > usize::MAX - uint_size!() || data.len() < pos + self.0 {
            return Err(SerializeError::InsufficientBuffer);
        }

        if self.0 == 0 {
            if v == 0 {
                proof {
                    assert(n_byte_max_unsigned!(0) == 0) by (bit_vector);
                    assert(fits_n_bytes_unsigned!((v as VarUIntResult) & n_byte_max_unsigned!(0), 0)) by (bit_vector);
                    VarUInt(0).lemma_serialize_ok((v as VarUIntResult) & n_byte_max_unsigned!(0));
                    VarUInt(0).lemma_serialize_ok_len((v as VarUIntResult) & n_byte_max_unsigned!(0));
                    assert(seq_splice(data@, pos, seq![]) =~= data@);
                }
                return Ok(0);
            } else {
                return Err(SerializeError::Other("Invalid zero encoding".to_string()));
            }
        }

        // Check if v is within bounds
        if v < n_byte_min_signed!(self.0) || v > n_byte_max_signed!(self.0) {
            return Err(SerializeError::Other("Size overflow".to_string()));
        }

        VarUInt(self.0).serialize((v as VarUIntResult) & n_byte_max_unsigned!(self.0), data, pos)
    }
}

}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_and_serialize() {
        assert_eq!(VarUInt(0).parse(&[1, 2, 3]).unwrap(), (0, 0));
        assert_eq!(
            VarUInt(8)
                .parse(&[0xff, 0x8f, 0x28, 0, 0, 0, 0, 0])
                .unwrap(),
            (8, 0xff8f_2800_0000_0000)
        );
        assert_eq!(VarInt(0).parse(&[0x7f]).unwrap(), (0, 0));
        assert_eq!(VarInt(1).parse(&[0xff]).unwrap(), (1, -1));
        assert_eq!(VarInt(2).parse(&[0x7f, 0xff]).unwrap(), (2, 0x7fff));
        assert_eq!(VarInt(2).parse(&[0x80, 0x00]).unwrap(), (2, -32768));

        let mut data = vec![0; 8];
        assert_eq!(VarUInt(0).serialize(0, &mut data, 0).unwrap(), 0);
        assert_eq!(data, [0; 8]);

        let mut data = vec![0; 8];
        assert_eq!(VarUInt(2).serialize(0xbeef, &mut data, 0).unwrap(), 2);
        assert_eq!(data, [0xbe, 0xef, 0, 0, 0, 0, 0, 0]);

        let mut data = vec![0; 8];
        assert_eq!(VarInt(2).serialize(0x7fff, &mut data, 0).unwrap(), 2);
        assert_eq!(data, [0x7f, 0xff, 0, 0, 0, 0, 0, 0]);

        let mut data = vec![0; 8];
        assert_eq!(VarInt(2).serialize(-1, &mut data, 0).unwrap(), 2);
        assert_eq!(data, [0xff, 0xff, 0, 0, 0, 0, 0, 0]);

        let mut data = vec![0; 8];
        assert_eq!(VarInt(0).serialize(0, &mut data, 0).unwrap(), 0);
        assert_eq!(data, [0, 0, 0, 0, 0, 0, 0, 0]);

        let mut data = vec![0; 8];
        assert!(VarUInt(1).serialize(256, &mut data, 0).is_err());
        assert!(VarInt(1).serialize(-1000, &mut data, 0).is_err());
        assert!(VarInt(1).serialize(0x80, &mut data, 0).is_err());
    }
}
