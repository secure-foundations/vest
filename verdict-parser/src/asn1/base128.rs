use super::*;
use vstd::prelude::*;

verus! {

/// Combinator for a single identifier component
/// in the OBJECT IDENTIFIER ASN.1 type (called "arc"
/// X.690)
///
/// Basically an Arc is encoded as a "base-128" integer
/// where the highest bit of every byte is set to 1
/// except for the last byte
///
/// e.g. 0b11111111 (0xff) => 0b1 * 128 + 0b01111111 => 0b10000001 0b011111111
///
/// NOTE: the first and second arcs of an OID are encoded differently
#[derive(Debug, View)]
pub struct Base128UInt;

impl SpecCombinator for Base128UInt {
    type Type = UInt;
    
    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }
    
    /// A wrapper around the *_helper version but first find the length of the first arc
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, UInt)>
    {
        match Self::find_first_arc(s) {
            Some(len) => {
                match Self::spec_parse_helper(s.take(len), true) {
                    Some(v) => Some((len, v)),
                    None => None
                }
            }
            None => None
        }
    }

    open spec fn spec_serialize(&self, v: UInt) -> Seq<u8> {
        Self::spec_serialize_helper(v, true)
    }
}

impl SecureSpecCombinator for Base128UInt {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        Self::lemma_spec_serialize_find_first_arc(v);
        Self::spec_serialize_parse_helper_roundtrip(v, true);

        let s = Self::spec_serialize_helper(v, true);
        assert(s.take(s.len() as int) == s);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some(len) = Self::find_first_arc(buf) {
            Self::lemma_find_first_arc_alt(buf);
            self.lemma_prefix_secure(buf.take(len), buf.skip(len));
            Self::spec_parse_serialize_helper_roundtrip(buf.take(len), true);

            assert(buf.take(len) + buf.skip(len) == buf);
            assert(buf.take(len) == buf.subrange(0, len));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        Self::lemma_find_first_arc_alt(s1);
        Self::lemma_find_first_arc_prefix_secure(s1, s2);

        if let Some(len) = Self::find_first_arc(s1) {
            assert(s1.take(len) == (s1 + s2).take(len));
        }
    }

    proof fn lemma_parse_length(&self, _s: Seq<u8>) {}

    proof fn lemma_parse_productive(&self, _s: Seq<u8>) {}
}

impl Base128UInt {
    /// last_byte is true iff s[-1] is the last byte (which must exist and have the highest bit set to 0)
    pub closed spec fn spec_parse_helper(s: Seq<u8>, last_byte: bool) -> Option<UInt>
        decreases s.len()
    {
        if s.len() == 0 {
            if last_byte {
                None
            } else {
                Some(0)
            }
        } else {
            if !last_byte && take_low_7_bits!(s.first()) == 0 {
                // The first byte (if not the last byte) should not be 0 for minimal encoding
                None
            } else if !last_byte && !is_high_8_bit_set!(s.last()) {
                // If s should not include the last byte, then all bytes must have the highest bit set to 1
                None
            } else if last_byte && is_high_8_bit_set!(s.last()) {
                // If s include the last byte, the last byte should have the highest bit unset
                None
            } else {
                // Parse the prefix first
                match Self::spec_parse_helper(s.drop_last(), false) {
                    Some(v) =>
                        // Check for overflow
                        if v <= n_bit_max_unsigned!(8 * uint_size!() - 7) {
                            // Remove the highest bit of s.last() when parsing
                            Some(v << 7 | take_low_7_bits!(s.last()) as UInt)
                        } else {
                            None
                        }
                    None => None
                }
            }
        }
    }

    /// Serialize v in base-128 encoding
    /// last_byte is true iff the encoding should have the highest bit of the last byte set to 0
    pub closed spec fn spec_serialize_helper(v: UInt, last_byte: bool) -> Seq<u8>
        decreases v via Self::spec_serialize_decreases
    {
        if v == 0 {
            if last_byte {
                seq![0]
            } else {
                seq![]
            }
        } else if last_byte {
            // Add the lowest 7 bits of v along with the highest bit set to 1
            Self::spec_serialize_helper(v >> 7, false) + seq![take_low_7_bits!(v)]
        } else {
            // Add the lowest 7 bits with the highest bit set to 0
            Self::spec_serialize_helper(v >> 7, false) + seq![set_high_8_bit!(v)]
        }
    }

    pub open spec fn find_first_arc(s: Seq<u8>) -> Option<int>
        decreases s.len()
    {
        if s.len() == 0 {
            None
        } else {
            if !is_high_8_bit_set!(s.first()) {
                Some(1)
            } else {
                match Self::find_first_arc(s.drop_first()) {
                    Some(len) => Some(len + 1),
                    None => None
                }
            }
        }
    }

    /// A spec fn wrapper of the macro for quantifier triggers
    closed spec fn is_high_8_bit_set(v: u8) -> bool
    {
        is_high_8_bit_set!(v)
    }

    closed spec fn all_high_8_bit_set(s: Seq<u8>) -> bool
    {
        forall |i: int| 0 <= i < s.len() ==> #[trigger] Self::is_high_8_bit_set(s.index(i))
    }

    /// An alternative characterization of find_first_arc
    proof fn lemma_find_first_arc_alt(s: Seq<u8>)
        ensures
            Self::find_first_arc(s) matches Some(len) ==> {
                let last = s[len - 1];

                &&& 0 < len <= s.len()
                &&& !Self::is_high_8_bit_set(last)
                &&& Self::all_high_8_bit_set(s.take(len - 1))
            },
            Self::find_first_arc(s) is None ==> Self::all_high_8_bit_set(s),

        decreases s.len()
    {
        if s.len() != 0 {
            if is_high_8_bit_set!(s.first()) {
                Self::lemma_find_first_arc_alt(s.drop_first());

                if let Some(len) = Self::find_first_arc(s.drop_first()) {
                    assert(0 < len <= s.drop_first().len());

                    let last = s[len];
                    assert(last == s.drop_first()[len - 1]);

                    assert forall |i: int| 0 <= i < len implies #[trigger] Self::is_high_8_bit_set(s.index(i))
                    by {
                        if i > 0 {
                            assert(s.index(i) == s.drop_first().take(len - 1).index(i - 1));
                        }
                    }
                } else {
                    assert forall |i: int| 0 <= i < s.len() implies #[trigger] Self::is_high_8_bit_set(s.index(i))
                    by {
                        if i > 0 {
                            assert(s.index(i) == s.drop_first().index(i - 1));
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_find_first_arc_prefix_secure(s1: Seq<u8>, s2: Seq<u8>)
        ensures
            Self::find_first_arc(s1) matches Some(len) ==>
                Self::find_first_arc(s1 + s2) == Some(len)

        decreases s1.len()
    {
        if s1.len() != 0 {
            Self::lemma_find_first_arc_prefix_secure(s1.drop_first(), s2);
            assert(s1.drop_first() + s2 == (s1 + s2).drop_first());
        }
    }

    proof fn lemma_spec_serialize_non_last_byte_all_high_8_bit_set(v: UInt)
        ensures
            Self::all_high_8_bit_set(Self::spec_serialize_helper(v, false))

        decreases v
    {
        if v != 0 {
            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            assert(is_high_8_bit_set!(set_high_8_bit!(v))) by (bit_vector);
            Self::lemma_spec_serialize_non_last_byte_all_high_8_bit_set(v >> 7);
        }
    }

    proof fn lemma_spec_serialize_find_first_arc(v: UInt)
        ensures
            ({
                let s = Self::spec_serialize_helper(v, true);
                Self::find_first_arc(s) == Some(s.len() as int)
            })
    {
        let s = Self::spec_serialize_helper(v, true);
        Self::lemma_spec_serialize_non_last_byte_all_high_8_bit_set(v >> 7);
        Self::lemma_find_first_arc_alt(s);

        assert(!is_high_8_bit_set!(take_low_7_bits!(v))) by (bit_vector);

        if Self::find_first_arc(s).is_none() {
            assert(Self::is_high_8_bit_set(s.last()));
        }
    }

    /// Same as lemma_spec_parse_unique_zero_encoding, but for last_byte = false
    proof fn lemma_spec_parse_unique_zero_encoding_alt(s: Seq<u8>)
        ensures Self::spec_parse_helper(s, false) matches Some(v) ==>
            (v == 0 <==> s.len() == 0)

        decreases s.len()
    {
        if let Some(v) = Self::spec_parse_helper(s, false) {
            if s.len() == 1 {
                // Show that the only byte should not be a zero

                let empty: Seq<u8> = seq![];
                assert(s.drop_last() == empty);

                let last = s.last();

                assert(Self::spec_parse_helper(s.drop_last(), false).unwrap() == 0);
                assert(
                    v == 0 ==>
                    (v << 7 | take_low_7_bits!(last) as UInt) == 0 ==>
                    take_low_7_bits!(last) == 0
                ) by (bit_vector);
            } else if s.len() > 1 {
                Self::lemma_spec_parse_unique_zero_encoding_alt(s.drop_last());

                let prefix = s.drop_last();
                let last = s.last();
                let parsed_prefix = Self::spec_parse_helper(prefix, false).unwrap();

                // Since prefix is not zero, neither is the final value
                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==>
                    parsed_prefix != 0 ==>
                    parsed_prefix << 7 | take_low_7_bits!(last) as UInt != 0
                ) by (bit_vector);
            }
        }
    }

    #[via_fn]
    proof fn spec_serialize_decreases(v: UInt, last_byte: bool) {
        assert(v != 0 ==> v >> 7 < v) by (bit_vector);
    }

    /// The encoding of 0 is unique
    proof fn lemma_spec_parse_unique_zero_encoding(s: Seq<u8>)
        ensures
            Self::spec_parse_helper(s, true) matches Some(v) ==>
            (v == 0 <==> s =~= seq![0u8])

        decreases s.len()
    {
        // reveal_with_fuel(Self::spec_parse, 2);

        if let Some(v) = Self::spec_parse_helper(s, true) {
            let prefix = s.drop_last();
            let last = s.last();
            let parsed_prefix = Self::spec_parse_helper(prefix, false).unwrap();

            assert(v == parsed_prefix << 7 | take_low_7_bits!(last) as UInt);

            if v == 0 {
                // If the concat the parsed prefix and last is 0
                // then both of them must be 0
                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==>
                    parsed_prefix << 7 | take_low_7_bits!(last) as UInt == 0 ==>
                    !is_high_8_bit_set!(last) ==>
                    last == 0 && parsed_prefix == 0
                ) by (bit_vector);

                if prefix.len() != 0 {
                    Self::lemma_spec_parse_unique_zero_encoding_alt(prefix);
                }
            } else {
                // WTS: s =~= seq![0u8]

                // If the final value is not 0,
                // then either the prefix or the last byte must not be 0
                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==>
                    (parsed_prefix << 7 | take_low_7_bits!(last) as UInt) != 0 ==>
                    parsed_prefix != 0 || last != 0
                ) by (bit_vector);

                Self::lemma_spec_parse_unique_zero_encoding(prefix);
            }
        }
    }

    // Serializing a non-zero value should not have a non-zero first byte
    proof fn lemma_spec_serialize_non_zero(v: UInt)
        requires v != 0
        ensures
            Self::spec_serialize_helper(v, false).len() > 0,
            take_low_7_bits!(Self::spec_serialize_helper(v, false).first()) != 0,

        decreases v
    {
        assert(
            v != 0 ==>
            take_low_7_bits!(v) != 0 ||
            v >> 7 != 0
        ) by (bit_vector);

        if v >> 7 != 0 {
            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            Self::lemma_spec_serialize_non_zero(v >> 7);
        } else {
            assert(take_low_7_bits!(v) != 0 ==> take_low_7_bits!(set_high_8_bit!(v)) != 0) by (bit_vector);
            assert(Self::spec_serialize_helper(v >> 7, false).len() == 0);
        }
    }

    proof fn lemma_spec_parse_helper_error_prop(s: Seq<u8>, len: int)
        requires
            0 < len <= s.len(),
            Self::spec_parse_helper(s.take(len), false).is_none(),

        ensures
            Self::spec_parse_helper(s, false).is_none()

        decreases s.len()
    {
        if len < s.len() {
            assert(s.drop_last().take(len) == s.take(len));
            Self::lemma_spec_parse_helper_error_prop(s.drop_last(), len);
        } else {
            assert(s.take(len) == s);
        }
    }

    proof fn spec_parse_serialize_helper_roundtrip(s: Seq<u8>, last_byte: bool)
        ensures
            Self::spec_parse_helper(s, last_byte) matches Some(v) ==>
            Self::spec_serialize_helper(v, last_byte) == s

        decreases s.len()
    {
        if let Some(v) = Self::spec_parse_helper(s, last_byte) {
            if s.len() == 0 {
                let empty: Seq<u8> = seq![];
                assert(s == empty);
            } else {
                let prefix = s.drop_last();
                let last = s.last();
                let parsed_prefix = Self::spec_parse_helper(prefix, false).unwrap();
                let s2 = Self::spec_serialize_helper(v, last_byte);

                Self::spec_parse_serialize_helper_roundtrip(prefix, false);

                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==> {
                        &&& (parsed_prefix << 7 | take_low_7_bits!(last) as UInt) >> 7 == parsed_prefix
                        &&& (!is_high_8_bit_set!(last) ==> take_low_7_bits!(parsed_prefix << 7 | take_low_7_bits!(last) as UInt) == last)
                        &&& (is_high_8_bit_set!(last) ==> set_high_8_bit!(parsed_prefix << 7 | take_low_7_bits!(last) as UInt) == last)
                    }
                ) by (bit_vector);

                Self::lemma_spec_parse_unique_zero_encoding(s);
                Self::lemma_spec_parse_unique_zero_encoding_alt(s);

                assert(s == s2);
            }
        }
    }

    proof fn spec_serialize_parse_helper_roundtrip(v: UInt, last_byte: bool)
        ensures
            Self::spec_parse_helper(Self::spec_serialize_helper(v, last_byte), last_byte) == Some(v)

        decreases v
    {
        if v == 0 {
            reveal_with_fuel(Base128UInt::spec_parse_helper, 2);
            Self::lemma_spec_parse_unique_zero_encoding(seq![0u8]);
        } else {
            let s = Self::spec_serialize_helper(v, last_byte);
            let prefix = Self::spec_serialize_helper(v >> 7, false);

            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            Self::spec_serialize_parse_helper_roundtrip(v >> 7, false);

            // By definition
            // assert(s == prefix + if last_byte {
            //     seq![take_low_7_bits!(v)]
            // } else {
            //     seq![set_high_8_bit!(v)]
            // });

            assert(s.drop_last() == prefix);

            // Some required BV facts
            assert(!is_high_8_bit_set!(take_low_7_bits!(v))) by (bit_vector);
            assert(is_high_8_bit_set!(set_high_8_bit!(v))) by (bit_vector);
            assert(v >> 7 <= n_bit_max_unsigned!(8 * uint_size!() - 7)) by (bit_vector);
            assert(v >> 7 << 7 | take_low_7_bits!(take_low_7_bits!(v)) as UInt == v) by (bit_vector);
            assert(v >> 7 << 7 | take_low_7_bits!(set_high_8_bit!(v)) as UInt == v) by (bit_vector);

            Self::lemma_spec_serialize_non_zero(v);
        }
    }

    /// Exec version of find_first_arc
    fn exec_find_first_arc<'a>(s: &'a [u8]) -> (res: Option<usize>)
        ensures
            res matches Some(len) ==> Self::find_first_arc(s@) == Some(len as int),
            res is None ==> Self::find_first_arc(s@) is None
    {
        let mut len = 0;

        // Compute the boundary first
        // TODO: this is somewhat unnecessary, but aligns with the spec better
        while len < s.len() && is_high_8_bit_set!(s[len])
            invariant
                0 <= len <= s.len(),
                Self::all_high_8_bit_set(s@.take(len as int)),
            decreases s.len() - len
        {
            len = len + 1;

            assert(Self::all_high_8_bit_set(s@.take(len as int))) by {
                assert forall |i| 0 <= i < len implies #[trigger] Self::is_high_8_bit_set(s@[i])
                by {
                    if i < len - 1 {
                        // By loop inv
                        assert(Self::is_high_8_bit_set(s@.take(len - 1)[i]));
                    }
                }
            }
        }

        // No first arc found
        if len == s.len() {
            proof {
                assert(s@ == s@.take(len as int));
                Self::lemma_find_first_arc_alt(s@);
            }
            return None;
        }

        len = len + 1;

        proof {
            // Prove that len is unique (TODO: factor this proof out)
            Self::lemma_find_first_arc_alt(s@);
            assert(!Self::is_high_8_bit_set(s@[len - 1]));
            assert(Self::find_first_arc(s@) == Some(len as int)) by {
                let len2 = Self::find_first_arc(s@).unwrap();

                if len2 < len {
                    assert(Self::is_high_8_bit_set(s@.take(len - 1)[len2 - 1]));
                } else if len < len2 {
                    assert(Self::is_high_8_bit_set(s@.take(len2 - 1)[len - 1]));
                }
            }
        }

        return Some(len);
    }

    /// TODO: change this to a non-recursive function
    #[inline(always)]
    fn serialize_helper(v: u64) -> (r: Vec<u8>)
        ensures r@ == Self::spec_serialize_helper(v, false)
        decreases v
    {
        if v == 0 {
            Vec::with_capacity(4) // usually OID arcs fit in 4 bytes
        } else {
            // Add the lowest 7 bits with the highest bit set to 0
            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            let mut r = Self::serialize_helper(v >> 7);
            let ghost old_r = r@;

            r.push(set_high_8_bit!(v));
            assert(r@ == old_r + seq![set_high_8_bit!(v)]);
            r
        }
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Base128UInt {
    type Type = UInt;
    type SType = &'a Self::Type;

    fn length(&self, v: Self::SType) -> usize {
        Self::serialize_helper(*v).len()
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        let len = if let Some(len) = Self::exec_find_first_arc(s) {
            len
        } else {
            return Err(ParseError::Other("No first arc found".to_string()));
        };

        proof {
            Self::lemma_find_first_arc_alt(s@);
        }

        // The prefix we will be parsing
        let ghost prefix = s@.take(len as int);

        // If the first byte is 0, the encoding is not minimal
        if len > 1 && take_low_7_bits!(s[0]) == 0 {
            assert(prefix.drop_last() == s@.take(len - 1));
            assert(Self::spec_parse_helper(s@.take(len - 1), false).is_none());
            assert(Self::spec_parse_helper(prefix, true).is_none());
            return Err(ParseError::Other("Non-minimal encoding".to_string()));
        }

        // Parse the high-8-bit part
        let mut v = 0;
        let mut i = 0;

        while i < len - 1
            invariant_except_break
                0 <= i <= len - 1,
                0 < len <= s.len(),

                // First byte is not 0
                len > 1 ==> { let first = s@.first(); take_low_7_bits!(first) != 0 },

                // Results of find_first_arc
                Self::all_high_8_bit_set(s@.take(len - 1)),
                !Self::is_high_8_bit_set(s@[len - 1]),
                Self::find_first_arc(s@) == Some(len as int),

                prefix == s@.take(len as int),

                // Invariant that the prefix s@.take(i) is correctly parsed
                Self::spec_parse_helper(s@.take(i as int), false).is_some(),
                v == Self::spec_parse_helper(s@.take(i as int), false).unwrap(),

            ensures
                i == len - 1,
                !Self::is_high_8_bit_set(s@[len - 1]),
                Self::spec_parse_helper(s@.take(i as int), false).is_some(),
                v == Self::spec_parse_helper(s@.take(i as int), false).unwrap(),

            decreases len - 1 - i
        {
            assert(s@.take(i + 1).drop_last() == s@.take(i as int));
            assert(Self::is_high_8_bit_set(s@.take(len - 1)[i as int]));

            if v > n_bit_max_unsigned!(8 * uint_size!() - 7) {
                // Show that if a prefix failed to parse, so does the entire sequence
                proof {
                    assert(prefix.drop_last().take(i + 1) == s@.take(i + 1));
                    Self::lemma_spec_parse_helper_error_prop(prefix.drop_last(), i + 1);
                }
                return Err(ParseError::Other("Size overflow".to_string()));
            }

            v = v << 7 | take_low_7_bits!(s[i]) as UInt;
            i = i + 1;
        }

        assert(prefix.drop_last() == s@.take(i as int));

        if v > n_bit_max_unsigned!(8 * uint_size!() - 7) {
            assert(Self::spec_parse_helper(prefix, true).is_none());
            return Err(ParseError::Other("Size overflow".to_string()));
        }

        // Add the last byte
        v = v << 7 | take_low_7_bits!(s[i]) as UInt;

        Ok((len, v))
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let v = *v;
        if pos >= data.len() {
            return Err(SerializeError::Other("Size overflow".to_string()));
        }

        // For 0, we just emit a single byte
        if v < 0x80 {
            data.set(pos, take_low_7_bits!(v));

            // Unfold the evaluation of the spec_serialize_helper
            assert(v < 0x80 ==> v >> 7 == 0) by (bit_vector);
            assert(v == 0 ==> take_low_7_bits!(v) == 0) by (bit_vector);
            if v != 0 {
                let ghost empty: Seq<u8> = seq![];
                assert(Self::spec_serialize_helper(0, false) == empty);
            }
            assert(data@ == seq_splice(old(data)@, pos, Self::spec_serialize_helper(v, true)));

            return Ok(1);
        }

        let rest = Self::serialize_helper(v >> 7);

        // Check some bounds
        let end = if let Some(end) = pos.checked_add(rest.len()) {
            end
        } else {
            return Err(SerializeError::Other("Size overflow".to_string()));
        };
        if end > data.len() - 1 {
            return Err(SerializeError::InsufficientBuffer);
        }

        // Write rest to data at pos
        for i in 0..rest.len()
            invariant
                data@.len() == old(data)@.len(),
                pos + rest.len() + 1 <= data.len(),
                data@ =~= seq_splice(old(data)@, pos, rest@.take(i as int)),
        {
            data.set(pos + i, rest[i]);
        }

        // Write the last byte
        data.set(pos + rest.len(), take_low_7_bits!(v));
        assert(data@ =~= seq_splice(old(data)@, pos, Self::spec_serialize_helper(v, true)));

        Ok(rest.len() + 1)
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;
    use der::Encode;

    /// Wrap a base 128 uint in an object identifier for testing
    fn serialize_base_128_uint(v: UInt) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; 3 + 10];
        data[0] = 0x06;
        data[2] = 0x2a;
        let len = Base128UInt.serialize(v, &mut data, 3)?;
        data.truncate(len + 3);
        data[1] = (len + 1) as u8;
        Ok(data)
    }

    #[test]
    fn diff_with_der() {
        let diff = |v: UInt| {
            let res1 = serialize_base_128_uint(v).map_err(|_| ());
            let res2 = der::asn1::ObjectIdentifier::new_unwrap(format!("1.2.{}", v).as_str())
                .to_der()
                .map_err(|_| ());
            assert_eq!(res1, res2);
        };

        for i in 0..16383 {
            // TODO: this seems to a bug in the der crate
            if i == 128 {
                continue;
            }

            diff(i);
        }
    }
}
