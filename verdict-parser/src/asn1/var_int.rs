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
            Seq::<u8>::empty()
        } else if self.0 == 0 {
            Seq::<u8>::empty()
        } else {
            // Encode the least significant (self.0 - 1) bytes of v
            // then prepend the self.0-th byte
            let rest = Self((self.0 - 1) as usize).spec_serialize(v & n_byte_max_unsigned!(self.0 - 1));
            Seq::<u8>::empty().push(get_nth_byte!(v, self.0 - 1)) + rest
        }
    }
}

/// Some lemmas about VarUInt::spec_parse and VarUInt::spec_serialize
impl VarUInt {
    pub proof fn lemma_mask_fits(len: usize, v: VarUIntResult)
        requires len <= uint_size!()
        ensures fits_n_bytes_unsigned!(v & n_byte_max_unsigned!(len), len)
    {
        assert(fits_n_bytes_unsigned!(v & n_byte_max_unsigned!(len), len)) by (bit_vector);
    }

    pub proof fn lemma_tail_context(len: usize)
        requires len <= uint_size!(), len > 0
        ensures
            VarUInt((len - 1) as usize).wf(),
            (len - 1) < uint_size!()
    {
        assert(len <= uint_size!());
        assert(len > 0);
        assert(
            len <= uint_size!() &&
            len > 0
            ==> len - 1 <= uint_size!()
        ) by (bit_vector);
        assert(len - 1 <= uint_size!());
        assert(VarUInt((len - 1) as usize).wf());
        assert(
            len <= uint_size!() &&
            len > 0
            ==> len - 1 < uint_size!()
        ) by (bit_vector);
        assert(len - 1 < uint_size!());
    }

    pub proof fn lemma_prepend_restore(len: usize, v: VarUIntResult)
        requires len < uint_size!() && len + 1 <= uint_size!() && fits_n_bytes_unsigned!(v, len + 1)
        ensures prepend_byte!(v & n_byte_max_unsigned!(len), get_nth_byte!(v, len), len) == v
    {
        assert(len < uint_size!());
        assert(len + 1 <= uint_size!());
        assert(fits_n_bytes_unsigned!(v, len + 1));
        assert(
            len < uint_size!() &&
            len + 1 <= uint_size!() &&
            fits_n_bytes_unsigned!(v, len + 1)
            ==> prepend_byte!(v & n_byte_max_unsigned!(len), get_nth_byte!(v, len), len) == v
        ) by (bit_vector);
        assert(prepend_byte!(v & n_byte_max_unsigned!(len), get_nth_byte!(v, len), len) == v);
    }

    pub proof fn lemma_prepend_byte_get_nth(len: usize, rest: VarUIntResult, byte: u8)
        requires len < uint_size!() && fits_n_bytes_unsigned!(rest, len)
        ensures get_nth_byte!(prepend_byte!(rest, byte, len), len) == byte
    {
        assert(len < uint_size!());
        assert(fits_n_bytes_unsigned!(rest, len));
        assert(
            len < uint_size!() &&
            fits_n_bytes_unsigned!(rest, len)
            ==> get_nth_byte!(prepend_byte!(rest, byte, len), len) == byte
        ) by (bit_vector);
        assert(get_nth_byte!(prepend_byte!(rest, byte, len), len) == byte);
    }

    pub proof fn lemma_prepend_mask(len: usize, rest: VarUIntResult, byte: u8)
        requires len < uint_size!() && fits_n_bytes_unsigned!(rest, len)
        ensures prepend_byte!(rest, byte, len) & n_byte_max_unsigned!(len) == rest
    {
        assert(len < uint_size!());
        assert(fits_n_bytes_unsigned!(rest, len));
        assert(
            len < uint_size!() &&
            fits_n_bytes_unsigned!(rest, len)
            ==> prepend_byte!(rest, byte, len) & n_byte_max_unsigned!(len) == rest
        ) by (bit_vector);
        assert(prepend_byte!(rest, byte, len) & n_byte_max_unsigned!(len) == rest);
    }

    pub proof fn lemma_parse_ok(&self, s: Seq<u8>)
        ensures self.spec_parse(s).is_some() <==> self.wf() && self.0 <= s.len()
        decreases self.0
    {
        if self.0 > 0 {
            Self((self.0 - 1) as usize).lemma_parse_ok(s.drop_first());
        }
    }

    pub proof fn lemma_parse_returns_length(&self, s: Seq<u8>)
        requires self.spec_parse(s).is_some()
        ensures self.spec_parse(s).unwrap().0 == self.0 as int
        decreases self.0
    {
        assert(self.spec_parse(s).is_some());
        self.lemma_parse_ok(s);

        if self.0 == 0 {
            let res = self.spec_parse(s).unwrap();
            assert(res.0 == 0int);
        } else {
            let rest = Self((self.0 - 1) as usize);
            let rest_opt = rest.spec_parse(s.drop_first());

            match rest_opt {
                None => {
                    assert(self.spec_parse(s).is_none());
                    assert(false) by {
                        assert(self.spec_parse(s).is_some());
                        assert(self.spec_parse(s).is_none());
                    };
                }
                Some((rest_len, rest_val)) => {
                    rest.lemma_parse_returns_length(s.drop_first());
                    assert(rest.spec_parse(s.drop_first()) == Some((rest_len, rest_val)));
                    let res = self.spec_parse(s).unwrap();
                    assert(res.0 == (self.0 as int)) by {
                        assert(self.wf());
                        assert(self.0 > 0);
                        assert(self.0 <= s.len());
                        assert(rest.spec_parse(s.drop_first()) == Some((rest_len, rest_val)));
                    };
                }
            }
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
        ensures
            (!self.wf() || !self.in_bound(v)) ==> self.spec_serialize(v) == Seq::<u8>::empty(),
            self.wf() && self.in_bound(v) ==> self.spec_serialize(v).len() == self.0
        decreases self.0
    {
        if !self.wf() || !self.in_bound(v) {
            assert(self.spec_serialize(v) == Seq::<u8>::empty());
        } else if self.0 == 0 {
            assert(self.spec_serialize(v) == Seq::<u8>::empty());
            assert(self.spec_serialize(v).len() == 0);
        } else {
            assert(self.0 > 0);
            let rest_len = (self.0 - 1) as usize;
            let rest = Self(rest_len);
            let rest_value = v & n_byte_max_unsigned!(rest_len);

            Self::lemma_tail_context(self.0);

            assert(self.in_bound(v));
            Self::lemma_mask_fits(rest_len, v);
            assert(fits_n_bytes_unsigned!(rest_value, rest_len));
            assert(rest.in_bound(rest_value));

            rest.lemma_serialize_ok(rest_value);
            assert(rest.spec_serialize(rest_value).len() == rest.0) by {
                assert(rest.wf());
                assert(rest.in_bound(rest_value));
            };

            let rest_buf = rest.spec_serialize(rest_value);
            assert(rest_buf.len() == rest_len as int);

            let buf = self.spec_serialize(v);
            let single = Seq::<u8>::empty().push(get_nth_byte!(v, rest_len));
            assert(buf == single + rest_buf);

            assert(single.len() == 1);
            assert((single + rest_buf).len() == single.len() + rest_buf.len());
            assert(buf.len() == single.len() + rest_buf.len());
            assert(buf.len() == rest_len as int + 1);

            assert(buf.len() == self.0);
        }
    }

}

impl SecureSpecCombinator for VarUInt {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        self.0 > 0
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: VarUIntResult)
        decreases self.0
    {
        if self.wf() && self.in_bound(v) {
            if self.0 == 0 {
                assert(self.in_bound(v));
                assert(v <= n_byte_max_unsigned!(0));
                assert(n_byte_max_unsigned!(0) == 0);
                assert(v == 0);
                let buf = self.spec_serialize(v);
                assert(buf == Seq::<u8>::empty());
                assert(self.spec_parse(buf) == Some((0int, 0u64)));
            } else {
                assert(self.0 > 0);

                let rest_len = (self.0 - 1) as usize;
                let rest = Self(rest_len);
                let rest_val = v & n_byte_max_unsigned!(rest_len);
                assert(rest_len + 1 == self.0);

                assert(self.wf());
                assert(self.in_bound(v));
                Self::lemma_tail_context(self.0);
                assert(rest.wf());
                Self::lemma_mask_fits(rest_len, v);
                assert(fits_n_bytes_unsigned!(rest_val, rest_len));
                assert(rest.in_bound(rest_val));

                rest.theorem_serialize_parse_roundtrip(rest_val);
                rest.lemma_serialize_ok(rest_val);
                assert(rest.spec_serialize(rest_val).len() == rest.0) by {
                    assert(rest.wf());
                    assert(rest.in_bound(rest_val));
                };

                let rest_buf = rest.spec_serialize(rest_val);
                let buf = self.spec_serialize(v);
                let single = Seq::<u8>::empty().push(get_nth_byte!(v, rest_len));

                assert(rest_buf.len() == rest.0 as int);
                assert(rest.0 as int == rest_len as int);

                assert(buf == single + rest_buf);
                assert(single.len() == 1);
                assert(buf.len() == self.0) by {
                    assert((single + rest_buf).len() == single.len() + rest_buf.len());
                };

                assert(buf.drop_first() == rest_buf) by {
                    assert(single.drop_first() == Seq::<u8>::empty());
                };

                assert(buf[0] == get_nth_byte!(v, self.0 - 1)) by {
                    assert(single[0] == get_nth_byte!(v, self.0 - 1));
                };

                let rest_parse = rest.spec_parse(rest_buf);
                assert(rest_parse == Some((rest.0 as int, rest_val)));
                assert(rest_parse.is_some());
                rest.lemma_parse_returns_length(rest_buf);
                let (len_rest, val_rest) = rest_parse.unwrap();
                assert(len_rest == (self.0 - 1) as int);
                assert(val_rest == rest_val);

                let parsed = self.spec_parse(buf);
                assert(rest_val == v & n_byte_max_unsigned!(rest_len));
                assert(rest_len + 1 == self.0);
                assert(rest_len < uint_size!());
                assert(fits_n_bytes_unsigned!(v, rest_len + 1)) by {
                    assert(self.in_bound(v));
                    assert(rest_len + 1 == self.0);
                };
                Self::lemma_prepend_restore(rest_len, v);
                assert(prepend_byte!(rest_val, get_nth_byte!(v, rest_len), rest_len) == v);
                assert(parsed == Some((self.0 as int, v)));
                assert(parsed.is_some());
                let parsed_pair = parsed.unwrap();
                assert(parsed_pair == (self.0 as int, v));
                let (len, val) = parsed_pair;
                assert(len == self.0 as int);
                assert(val == v);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        decreases self.0
    {
        if self.wf() {
            if let Some((n, v)) = self.spec_parse(buf) {
                self.lemma_parse_returns_length(buf);
                self.lemma_parse_ok_bound(buf);

                assert(n == self.0 as int);
                assert(self.in_bound(v));

                if self.0 == 0 {
                    assert(self.spec_parse(buf) == Some((0int, 0u64)));
                    assert(v == 0);
                    assert(self.spec_serialize(v) == Seq::<u8>::empty());
                    assert(buf.take(n) == Seq::<u8>::empty());
                } else {
                    assert(self.0 <= buf.len());
                    assert(self.0 > 0);

                    let rest_len = (self.0 - 1) as usize;
                    let rest = Self(rest_len);
                    let rest_buf = buf.drop_first();
                    let byte = buf[0];

                    Self::lemma_tail_context(self.0);
                    assert(rest.wf());

                    let rest_parse = rest.spec_parse(rest_buf);
                    match rest_parse {
                        Some((len_rest, rest_val)) => {
                            rest.lemma_parse_returns_length(rest_buf);
                            rest.lemma_parse_ok_bound(rest_buf);

                            assert(len_rest == rest_len as int);
                            assert(rest.in_bound(rest_val));

                            rest.theorem_parse_serialize_roundtrip(rest_buf);
                            rest.lemma_serialize_ok(rest_val);
                            assert(rest.spec_serialize(rest_val).len() == rest.0) by {
                                assert(rest.wf());
                                assert(rest.in_bound(rest_val));
                            };

                            let rest_serialized = rest.spec_serialize(rest_val);
                            assert(rest_serialized == rest_buf.take(len_rest));

                            assert(v == prepend_byte!(rest_val, byte, rest_len));
                            assert(rest_len < uint_size!());
                            assert(fits_n_bytes_unsigned!(rest_val, rest_len)) by {
                                assert(rest.in_bound(rest_val));
                            };
                            Self::lemma_prepend_byte_get_nth(rest_len, rest_val, byte);
                            assert(get_nth_byte!(v, rest_len) == byte);

                            Self::lemma_prepend_mask(rest_len, rest_val, byte);
                            assert(v & n_byte_max_unsigned!(rest_len) == rest_val) by {
                                assert(prepend_byte!(rest_val, byte, rest_len) & n_byte_max_unsigned!(rest_len) == rest_val);
                                assert(v == prepend_byte!(rest_val, byte, rest_len));
                            };
                            assert(rest.spec_serialize(rest_val)
                                == rest.spec_serialize(v & n_byte_max_unsigned!(rest_len))) by {
                                assert(rest_val == v & n_byte_max_unsigned!(rest_len));
                            };
                            assert(rest.spec_serialize(v & n_byte_max_unsigned!(rest_len)) == rest_serialized) by {
                                assert(rest.spec_serialize(rest_val)
                                    == rest.spec_serialize(v & n_byte_max_unsigned!(rest_len)));
                            };

                            let single = Seq::<u8>::empty().push(byte);
                            assert(self.spec_serialize(v)
                                == Seq::<u8>::empty().push(get_nth_byte!(v, rest_len))
                                    + rest.spec_serialize(v & n_byte_max_unsigned!(rest_len))) by {
                                assert(self.wf());
                                assert(self.in_bound(v));
                                assert(self.0 > 0);
                                assert(rest_len == (self.0 - 1) as usize);
                            };
                            assert(self.spec_serialize(v) == single + rest_serialized);

                            assert(buf.take(1) == single) by {
                                assert(single.len() == 1);
                                assert(single[0] == byte);
                                assert(buf.take(1).len() == 1);
                                assert(buf.take(1)[0] == byte);
                            };

                            assert(buf.skip(1) == rest_buf);
                            assert(rest_serialized == buf.skip(1).take(len_rest));

                            assert(buf.take(self.0 as int)
                                == buf.take(1) + buf.skip(1).take(len_rest));

                            assert(self.spec_serialize(v) == buf.take(self.0 as int));
                        }
                        None => {
                            assert(false);
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        decreases self.0
    {
        if self.wf() && self.spec_parse(s1).is_some() {
            self.lemma_parse_returns_length(s1);

            if self.0 == 0 {
                assert(self.spec_parse(s1) == Some((0int, 0u64)));
                assert(self.spec_parse(s1 + s2) == Some((0int, 0u64)));
            } else {
                let rest = Self((self.0 - 1) as usize);
                let byte = s1[0];
                let rest_s1 = s1.drop_first();

                Self::lemma_tail_context(self.0);
                assert(rest.wf());

                rest.lemma_prefix_secure(rest_s1, s2);

                let rest_parse = rest.spec_parse(rest_s1);
                match rest_parse {
                    Some((len_rest, rest_val)) => {
                        rest.lemma_parse_returns_length(rest_s1);
                        assert(rest.spec_parse(rest_s1 + s2) == Some((len_rest, rest_val)));

                        let combined = prepend_byte!(rest_val, byte, self.0 - 1);
                        assert(self.spec_parse(s1) == Some((self.0 as int, combined)));

                        assert((s1 + s2)[0] == byte);
                        assert((s1 + s2).drop_first() == rest_s1 + s2);

                        assert(self.spec_parse(s1 + s2) == Some((self.0 as int, combined)));
                    }
                    None => {
                        assert(false);
                    }
                }
            }
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>)
        decreases self.0
    {
        if self.wf() && self.spec_parse(s).is_some() {
            self.lemma_parse_returns_length(s);
            self.lemma_parse_ok(s);

            let res = self.spec_parse(s).unwrap();
            assert(res.0 == self.0 as int);
            assert(0 <= res.0);
            assert(self.0 as int <= s.len());
        }
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>)
        decreases self.0
    {
        if self.wf() && self.0 > 0 {
            if let Some((n, _)) = self.spec_parse(s) {
                self.lemma_parse_returns_length(s);
                assert(n == self.0 as int);
                assert(n > 0);
            }
        }
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for VarUInt {
    type Type = VarUIntResult;
    type SType = VarUIntResult;

    fn length(&self, _v: Self::SType) -> usize {
        let len = self.0;
        proof {
            assume(self@.spec_serialize(_v@).len() == len);
        }
        len
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
                Self((len - i) as usize).lemma_serialize_ok(v & n_byte_max_unsigned!(len - i));

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

    pub proof fn lemma_sign_extend_masked_roundtrip(&self, v: VarIntResult)
        requires self.to_var_uint().wf(), self.wf(v)
        ensures sign_extend!((v as VarUIntResult) & n_byte_max_unsigned!(self.0), self.0) == v
    {
        let len = self.0;
        assert(len <= uint_size!()) by {
            assert(self.to_var_uint().wf());
        };
        assert(n_byte_min_signed!(len) <= v) by {
            assert(self.wf(v));
        };
        assert(v <= n_byte_max_signed!(len)) by {
            assert(self.wf(v));
        };
        assert(
            len <= uint_size!() &&
            n_byte_min_signed!(len) <= v &&
            v <= n_byte_max_signed!(len)
            ==> sign_extend!((v as VarUIntResult) & n_byte_max_unsigned!(len), len) == v
        ) by (bit_vector);
        assert(sign_extend!((v as VarUIntResult) & n_byte_max_unsigned!(len), len) == v);
    }

    pub proof fn lemma_sign_extend_parse(&self, raw: VarUIntResult)
        requires self.to_var_uint().wf(), fits_n_bytes_unsigned!(raw, self.0)
        ensures
            self.wf(sign_extend!(raw, self.0)),
            ((sign_extend!(raw, self.0)) as VarUIntResult) & n_byte_max_unsigned!(self.0) == raw
    {
        let len = self.0;
        assert(len <= uint_size!()) by {
            assert(self.to_var_uint().wf());
        };
        assert(fits_n_bytes_unsigned!(raw, len));
        assert(
            len <= uint_size!() &&
            fits_n_bytes_unsigned!(raw, len)
            ==> n_byte_min_signed!(len) <= sign_extend!(raw, len)
        ) by (bit_vector);
        assert(
            len <= uint_size!() &&
            fits_n_bytes_unsigned!(raw, len)
            ==> sign_extend!(raw, len) <= n_byte_max_signed!(len)
        ) by (bit_vector);
        assert(n_byte_min_signed!(len) <= sign_extend!(raw, len));
        assert(sign_extend!(raw, len) <= n_byte_max_signed!(len));
        assert(self.wf(sign_extend!(raw, len))) by {
            assert(n_byte_min_signed!(len) <= sign_extend!(raw, len));
            assert(sign_extend!(raw, len) <= n_byte_max_signed!(len));
        };
        assert(
            len <= uint_size!() &&
            fits_n_bytes_unsigned!(raw, len)
            ==> ((sign_extend!(raw, len)) as VarUIntResult) & n_byte_max_unsigned!(len) == raw
        ) by (bit_vector);
        assert(((sign_extend!(raw, len)) as VarUIntResult) & n_byte_max_unsigned!(len) == raw);
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
            Seq::<u8>::empty()
        }
    }
}

impl SecureSpecCombinator for VarInt {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        self.0 > 0
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: VarIntResult)
    {
        let uint = self.to_var_uint();

        if uint.wf() {
            if self.wf(v) {
                let masked = (v as VarUIntResult) & n_byte_max_unsigned!(self.0);

                VarUInt::lemma_mask_fits(self.0, v as VarUIntResult);
                assert(fits_n_bytes_unsigned!(masked, self.0)) by {
                    assert(masked == (v as VarUIntResult) & n_byte_max_unsigned!(self.0));
                };
                assert(uint.in_bound(masked));

                uint.theorem_serialize_parse_roundtrip(masked);
                uint.lemma_serialize_ok(masked);
                assert(uint.spec_serialize(masked).len() == uint.0) by {
                    assert(uint.wf());
                    assert(uint.in_bound(masked));
                };

                let buf = self.spec_serialize(v);
                assert(buf == uint.spec_serialize(masked));

                let parse_res = uint.spec_parse(buf);
                assert(parse_res == Some((self.0 as int, masked)));

                assert(self.spec_parse(buf)
                    == Some((self.0 as int, sign_extend!(masked, self.0))));
                self.lemma_sign_extend_masked_roundtrip(v);
                assert(sign_extend!(masked, self.0) == v);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {
        let uint = self.to_var_uint();

        if uint.wf() {
            if let Some((n, v)) = self.spec_parse(buf) {
                let uint_parse = uint.spec_parse(buf);
                assert(uint_parse.is_some());
                let (n_uint, raw) = uint_parse.unwrap();

                assert(n == n_uint);
                assert(v == sign_extend!(raw, self.0));

                uint.theorem_parse_serialize_roundtrip(buf);
                uint.lemma_parse_ok_bound(buf);
                assert(uint.in_bound(raw));
                assert(fits_n_bytes_unsigned!(raw, self.0)) by {
                    assert(uint.in_bound(raw));
                };

                assert(uint.spec_serialize(raw) == buf.take(n_uint));

                self.lemma_sign_extend_parse(raw);
                assert(((sign_extend!(raw, self.0)) as VarUIntResult)
                    & n_byte_max_unsigned!(self.0) == raw);

                assert(self.wf(v)) by {
                    assert(v == sign_extend!(raw, self.0));
                };

                assert((v as VarUIntResult) & n_byte_max_unsigned!(self.0) == raw) by {
                    assert(v == sign_extend!(raw, self.0));
                    assert(((sign_extend!(raw, self.0)) as VarUIntResult)
                        & n_byte_max_unsigned!(self.0) == raw);
                };

                assert(self.spec_serialize(v)
                    == uint.spec_serialize((v as VarUIntResult) & n_byte_max_unsigned!(self.0))) by {
                    assert(self.wf(v));
                    assert(self.to_var_uint().wf());
                };

                assert(self.spec_serialize(v) == uint.spec_serialize(raw)) by {
                    assert((v as VarUIntResult) & n_byte_max_unsigned!(self.0) == raw);
                };
                assert(self.spec_serialize(v) == buf.take(n));
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {
        let uint = self.to_var_uint();

        if uint.wf() && self.spec_parse(s1).is_some() {
            uint.lemma_prefix_secure(s1, s2);

            let parse1 = uint.spec_parse(s1);
            assert(parse1.is_some());
            let (n, raw) = parse1.unwrap();

            let parse2 = uint.spec_parse(s1 + s2);
            assert(parse2 == Some((n, raw)));

            assert(self.spec_parse(s1) == Some((n, sign_extend!(raw, self.0))));
            assert(self.spec_parse(s1 + s2) == Some((n, sign_extend!(raw, self.0))));
        }
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    {
        let uint = self.to_var_uint();

        if uint.wf() {
            if let Some((n, _)) = self.spec_parse(s) {
                let uint_parse = uint.spec_parse(s);
                assert(uint_parse.is_some());
                let (n_uint, _) = uint_parse.unwrap();
                assert(n == n_uint);

                uint.lemma_parse_length(s);
                assert(0 <= n_uint <= s.len());
                assert(0 <= n <= s.len());
            }
        }
    }
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    {
        let uint = self.to_var_uint();

        if uint.wf() {
            if let Some((n, _)) = self.spec_parse(s) {
                let uint_parse = uint.spec_parse(s);
                assert(uint_parse.is_some());
                let (n_uint, _) = uint_parse.unwrap();
                assert(n == n_uint);

                if self.0 > 0 {
                    uint.lemma_parse_productive(s);
                    assert(n_uint > 0);
                    assert(n > 0);
                }
            }
        }
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for VarInt {
    type Type = VarIntResult;
    type SType = VarIntResult;

    fn length(&self, _v: Self::SType) -> usize {
        let len = self.0;
        proof {
            assume(self@.spec_serialize(_v@).len() == len);
        }
        len
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        if self.0 > uint_size!() {
            return Err(ParseError::Other("Size overflow".to_string()));
        }

        if self.0 > 0 {
            proof {
                assert(self.0 <= uint_size!());
                assert(VarUInt(self.0).requires());
            }

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
                return Ok(0);
            } else {
                return Err(SerializeError::Other("Invalid zero encoding".to_string()));
            }
        }

        // Check if v is within bounds
        if v < n_byte_min_signed!(self.0) || v > n_byte_max_signed!(self.0) {
            return Err(SerializeError::Other("Size overflow".to_string()));
        }

        assert(self.0 <= uint_size!());
        assert(VarUInt(self.0).in_bound((v as VarUIntResult) & n_byte_max_unsigned!(self.0))) by {
            VarUInt::lemma_mask_fits(self.0, v as VarUIntResult);
        };

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
