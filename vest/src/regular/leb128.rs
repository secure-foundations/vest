use alloc::string::ToString;

use crate::properties::*;
use vstd::assert_seqs_equal;
use vstd::prelude::*;

verus! {

/// Unsigned LEB128
pub struct UnsignedLEB128;

/// Result of UnsignedLEB128
pub type UInt = u64;

impl View for UnsignedLEB128 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        Self
    }
}

/// Byte size of UInt
#[allow(unused_macros)]
macro_rules! uint_size { () => { 8 } }

pub(super) use uint_size;

/// Check if the highest bit is set in an u8
#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => { $v as u8 >= 0x80 };
}

pub(crate) use is_high_8_bit_set;

/// Take the lowest 7 bits as an u8
#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => { $v as u8 & 0x7f };
}

pub(crate) use take_low_7_bits;

/// Set the highest bit to 1 as an u8
#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}

pub(super) use set_high_8_bit;

/// Max value for an n-bit unsigned integer
#[allow(unused_macros)]
macro_rules! n_bit_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (((8 * uint_size!()) - $n) as usize) } }
}

pub(super) use n_bit_max_unsigned;

impl SpecCombinator for UnsignedLEB128 {
    type Type = UInt;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
        decreases s.len(),
    {
        let v = take_low_7_bits!(s.first());

        if s.len() != 0 {
            if is_high_8_bit_set!(s.first()) {
                match self.spec_parse(s.drop_first()) {
                    Some(
                        (n, v2),
                    ) =>
                    // Check for overflow and canonicity (v2 should not be 0)
                    if n < usize::MAX && 0 < v2 <= n_bit_max_unsigned!(8 * uint_size!() - 7) {
                        Some((n + 1, v2 << 7 | v as Self::Type))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                Some((1, v as Self::Type))
            }
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        Self::spec_serialize_helper(v)
    }
}

impl UnsignedLEB128 {
    /// Helper function for spec_serialize
    pub open spec fn spec_serialize_helper(v: UInt) -> Seq<u8>
        decreases v,
        via Self::spec_serialize_decreases
    {
        let lo = take_low_7_bits!(v);
        let hi = v >> 7;

        if hi == 0 {
            seq![lo]
        } else {
            seq![set_high_8_bit!(lo)] + Self::spec_serialize_helper(hi)
        }
    }

    #[via_fn]
    proof fn spec_serialize_decreases(v: UInt) {
        assert(v >> 7 != 0 ==> v >> 7 < v) by (bit_vector);
    }

    proof fn lemma_spec_serialize_length(&self, v: UInt)
        ensures
            self.spec_serialize(v).len() <= 10,
    {
        reveal_with_fuel(UnsignedLEB128::spec_serialize_helper, 10);
        assert(v >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 == 0) by (bit_vector);
    }

    proof fn lemma_serialize_last_byte_high_8_bit_not_set(&self, v: UInt)
        ensures
            !is_high_8_bit_set!(self.spec_serialize(v).last()),
        decreases v,
    {
        let lo = take_low_7_bits!(v);
        let hi = v >> 7;

        if hi == 0 {
            assert(!is_high_8_bit_set!(take_low_7_bits!(v))) by (bit_vector);
            assert(self.spec_serialize(v) == seq![lo]);
        } else {
            let s = Self::spec_serialize_helper(hi);
            assert(Self::spec_serialize_helper(v) == seq![set_high_8_bit!(lo)] + s);
            assert(v >> 7 != 0 ==> v >> 7 < v) by (bit_vector);
            self.lemma_serialize_last_byte_high_8_bit_not_set(hi);
        }
    }

    proof fn lemma_parse_high_8_bits_set_until_last(&self, s: Seq<u8>)
        ensures
            self.spec_parse(s) matches Some((n, v)) ==> {
                &&& forall|i: int| 0 <= i < n - 1 ==> is_high_8_bit_set!(s.spec_index(i))
            },
        decreases s.len(),
    {
        if let Some((n, v)) = self.spec_parse(s) {
            assert(n <= s.len()) by { self.lemma_parse_length(s) };
            let s0 = s[0];
            if n == 1 {
                // assert(!is_high_8_bit_set!(s0));
                if (is_high_8_bit_set!(s0)) {
                    assert(self.spec_parse(s.drop_first()) matches Some((n1, _)) && n1 == 0);
                    self.lemma_parse_productive(s.drop_first());
                }
            } else {
                assert(is_high_8_bit_set!(s0));
                self.lemma_parse_high_8_bits_set_until_last(s.drop_first());
                assert_seqs_equal!(s == seq![s0] + s.drop_first());
            }
        }
    }

    proof fn lemma_spec_parse_low_7_bits(&self, s: Seq<u8>)
        requires
            s.len() != 0,
        ensures
            self.spec_parse(s) matches Some((_, x)) ==> {
                let s0 = s[0];
                take_low_7_bits!(x) == take_low_7_bits!(s0)
            },
    {
        let s0 = s[0];
        if is_high_8_bit_set!(s0) {
            if let Some((_, rest)) = self.spec_parse(s.drop_first()) {
                assert(take_low_7_bits!(rest << 7 | take_low_7_bits!(s0) as UInt)
                    == take_low_7_bits!(s0)) by (bit_vector);
            }
        } else {
            assert(take_low_7_bits!(take_low_7_bits!(s0)) == take_low_7_bits!(s0)) by (bit_vector);
        }
    }

    proof fn lemma_spec_parse_non_zero(&self, s: Seq<u8>)
        requires
            ({
                let s0 = s[0];
                is_high_8_bit_set!(s0)
            }),
        ensures
            self.spec_parse(s) matches Some((_, x)) ==> x > 1,
    {
        if let Some((_, x)) = self.spec_parse(s) {
            let (_, rest) = self.spec_parse(s.drop_first()).unwrap();
            let s0 = s[0];

            assert(0 < rest <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==> rest << 7
                | take_low_7_bits!(s0) as UInt > 1) by (bit_vector);
        }
    }
}

impl SecureSpecCombinator for UnsignedLEB128 {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        decreases s1.len(),
    {
        if Self::is_prefix_secure() {
            if let Some((n1, v1)) = self.spec_parse(s1) {
                self.lemma_prefix_secure(s1.drop_first(), s2);
                assert((s1 + s2).drop_first() == s1.drop_first() + s2);
            }
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>)
        decreases s.len(),
    {
        if s.len() != 0 {
            self.lemma_parse_length(s.drop_first());
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        decreases v,
    {
        let s = self.spec_serialize(v);
        let lo = take_low_7_bits!(v);
        let hi = v >> 7;

        self.lemma_spec_serialize_length(v);

        assert({
            &&& !is_high_8_bit_set!(take_low_7_bits!(v))
            &&& v >> 7 == 0 ==> v == take_low_7_bits!(v)
            &&& v >> 7 != 0 ==> v >> 7 < v
            &&& is_high_8_bit_set!(set_high_8_bit!(lo))
            &&& (v >> 7) << 7 | take_low_7_bits!(v) as UInt == v
            &&& (v >> 7) <= n_bit_max_unsigned!(8 * uint_size!() - 7)
            &&& take_low_7_bits!(set_high_8_bit!(take_low_7_bits!(v))) == take_low_7_bits!(v)
        }) by (bit_vector);

        if hi != 0 {
            self.theorem_serialize_parse_roundtrip(hi);

            let hi_bytes = self.spec_serialize(hi);
            assert(s.drop_first() == hi_bytes);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>)
        decreases s.len(),
    {
        if let Some((n, v)) = self.spec_parse(s) {
            let s0 = s.first();

            if is_high_8_bit_set!(s.first()) {
                self.theorem_parse_serialize_roundtrip(s.drop_first());

                let (n2, v2) = self.spec_parse(s.drop_first()).unwrap();

                if n2 < usize::MAX && 0 < v2 <= n_bit_max_unsigned!(8 * uint_size!() - 7) {
                    self.lemma_parse_length(s.drop_first());

                    assert(self.spec_serialize(v2) == s.drop_first().take(n2 as int));
                    assert(v == v2 << 7 | take_low_7_bits!(s0) as Self::Type);

                    assert(0 < v2 <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==> v == v2 << 7
                        | take_low_7_bits!(s0) as Self::Type ==> is_high_8_bit_set!(s0) ==> v >> 7
                        != 0 && take_low_7_bits!(v) == take_low_7_bits!(s0)
                        && set_high_8_bit!(take_low_7_bits!(v)) == s0 && v2 == v >> 7)
                        by (bit_vector);

                    assert(self.spec_serialize(v) =~= seq![s0] + self.spec_serialize(v2));

                    assert(n == n2 + 1);
                    assert(seq![s0] + s.drop_first().take(n2 as int) =~= s.take(n as int));
                }
            } else {
                assert(!is_high_8_bit_set!(s0) ==> v == take_low_7_bits!(s0) ==> take_low_7_bits!(v)
                    == v && s0 == v && v >> 7 == 0) by (bit_vector);

                assert(seq![v as u8] == s.take(1));
                assert(self.spec_serialize(v) =~= seq![v as u8]);
            }
        }
    }

    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>)
        decreases s.len(),
    {
        if s.len() != 0 {
            self.lemma_parse_productive(s.drop_first());
        }
    }
}

impl<'x, I, O> Combinator<'x, I, O> for UnsignedLEB128 where
    I: VestPublicInput,
    O: VestPublicOutput<I>,
 {
    type Type = UInt;

    type SType = &'x UInt;

    #[verifier::external_body]
    fn length(&self, v: Self::SType) -> usize {
        let mut acc = 0;
        let mut v = *v;

        while v > 0 {
            acc += 1;
            v >>= 7;
        }

        acc
    }

    fn parse(&self, ss: I) -> (res: PResult<Self::Type, ParseError>) {
        let s = ss.as_byte_slice();
        let mut acc: Self::Type = 0;
        let mut i = 0;
        let mut shift = 0;

        // Invariants before the loop
        proof {
            assert(s@.skip(0) == s@);
            if self.spec_parse(s@) is Some {
                let rest = self.spec_parse(s@).unwrap().1;
                assert(0 | rest << 0 == rest) by (bit_vector);
            }
            assert(n_bit_max_unsigned!(8 * uint_size!()) == UInt::MAX) by (bit_vector);
        }

        while i < s.len()
            invariant
                0 <= i <= s@.len(),
                i <= 9,
                s@ == ss@,
                shift == i * 7,
                // IH 1
                self.spec_parse(s@) matches Some((n, res)) ==> {
                    &&& self.spec_parse(s@.skip(i as int)) matches Some((n_rest, rest))
                    &&& res == acc | rest << (i * 7)
                    &&& n == i
                        + n_rest
                    // &&& rest <= n_bit_max_unsigned!(8 * uint_size!() - 7 * i)

                },
                // IH 2
                ({
                    &&& self.spec_parse(s@.skip(i as int)) matches Some((n, rest))
                    &&& n <= s@.len() - i
                    &&& 0 < rest <= n_bit_max_unsigned!(8 * uint_size!() - 7 * i)
                }) ==> self.spec_parse(s@) is Some,
                // IH 3
                forall|j|
                    0 <= j < i ==> self.spec_parse(#[trigger] s@.skip(j)) is None
                        ==> self.spec_parse(s@) is None,
                // IH 4
                forall|j|
                    0 <= j < i ==> {
                        let s_j = #[trigger] s@[j];
                        is_high_8_bit_set!(s_j)
                    },
                acc <= n_bit_max_unsigned!(i * 7),
            decreases s.len() - i,
        {
            let s_i = s[i];
            let v = take_low_7_bits!(s_i);
            let hi_set = is_high_8_bit_set!(s_i);

            if i == 9 && (hi_set || v > 1) {
                proof {
                    if let Some((n_rest, rest)) = self.spec_parse(s@.skip(i as int)) {
                        if rest != 0 {
                            // TODO: make this an inductive proof
                            let s0 = s@[0];
                            let s1 = s@[1];
                            let s2 = s@[2];
                            let s3 = s@[3];
                            let s4 = s@[4];
                            let s5 = s@[5];
                            let s6 = s@[6];
                            let s7 = s@[7];
                            let s8 = s@[8];

                            assert(rest > 1) by {
                                assert(take_low_7_bits!(rest) == v && v > 1 ==> rest > 1)
                                    by (bit_vector);
                                self.lemma_spec_parse_low_7_bits(s@.skip(i as int));

                                if hi_set {
                                    self.lemma_spec_parse_non_zero(s@.skip(i as int));
                                }
                            }

                            assert(rest > 1 ==> rest <= n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ==> {
                                ||| ((((((((rest << 7 | take_low_7_bits!(s8) as Self::Type) << 7
                                    | take_low_7_bits!(s7) as Self::Type) << 7
                                    | take_low_7_bits!(s6) as Self::Type) << 7
                                    | take_low_7_bits!(s5) as Self::Type) << 7
                                    | take_low_7_bits!(s4) as Self::Type) << 7
                                    | take_low_7_bits!(s3) as Self::Type) << 7
                                    | take_low_7_bits!(s2) as Self::Type) << 7
                                    | take_low_7_bits!(s1) as Self::Type)
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ||| (((((((rest << 7 | take_low_7_bits!(s8) as Self::Type) << 7
                                    | take_low_7_bits!(s7) as Self::Type) << 7
                                    | take_low_7_bits!(s6) as Self::Type) << 7
                                    | take_low_7_bits!(s5) as Self::Type) << 7
                                    | take_low_7_bits!(s4) as Self::Type) << 7
                                    | take_low_7_bits!(s3) as Self::Type) << 7
                                    | take_low_7_bits!(s2) as Self::Type)
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ||| (((((((rest << 7 | take_low_7_bits!(s8) as Self::Type) << 7
                                    | take_low_7_bits!(s7) as Self::Type) << 7
                                    | take_low_7_bits!(s6) as Self::Type) << 7
                                    | take_low_7_bits!(s5) as Self::Type) << 7
                                    | take_low_7_bits!(s4) as Self::Type) << 7
                                    | take_low_7_bits!(s3) as Self::Type) << 7
                                    | take_low_7_bits!(s2) as Self::Type)
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ||| ((((((rest << 7 | take_low_7_bits!(s8) as Self::Type) << 7
                                    | take_low_7_bits!(s7) as Self::Type) << 7
                                    | take_low_7_bits!(s6) as Self::Type) << 7
                                    | take_low_7_bits!(s5) as Self::Type) << 7
                                    | take_low_7_bits!(s4) as Self::Type) << 7
                                    | take_low_7_bits!(s3) as Self::Type)
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ||| (((((rest << 7 | take_low_7_bits!(s8) as Self::Type) << 7
                                    | take_low_7_bits!(s7) as Self::Type) << 7
                                    | take_low_7_bits!(s6) as Self::Type) << 7
                                    | take_low_7_bits!(s5) as Self::Type) << 7
                                    | take_low_7_bits!(s4) as Self::Type)
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ||| ((((rest << 7 | take_low_7_bits!(s8) as Self::Type) << 7
                                    | take_low_7_bits!(s7) as Self::Type) << 7
                                    | take_low_7_bits!(s6) as Self::Type) << 7
                                    | take_low_7_bits!(s5) as Self::Type)
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ||| (((rest << 7 | take_low_7_bits!(s8) as Self::Type) << 7
                                    | take_low_7_bits!(s7) as Self::Type) << 7
                                    | take_low_7_bits!(s6) as Self::Type)
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ||| ((rest << 7 | take_low_7_bits!(s8) as Self::Type) << 7
                                    | take_low_7_bits!(s7) as Self::Type)
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                                ||| rest << 7 | take_low_7_bits!(s8) as Self::Type
                                    > n_bit_max_unsigned!(8 * uint_size!() - 7)
                            }) by (bit_vector);

                            assert(self.spec_parse(s@) is None) by {
                                reveal_with_fuel(
                                    <UnsignedLEB128 as SpecCombinator>::spec_parse,
                                    10,
                                );

                                if self.spec_parse(s@) is Some {
                                    assert(self.spec_parse(s@).unwrap().1 == self.spec_parse(
                                        s@.drop_first(),
                                    ).unwrap().1 << 7 | take_low_7_bits!(s0) as Self::Type);

                                    assert(self.spec_parse(s@).unwrap().1 == (self.spec_parse(
                                        s@.drop_first().drop_first(),
                                    ).unwrap().1 << 7 | take_low_7_bits!(s1) as Self::Type) << 7
                                        | take_low_7_bits!(s0) as Self::Type);

                                    assert(s@.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first()
                                        == s@.skip(9));

                                    assert(s@.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first()
                                        == s@.skip(8));

                                    assert(s@.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first()
                                        == s@.skip(7));

                                    assert(s@.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first()
                                        == s@.skip(6));

                                    assert(s@.drop_first().drop_first().drop_first().drop_first().drop_first()
                                        == s@.skip(5));

                                    assert(s@.drop_first().drop_first().drop_first().drop_first()
                                        == s@.skip(4));

                                    assert(s@.drop_first().drop_first().drop_first() == s@.skip(3));

                                    assert(s@.drop_first().drop_first() == s@.skip(2));
                                    assert(s@.drop_first() == s@.skip(1));
                                    assert(s@ == s@.skip(0));
                                }
                            }
                        } else {
                            // Otherwise parsing s@.skip(i - 1) should fail
                            // due to failing canonicity
                            assert(s@.skip(i - 1).drop_first() == s@.skip(i as int));
                        }
                    }
                }

                return Err(ParseError::Other("LEB128 overflow".to_string()));
            }
            // No overflow for i < 9

            assert(i < 9 ==> v == take_low_7_bits!(s_i) ==> acc <= n_bit_max_unsigned!(i * 7)
                ==> acc | (v as Self::Type) << (i * 7) <= n_bit_max_unsigned!((i + 1) * 7))
                by (bit_vector);

            // No overflow for i == 9
            assert(v == 1 && i == 9 ==> (v as u128) << (i * 7) <= UInt::MAX) by (bit_vector);
            assert(v == 1 ==> 0 < v <= n_bit_max_unsigned!(8 * uint_size!() - 7 * 9))
                by (bit_vector);

            let ghost prev_acc = acc;
            acc = acc | (v as Self::Type) << shift;

            if !hi_set {
                // Defined by defn of spec_parse
                let ghost (n_rest, rest) = self.spec_parse(s@.skip(i as int)).unwrap();

                if i != 0 && v == 0 {
                    assert(rest == 0);
                    assert(s@.skip(i - 1).drop_first() == s@.skip(i as int));
                    assert(self.spec_parse(s@.skip(i - 1)) is None);
                    return Err(ParseError::Other("failing LEB128 canonicity".to_string()));
                }
                proof {
                    if i != 0 {
                        assert(n_rest <= s@.len() - i);
                        assert(i < 9 ==> i != 0 && v != 0 ==> v == take_low_7_bits!(s_i) ==> 0 < v
                            <= n_bit_max_unsigned!(8 * uint_size!() - 7 * i)) by (bit_vector);

                        // Defined by IH 2
                        let (n, res) = self.spec_parse(s@).unwrap();
                        assert(acc == res);
                    }
                }

                return Ok((i + 1, acc));
            }
            proof {
                assert(s@.skip(i as int).drop_first() == s@.skip(i + 1));

                // Prove IH 1
                if let Some((_, res)) = self.spec_parse(s@) {
                    // Defined by IH
                    let rest1 = self.spec_parse(s@.skip(i as int)).unwrap().1;
                    // Defined by rest1
                    let rest2 = self.spec_parse(s@.skip(i as int).drop_first()).unwrap().1;

                    assert(v == take_low_7_bits!(s_i) ==> acc == prev_acc | (v as Self::Type) << (i
                        * 7)
                    // By defn of spec_parse
                     ==> rest1 == rest2 << 7 | v as Self::Type
                    // By IH
                     ==> res == prev_acc | rest1 << (i * 7) ==> res == acc | rest2 << ((i + 1) * 7))
                        by (bit_vector);

                    // assert(
                    //     i < 9
                    //     ==> rest2 > n_bit_max_unsigned!(8 * uint_size!() - 7 * (i + 1))
                    //     ==> rest2 << 7 | take_low_7_bits!(s_i) as Self::Type
                    //         > n_bit_max_unsigned!(8 * uint_size!() - 7 * i)
                    // ) by (bit_vector);
                }
                // Prove IH 2

                if let Some((n2, rest2)) = self.spec_parse(s@.skip(i as int).drop_first()) {
                    if n2 <= s@.len() - (i + 1) && 0 < rest2
                        <= n_bit_max_unsigned!(8 * uint_size!() - 7 * (i + 1)) {
                        assert(n2 + 1 <= s@.len() - i);

                        // The inductive bound is less than the bound in parse_spec
                        assert(i < 9 ==> n_bit_max_unsigned!(8 * uint_size!() - 7 * (i + 1))
                            <= n_bit_max_unsigned!(8 * uint_size!() - 7)) by (bit_vector);

                        // Prove precondition of IH 2
                        assert(i < 9 ==> v == take_low_7_bits!(s_i) ==> 0 < rest2
                            <= n_bit_max_unsigned!(8 * uint_size!() - 7 * (i + 1)) ==> 0 < (rest2
                            << 7 | v as Self::Type)
                            <= n_bit_max_unsigned!(8 * uint_size!() - 7 * i)) by (bit_vector);
                    }
                }
            }

            i += 1;
            shift += 7;
        }

        Err(ParseError::UnexpectedEndOfInput)
    }

    #[verifier::external_body]
    fn serialize(&self, v: Self::SType, buf: &mut O, pos: usize) -> (res: SResult<
        usize,
        SerializeError,
    >) {
        let mut v = *v;
        let mut i = 0;
        let mut pos = pos;

        let ghost orig_v = v;
        let ghost spec_res = self.spec_serialize(v);
        proof { self.lemma_spec_serialize_length(v) }

        assert(v == orig_v >> 0) by (bit_vector)
            requires
                v == orig_v,
        ;

        while v > 0
            invariant
                0 <= i <= 10,
                buf@.len() == old(buf)@.len(),
                v == orig_v >> (i * 7),
                self.spec_serialize(orig_v).len() <= 10,
                self.spec_serialize(orig_v).subrange(0, i as int) == buf@.subrange(
                    pos as int,
                    pos + i as int,
                ),
            decreases v,
        {
            let lo = take_low_7_bits!(v);
            let hi = v >> 7;
            let byte = if hi == 0 {
                lo
            } else {
                set_high_8_bit!(lo)
            };

            if pos >= buf.len() {
                return Err(SerializeError::InsufficientBuffer);
            }
            buf.set_byte(pos, byte);

            pos += 1;

            assert(v >> 7 != 0 ==> v >> 7 < v) by (bit_vector);
            assert(v >> 7 == orig_v >> ((i as u64 + 1) * 7)) by (bit_vector)
                requires
                    v == orig_v >> (i as u64 * 7),
                    0 <= i <= 10,
            ;
            v = hi;
            i += 1;
            if i > 10 {
                // should be unreachable for well-formed inputs
                proof { self.lemma_spec_serialize_length(orig_v) }
                // assert(self.spec_serialize(orig_v) is Err);
                return Err(
                    SerializeError::Other("Failed to serialize LEB128: too long".to_string()),
                );
            }
            assert(i <= 10);
        }
        Ok(pos)
    }
}

} // verus!
// #[cfg(test)]
// mod test {
//     use super::*;
//     use leb128::read;
//     use leb128::write;
//     fn test_vest_parser(v: u64) {
//         let mut buf = vec![0u8; 20];
//         let num_written = leb128::write::unsigned(&mut buf, v).expect("leb128 crate write failed");
//         let pres = <_ as Combinator<&[u8], Vec<u8>>>::parse(
//             &UnsignedLEB128,
//             &buf[buf.len() - num_written..],
//         );
//         match pres {
//             Ok((_n_parsed, v_parsed)) => {
//                 assert_eq!(v, v_parsed);
//             }
//             Err(e) => {
//                 panic!("Failed to parse: {:?}", e);
//             }
//         }
//     }
//     fn test_vest_serializer(v: u64) {
//         let mut buf = vec![0u8; 20];
//         let sres = <_ as Combinator<&[u8], Vec<u8>>>::serialize(&UnsignedLEB128, v, &mut buf, 0);
//         if let Err(e) = sres {
//             panic!("Failed to serialize: {:?}", e);
//         }
//         let v_parsed =
//             leb128::read::unsigned(&mut buf.as_slice()).expect("leb128 crate read failed");
//         assert_eq!(v, v_parsed);
//     }
//     #[test]
//     fn randomly_test_vest_leb128() {
//         use rand::Rng;
//         let mut rng = rand::thread_rng();
//         for _ in 0..100000 {
//             let v: u64 = rng.gen();
//             test_vest_parser(v);
//             test_vest_serializer(v);
//         }
//     }
// }
