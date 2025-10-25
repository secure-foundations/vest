use super::*;
/// Some bounds on n-byte integers
/// Most implemented in macros so that they can be used in BV proofs
/// NOTE: many macro definitions here are actually part of the spec
use vstd::prelude::*;

verus! {

/// Signed/unsigned integer types used to represent values in ASN.1
/// All definitions below are relative to these two types
///
/// NOTE: proofs in this module should be independent of the choice of UInt/Int.
/// To change their definitions (to u128/i128, for example), we only need to
/// change the macro uint_size!
pub type UInt = u64;
pub type Int = i64;

#[allow(unused_macros)]
macro_rules! uint_size { () => { 8 } }
pub(super) use uint_size;

/// Max value for an n-byte unsigned integer
#[allow(unused_macros)]
macro_rules! n_byte_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (8 * (uint_size!() - $n) as usize) } }
}
pub(super) use n_byte_max_unsigned;

/// Max value for an n-byte signed integer
#[allow(unused_macros)]
macro_rules! n_byte_max_signed {
    ($n:expr) => { (n_byte_max_unsigned!($n) >> 1) as Int }
}
pub(super) use n_byte_max_signed;

/// Min value for an n-byte signed integer
#[allow(unused_macros)]
macro_rules! n_byte_min_signed {
    ($n:expr) => { if $n == 0 { 0 as Int } else { !(n_byte_max_unsigned!($n) >> 1) as Int } }
}
pub(super) use n_byte_min_signed;

/// Check if the unsigned value can be represented in n bytes
#[allow(unused_macros)]
macro_rules! fits_n_bytes_unsigned {
    ($v:expr, $n:expr) => {
        $v <= n_byte_max_unsigned!($n)
    };
}
pub(super) use fits_n_bytes_unsigned;

/// Check if the signed value can be represented in n bytes
#[allow(unused_macros)]
macro_rules! fits_n_bytes_signed {
    ($v:expr, $n:expr) => {
        n_byte_min_signed!($n) <= $v && $v <= n_byte_max_signed!($n)
    };
}
pub(super) use fits_n_bytes_signed;

#[allow(unused_macros)]
macro_rules! n_bit_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (((8 * uint_size!()) - $n) as usize) } }
}
pub(super) use n_bit_max_unsigned;

/// Get the nth-least significant byte (counting from 0)
#[allow(unused_macros)]
macro_rules! get_nth_byte {
    ($v:expr, $n:expr) => {
        (($v as UInt) >> (8 * ($n as usize))) as u8
    };
}
pub(super) use get_nth_byte;

/// Prepend $b as the $n-th byte (counting from 0) of $v
/// Assuming $v fits in $n bytes
#[allow(unused_macros)]
macro_rules! prepend_byte {
    ($v:expr, $b:expr, $n:expr) => {
        ($v + (($b as UInt) << (8 * ($n as usize)))) as UInt
    };
}
pub(super) use prepend_byte;

/// Sign extend a UInt (assumed to have $n bytes only) to a Int
#[allow(unused_macros)]
macro_rules! sign_extend {
    ($v:expr, $n:expr) => {
        if get_nth_byte!($v, $n - 1) & 0x80 == 0 {
            $v as Int
        } else {
            ($v as UInt + !n_byte_max_unsigned!($n)) as Int
        }
    };
}
pub(super) use sign_extend;

/// Take the lowest 7 bits as an u8
#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => {
        $v as u8 & 0x7f
    };
}
pub(super) use take_low_7_bits;

/// Set the highest bit to 1 as an u8
#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}
pub(super) use set_high_8_bit;

/// Check if the highest bit is set in an u8
#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => {
        $v as u8 >= 0x80
    };
}
pub(super) use is_high_8_bit_set;

/// Specifies the minimum number of bytes required to represent an unsigned integer
pub open spec fn is_min_num_bytes_unsigned(v: UInt, n: UInt) -> bool
{
    &&& 0 < n <= uint_size!()
    &&& if v == 0 {
        n == 1
    } else {
        &&& n > 0
        &&& fits_n_bytes_unsigned!(v, n)
        &&& !fits_n_bytes_unsigned!(v, n - 1)
    }
}

/// Signed version of is_min_num_bytes_unsigned
/// TODO: merge with is_min_num_bytes_unsigned?
pub open spec fn is_min_num_bytes_signed(v: Int, n: UInt) -> bool {
    &&& 0 < n <= uint_size!()
    &&& if v == 0 {
        n == 1
    } else {
        &&& fits_n_bytes_signed!(v, n)
        &&& !fits_n_bytes_signed!(v, n - 1)
    }
}

pub open spec fn min_num_bytes_unsigned(v: UInt) -> UInt
{
    choose |n| is_min_num_bytes_unsigned(v, n)
}

pub open spec fn min_num_bytes_signed(v: Int) -> UInt
{
    choose |n| is_min_num_bytes_signed(v, n)
}

/// A helper induction lemma
proof fn lemma_well_ordering(p: spec_fn(UInt) -> bool, n: UInt)
    requires p(n) && !p(0)
    ensures exists |i| 0 < i <= n && (#[trigger] p(i)) && !p((i - 1) as UInt)
    decreases n
{
    if n > 1 && p((n - 1) as UInt) {
        lemma_well_ordering(p, (n - 1) as UInt);
    }
}

/// min_num_bytes_unsigned exists and is unique
pub proof fn lemma_min_num_bytes_unsigned(v: UInt)
    ensures
        exists |n| is_min_num_bytes_unsigned(v, n),
        forall |n1, n2|
            is_min_num_bytes_unsigned(v, n1) &&
            is_min_num_bytes_unsigned(v, n2) ==> n1 == n2,
{
    // Show uniqueness
    if v == 0 {
        assert(is_min_num_bytes_unsigned(v, 1));
    } else {
        assert(v != 0 ==> !fits_n_bytes_unsigned!(v, 0)) by (bit_vector);
        assert(fits_n_bytes_unsigned!(v, uint_size!())) by (bit_vector);

        let fits_n = |n: UInt| fits_n_bytes_unsigned!(v, n);
        let bytes = choose |i| 0 < i <= uint_size!() && #[trigger] fits_n(i) && !fits_n((i - 1) as UInt);

        lemma_well_ordering(fits_n, uint_size!());
        assert(is_min_num_bytes_unsigned(v, bytes));
    }

    // Show existence
    assert forall |n1, n2|
        is_min_num_bytes_unsigned(v, n1) &&
        is_min_num_bytes_unsigned(v, n2)
    implies n1 == n2 by {
        // By contradiction: if n2 < n1 or n1 < n2, then we can derive false by BV reasoning
        assert(n2 < n1 <= uint_size!() ==> !(fits_n_bytes_unsigned!(v, n2) && !fits_n_bytes_unsigned!(v, n1 - 1))) by (bit_vector);
        assert(n1 < n2 <= uint_size!() ==> !(fits_n_bytes_unsigned!(v, n1) && !fits_n_bytes_unsigned!(v, n2 - 1))) by (bit_vector);
    };
}

/// Exec version of is_min_num_bytes_signed
pub fn is_min_num_bytes_signed_exec(v: Int, n: UInt) -> (res: bool)
    ensures res == is_min_num_bytes_signed(v, n)
{
    n > 0 &&
    n <= uint_size!() &&
    if v == 0 {
        n == 1
    } else {
        fits_n_bytes_signed!(v, n) &&
        !fits_n_bytes_signed!(v, n - 1)
    }
}

/// min_num_bytes_signed exists and is unique
pub proof fn lemma_min_num_bytes_signed(v: Int)
    ensures
        exists |n| is_min_num_bytes_signed(v, n),
        forall |n1, n2|
            is_min_num_bytes_signed(v, n1) &&
            is_min_num_bytes_signed(v, n2) ==> n1 == n2,
{
    // Uniqueness
    if v == 0 {
        assert(is_min_num_bytes_signed(v, 1));
    } else {
        assert(v != 0 ==> !fits_n_bytes_signed!(v, 0)) by (bit_vector);
        assert(fits_n_bytes_signed!(v, uint_size!())) by (bit_vector);

        let fits_n = |n: UInt| fits_n_bytes_signed!(v, n);
        let bytes = choose |i| 0 < i <= uint_size!() && #[trigger] fits_n(i) && !fits_n((i - 1) as UInt);

        lemma_well_ordering(fits_n, uint_size!());
        assert(is_min_num_bytes_signed(v, bytes));
    }

    // Existence
    assert forall |n1, n2|
        is_min_num_bytes_signed(v, n1) &&
        is_min_num_bytes_signed(v, n2)
    implies n1 == n2 by {
        // By contradiction: if n2 < n1 or n1 < n2, then we can derive false by BV reasoning
        assert(n2 < n1 <= uint_size!() ==> !(fits_n_bytes_signed!(v, n2) && !fits_n_bytes_signed!(v, n1 - 1))) by (bit_vector);
        assert(n1 < n2 <= uint_size!() ==> !(fits_n_bytes_signed!(v, n1) && !fits_n_bytes_signed!(v, n2 - 1))) by (bit_vector);
    };
}

/// Exec version of min_num_bytes_unsigned
pub fn min_num_bytes_unsigned_exec(v: UInt) -> (res: UInt)
    ensures is_min_num_bytes_unsigned(v, res)
{
    let mut n = uint_size!();

    assert(n == uint_size!() ==> fits_n_bytes_unsigned!(v, n)) by (bit_vector);

    while n > 0
        invariant
            0 <= n <= uint_size!(),
            fits_n_bytes_unsigned!(v, n),
        decreases n
    {
        if !fits_n_bytes_unsigned!(v, n - 1) {
            return n;
        }
        n = n - 1;
    }

    assert(fits_n_bytes_unsigned!(v, 0) ==> v == 0) by (bit_vector);

    return 1;
}

/// Exec version of min_num_bytes_signed
pub fn min_num_bytes_signed_exec(v: Int) -> (res: UInt)
    ensures is_min_num_bytes_signed(v, res)
{
    let mut n = uint_size!();

    assert(n == uint_size!() ==> fits_n_bytes_signed!(v, n)) by (bit_vector);

    while n > 0
        invariant
            0 <= n <= uint_size!(),
            fits_n_bytes_signed!(v, n),
        decreases n
    {
        if !fits_n_bytes_signed!(v, n - 1) {
            assert(v == 0 && !fits_n_bytes_signed!(v, n - 1) ==> n == 1) by (bit_vector);
            return n;
        }
        n = n - 1;
    }

    assert(fits_n_bytes_signed!(v, 0) ==> v == 0) by (bit_vector);

    return 1;
}

impl PolyfillClone for UInt {
    fn clone(&self) -> Self {
        *self
    }
}

impl PolyfillClone for Int {
    fn clone(&self) -> Self {
        *self
    }
}

}
