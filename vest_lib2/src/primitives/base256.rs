use vstd::arithmetic::{div_mod::*, power::*, power2::*};
use vstd::bits::*;
use vstd::{calc, prelude::*};

verus! {

const USIZE_MODULUS_32: u64 = 0x100000000;

const USIZE_MODULUS_64: u128 = 0x10000000000000000u128;

/// Unsigned big-endian base-256 decoding.
pub open spec fn nat_from_be_bytes(bytes: Seq<u8>) -> nat
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        0
    } else {
        nat_from_be_bytes(bytes.drop_last()) * 256 + bytes.last() as nat
    }
}

/// Unsigned big-endian base-256 encoding.
pub open spec fn nat_to_be_bytes(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 256 {
        seq![n as u8]
    } else {
        nat_to_be_bytes((n / 256) as nat).push((n % 256) as u8)
    }
}

/// Number of bytes in `usize`.
pub open spec fn size_of_usize() -> nat {
    if usize::BITS == 32 {
        4
    } else {
        8
    }
}

proof fn lemma_usize_shr8_is_div256(v: usize)
    ensures
        (v >> 8usize) as nat == v as nat / 256,
{
    lemma_usize_shr_is_div(v, 8usize);
    assert(pow2(8) == 256) by (compute_only);
}

proof fn lemma_usize_low8_is_mod256(v: usize)
    ensures
        (v & 0xffusize) as nat == v as nat % 256,
{
    lemma_usize_low_bits_mask_is_mod(v, 8);
    assert(pow2(8) == 256) by (compute_only);
}

proof fn lemma_nat_from_be_bytes_fits_shr8(bytes: Seq<u8>)
    requires
        bytes.len() <= size_of_usize(),
    ensures
        usize::BITS == 32 ==> nat_from_be_bytes(bytes) < USIZE_MODULUS_32 as nat,
        usize::BITS == 64 ==> nat_from_be_bytes(bytes) < USIZE_MODULUS_64 as nat,
{
    lemma_from_be_bytes_upper_bound(bytes);
    assert(usize::BITS == 32 || usize::BITS == 64);
    if usize::BITS == 32 {
        assert(size_of_usize() == 4);
        reveal_with_fuel(pow, 5);
    } else {
        assert(usize::BITS == 64);
        assert(size_of_usize() == 8);
        reveal_with_fuel(pow, 9);
    }
}

proof fn lemma_usize32_shl8_or_is_base256(v: usize, b: u8)
    by (bit_vector)
    requires
        usize::BITS == 32,
    ensures
        (((v << 8usize) | b as usize) as nat) == (v as nat * 256 + b as nat) % (
        USIZE_MODULUS_32 as nat),
{
}

proof fn lemma_usize64_shl8_or_is_base256(v: usize, b: u8)
    by (bit_vector)
    requires
        usize::BITS == 64,
    ensures
        (((v << 8usize) | b as usize) as nat) == (v as nat * 256 + b as nat) % (
        USIZE_MODULUS_64 as nat),
{
}

pub proof fn lemma_nat_from_be_bytes_fits_usize(bytes: Seq<u8>)
    requires
        bytes.len() <= size_of_usize(),
    ensures
        nat_from_be_bytes(bytes) <= usize::MAX,
{
    // nat_from_be_bytes(bytes) < pow(256, bytes.len()) <= pow(256, size_of_usize())
    // For 32-bit: pow(256, 4) = 2^32 = usize::MAX + 1, so < pow(256,4) means <= usize::MAX.
    // For 64-bit: pow(256, 8) = 2^64 = usize::MAX + 1, same argument.
    lemma_from_be_bytes_upper_bound(bytes);
    if usize::BITS == 32 {
        reveal_with_fuel(pow, 5);  // unfolds pow(256, 0..4)
    } else {
        reveal_with_fuel(pow, 9);  // unfolds pow(256, 0..8)
    }
}

pub proof fn lemma_from_be_bytes_push(bytes: Seq<u8>, b: u8)
    ensures
        nat_from_be_bytes(bytes.push(b)) == nat_from_be_bytes(bytes) * 256 + b as nat,
{
    assert(bytes.push(b).drop_last() == bytes);
}

pub proof fn lemma_from_be_bytes_singleton(b: u8)
    ensures
        nat_from_be_bytes(seq![b]) == b as nat,
{
    lemma_from_be_bytes_push(seq![], b);
}

pub proof fn lemma_pow256_succ(exp: nat)
    ensures
        pow(256, exp + 1) == pow(256, exp) * 256,
{
    lemma_pow_adds(256, exp, 1);
    lemma_pow1(256);
}

pub proof fn lemma_from_be_bytes_upper_bound(bytes: Seq<u8>)
    ensures
        nat_from_be_bytes(bytes) < pow(256, bytes.len()),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        lemma_pow0(256);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_be_bytes_upper_bound(prefix);
        lemma_pow256_succ(prefix.len());
    }
}

pub proof fn lemma_from_be_bytes_lower_bound(bytes: Seq<u8>)
    requires
        bytes.len() > 0,
        bytes[0] != 0,
    ensures
        pow(256, (bytes.len() - 1) as nat) <= nat_from_be_bytes(bytes),
    decreases bytes.len(),
{
    if bytes.len() == 1 {
        lemma_pow0(256);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_be_bytes_lower_bound(prefix);
        lemma_pow256_succ((prefix.len() - 1) as nat);
    }
}

pub proof fn lemma_to_be_bytes_props(n: nat)
    ensures
        nat_to_be_bytes(n).len() > 0,
        n > 0 ==> nat_to_be_bytes(n)[0] != 0,
        n > 0 ==> pow(256, (nat_to_be_bytes(n).len() - 1) as nat) <= n,
    decreases n,
{
    if n < 256 {
        lemma_pow0(256);
    } else {
        let q = (n / 256) as nat;
        lemma_to_be_bytes_props(q);
        lemma_pow256_succ((nat_to_be_bytes(q).len() - 1) as nat);
    }
}

pub proof fn lemma_to_be_bytes_len_bound(n: nat, max_len: nat)
    requires
        0 < max_len,
        n < pow(256, max_len),
    ensures
        nat_to_be_bytes(n).len() <= max_len,
{
    if n == 0 {
    } else {
        lemma_to_be_bytes_props(n);
        lemma_pow_strictly_increases_converse(256, (nat_to_be_bytes(n).len() - 1) as nat, max_len);
    }
}

pub proof fn lemma_usize_to_be_bytes_len_bound(n: usize)
    ensures
        usize::BITS == 32 ==> nat_to_be_bytes(n as nat).len() <= 4,
        usize::BITS == 64 ==> nat_to_be_bytes(n as nat).len() <= 8,
{
    if usize::BITS == 32 {
        reveal_with_fuel(pow, 5);
        lemma_to_be_bytes_len_bound(n as nat, 4);
    } else {
        reveal_with_fuel(pow, 9);
        lemma_to_be_bytes_len_bound(n as nat, 8);
    }
}

pub proof fn lemma_to_from_be_bytes_roundtrip(n: nat)
    ensures
        nat_from_be_bytes(nat_to_be_bytes(n)) == n,
    decreases n,
{
    if n < 256 {
        lemma_from_be_bytes_singleton(n as u8);
    } else {
        let q = (n / 256) as nat;
        let r = (n % 256) as nat;
        lemma_to_from_be_bytes_roundtrip(q);
        lemma_from_be_bytes_push(nat_to_be_bytes(q), r as u8);
    }
}

pub proof fn lemma_from_to_be_bytes_roundtrip(bytes: Seq<u8>)
    requires
        bytes.len() > 0,
        bytes.len() > 1 ==> bytes[0] != 0,
    ensures
        nat_to_be_bytes(nat_from_be_bytes(bytes)) == bytes,
    decreases bytes.len(),
{
    if bytes.len() == 1 {
        lemma_from_be_bytes_singleton(bytes[0]);
        assert(bytes == seq![bytes[0]]);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_to_be_bytes_roundtrip(prefix);
    }
}

pub proof fn lemma_from_be_bytes_prepend(bytes: Seq<u8>, b: u8)
    ensures
        nat_from_be_bytes(seq![b] + bytes) == b as nat * pow(256, bytes.len()) + nat_from_be_bytes(
            bytes,
        ),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        lemma_from_be_bytes_singleton(b);
        lemma_pow0(256);
    } else {
        let prefix = bytes.drop_last();
        let last = bytes.last();
        lemma_from_be_bytes_prepend(prefix, b);
        lemma_from_be_bytes_push(prefix, last);
        lemma_from_be_bytes_push(seq![b] + prefix, last);
        lemma_pow256_succ(prefix.len());
        assert(seq![b] + bytes == (seq![b] + prefix).push(last));
        assert((b as nat * pow(256, prefix.len()) + nat_from_be_bytes(prefix)) * 256 + last as nat
            == b as nat * (pow(256, prefix.len()) * 256) + (nat_from_be_bytes(prefix) * 256
            + last as nat)) by (nonlinear_arith);
    }
}

/// Executable loop-based big-endian base-256 decoding into `usize`.
/// Verified against [`nat_from_be_bytes`].
pub fn usize_from_be_bytes_exec(bytes: &[u8]) -> (result: usize)
    requires
        bytes.len() <= size_of_usize(),
    ensures
        result as nat == nat_from_be_bytes(bytes.deep_view()),
{
    let n = bytes.len();
    let mut acc: usize = 0;
    for i in 0..n
        invariant
            n == bytes.len(),
            n <= size_of_usize(),
            acc == nat_from_be_bytes(bytes@.take(i as int)),
    {
        let b = bytes[i];
        proof {
            let prefix = bytes@.take(i as int);
            let current = prefix.push(b);
            assert(bytes@.take(i as int + 1) == current);
            assert(current.drop_last() == prefix);
            lemma_nat_from_be_bytes_fits_shr8(current);
            if usize::BITS == 32 {
                lemma_usize32_shl8_or_is_base256(acc, b);
            } else {
                lemma_usize64_shl8_or_is_base256(acc, b);
            }
        }
        acc = (acc << 8usize) | (b as usize);
    }
    assert(bytes@.take(n as int) == bytes.deep_view());
    acc
}

/// Executable big-endian base-256 encoding from `usize`.
/// Verified against [`nat_to_be_bytes`].
///
/// TODO: Optimize this function?
pub fn usize_to_be_bytes_exec(v: usize) -> (buf: Vec<u8>)
    ensures
        buf@ == nat_to_be_bytes(v as nat),
    decreases v,
{
    if v < 256 {
        vec![v as u8]
    } else {
        proof {
            lemma_usize_shr8_is_div256(v);
            lemma_usize_low8_is_mod256(v);
        }
        let mut buf = usize_to_be_bytes_exec(v >> 8);
        buf.push((v & 0xff) as u8);
        buf
    }
}

/// Executable loop-based byte-length computation.
/// verified against [`nat_to_be_bytes`].
pub fn usize_to_be_bytes_len(v: usize) -> (len: usize)
    ensures
        len == nat_to_be_bytes(v as nat).len(),
{
    let mut cur = v;
    let mut len: usize = 1;
    while cur >= 256
        invariant
            len + nat_to_be_bytes(cur as nat).len() == nat_to_be_bytes(v as nat).len() + 1,
        decreases cur,
    {
        proof {
            lemma_usize_shr8_is_div256(cur);
            lemma_usize_to_be_bytes_len_bound(v);
        }
        cur >>= 8;
        len += 1;
    }
    len
}

#[verifier::external_body]
fn bytes_needed(n: usize) -> (need: usize)
    ensures
        need == nat_to_be_bytes(n as nat).len(),
{
    let active_bits = match usize::BITS {
        total @ 32 => total - (n as u32).leading_zeros(),
        total @ 64 => total - (n as u64).leading_zeros(),
        _ => 0,  // unreachable
    };

    if active_bits == 0 {
        1
    } else {
        ((active_bits + 7) / 8) as usize
    }
}

// Executable loop-based big-endian base-256 encoding from `usize`.
// Verified against [`usize_to_be_bytes`].
// pub fn usize_to_be_bytes_exec(mut v: usize, obuf: &mut Vec<u8>)
//     ensures
//         final(obuf)@ == old(obuf)@ + usize_to_be_bytes(v),
//  {
// }
} // verus!
