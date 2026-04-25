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

/// Unsigned big-endian base-256 decoding into `usize`.
pub open spec fn usize_from_be_bytes_total(bytes: Seq<u8>) -> usize
    recommends
        bytes.len() <= size_of_usize(),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        0
    } else {
        (usize_from_be_bytes_total(bytes.drop_last()) << 8) | bytes.last() as usize
    }
}

/// Unsigned big-endian base-256 encoding from `usize`.
pub open spec fn usize_to_be_bytes(v: usize) -> Seq<u8>
    decreases v as nat,
    via usize_to_be_bytes_decreases
{
    if v < 256 {
        seq![v as u8]
    } else {
        usize_to_be_bytes(v >> 8).push((v & 0xff) as u8)
    }
}

#[via_fn]
proof fn usize_to_be_bytes_decreases(v: usize) {
    if v >= 256 {
        lemma_usize_shr8_is_div256(v);
        lemma_div_decreases(v as int, 256);
    }
}

/// Checked decoding wrapper for [`len_from_be_bytes_total`].
pub open spec fn usize_from_be_bytes(bytes: Seq<u8>) -> Option<usize> {
    if bytes.len() <= size_of_usize() {
        Some(usize_from_be_bytes_total(bytes))
    } else {
        None
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

pub proof fn lemma_len_to_be_bytes_equiv_nat(v: usize)
    ensures
        usize_to_be_bytes(v) == nat_to_be_bytes(v as nat),
    decreases v as nat,
{
    if v < 256usize {
    } else {
        let q = v >> 8usize;
        let r = (v & 0xffusize) as u8;
        lemma_usize_shr8_is_div256(v);
        lemma_usize_low8_is_mod256(v);
        lemma_len_to_be_bytes_equiv_nat(q);
        assert(v as nat >= 256);

        calc! {
            (==)
            usize_to_be_bytes(v); {}
            usize_to_be_bytes(q).push(r); {}
            nat_to_be_bytes(q as nat).push(r); {}
            nat_to_be_bytes((v as nat / 256) as nat).push((v as nat % 256) as u8); {}
            nat_to_be_bytes(v as nat);
        }
    }
}

pub proof fn lemma_len_from_be_bytes_total_equiv_nat(bytes: Seq<u8>)
    requires
        bytes.len() <= size_of_usize(),
    ensures
        usize_from_be_bytes_total(bytes) as nat == nat_from_be_bytes(bytes),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
    } else {
        let prefix = bytes.drop_last();
        let last = bytes.last();
        let prefix_v = usize_from_be_bytes_total(prefix);
        lemma_len_from_be_bytes_total_equiv_nat(prefix);
        lemma_nat_from_be_bytes_fits_shr8(bytes);
        if usize::BITS == 32 {
            lemma_usize32_shl8_or_is_base256(prefix_v, last);
        } else {
            lemma_usize64_shl8_or_is_base256(prefix_v, last);
        }
    }
}

pub proof fn lemma_len_from_be_bytes_equiv_nat(bytes: Seq<u8>)
    ensures
        usize_from_be_bytes(bytes) matches Some(v) ==> v == nat_from_be_bytes(bytes),
{
    if bytes.len() <= size_of_usize() {
        lemma_len_from_be_bytes_total_equiv_nat(bytes);
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

} // verus!
