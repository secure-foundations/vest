use vstd::arithmetic::{
    div_mod::{
        lemma_div_decreases, lemma_div_non_zero, lemma_fundamental_div_mod,
        lemma_fundamental_div_mod_converse, lemma_mod_bound,
    },
    power::{lemma_pow0, lemma_pow1, lemma_pow_adds, lemma_pow_strictly_increases_converse, pow},
};
use vstd::prelude::*;

verus! {

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
