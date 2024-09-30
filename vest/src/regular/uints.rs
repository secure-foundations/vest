use crate::properties::*;
use std::mem::size_of;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::slice::*;

verus! {

global size_of u8 == 1;

global size_of u16 == 2;

global size_of u32 == 4;

global size_of u64 == 8;

global size_of usize == 8;

/// Proof that the size of the unsigned integer types is as expected.
pub broadcast proof fn size_of_facts()
    ensures
        #[trigger] size_of::<u8>() == 1,
        #[trigger] size_of::<u16>() == 2,
        #[trigger] size_of::<u32>() == 4,
        #[trigger] size_of::<u64>() == 8,
        #[trigger] size_of::<usize>() == 8,
{
}

/// Combinator for parsing and serializing unsigned u8 integers.
///
/// > **Note**: Currently, little-endian byte order is used for serialization and parsing.
pub struct U8;

impl View for U8 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u16 integers.
///
/// > **Note**: Currently, little-endian byte order is used for serialization and parsing.
pub struct U16;

impl View for U16 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u32 integers.
///
/// > **Note**: Currently, little-endian byte order is used for serialization and parsing.
pub struct U32;

impl View for U32 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u64 integers.
///
/// > **Note**: Currently, little-endian byte order is used for serialization and parsing.
pub struct U64;

impl View for U64 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

macro_rules! impl_combinator_for_int_type {
    ($combinator:ty, $int_type:ty) => {
        ::builtin_macros::verus! {
            impl SpecCombinator for $combinator {
                type SpecResult = $int_type;

                open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, $int_type), ()> {
                    if s.len() >= size_of::<$int_type>() {
                        Ok((size_of::<$int_type>() as usize, <$int_type>::spec_from_le_bytes(s)))
                    } else {
                        Err(())
                    }
                }

                proof fn spec_parse_wf(&self, s: Seq<u8>) {
                }

                open spec fn spec_serialize(&self, v: $int_type) -> Result<Seq<u8>, ()> {
                    Ok(<$int_type>::spec_to_le_bytes(&v))
                }
            }

            impl SecureSpecCombinator for $combinator {
                open spec fn is_prefix_secure() -> bool {
                    true
                }

                proof fn theorem_serialize_parse_roundtrip(&self, v: $int_type) {
                    $int_type::lemma_spec_to_from_le_bytes(&v);
                }

                proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
                    let n = size_of::<$int_type>();
                    if buf.len() >= n {
                        let fst = buf.subrange(0, n as int);
                        let snd = buf.subrange(n as int, buf.len() as int);
                        $int_type::lemma_spec_from_to_le_bytes(fst);
                        self.lemma_prefix_secure(fst, snd);
                        assert(fst.add(snd) == buf);
                    }
                }

                proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
                    $int_type::lemma_spec_from_le_bytes_no_lookahead(s1, s2);
                }
            }

            impl Combinator for $combinator {
                type Result<'a> = $int_type;

                type Owned = $int_type;

                open spec fn spec_length(&self) -> Option<usize> {
                    Some(size_of::<$int_type>())
                }

                fn length(&self) -> Option<usize> {
                    Some(size_of::<$int_type>())
                }

                fn parse(&self, s: &[u8]) -> (res: Result<(usize, $int_type), ParseError>) {
                    if s.len() >= size_of::<$int_type>() {
                        let s_ = slice_subrange(s, 0, size_of::<$int_type>());
                        let v = $int_type::ex_from_le_bytes(s_);
                        proof {
                            let s_ = s_@;
                            let s__ = s@.subrange(size_of::<$int_type>() as int, s@.len() as int);
                            $int_type::lemma_spec_from_le_bytes_no_lookahead(s_, s__);
                            assert(s_.add(s__) == s@);
                            assert($int_type::spec_from_le_bytes(s@) == v);
                            v.reflex();
                        }
                        Ok((size_of::<$int_type>(), v))
                    } else {
                        Err(ParseError::UnexpectedEndOfInput)
                    }
                }

                fn serialize(&self, v: $int_type, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
                    if pos <= data.len() {
                        if size_of::<$int_type>() <= data.len() - pos {
                            $int_type::ex_to_le_bytes(&v, data, pos);
                            proof {
                                v.reflex();
                                assert(data@.subrange(pos as int, pos + size_of::<$int_type>() as int)
                                    == self.spec_serialize(v@).unwrap());
                            }
                            Ok(size_of::<$int_type>())
                        } else {
                            Err(SerializeError::InsufficientBuffer)
                        }
                    } else {
                        Err(SerializeError::InsufficientBuffer)
                    }
                }
            }
        } // verus!
    };
}

impl_combinator_for_int_type!(U8, u8);

impl_combinator_for_int_type!(U16, u16);

impl_combinator_for_int_type!(U32, u32);

impl_combinator_for_int_type!(U64, u64);

// helpers
/// A trait for converting an integer type to and from a sequence of bytes.
pub trait FromToBytes where Self: ViewReflex + std::marker::Sized + Copy {
    /// Spec version of [`Self::ex_from_le_bytes`]
    spec fn spec_from_le_bytes(s: Seq<u8>) -> Self;

    /// Spec version of [`Self::ex_to_le_bytes`]
    spec fn spec_to_le_bytes(&self) -> Seq<u8>;

    // spec fn spec_from_be_bytes(s: Seq<u8>) -> Self;
    // spec fn spec_to_be_bytes(&self) -> Seq<u8>;
    /// Lemma that asserts that converting an integer to bytes and back results in the original
    proof fn lemma_spec_to_from_le_bytes(&self)
    // requires
    //     is_sized::<Self>(),

        ensures
            self.spec_to_le_bytes().len() == size_of::<Self>(),
            Self::spec_from_le_bytes(self.spec_to_le_bytes()) == *self,
    ;

    /// Lemma that asserts that converting a sequence of bytes to an integer and back results in
    /// the original sequence
    proof fn lemma_spec_from_to_le_bytes(s: Seq<u8>)
    // requires
    //     is_sized::<Self>(),

        ensures
            s.len() == size_of::<Self>() ==> Self::spec_to_le_bytes(&Self::spec_from_le_bytes(s))
                == s,
    ;

    /// Helper lemma for proving [`SecureSpecCombinator::lemma_prefix_secure`]
    proof fn lemma_spec_from_le_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>)
        requires
            s1.len() + s2.len() <= usize::MAX,
        ensures
            s1.len() >= size_of::<Self>() ==> Self::spec_from_le_bytes(s1)
                == Self::spec_from_le_bytes(s1.add(s2)),
    ;

    /// Converts a sequence of bytes to an integer in little-endian byte order.
    fn ex_from_le_bytes(s: &[u8]) -> (x: Self)
        requires
            s@.len() == size_of::<Self>(),
        ensures
            x == Self::spec_from_le_bytes(s@),
    ;

    /// Converts an integer to a sequence of bytes in little-endian byte order.
    fn ex_to_le_bytes(&self, s: &mut Vec<u8>, pos: usize)
        requires
            old(s)@.len() - pos >= size_of::<Self>(),
        ensures
            old(s)@.len() == s@.len(),
            self.spec_to_le_bytes().len() == size_of::<Self>(),
            s@ == seq_splice(old(s)@, pos, self.spec_to_le_bytes()),
    ;

    /// Compares two integers for equality.
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res == (self@ == other@),
    ;
}

impl FromToBytes for u8 {
    open spec fn spec_from_le_bytes(s: Seq<u8>) -> Self {
        s[0]
    }

    open spec fn spec_to_le_bytes(&self) -> Seq<u8> {
        seq![*self]
    }

    // open spec fn spec_from_be_bytes(s: Seq<u8>) -> Self { s[0] }
    // open spec fn spec_to_be_bytes(&self) -> Seq<u8> { seq![*self] }
    proof fn lemma_spec_to_from_le_bytes(&self) {
    }

    proof fn lemma_spec_from_to_le_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u8>() {
            assert(Self::spec_to_le_bytes(&Self::spec_from_le_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_le_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    fn ex_from_le_bytes(s: &[u8]) -> (x: u8) {
        *slice_index_get(s, 0)
    }

    fn ex_to_le_bytes(&self, s: &mut Vec<u8>, pos: usize) {
        let ghost old = s@;
        s.set(pos, *self);
        proof {
            assert(s@ == seq_splice(old, pos, self.spec_to_le_bytes()));
        }
    }

    fn eq(&self, other: &u8) -> (res: bool) {
        *self == *other
    }
}

impl FromToBytes for u16 {
    open spec fn spec_from_le_bytes(s: Seq<u8>) -> Self {
        (s[0] as u16) | (s[1] as u16) << 8
    }

    open spec fn spec_to_le_bytes(&self) -> Seq<u8> {
        seq![(self & 0xff) as u8, ((self >> 8) & 0xff) as u8]
    }

    // open spec fn spec_from_be_bytes(s: Seq<u8>) -> Self {  }
    // open spec fn spec_to_be_bytes(&self) -> Seq<u8> {  }
    proof fn lemma_spec_to_from_le_bytes(&self) {
        let s = self.spec_to_le_bytes();
        assert({
            &&& self & 0xff < 256
            &&& (self >> 8) & 0xff < 256
        }) by (bit_vector);
        assert(self == ((self & 0xff) | ((self >> 8) & 0xff) << 8)) by (bit_vector);
    }

    proof fn lemma_spec_from_to_le_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u16>() {
            let x = Self::spec_from_le_bytes(s);
            let s0 = s[0] as u16;
            let s1 = s[1] as u16;
            assert(((x == s0 | s1 << 8) && (s0 < 256) && (s1 < 256)) ==> s0 == (x & 0xff) && s1 == (
            (x >> 8) & 0xff)) by (bit_vector);
            assert_seqs_equal!(Self::spec_to_le_bytes(&Self::spec_from_le_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_le_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    #[verifier::external_body]
    fn ex_from_le_bytes(s: &[u8]) -> (x: u16) {
        use core::convert::TryInto;
        u16::from_le_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_le_bytes(&self, s: &mut Vec<u8>, pos: usize) {
        let bytes = self.to_le_bytes();
        s[pos..pos + 2].copy_from_slice(&bytes);
    }

    fn eq(&self, other: &u16) -> (res: bool) {
        *self == *other
    }
}

impl FromToBytes for u32 {
    open spec fn spec_from_le_bytes(s: Seq<u8>) -> Self {
        (s[0] as u32) | (s[1] as u32) << 8 | (s[2] as u32) << 16 | (s[3] as u32) << 24
    }

    open spec fn spec_to_le_bytes(&self) -> Seq<u8> {
        seq![
            (self & 0xff) as u8,
            ((self >> 8) & 0xff) as u8,
            ((self >> 16) & 0xff) as u8,
            ((self >> 24) & 0xff) as u8,
        ]
    }

    // open spec fn spec_from_be_bytes(s: Seq<u8>) -> Self {  }
    // open spec fn spec_to_be_bytes(&self) -> Seq<u8> {  }
    proof fn lemma_spec_to_from_le_bytes(&self) {
        let s = self.spec_to_le_bytes();
        assert({
            &&& self & 0xff < 256
            &&& (self >> 8) & 0xff < 256
            &&& (self >> 16) & 0xff < 256
            &&& (self >> 24) & 0xff < 256
        }) by (bit_vector);
        assert(self == ((self & 0xff) | ((self >> 8) & 0xff) << 8 | ((self >> 16) & 0xff) << 16 | ((
        self >> 24) & 0xff) << 24)) by (bit_vector);
    }

    proof fn lemma_spec_from_to_le_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u32>() {
            let x = Self::spec_from_le_bytes(s);
            let s0 = s[0] as u32;
            let s1 = s[1] as u32;
            let s2 = s[2] as u32;
            let s3 = s[3] as u32;
            assert(((x == s0 | s1 << 8 | s2 << 16 | s3 << 24) && (s0 < 256) && (s1 < 256) && (s2
                < 256) && (s3 < 256)) ==> s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff) && s2 == ((x
                >> 16) & 0xff) && s3 == ((x >> 24) & 0xff)) by (bit_vector);
            assert_seqs_equal!(Self::spec_to_le_bytes(&Self::spec_from_le_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_le_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    #[verifier::external_body]
    fn ex_from_le_bytes(s: &[u8]) -> (x: u32) {
        use core::convert::TryInto;
        u32::from_le_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_le_bytes(&self, s: &mut Vec<u8>, pos: usize) {
        let bytes = self.to_le_bytes();
        s[pos..pos + 4].copy_from_slice(&bytes);
    }

    fn eq(&self, other: &u32) -> (res: bool) {
        *self == *other
    }
}

impl FromToBytes for u64 {
    open spec fn spec_from_le_bytes(s: Seq<u8>) -> Self {
        (s[0] as u64) | (s[1] as u64) << 8 | (s[2] as u64) << 16 | (s[3] as u64) << 24 | (
        s[4] as u64) << 32 | (s[5] as u64) << 40 | (s[6] as u64) << 48 | (s[7] as u64) << 56
    }

    open spec fn spec_to_le_bytes(&self) -> Seq<u8> {
        seq![
            (self & 0xff) as u8,
            ((self >> 8) & 0xff) as u8,
            ((self >> 16) & 0xff) as u8,
            ((self >> 24) & 0xff) as u8,
            ((self >> 32) & 0xff) as u8,
            ((self >> 40) & 0xff) as u8,
            ((self >> 48) & 0xff) as u8,
            ((self >> 56) & 0xff) as u8,
        ]
    }

    // open spec fn spec_from_be_bytes(s: Seq<u8>) -> Self {  }
    // open spec fn spec_to_be_bytes(&self) -> Seq<u8> {  }
    proof fn lemma_spec_to_from_le_bytes(&self) {
        let s = self.spec_to_le_bytes();
        assert({
            &&& self & 0xff < 256
            &&& (self >> 8) & 0xff < 256
            &&& (self >> 16) & 0xff < 256
            &&& (self >> 24) & 0xff < 256
            &&& (self >> 32) & 0xff < 256
            &&& (self >> 40) & 0xff < 256
            &&& (self >> 48) & 0xff < 256
            &&& (self >> 56) & 0xff < 256
        }) by (bit_vector);
        assert(self == ((self & 0xff) | ((self >> 8) & 0xff) << 8 | ((self >> 16) & 0xff) << 16 | ((
        self >> 24) & 0xff) << 24 | ((self >> 32) & 0xff) << 32 | ((self >> 40) & 0xff) << 40 | ((
        self >> 48) & 0xff) << 48 | ((self >> 56) & 0xff) << 56)) by (bit_vector);
    }

    proof fn lemma_spec_from_to_le_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u64>() {
            let x = Self::spec_from_le_bytes(s);
            let s0 = s[0] as u64;
            let s1 = s[1] as u64;
            let s2 = s[2] as u64;
            let s3 = s[3] as u64;
            let s4 = s[4] as u64;
            let s5 = s[5] as u64;
            let s6 = s[6] as u64;
            let s7 = s[7] as u64;
            assert(((x == s0 | s1 << 8 | s2 << 16 | s3 << 24 | s4 << 32 | s5 << 40 | s6 << 48 | s7
                << 56) && (s0 < 256) && (s1 < 256) && (s2 < 256) && (s3 < 256) && (s4 < 256) && (s5
                < 256) && (s6 < 256) && (s7 < 256)) ==> s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff)
                && s2 == ((x >> 16) & 0xff) && s3 == ((x >> 24) & 0xff) && s4 == ((x >> 32) & 0xff)
                && s5 == ((x >> 40) & 0xff) && s6 == ((x >> 48) & 0xff) && s7 == ((x >> 56) & 0xff))
                by (bit_vector);
            assert_seqs_equal!(Self::spec_to_le_bytes(&Self::spec_from_le_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_le_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    #[verifier::external_body]
    fn ex_from_le_bytes(s: &[u8]) -> (x: u64) {
        use core::convert::TryInto;
        u64::from_le_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_le_bytes(&self, s: &mut Vec<u8>, pos: usize) {
        let bytes = self.to_le_bytes();
        s[pos..pos + 8].copy_from_slice(&bytes);
    }

    fn eq(&self, other: &u64) -> (res: bool) {
        *self == *other
    }
}

} // verus!
