use alloc::vec::Vec;

use crate::properties::*;
use core::mem::size_of;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::slice::*;

use super::bytes::Fixed;

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
pub struct U8;

impl View for U8 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u16 integers in little-endian byte order.
pub struct U16Le;

impl View for U16Le {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u32 integers in little-endian byte order.
pub struct U32Le;

impl View for U32Le {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u64 integers in little-endian byte order.
pub struct U64Le;

impl View for U64Le {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u16 integers in big-endian byte order.
pub struct U16Be;

impl View for U16Be {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u32 integers in big-endian byte order.
pub struct U32Be;

impl View for U32Be {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Combinator for parsing and serializing unsigned u64 integers in big-endian byte order.
pub struct U64Be;

impl View for U64Be {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

macro_rules! impl_combinator_for_le_uint_type {
    ($combinator:ty, $int_type:ty) => {
        ::vstd::prelude::verus! {
            impl SpecCombinator for $combinator {
                type Type = $int_type;

                open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, $int_type)> {
                    if s.len() >= size_of::<$int_type>() {
                        Some((size_of::<$int_type>() as int, <$int_type>::spec_from_le_bytes(s)))
                    } else {
                        None
                    }
                }

                open spec fn spec_serialize(&self, v: $int_type) -> Seq<u8> {
                    <$int_type>::spec_to_le_bytes(&v)
                }
            }

            impl SecureSpecCombinator for $combinator {
                open spec fn is_prefix_secure() -> bool {
                    true
                }

                open spec fn is_productive(&self) -> bool {
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

                proof fn lemma_parse_length(&self, s: Seq<u8>) {
                }

                proof fn lemma_parse_productive(&self, s: Seq<u8>) {
                }
            }

            impl<'x, I: VestPublicInput, O: VestPublicOutput<I>> Combinator<'x, I, O> for $combinator {
                type Type = $int_type;

                type SType = &'x $int_type;

                fn length(&self, _v: Self::SType) -> usize {
                    size_of::<$int_type>()
                }

                fn parse(&self, s: I) -> (res: Result<(usize, $int_type), ParseError>) {
                    if s.len() >= size_of::<$int_type>() {
                        let s_ = s.subrange(0, size_of::<$int_type>());
                        let v = $int_type::ex_from_le_bytes(s_.as_byte_slice());
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

                fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<usize, SerializeError>) {
                    if size_of::<$int_type>() <= data.len() - pos {
                        $int_type::ex_to_le_bytes(&v, data, pos);
                        proof {
                            v.reflex();
                            assert(data@.subrange(pos as int, pos + size_of::<$int_type>() as int)
                                == self.spec_serialize(v@));
                        }
                        Ok(size_of::<$int_type>())
                    } else {
                        Err(SerializeError::InsufficientBuffer)
                    }
                }
            }
        } // verus!
    };
}

macro_rules! impl_combinator_for_be_uint_type {
    ($combinator:ty, $int_type:ty) => {
        ::vstd::prelude::verus! {
            impl SpecCombinator for $combinator {
                type Type = $int_type;

                open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, $int_type)> {
                    if s.len() >= size_of::<$int_type>() {
                        Some((size_of::<$int_type>() as int, <$int_type>::spec_from_be_bytes(s)))
                    } else {
                        None
                    }
                }

                open spec fn spec_serialize(&self, v: $int_type) -> Seq<u8> {
                    <$int_type>::spec_to_be_bytes(&v)
                }
            }

            impl SecureSpecCombinator for $combinator {
                open spec fn is_prefix_secure() -> bool {
                    true
                }

                open spec fn is_productive(&self) -> bool {
                    true
                }

                proof fn theorem_serialize_parse_roundtrip(&self, v: $int_type) {
                    $int_type::lemma_spec_to_from_be_bytes(&v);
                }

                proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
                    let n = size_of::<$int_type>();
                    if buf.len() >= n {
                        let fst = buf.subrange(0, n as int);
                        let snd = buf.subrange(n as int, buf.len() as int);
                        $int_type::lemma_spec_from_to_be_bytes(fst);
                        self.lemma_prefix_secure(fst, snd);
                        assert(fst.add(snd) == buf);
                    }
                }

                proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
                    $int_type::lemma_spec_from_be_bytes_no_lookahead(s1, s2);
                }

                proof fn lemma_parse_length(&self, s: Seq<u8>) {
                }

                proof fn lemma_parse_productive(&self, s: Seq<u8>) {
                }
            }

            impl<'x, I: VestPublicInput, O: VestPublicOutput<I>> Combinator<'x, I, O> for $combinator {
                type Type = $int_type;

                type SType = &'x $int_type;

                fn length(&self, _v: Self::SType) -> usize {
                    size_of::<$int_type>()
                }

                fn parse(&self, s: I) -> (res: Result<(usize, $int_type), ParseError>) {
                    if s.len() >= size_of::<$int_type>() {
                        let s_ = s.subrange(0, size_of::<$int_type>());
                        let v = $int_type::ex_from_be_bytes(s_.as_byte_slice());
                        proof {
                            let s_ = s_@;
                            let s__ = s@.subrange(size_of::<$int_type>() as int, s@.len() as int);
                            $int_type::lemma_spec_from_be_bytes_no_lookahead(s_, s__);
                            assert(s_.add(s__) == s@);
                            assert($int_type::spec_from_be_bytes(s@) == v);
                            v.reflex();
                        }
                        Ok((size_of::<$int_type>(), v))
                    } else {
                        Err(ParseError::UnexpectedEndOfInput)
                    }
                }

                fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<usize, SerializeError>) {
                    if size_of::<$int_type>() <= data.len() - pos {
                        $int_type::ex_to_be_bytes(&v, data, pos);
                        proof {
                            v.reflex();
                            assert(data@.subrange(pos as int, pos + size_of::<$int_type>() as int)
                                == self.spec_serialize(v@));
                        }
                        Ok(size_of::<$int_type>())
                    } else {
                        Err(SerializeError::InsufficientBuffer)
                    }
                }
            }
        } // verus!
    };
}

impl_combinator_for_le_uint_type!(U8, u8);

impl_combinator_for_le_uint_type!(U16Le, u16);

impl_combinator_for_le_uint_type!(U32Le, u32);

impl_combinator_for_le_uint_type!(U64Le, u64);

impl_combinator_for_be_uint_type!(U16Be, u16);

impl_combinator_for_be_uint_type!(U32Be, u32);

impl_combinator_for_be_uint_type!(U64Be, u64);

// helpers
/// A trait for converting an integer type to and from a sequence of bytes.
pub trait FromToBytes where Self: ViewReflex + core::marker::Sized + Copy {
    /// Spec version of [`Self::ex_from_le_bytes`]
    spec fn spec_from_le_bytes(s: Seq<u8>) -> Self;

    /// Spec version of [`Self::ex_to_le_bytes`]
    spec fn spec_to_le_bytes(&self) -> Seq<u8>;

    /// Spec version of [`Self::ex_from_be_bytes`]
    spec fn spec_from_be_bytes(s: Seq<u8>) -> Self;

    /// Spec version of [`Self::ex_to_be_bytes`]
    spec fn spec_to_be_bytes(&self) -> Seq<u8>;

    /// Lemma that asserts that converting an integer in little-endian byte order to bytes and back
    /// results in the original integer
    proof fn lemma_spec_to_from_le_bytes(&self)
    // requires
    //     is_sized::<Self>(),

        ensures
            self.spec_to_le_bytes().len() == size_of::<Self>(),
            Self::spec_from_le_bytes(self.spec_to_le_bytes()) == *self,
    ;

    /// Lemma that asserts that converting a sequence of bytes to an integer in little-endian byte
    /// order and back results in the original sequence
    proof fn lemma_spec_from_to_le_bytes(s: Seq<u8>)
    // requires
    //     is_sized::<Self>(),

        ensures
            s.len() == size_of::<Self>() ==> Self::spec_to_le_bytes(&Self::spec_from_le_bytes(s))
                == s,
    ;

    /// Helper lemma for proving [`SecureSpecCombinator::lemma_prefix_secure`]
    proof fn lemma_spec_from_le_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>)
        ensures
            s1.len() >= size_of::<Self>() ==> Self::spec_from_le_bytes(s1)
                == Self::spec_from_le_bytes(s1.add(s2)),
    ;

    /// Lemma that asserts that converting an integer in big-endian byte order to bytes and back
    /// results in the original integer
    proof fn lemma_spec_to_from_be_bytes(&self)
        ensures
            self.spec_to_be_bytes().len() == size_of::<Self>(),
            Self::spec_from_be_bytes(self.spec_to_be_bytes()) == *self,
    ;

    /// Lemma that asserts that converting a sequence of bytes to an integer in big-endian byte
    /// order and back results in the original sequence
    proof fn lemma_spec_from_to_be_bytes(s: Seq<u8>)
        ensures
            s.len() == size_of::<Self>() ==> Self::spec_to_be_bytes(&Self::spec_from_be_bytes(s))
                == s,
    ;

    /// Helper lemma for proving [`SecureSpecCombinator::lemma_prefix_secure`]
    proof fn lemma_spec_from_be_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>)
        ensures
            s1.len() >= size_of::<Self>() ==> Self::spec_from_be_bytes(s1)
                == Self::spec_from_be_bytes(s1.add(s2)),
    ;

    /// Converts a sequence of bytes to an integer in little-endian byte order.
    fn ex_from_le_bytes(s: &[u8]) -> (x: Self)
        requires
            s@.len() == size_of::<Self>(),
        ensures
            x == Self::spec_from_le_bytes(s@),
    ;

    /// Converts an integer to a sequence of bytes in little-endian byte order.
    fn ex_to_le_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,

        requires
            old(s)@.len() - pos >= size_of::<Self>(),
        ensures
            old(s)@.len() == s@.len(),
            self.spec_to_le_bytes().len() == size_of::<Self>(),
            s@ == seq_splice(old(s)@, pos, self.spec_to_le_bytes()),
    ;

    /// Converts a sequence of bytes to an integer in big-endian byte order.
    fn ex_from_be_bytes(s: &[u8]) -> (x: Self)
        requires
            s@.len() == size_of::<Self>(),
        ensures
            x == Self::spec_from_be_bytes(s@),
    ;

    /// Converts an integer to a sequence of bytes in big-endian byte order.
    fn ex_to_be_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,

        requires
            old(s)@.len() - pos >= size_of::<Self>(),
        ensures
            old(s)@.len() == s@.len(),
            self.spec_to_be_bytes().len() == size_of::<Self>(),
            s@ == seq_splice(old(s)@, pos, self.spec_to_be_bytes()),
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

    open spec fn spec_from_be_bytes(s: Seq<u8>) -> Self {
        s[0]
    }

    open spec fn spec_to_be_bytes(&self) -> Seq<u8> {
        seq![*self]
    }

    proof fn lemma_spec_to_from_le_bytes(&self) {
    }

    proof fn lemma_spec_from_to_le_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u8>() {
            assert(Self::spec_to_le_bytes(&Self::spec_from_le_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_le_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn lemma_spec_to_from_be_bytes(&self) {
    }

    proof fn lemma_spec_from_to_be_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u8>() {
            assert(Self::spec_to_be_bytes(&Self::spec_from_be_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_be_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    fn ex_from_le_bytes(s: &[u8]) -> (x: u8) {
        *slice_index_get(s, 0)
    }

    fn ex_to_le_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
     {
        let ghost old = s@;
        s.set_byte(pos, *self);
        proof {
            assert(s@ == seq_splice(old, pos, self.spec_to_le_bytes()));
        }
    }

    fn ex_from_be_bytes(s: &[u8]) -> (x: u8) {
        *slice_index_get(s, 0)
    }

    fn ex_to_be_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
     {
        let ghost old = s@;
        s.set_byte(pos, *self);
        proof {
            assert(s@ == seq_splice(old, pos, self.spec_to_be_bytes()));
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

    open spec fn spec_from_be_bytes(s: Seq<u8>) -> Self {
        (s[0] as u16) << 8 | (s[1] as u16)
    }

    open spec fn spec_to_be_bytes(&self) -> Seq<u8> {
        seq![((self >> 8) & 0xff) as u8, (self & 0xff) as u8]
    }

    proof fn lemma_spec_to_from_le_bytes(&self) {
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

    proof fn lemma_spec_to_from_be_bytes(&self) {
        assert({
            &&& self & 0xff < 256
            &&& (self >> 8) & 0xff < 256
        }) by (bit_vector);
        assert(self == (((self >> 8) & 0xff) << 8 | (self & 0xff))) by (bit_vector);
    }

    proof fn lemma_spec_from_to_be_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u16>() {
            let x = Self::spec_from_be_bytes(s);
            let s0 = s[0] as u16;
            let s1 = s[1] as u16;
            assert(((x == s0 << 8 | s1) && (s0 < 256) && (s1 < 256)) ==> s0 == ((x >> 8) & 0xff)
                && s1 == (x & 0xff)) by (bit_vector);
            assert_seqs_equal!(Self::spec_to_be_bytes(&Self::spec_from_be_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_be_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    #[verifier::external_body]
    fn ex_from_le_bytes(s: &[u8]) -> (x: u16) {
        use core::convert::TryInto;
        u16::from_le_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_le_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
     {
        let bytes = self.to_le_bytes();
        // s[pos..pos + 2].copy_from_slice(&bytes);
        // s.set_byte(pos, bytes[0]);
        // s.set_byte(pos + 1, bytes[1]);
        s.set_byte_range(pos, &bytes.as_slice());
    }

    #[verifier::external_body]
    fn ex_from_be_bytes(s: &[u8]) -> (x: u16) {
        use core::convert::TryInto;
        u16::from_be_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_be_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
     {
        let bytes = self.to_be_bytes();
        // s[pos..pos + 2].copy_from_slice(&bytes);
        // s.set_byte(pos, bytes[0]);
        // s.set_byte(pos + 1, bytes[1]);
        s.set_byte_range(pos, &bytes.as_slice());
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

    open spec fn spec_from_be_bytes(s: Seq<u8>) -> Self {
        (s[0] as u32) << 24 | (s[1] as u32) << 16 | (s[2] as u32) << 8 | (s[3] as u32)
    }

    open spec fn spec_to_be_bytes(&self) -> Seq<u8> {
        seq![
            ((self >> 24) & 0xff) as u8,
            ((self >> 16) & 0xff) as u8,
            ((self >> 8) & 0xff) as u8,
            (self & 0xff) as u8,
        ]
    }

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

    proof fn lemma_spec_to_from_be_bytes(&self) {
        let s = self.spec_to_be_bytes();
        assert({
            &&& self & 0xff < 256
            &&& (self >> 8) & 0xff < 256
            &&& (self >> 16) & 0xff < 256
            &&& (self >> 24) & 0xff < 256
        }) by (bit_vector);
        assert(self == (((self >> 24) & 0xff) << 24 | ((self >> 16) & 0xff) << 16 | ((self >> 8)
            & 0xff) << 8 | (self & 0xff))) by (bit_vector);
    }

    proof fn lemma_spec_from_to_be_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u32>() {
            let x = Self::spec_from_be_bytes(s);
            let s0 = s[0] as u32;
            let s1 = s[1] as u32;
            let s2 = s[2] as u32;
            let s3 = s[3] as u32;
            assert(((x == s0 << 24 | s1 << 16 | s2 << 8 | s3) && (s0 < 256) && (s1 < 256) && (s2
                < 256) && (s3 < 256)) ==> s0 == ((x >> 24) & 0xff) && s1 == ((x >> 16) & 0xff) && s2
                == ((x >> 8) & 0xff) && s3 == (x & 0xff)) by (bit_vector);
            assert_seqs_equal!(Self::spec_to_be_bytes(&Self::spec_from_be_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_be_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    #[verifier::external_body]
    fn ex_from_le_bytes(s: &[u8]) -> (x: u32) {
        use core::convert::TryInto;
        u32::from_le_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_le_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
     {
        let bytes = self.to_le_bytes();
        // s[pos..pos + 4].copy_from_slice(&bytes);
        // s.set_byte(pos, bytes[0]);
        // s.set_byte(pos + 1, bytes[1]);
        // s.set_byte(pos + 2, bytes[2]);
        // s.set_byte(pos + 3, bytes[3]);
        s.set_byte_range(pos, &bytes.as_slice());
    }

    #[verifier::external_body]
    fn ex_from_be_bytes(s: &[u8]) -> (x: u32) {
        use core::convert::TryInto;
        u32::from_be_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_be_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
     {
        let bytes = self.to_be_bytes();
        // s[pos..pos + 4].copy_from_slice(&bytes);
        // s.set_byte(pos, bytes[0]);
        // s.set_byte(pos + 1, bytes[1]);
        // s.set_byte(pos + 2, bytes[2]);
        // s.set_byte(pos + 3, bytes[3]);
        s.set_byte_range(pos, &bytes.as_slice());
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

    open spec fn spec_from_be_bytes(s: Seq<u8>) -> Self {
        (s[0] as u64) << 56 | (s[1] as u64) << 48 | (s[2] as u64) << 40 | (s[3] as u64) << 32 | (
        s[4] as u64) << 24 | (s[5] as u64) << 16 | (s[6] as u64) << 8 | (s[7] as u64)
    }

    open spec fn spec_to_be_bytes(&self) -> Seq<u8> {
        seq![
            ((self >> 56) & 0xff) as u8,
            ((self >> 48) & 0xff) as u8,
            ((self >> 40) & 0xff) as u8,
            ((self >> 32) & 0xff) as u8,
            ((self >> 24) & 0xff) as u8,
            ((self >> 16) & 0xff) as u8,
            ((self >> 8) & 0xff) as u8,
            (self & 0xff) as u8,
        ]
    }

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

    proof fn lemma_spec_to_from_be_bytes(&self) {
        let s = self.spec_to_be_bytes();
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
        assert(self == (((self >> 56) & 0xff) << 56 | ((self >> 48) & 0xff) << 48 | ((self >> 40)
            & 0xff) << 40 | ((self >> 32) & 0xff) << 32 | ((self >> 24) & 0xff) << 24 | ((self
            >> 16) & 0xff) << 16 | ((self >> 8) & 0xff) << 8 | (self & 0xff))) by (bit_vector);
    }

    proof fn lemma_spec_from_to_be_bytes(s: Seq<u8>) {
        if s.len() == size_of::<u64>() {
            let x = Self::spec_from_be_bytes(s);
            let s0 = s[0] as u64;
            let s1 = s[1] as u64;
            let s2 = s[2] as u64;
            let s3 = s[3] as u64;
            let s4 = s[4] as u64;
            let s5 = s[5] as u64;
            let s6 = s[6] as u64;
            let s7 = s[7] as u64;
            assert(((x == s0 << 56 | s1 << 48 | s2 << 40 | s3 << 32 | s4 << 24 | s5 << 16 | s6 << 8
                | s7) && (s0 < 256) && (s1 < 256) && (s2 < 256) && (s3 < 256) && (s4 < 256) && (s5
                < 256) && (s6 < 256) && (s7 < 256)) ==> s0 == ((x >> 56) & 0xff) && s1 == ((x >> 48)
                & 0xff) && s2 == ((x >> 40) & 0xff) && s3 == ((x >> 32) & 0xff) && s4 == ((x >> 24)
                & 0xff) && s5 == ((x >> 16) & 0xff) && s6 == ((x >> 8) & 0xff) && s7 == (x & 0xff))
                by (bit_vector);
            assert_seqs_equal!(Self::spec_to_be_bytes(&Self::spec_from_be_bytes(s)) == s);
        }
    }

    proof fn lemma_spec_from_be_bytes_no_lookahead(s1: Seq<u8>, s2: Seq<u8>) {
    }

    #[verifier::external_body]
    fn ex_from_le_bytes(s: &[u8]) -> (x: u64) {
        use core::convert::TryInto;
        u64::from_le_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_le_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
     {
        let bytes = self.to_le_bytes();
        // s[pos..pos + 8].copy_from_slice(&bytes);
        // s.set_byte(pos, bytes[0]);
        // s.set_byte(pos + 1, bytes[1]);
        // s.set_byte(pos + 2, bytes[2]);
        // s.set_byte(pos + 3, bytes[3]);
        // s.set_byte(pos + 4, bytes[4]);
        // s.set_byte(pos + 5, bytes[5]);
        // s.set_byte(pos + 6, bytes[6]);
        // s.set_byte(pos + 7, bytes[7]);
        s.set_byte_range(pos, &bytes.as_slice());
    }

    #[verifier::external_body]
    fn ex_from_be_bytes(s: &[u8]) -> (x: u64) {
        use core::convert::TryInto;
        u64::from_be_bytes(s.try_into().unwrap())
    }

    #[verifier::external_body]
    fn ex_to_be_bytes<I, O>(&self, s: &mut O, pos: usize) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
     {
        let bytes = self.to_be_bytes();
        // s[pos..pos + 8].copy_from_slice(&bytes);
        // s.set_byte(pos, bytes[0]);
        // s.set_byte(pos + 1, bytes[1]);
        // s.set_byte(pos + 2, bytes[2]);
        // s.set_byte(pos + 3, bytes[3]);
        // s.set_byte(pos + 4, bytes[4]);
        // s.set_byte(pos + 5, bytes[5]);
        // s.set_byte(pos + 6, bytes[6]);
        // s.set_byte(pos + 7, bytes[7]);
        s.set_byte_range(pos, &bytes.as_slice());
    }

    fn eq(&self, other: &u64) -> (res: bool) {
        *self == *other
    }
}

impl SpecFrom<u8> for usize {
    open spec fn spec_from(t: u8) -> usize {
        t as usize
    }
}

impl SpecFrom<u16> for usize {
    open spec fn spec_from(t: u16) -> usize {
        t as usize
    }
}

impl SpecFrom<u32> for usize {
    open spec fn spec_from(t: u32) -> usize {
        t as usize
    }
}

impl SpecFrom<u64> for usize {
    open spec fn spec_from(t: u64) -> usize {
        t as usize
    }
}

impl SpecFrom<u24> for usize {
    open spec fn spec_from(t: u24) -> usize {
        t.spec_as_u32() as usize
    }
}

impl From<u8> for usize {
    fn ex_from(t: u8) -> usize {
        t as usize
    }
}

impl From<u16> for usize {
    fn ex_from(t: u16) -> usize {
        t as usize
    }
}

impl From<u32> for usize {
    fn ex_from(t: u32) -> usize {
        t as usize
    }
}

impl From<u64> for usize {
    fn ex_from(t: u64) -> usize {
        t as usize
    }
}

impl From<u24> for usize {
    fn ex_from(t: u24) -> usize {
        t.as_u32() as usize
    }
}

/// Vest's u24 (3-byte unsigned integer) type.
/// For simplicity, this type always stores the integer in big-endian byte order.
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct u24(pub [u8; 3]);

impl View for u24 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl u24 {
    /// Converts the `u24` to a `u32`.
    pub open spec fn spec_as_u32(&self) -> u32 {
        let s = self.0;
        let bytes = seq![0, s[0], s[1], s[2]];
        u32::spec_from_be_bytes(bytes)
    }

    /// Converts the `u24` to a `u32`.
    pub fn as_u32(&self) -> (o: u32)
        ensures
            o == self.spec_as_u32(),
    {
        let mut bytes = [0;4];
        bytes.set(1, self.0[0]);
        bytes.set(2, self.0[1]);
        bytes.set(3, self.0[2]);
        u32::ex_from_be_bytes(bytes.as_slice())
    }
}

/// Combinator for parsing and serializing unsigned u24 integers in little-endian byte order.
pub struct U24Le;

impl View for U24Le {
    type V = U24Le;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for U24Le {
    type Type = u24;

    // To parse a u24 in little-endian byte order, we simply reverse the 3 bytes parsed by the
    // `Fixed<3>` combinator.
    // Later when this `u24` is used, it's converted to a `u32` in big-endian byte order.
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, u24)> {
        match Fixed::<3>.spec_parse(s) {
            Some((n, bytes)) => Some((n, u24([bytes[2], bytes[1], bytes[0]]))),
            _ => None,
        }
    }

    open spec fn spec_serialize(&self, v: u24) -> Seq<u8> {
        let bytes = v.0;
        Fixed::<3>.spec_serialize([bytes[2], bytes[1], bytes[0]]@)
    }
}

impl SecureSpecCombinator for U24Le {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        Fixed::<3>.lemma_prefix_secure(s1, s2);
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: u24) {
        let v_rev = u24([v.0[2], v.0[1], v.0[0]]);
        Fixed::<3>.theorem_serialize_parse_roundtrip(v_rev.0@);
        match Fixed::<3>.spec_parse(Fixed::<3>.spec_serialize(v_rev.0@)) {
            Some((n, bytes)) => {
                bytes_eq_view_implies_eq([bytes[2], bytes[1], bytes[0]], v.0);
            },
            _ => {},
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        Fixed::<3>.theorem_parse_serialize_roundtrip(s);
        match Fixed::<3>.spec_parse(s) {
            Some((n, bytes)) => {
                assert([bytes[0], bytes[1], bytes[2]]@ == bytes);
            },
            _ => {},
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<'x> Combinator<'x, &[u8], Vec<u8>> for U24Le {
    type Type = u24;

    type SType = &'x u24;

    fn length(&self, v: Self::SType) -> usize {
        3
    }

    fn parse(&self, s: &[u8]) -> (res: Result<(usize, u24), ParseError>) {
        let (n, bytes) = <_ as Combinator<&[u8], Vec<u8>>>::parse(&Fixed::<3>, s)?;
        Ok((n, u24([bytes[2], bytes[1], bytes[0]])))
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(
            &Fixed::<3>,
            &[v.0[2], v.0[1], v.0[0]].as_slice(),
            data,
            pos,
        )
    }
}

/// Combinator for parsing and serializing unsigned u24 integers in big-endian byte order.
pub struct U24Be;

impl View for U24Be {
    type V = U24Be;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for U24Be {
    type Type = u24;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, u24)> {
        match Fixed::<3>.spec_parse(s) {
            Some((n, bytes)) => Some((n, u24([bytes[0], bytes[1], bytes[2]]))),
            _ => None,
        }
    }

    open spec fn spec_serialize(&self, v: u24) -> Seq<u8> {
        let bytes = v.0;
        Fixed::<3>.spec_serialize(bytes@)
    }
}

impl SecureSpecCombinator for U24Be {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        Fixed::<3>.lemma_prefix_secure(s1, s2);
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: u24) {
        Fixed::<3>.theorem_serialize_parse_roundtrip(v.0@);
        match Fixed::<3>.spec_parse(Fixed::<3>.spec_serialize(v.0@)) {
            Some((n, bytes)) => {
                bytes_eq_view_implies_eq([bytes[0], bytes[1], bytes[2]], v.0);
            },
            _ => {},
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        Fixed::<3>.theorem_parse_serialize_roundtrip(s);
        match Fixed::<3>.spec_parse(s) {
            Some((n, bytes)) => {
                assert([bytes[0], bytes[1], bytes[2]]@ == bytes);
            },
            _ => {},
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

proof fn bytes_eq_view_implies_eq<const N: usize>(a: [u8; N], b: [u8; N])
    ensures
        a@ =~= b@ <==> a == b,
{
    if a@ == b@ {
        assert(a == b);
    }
}

impl<'x> Combinator<'x, &[u8], Vec<u8>> for U24Be {
    type Type = u24;

    type SType = &'x u24;

    fn length(&self, v: Self::SType) -> usize {
        3
    }

    fn parse(&self, s: &[u8]) -> (res: Result<(usize, u24), ParseError>) {
        let (n, bytes) = <_ as Combinator<&[u8], Vec<u8>>>::parse(&Fixed::<3>, s)?;
        Ok((n, u24([bytes[0], bytes[1], bytes[2]])))
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&Fixed::<3>, &v.0.as_slice(), data, pos)
    }
}

} // verus!
