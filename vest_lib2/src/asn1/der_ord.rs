//! Allocation-free comparison of values by their complete DER encodings.
#![allow(unused_variables)]

use crate::asn1::set_of::*;
use crate::asn1::tag::TAG_FMT_MAX_BYTE_LEN;
use crate::asn1::{
    ASN1Fmt, Any, AnyFmt, AnySpec, BitString, BitStringFmt, BitStringSpec, BmpStringFmt,
    BmpStringSpec, BoolFmt, DefaultedFmt, EnumeratedFmt, GeneralizedTime, GeneralizedTimeFmt,
    GeneralizedTimeSpec, Ia5String, Ia5StringFmt, Ia5StringSpec, ImplicitlyTaggedFmt, Integer,
    Integer16Fmt, Integer8Fmt, IntegerFmt, LengthFmt, ObjectIdentifierFmt, ObjectIdentifierSpec,
    PrintableString, PrintableStringFmt, PrintableStringSpec, Real, RealFmt, Retaggable, SetOfFmt,
    Tag, TagFmt, TeletexString, TeletexStringFmt, TeletexStringSpec, UniversalStringFmt, UtcTime,
    UtcTimeFmt, Utf8StringFmt,
};
#[cfg(feature = "alloc")]
use crate::asn1::{BmpString, ObjectIdentifier, UniversalString};
use crate::combinators::choice::Sum;
use crate::combinators::mapped::spec::{BiMap, SpecMap};
use crate::combinators::{
    Choice, Empty, Eof, Mapped, Opt, Optional, Pair, Ref, Refined, RepeatTillEnd, Star, Tail, U8,
};
use crate::core::exec::fns::{Map, Pred};
use crate::core::exec::serializer::{ByteLen, SerializerExt};
use crate::core::spec::{Consistency, GoodSerializer, SpecByteLen, SpecSerializer};
use crate::primitives::base128::{Base128Fmt, BASE128_MAX_BYTES};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::calc;
use vstd::prelude::*;
#[cfg(feature = "alloc")]
use vstd::string::StrSliceExecFns;

verus! {

/// Cursor-state type for a format. It is format-specific rather than value-type-specific.
pub trait DerState {
    type State: Copy + Default;
}

/// Executable values whose deep view is the value itself.
///
/// ASN.1 `DEFAULT` needs this law to make its executable equality test line up with the
/// spec-level decision to omit the field. Generated ENUMERATED value types implement it.
pub trait DeepViewIdentity: DeepView<V = Self> + Copy {
    proof fn lemma_deep_view_identity(&self)
        ensures
            self.deep_view() == *self,
    ;
}

impl DeepViewIdentity for bool {
    proof fn lemma_deep_view_identity(&self) {
    }
}

impl DeepViewIdentity for i8 {
    proof fn lemma_deep_view_identity(&self) {
    }
}

impl DeepViewIdentity for i16 {
    proof fn lemma_deep_view_identity(&self) {
    }
}

impl DeepViewIdentity for u8 {
    proof fn lemma_deep_view_identity(&self) {
    }
}

impl DeepViewIdentity for UtcTime {
    proof fn lemma_deep_view_identity(&self) {
        crate::asn1::utctime::lemma_utc_time_deep_view(self);
    }
}

/// A format whose executable values can be traversed in serialization order without producing
/// an intermediate byte buffer.
///
/// `State` contains only traversal state; it must not own a serialization of the value.
pub trait DerOrd<T>: DerState + SpecSerializer<SVal = T::V> + SpecByteLen<T = T::V> + Consistency<
    Val = T::V,
> where T: DeepView + ?Sized {
    /// DER cursors range over the same number of octets as the format's byte-length model.
    ///
    /// Unlike [`crate::core::spec::GoodSerializer::lemma_serialize_len`], this law is
    /// unconditional once the value is consistent.
    proof fn lemma_der_serialize_len(&self, value: T::V)
        requires
            self.consistent(value),
        ensures
            self.spec_serialize(value).len() == self.byte_len(value),
    ;

    /// The portion of `spec_serialize(value)` not yet returned by the cursor.
    spec fn der_remaining(&self, value: T::V, state: <Self as DerState>::State) -> Seq<u8>;

    /// The format-specific cursor invariant.
    spec fn der_state_valid(&self, value: T::V, state: <Self as DerState>::State) -> bool;

    /// Start traversing the encoding of `value`.
    fn der_start(&self, value: &T) -> (state: <Self as DerState>::State)
        requires
            self.consistent(value.deep_view()),
        ensures
            self.der_state_valid(value.deep_view(), state),
            self.der_remaining(value.deep_view(), state) == self.spec_serialize(value.deep_view()),
    ;

    /// Return the next encoded octet, or `None` exactly at the end of the encoding.
    fn der_next(&self, value: &T, state: &mut <Self as DerState>::State) -> (next: Option<u8>)
        requires
            self.consistent(value.deep_view()),
            self.der_state_valid(value.deep_view(), *old(state)),
        ensures
            self.der_state_valid(value.deep_view(), *final(state)),
            match next {
                Some(byte) => {
                    self.der_remaining(value.deep_view(), *old(state)) == seq![byte]
                        + self.der_remaining(value.deep_view(), *final(state))
                },
                None => {
                    &&& self.der_remaining(value.deep_view(), *old(state)).len() == 0
                    &&& self.der_remaining(value.deep_view(), *final(state)).len() == 0
                },
            },
    ;

    /// Compare two values by the complete DER TLV octets produced by this format.
    #[verifier::loop_isolation(false)]
    fn der_leq(&self, left: &T, right: &T) -> (leq: bool)
        requires
            self.consistent(left.deep_view()),
            self.consistent(right.deep_view()),
        ensures
            leq == der_octets_leq(
                self.spec_serialize(left.deep_view()),
                self.spec_serialize(right.deep_view()),
            ),
    {
        let mut left_state = self.der_start(left);
        let mut right_state = self.der_start(right);
        let ghost leftvv = left.deep_view();
        let ghost rightvv = right.deep_view();
        let ghost left_encoding = self.spec_serialize(leftvv);
        let ghost right_encoding = self.spec_serialize(right.deep_view());

        loop
            invariant
                self.der_state_valid(leftvv, left_state),
                self.der_state_valid(right.deep_view(), right_state),
                der_octets_leq(left_encoding, right_encoding) == der_octets_leq(
                    self.der_remaining(leftvv, left_state),
                    self.der_remaining(rightvv, right_state),
                ),
            decreases
                    self.der_remaining(leftvv, left_state).len() + self.der_remaining(
                        rightvv,
                        right_state,
                    ).len(),
        {
            let ghost old_l = self.der_remaining(leftvv, left_state);
            let ghost old_r = self.der_remaining(rightvv, right_state);
            let left_next = self.der_next(left, &mut left_state);
            let right_next = self.der_next(right, &mut right_state);
            let left_byte = match left_next {
                Some(byte) => byte,
                None => 0,
            };
            let right_byte = match right_next {
                Some(byte) => byte,
                None => 0,
            };

            if left_next.is_none() && right_next.is_none() {
                return true;
            }
            proof {
                assert(der_octets_drop_head(old_l) == self.der_remaining(leftvv, left_state));
                assert(der_octets_drop_head(old_r) == self.der_remaining(rightvv, right_state));
                lemma_der_octets_leq_step(old_l, old_r);
            }

            if left_byte < right_byte {
                return true;
            }
            if left_byte > right_byte {
                return false;
            }
        }
    }
}

} // verus!
/// Prove that the cursor is valid and positioned at the start of the value's complete DER encoding.
#[allow(unused_macros)]
macro_rules! good_start {
    ($fmt:expr, $value:expr, $state:expr) => {
        ::vstd::prelude::assert_(::vstd::prelude::ext_equal(
            $fmt.der_remaining($value, $state),
            $fmt.spec_serialize($value),
        ));
        ::vstd::prelude::assert_($fmt.der_state_valid($value, $state));
    };
}

verus! {

/// Stack-resident serialization cursor for a DER tag.
#[derive(Copy, Clone)]
pub struct TagDerState {
    pub bytes: [u8; TAG_FMT_MAX_BYTE_LEN],
    pub len: usize,
    pub pos: usize,
}

impl Default for TagDerState {
    fn default() -> (state: Self) {
        Self { bytes: [0u8;TAG_FMT_MAX_BYTE_LEN], len: 0, pos: 0 }
    }
}

/// Stack-resident serialization cursor for a DER length.
///
/// Nine octets cover the one-octet prefix plus every byte of a 64-bit `usize`, and are also
/// sufficient on narrower targets.
#[derive(Copy, Clone)]
pub struct LengthDerState {
    pub bytes: [u8; 9],
    pub len: usize,
    pub pos: usize,
}

impl Default for LengthDerState {
    fn default() -> (state: Self) {
        Self { bytes: [0u8;9], len: 0, pos: 0 }
    }
}

impl DerState for TagFmt {
    type State = TagDerState;
}

impl DerOrd<Tag> for TagFmt {
    proof fn lemma_der_serialize_len(&self, tag: Tag) {
        self.lemma_serialize_len(tag);
    }

    open spec fn der_remaining(&self, tag: Tag, state: TagDerState) -> Seq<u8> {
        self.spec_serialize(tag).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, tag: Tag, state: TagDerState) -> bool {
        &&& state.pos <= state.len
        &&& state.len <= state.bytes@.len()
        &&& state.len == self.spec_serialize(tag).len()
        &&& state.bytes@.take(state.len as int) == self.spec_serialize(tag)
    }

    fn der_start(&self, t: &Tag) -> (state: TagDerState) {
        proof {
            crate::asn1::tag::lemma_tag_fmt_byte_len_bound(*t);
            self.lemma_serialize_len(*t);
        }
        let len = self.length(t);
        let mut bytes = [0u8;TAG_FMT_MAX_BYTE_LEN];
        let (encoded, tail) = bytes.split_at_mut(len);
        self.serialize(t, encoded);
        let state = TagDerState { bytes, len, pos: 0 };
        proof {
            vstd::seq_lib::lemma_seq_append_take_skip(encoded@, tail@, len as int);
            good_start!(self, *t, state);
        }
        state
    }

    fn der_next(&self, t: &Tag, state: &mut TagDerState) -> (next: Option<u8>) {
        if state.pos == state.len {
            None
        } else {
            let byte = state.bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

impl DerState for LengthFmt<true> {
    type State = LengthDerState;
}

impl DerOrd<usize> for LengthFmt<true> {
    proof fn lemma_der_serialize_len(&self, value: usize) {
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: usize, state: LengthDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: usize, state: LengthDerState) -> bool {
        &&& state.pos <= state.len
        &&& state.len <= 9
        &&& state.len == self.spec_serialize(value).len()
        &&& state.bytes@.take(state.len as int) == self.spec_serialize(value)
    }

    fn der_start(&self, l: &usize) -> (state: LengthDerState) {
        proof {
            crate::asn1::length::lemma_length_fmt_byte_len_bound::<true>(*l);
            self.lemma_serialize_len(*l);
        }
        let len = self.length(l);
        let mut bytes = [0u8;9];
        let (encoded, tail) = bytes.split_at_mut(len);
        self.serialize(l, encoded);
        let state = LengthDerState { bytes, len, pos: 0 };
        proof {
            vstd::seq_lib::lemma_seq_append_take_skip(encoded@, tail@, len as int);
            good_start!(self, *l, state);
        }
        state
    }

    fn der_next(&self, l: &usize, state: &mut LengthDerState) -> (next: Option<u8>) {
        if state.pos == state.len {
            None
        } else {
            let byte = state.bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

/// Stack-resident cursor for one minimally encoded OBJECT IDENTIFIER subidentifier.
#[derive(Copy, Clone)]
pub struct Base128DerState {
    pub bytes: [u8; BASE128_MAX_BYTES],
    pub len: usize,
    pub pos: usize,
}

impl Default for Base128DerState {
    fn default() -> (state: Self) {
        Self { bytes: [0u8;BASE128_MAX_BYTES], len: 0, pos: 0 }
    }
}

impl DerState for Base128Fmt<true> {
    type State = Base128DerState;
}

impl DerOrd<u64> for Base128Fmt<true> {
    proof fn lemma_der_serialize_len(&self, value: u64) {
        assert(self.serialize_inv());
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: u64, state: Base128DerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: u64, state: Base128DerState) -> bool {
        &&& state.pos <= state.len
        &&& state.len <= state.bytes@.len()
        &&& state.len == self.spec_serialize(value).len()
        &&& state.bytes@.take(state.len as int) == self.spec_serialize(value)
    }

    fn der_start(&self, i: &u64) -> (state: Base128DerState) {
        proof {
            self.lemma_der_serialize_len(*i);
            crate::primitives::base128::lemma_base128_fmt_consistent_byte_len_bound::<true>(*i);
        }
        let len = self.length(i);
        let mut bytes = [0u8;BASE128_MAX_BYTES];
        let (encoded, tail) = bytes.split_at_mut(len);
        self.serialize(i, encoded);
        let state = Base128DerState { bytes, len, pos: 0 };
        proof {
            vstd::seq_lib::lemma_seq_append_take_skip(encoded@, tail@, len as int);
            good_start!(self, *i, state);
        }
        state
    }

    fn der_next(&self, i: &u64, state: &mut Base128DerState) -> (next: Option<u8>) {
        if state.pos == state.len {
            None
        } else {
            let byte = state.bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

/// Cursor for a complete DER tag-length-value encoding.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Copy, Clone, Default)]
pub struct TlvDerState<Content> {
    pub tag: TagDerState,
    pub length: LengthDerState,
    pub content: Content,
    pub content_len: usize,
    /// `0`: tag, `1`: length, `2`: content.
    pub phase: u8,
}

impl<Content: DerState> DerState for ASN1Fmt<Content, true> {
    type State = TlvDerState<Content::State>;
}

impl<Content, T> DerOrd<T> for ASN1Fmt<Content, true> where
    T: DeepView + ?Sized,
    Content: crate::core::spec::SpecCombinator<T = T::V> + DerOrd<T>,
 {
    proof fn lemma_der_serialize_len(&self, value: T::V) {
        self.1.lemma_der_serialize_len(value);
        TagFmt.lemma_der_serialize_len(self.0);
        LengthFmt::<true>.lemma_der_serialize_len(self.1.byte_len(value) as usize);
    }

    #[verusfmt::skip]
    open spec fn der_remaining(&self, value: T::V, state: TlvDerState<Content::State>) -> Seq<u8> {
        match state.phase {
            0 => {
                TagFmt.der_remaining(self.0, state.tag)
                + LengthFmt::<true>.der_remaining(state.content_len, state.length)
                + self.1.der_remaining(value, state.content)
            },
            1 => {
                LengthFmt::<true>.der_remaining(state.content_len, state.length)
                + self.1.der_remaining(value, state.content)
            },
            _ => self.1.der_remaining(value, state.content),
        }
    }

    #[verusfmt::skip]
    open spec fn der_state_valid(&self, value: T::V, state: TlvDerState<Content::State>) -> bool {
        &&& TagFmt.der_state_valid(self.0, state.tag)
        &&& LengthFmt::<true>.der_state_valid(state.content_len, state.length)
        &&& self.1.der_state_valid(value, state.content)
        &&& state.content_len as nat == self.1.byte_len(value)
        &&& state.phase <= 2
        &&& state.phase >= 1 ==> TagFmt.der_remaining(self.0, state.tag).len() == 0
        &&& state.phase >= 2 ==> LengthFmt::<true>.der_remaining(state.content_len, state.length).len() == 0
    }

    fn der_start(&self, v: &T) -> (state: TlvDerState<Content::State>) {
        /// Count a cursor's encoded octets without materializing them.
        #[verifier::loop_isolation(false)]
        fn der_len<F, T>(fmt: &F, v: &T) -> (len: usize) where T: DeepView + ?Sized, F: DerOrd<T>
            requires
                fmt.consistent(v.deep_view()),
                fmt.spec_serialize(v.deep_view()).len() <= usize::MAX,
            ensures
                len == fmt.spec_serialize(v.deep_view()).len(),
        {
            let mut state = fmt.der_start(v);
            let mut len = 0usize;
            let ghost encoding = fmt.spec_serialize(v.deep_view());
            loop
                invariant
                    fmt.der_state_valid(v.deep_view(), state),
                    len as nat + fmt.der_remaining(v.deep_view(), state).len() == encoding.len(),
                decreases fmt.der_remaining(v.deep_view(), state).len(),
            {
                if let None = fmt.der_next(v, &mut state) {
                    return len;
                }
                len += 1;
            }
        }
        proof {
            self.1.lemma_der_serialize_len(v.deep_view());
        }
        let content_len = der_len(&self.1, v);
        let state = TlvDerState {
            tag: TagFmt.der_start(&self.0),
            length: LengthFmt::<true>.der_start(&content_len),
            content: self.1.der_start(v),
            content_len,
            phase: 0,
        };
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &T, state: &mut TlvDerState<Content::State>) -> (next: Option<u8>) {
        if state.phase == 0 {
            match TagFmt.der_next(&self.0, &mut state.tag) {
                Some(byte) => {
                    return Some(byte);
                },
                None => {
                    state.phase = 1;
                },
            }
        }
        if state.phase == 1 {
            match LengthFmt::<true>.der_next(&state.content_len, &mut state.length) {
                Some(byte) => {
                    return Some(byte);
                },
                None => {
                    state.phase = 2;
                },
            }
        }
        let next = self.1.der_next(v, &mut state.content);
        next
    }
}

impl DerState for BoolFmt<true> {
    type State = bool;
}

impl DerOrd<bool> for BoolFmt<true> {
    proof fn lemma_der_serialize_len(&self, value: bool) {
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: bool, state: bool) -> Seq<u8> {
        if state {
            Seq::empty()
        } else {
            self.spec_serialize(value)
        }
    }

    open spec fn der_state_valid(&self, _value: bool, _state: bool) -> bool {
        true
    }

    fn der_start(&self, b: &bool) -> (state: bool) {
        let state = false;
        proof {
            good_start!(self, *b, state);
        }
        state
    }

    fn der_next(&self, b: &bool, state: &mut bool) -> (next: Option<u8>) {
        if *state {
            None
        } else {
            *state = true;
            let mut bytes = [0u8;1];
            self.serialize(b, &mut bytes);
            Some(bytes[0])
        }
    }
}

impl DerState for Integer8Fmt {
    type State = bool;
}

impl DerOrd<i8> for Integer8Fmt {
    proof fn lemma_der_serialize_len(&self, value: i8) {
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: i8, state: bool) -> Seq<u8> {
        if state {
            Seq::empty()
        } else {
            self.spec_serialize(value)
        }
    }

    open spec fn der_state_valid(&self, _value: i8, _state: bool) -> bool {
        true
    }

    fn der_start(&self, i: &i8) -> (state: bool) {
        let state = false;
        proof {
            good_start!(self, *i, state);
        }
        state
    }

    fn der_next(&self, i: &i8, state: &mut bool) -> (next: Option<u8>) {
        if *state {
            None
        } else {
            *state = true;
            let mut bytes = [0u8;1];
            self.serialize(i, &mut bytes);
            Some(bytes[0])
        }
    }
}

/// Stack cursor for the specialized small INTEGER content formats.
#[derive(Copy, Clone)]
pub struct Integer16DerState {
    pub bytes: [u8; 2],
    pub len: usize,
    pub pos: usize,
}

impl Default for Integer16DerState {
    fn default() -> (state: Self) {
        Self { bytes: [0u8;2], len: 0, pos: 0 }
    }
}

impl DerState for Integer16Fmt {
    type State = Integer16DerState;
}

impl DerOrd<i16> for Integer16Fmt {
    proof fn lemma_der_serialize_len(&self, value: i16) {
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: i16, state: Integer16DerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: i16, state: Integer16DerState) -> bool {
        &&& state.pos <= state.len <= 2
        &&& state.len == self.spec_serialize(value).len()
        &&& state.bytes@.take(state.len as int) == self.spec_serialize(value)
    }

    fn der_start(&self, i: &i16) -> (state: Integer16DerState) {
        proof {
            crate::asn1::integer::lemma_integer16_fmt_byte_len_bound(*i);
            self.lemma_serialize_len(*i);
        }
        let len = self.length(i);
        let mut bytes = [0u8;2];
        let (encoded, tail) = bytes.split_at_mut(len);
        self.serialize(i, encoded);
        let state = Integer16DerState { bytes, len, pos: 0 };
        proof {
            vstd::seq_lib::lemma_seq_append_take_skip(encoded@, tail@, len as int);
            good_start!(self, *i, state);
        }
        state
    }

    fn der_next(&self, i: &i16, state: &mut Integer16DerState) -> (next: Option<u8>) {
        if state.pos == state.len {
            None
        } else {
            let byte = state.bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

#[derive(Copy, Clone)]
pub struct UtcTimeDerState {
    pub bytes: [u8; 13],
    pub pos: usize,
}

impl Default for UtcTimeDerState {
    fn default() -> (state: Self) {
        Self { bytes: [0u8;13], pos: 0 }
    }
}

impl DerState for UtcTimeFmt<true> {
    type State = UtcTimeDerState;
}

/// DER always emits UTCTime with seconds and the trailing `Z`, for 13 content octets.
proof fn lemma_utc_time_der_serialized_len(value: UtcTime)
    requires
        UtcTimeFmt::<true>.consistent(value),
    ensures
        UtcTimeFmt::<true>.spec_serialize(value).len() == 13,
        UtcTimeFmt::<true>.byte_len(value) == 13,
{
}

impl DerOrd<UtcTime> for UtcTimeFmt<true> {
    proof fn lemma_der_serialize_len(&self, value: UtcTime) {
        lemma_utc_time_der_serialized_len(value);
    }

    open spec fn der_remaining(&self, value: UtcTime, state: UtcTimeDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: UtcTime, state: UtcTimeDerState) -> bool {
        &&& state.pos <= 13
        &&& state.bytes@ == self.spec_serialize(value)
    }

    fn der_start(&self, t: &UtcTime) -> (state: UtcTimeDerState) {
        proof {
            t.lemma_deep_view_identity();
            assert(UtcTimeFmt::<true>.consistent(*t));
            lemma_utc_time_der_serialized_len(*t);
        }
        let mut bytes = [0u8;13];
        self.serialize(t, &mut bytes);
        let state = UtcTimeDerState { bytes, pos: 0 };
        proof {
            good_start!(self, t.deep_view(), state);
        }
        state
    }

    fn der_next(&self, t: &UtcTime, state: &mut UtcTimeDerState) -> (next: Option<u8>) {
        if state.pos == 13 {
            None
        } else {
            let byte = state.bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

#[derive(Copy, Clone)]
pub struct GeneralizedTimeDerState {
    pub prefix: [u8; 14],
    pub pos: usize,
}

impl Default for GeneralizedTimeDerState {
    fn default() -> (state: Self) {
        Self { prefix: [0u8;14], pos: 0 }
    }
}

impl DerState for GeneralizedTimeFmt<true> {
    type State = GeneralizedTimeDerState;
}

impl<'a> DerOrd<GeneralizedTime<'a>> for GeneralizedTimeFmt<true> {
    proof fn lemma_der_serialize_len(&self, value: GeneralizedTimeSpec) {
        crate::asn1::generalizedtime::lemma_der_generalized_time_model(value);
    }

    open spec fn der_remaining(
        &self,
        value: GeneralizedTimeSpec,
        state: GeneralizedTimeDerState,
    ) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(
        &self,
        value: GeneralizedTimeSpec,
        state: GeneralizedTimeDerState,
    ) -> bool {
        &&& state.pos <= self.spec_serialize(value).len()
        &&& state.prefix@ == crate::asn1::generalizedtime::generalized_time_prefix(value)
    }

    fn der_start(&self, t: &GeneralizedTime<'a>) -> (state: GeneralizedTimeDerState) {
        proof {
            crate::asn1::generalizedtime::lemma_der_generalized_time_model(t.deep_view());
        }
        let prefix = crate::asn1::generalizedtime::generalized_time_der_prefix_bytes(t);
        let state = GeneralizedTimeDerState { prefix, pos: 0 };
        proof {
            good_start!(self, t.deep_view(), state);
        }
        state
    }

    fn der_next(&self, t: &GeneralizedTime<'a>, state: &mut GeneralizedTimeDerState) -> (next:
        Option<u8>) {
        let ghost old_pos = state.pos;
        proof {
            crate::asn1::generalizedtime::lemma_der_generalized_time_model(t.deep_view());
            crate::asn1::generalizedtime::lemma_der_generalized_time_layout(
                t.deep_view(),
                state.pos,
            );
        }
        let fraction = t.fraction();
        let total = if fraction.len() == 0 {
            15usize
        } else {
            fraction.len() + 16
        };
        if state.pos == total {
            None
        } else {
            let byte;
            if state.pos < 14 {
                byte = state.prefix[state.pos];
            } else if fraction.len() == 0 {
                byte = 0x5a;
            } else if state.pos == 14 {
                byte = 0x2e;
            } else if state.pos < fraction.len() + 15 {
                byte = fraction[state.pos - 15];
            } else {
                byte = 0x5a;
            }
            state.pos += 1;
            Some(byte)
        }
    }
}

/// Cursor for arbitrary-size INTEGER contents. Small values cache at most nine content octets;
/// large values retain the zero-copy representation and are traversed directly.
#[derive(Copy, Clone)]
pub struct IntegerDerState {
    pub bytes: [u8; 9],
    pub len: usize,
    pub pos: usize,
    pub small: bool,
}

impl Default for IntegerDerState {
    fn default() -> (state: Self) {
        Self { bytes: [0u8;9], len: 0, pos: 0, small: false }
    }
}

impl DerState for IntegerFmt {
    type State = IntegerDerState;
}

impl<'a> DerOrd<Integer<'a>> for IntegerFmt {
    proof fn lemma_der_serialize_len(&self, value: int) {
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: int, state: IntegerDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: int, state: IntegerDerState) -> bool {
        &&& state.pos <= state.len
        &&& state.len == self.spec_serialize(value).len()
        &&& state.small == (i64::MIN as int <= value <= i64::MAX as int)
        &&& state.small ==> {
            &&& state.len <= 9
            &&& state.bytes@.take(state.len as int) == self.spec_serialize(value)
        }
    }

    fn der_start(&self, i: &super::Integer<'a>) -> (state: IntegerDerState) {
        let state = match i {
            super::Integer::Small { v } => {
                let len = crate::asn1::integer::i64_to_be_bytes_len(*v);
                let mut bytes = [0u8;9];
                let (encoded, tail) = bytes.split_at_mut(len);
                crate::asn1::integer::i64_to_be_bytes_in_place(*v, encoded);
                proof {
                    crate::asn1::integer::lemma_integer_small_view(*v);
                    vstd::seq_lib::lemma_seq_append_take_skip(encoded@, tail@, len as int);
                }
                IntegerDerState { bytes, len, pos: 0, small: true }
            },
            super::Integer::Big { raw } => {
                let bytes = raw.as_slice();
                proof {
                    use_type_invariant(raw);
                    crate::asn1::integer::lemma_large_integer_outside_i64(raw.view());
                    crate::asn1::integer::lemma_integer_big_view(*raw);
                    crate::asn1::integer::lemma_integer_from_to_bytes(bytes.deep_view());
                }
                IntegerDerState { bytes: [0u8;9], len: bytes.len(), pos: 0, small: false }
            },
        };
        proof {
            good_start!(self, i.deep_view(), state);
        }
        state
    }

    fn der_next(&self, i: &super::Integer<'a>, state: &mut IntegerDerState) -> (next: Option<u8>) {
        if state.pos == state.len {
            None
        } else {
            let byte = match i {
                super::Integer::Small { v: _v } => {
                    proof {
                        crate::asn1::integer::lemma_integer_small_view(*_v);
                    }
                    state.bytes[state.pos]
                },
                super::Integer::Big { raw } => {
                    let bytes = raw.as_slice();
                    proof {
                        use_type_invariant(raw);
                        crate::asn1::integer::lemma_large_integer_outside_i64(raw.view());
                        crate::asn1::integer::lemma_integer_big_view(*raw);
                        crate::asn1::integer::lemma_integer_from_to_bytes(bytes.deep_view());
                    }
                    bytes[state.pos]
                },
            };
            state.pos += 1;
            Some(byte)
        }
    }
}

impl DerState for EnumeratedFmt {
    type State = IntegerDerState;
}

impl<'a> DerOrd<Integer<'a>> for EnumeratedFmt {
    proof fn lemma_der_serialize_len(&self, value: int) {
        IntegerFmt.lemma_der_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: int, state: IntegerDerState) -> Seq<u8> {
        IntegerFmt.der_remaining(value, state)
    }

    open spec fn der_state_valid(&self, value: int, state: IntegerDerState) -> bool {
        IntegerFmt.der_state_valid(value, state)
    }

    fn der_start(&self, i: &Integer<'a>) -> (state: IntegerDerState) {
        let state = IntegerFmt.der_start(i);
        proof {
            good_start!(self, i.deep_view(), state);
        }
        state
    }

    fn der_next(&self, i: &Integer<'a>, state: &mut IntegerDerState) -> (next: Option<u8>) {
        IntegerFmt.der_next(i, state)
    }
}

/// Cursor for a direct byte sequence.
#[derive(Copy, Clone, Default)]
pub struct BytesDerState {
    pub pos: usize,
}

impl DerState for Tail {
    type State = BytesDerState;
}

impl DerOrd<[u8]> for Tail {
    proof fn lemma_der_serialize_len(&self, value: Seq<u8>) {
    }

    open spec fn der_remaining(&self, value: Seq<u8>, state: BytesDerState) -> Seq<u8> {
        value.skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: Seq<u8>, state: BytesDerState) -> bool {
        state.pos <= value.len()
    }

    fn der_start(&self, b: &[u8]) -> (state: BytesDerState) {
        let state = BytesDerState { pos: 0 };
        proof {
            assert(<Self as DerOrd<[u8]>>::der_remaining(self, b@, state) == self.spec_serialize(
                b@,
            ));
            assert(<Self as DerOrd<[u8]>>::der_state_valid(self, b@, state));
        }
        state
    }

    fn der_next(&self, b: &[u8], state: &mut BytesDerState) -> (next: Option<u8>) {
        if state.pos == b.len() {
            None
        } else {
            let byte = b[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

impl<'a> DerOrd<&'a [u8]> for Tail {
    proof fn lemma_der_serialize_len(&self, value: Seq<u8>) {
    }

    open spec fn der_remaining(&self, value: Seq<u8>, state: BytesDerState) -> Seq<u8> {
        value.skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: Seq<u8>, state: BytesDerState) -> bool {
        state.pos <= value.len()
    }

    fn der_start(&self, b: &&'a [u8]) -> (state: BytesDerState) {
        let state = BytesDerState { pos: 0 };
        proof {
            assert(<Self as DerOrd<&'a [u8]>>::der_remaining(self, b.deep_view(), state)
                == self.spec_serialize(b.deep_view()));
            assert(<Self as DerOrd<&'a [u8]>>::der_state_valid(self, b.deep_view(), state));
        }
        state
    }

    fn der_next(&self, b: &&'a [u8], state: &mut BytesDerState) -> (next: Option<u8>) {
        if state.pos == b.len() {
            None
        } else {
            let byte = b[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

impl DerState for RealFmt<true> {
    type State = BytesDerState;
}

impl<'a> DerOrd<Real<'a, true>> for RealFmt<true> {
    proof fn lemma_der_serialize_len(&self, value: Seq<u8>) {
        assert(self.serialize_inv());
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: Seq<u8>, state: BytesDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: Seq<u8>, state: BytesDerState) -> bool {
        state.pos <= self.spec_serialize(value).len()
    }

    fn der_start(&self, r: &Real<'a, true>) -> (state: BytesDerState) {
        let bytes = r.contents();
        let state = BytesDerState { pos: 0 };
        proof {
            good_start!(self, r.deep_view(), state);
        }
        state
    }

    fn der_next(&self, r: &Real<'a, true>, state: &mut BytesDerState) -> (next: Option<u8>) {
        let bytes = r.contents();
        if state.pos == bytes.len() {
            None
        } else {
            let byte = bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

impl DerState for Utf8StringFmt {
    type State = BytesDerState;
}

impl<'a> DerOrd<&'a str> for Utf8StringFmt {
    proof fn lemma_der_serialize_len(&self, value: Seq<char>) {
        assert(self.serialize_inv());
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: Seq<char>, state: BytesDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: Seq<char>, state: BytesDerState) -> bool {
        state.pos <= self.spec_serialize(value).len()
    }

    fn der_start(&self, s: &&'a str) -> (state: BytesDerState) {
        let bytes = s.as_bytes();
        let state = BytesDerState { pos: 0 };
        proof {
            good_start!(self, s.deep_view(), state);
        }
        state
    }

    fn der_next(&self, s: &&'a str, state: &mut BytesDerState) -> (next: Option<u8>) {
        let bytes = s.as_bytes();
        if state.pos == bytes.len() {
            None
        } else {
            let byte = bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

impl DerState for PrintableStringFmt {
    type State = BytesDerState;
}

impl<'a> DerOrd<PrintableString<'a>> for PrintableStringFmt {
    proof fn lemma_der_serialize_len(&self, value: PrintableStringSpec) {
        assert(self.serialize_inv());
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: PrintableStringSpec, state: BytesDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: PrintableStringSpec, state: BytesDerState) -> bool {
        state.pos <= self.spec_serialize(value).len()
    }

    fn der_start(&self, s: &PrintableString<'a>) -> (state: BytesDerState) {
        let inner = s.inner();
        let bytes = inner.as_bytes();
        let state = BytesDerState { pos: 0 };
        proof {
            good_start!(self, s.deep_view(), state);
        }
        state
    }

    fn der_next(&self, s: &PrintableString<'a>, state: &mut BytesDerState) -> (next: Option<u8>) {
        let inner = s.inner();
        let bytes = inner.as_bytes();
        if state.pos == bytes.len() {
            None
        } else {
            let byte = bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

impl DerState for Ia5StringFmt {
    type State = BytesDerState;
}

impl<'a> DerOrd<Ia5String<'a>> for Ia5StringFmt {
    proof fn lemma_der_serialize_len(&self, value: Ia5StringSpec) {
        assert(self.serialize_inv());
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: Ia5StringSpec, state: BytesDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: Ia5StringSpec, state: BytesDerState) -> bool {
        state.pos <= self.spec_serialize(value).len()
    }

    fn der_start(&self, s: &Ia5String<'a>) -> (state: BytesDerState) {
        let inner = s.inner();
        let bytes = inner.as_bytes();
        let state = BytesDerState { pos: 0 };
        proof {
            good_start!(self, s.deep_view(), state);
        }
        state
    }

    fn der_next(&self, s: &Ia5String<'a>, state: &mut BytesDerState) -> (next: Option<u8>) {
        let inner = s.inner();
        let bytes = inner.as_bytes();
        if state.pos == bytes.len() {
            None
        } else {
            let byte = bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

impl DerState for TeletexStringFmt {
    type State = BytesDerState;
}

impl<'a> DerOrd<TeletexString<'a>> for TeletexStringFmt {
    proof fn lemma_der_serialize_len(&self, value: TeletexStringSpec) {
        assert(self.serialize_inv());
        self.lemma_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: TeletexStringSpec, state: BytesDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(state.pos as int)
    }

    open spec fn der_state_valid(&self, value: TeletexStringSpec, state: BytesDerState) -> bool {
        state.pos <= self.spec_serialize(value).len()
    }

    fn der_start(&self, s: &TeletexString<'a>) -> (state: BytesDerState) {
        let inner = s.inner();
        let bytes = inner.as_bytes();
        let state = BytesDerState { pos: 0 };
        proof {
            good_start!(self, s.deep_view(), state);
        }
        state
    }

    fn der_next(&self, s: &TeletexString<'a>, state: &mut BytesDerState) -> (next: Option<u8>) {
        let inner = s.inner();
        let bytes = inner.as_bytes();
        if state.pos == bytes.len() {
            None
        } else {
            let byte = bytes[state.pos];
            state.pos += 1;
            Some(byte)
        }
    }
}

impl DerState for U8 {
    type State = bool;
}

impl DerOrd<u8> for U8 {
    proof fn lemma_der_serialize_len(&self, value: u8) {
    }

    open spec fn der_remaining(&self, value: u8, state: bool) -> Seq<u8> {
        if state {
            Seq::empty()
        } else {
            seq![value]
        }
    }

    open spec fn der_state_valid(&self, _value: u8, _state: bool) -> bool {
        true
    }

    fn der_start(&self, v: &u8) -> (state: bool) {
        let state = false;
        proof {
            good_start!(self, *v, state);
        }
        state
    }

    fn der_next(&self, v: &u8, state: &mut bool) -> (next: Option<u8>) {
        if *state {
            None
        } else {
            *state = true;
            Some(*v)
        }
    }
}

impl DerState for Eof {
    type State = bool;
}

impl DerOrd<()> for Eof {
    proof fn lemma_der_serialize_len(&self, _value: ()) {
    }

    open spec fn der_remaining(&self, _value: (), _state: bool) -> Seq<u8> {
        Seq::empty()
    }

    open spec fn der_state_valid(&self, _value: (), _state: bool) -> bool {
        true
    }

    fn der_start(&self, _v: &()) -> (state: bool) {
        let state = false;
        proof {
            good_start!(self, *_v, state);
        }
        state
    }

    fn der_next(&self, _v: &(), _state: &mut bool) -> (next: Option<u8>) {
        None
    }
}

impl DerState for Empty {
    type State = bool;
}

impl DerOrd<()> for Empty {
    proof fn lemma_der_serialize_len(&self, _value: ()) {
    }

    open spec fn der_remaining(&self, _value: (), _state: bool) -> Seq<u8> {
        Seq::empty()
    }

    open spec fn der_state_valid(&self, _value: (), _state: bool) -> bool {
        true
    }

    fn der_start(&self, _v: &()) -> (state: bool) {
        let state = false;
        proof {
            good_start!(self, *_v, state);
        }
        state
    }

    fn der_next(&self, _v: &(), _state: &mut bool) -> (next: Option<u8>) {
        None
    }
}

/// Cursor for sequential composition.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Copy, Clone, Default)]
pub struct PairDerState<Left, Right> {
    pub left: Left,
    pub right: Right,
    pub in_left: bool,
}

impl<A: DerState, B: DerState> DerState for Pair<A, B> {
    type State = PairDerState<A::State, B::State>;
}

impl<A, B, TA, TB> DerOrd<(TA, TB)> for Pair<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: DerOrd<TA>,
    B: DerOrd<TB>,
 {
    proof fn lemma_der_serialize_len(&self, value: (TA::V, TB::V)) {
        self.0.lemma_der_serialize_len(value.0);
        self.1.lemma_der_serialize_len(value.1);
    }

    open spec fn der_remaining(
        &self,
        value: (TA::V, TB::V),
        state: PairDerState<A::State, B::State>,
    ) -> Seq<u8> {
        if state.in_left {
            self.0.der_remaining(value.0, state.left) + self.1.der_remaining(value.1, state.right)
        } else {
            self.1.der_remaining(value.1, state.right)
        }
    }

    open spec fn der_state_valid(
        &self,
        value: (TA::V, TB::V),
        state: PairDerState<A::State, B::State>,
    ) -> bool {
        &&& self.0.der_state_valid(value.0, state.left)
        &&& self.1.der_state_valid(value.1, state.right)
        &&& !state.in_left ==> self.0.der_remaining(value.0, state.left).len() == 0
    }

    fn der_start(&self, v: &(TA, TB)) -> (state: PairDerState<A::State, B::State>) {
        let left = self.0.der_start(&v.0);
        let right = self.1.der_start(&v.1);
        let state = PairDerState { left, right, in_left: true };
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &(TA, TB), state: &mut PairDerState<A::State, B::State>) -> (next: Option<
        u8,
    >) {
        if state.in_left {
            match self.0.der_next(&v.0, &mut state.left) {
                Some(byte) => {
                    return Some(byte);
                },
                None => state.in_left = false,
            }
        }
        let next = self.1.der_next(&v.1, &mut state.right);
        next
    }
}

impl DerState for BitStringFmt<true> {
    type State = PairDerState<bool, BytesDerState>;
}

impl<'a> DerOrd<BitString<'a, true>> for BitStringFmt<true> {
    proof fn lemma_der_serialize_len(&self, value: BitStringSpec) {
        <Pair<U8, Tail> as DerOrd<(u8, &'a [u8])>>::lemma_der_serialize_len(
            &Pair(U8, Tail),
            (value.unused, value.bits),
        );
        crate::asn1::bitstring::lemma_bit_string_fmt_serialization::<true>(value);
    }

    open spec fn der_remaining(
        &self,
        value: BitStringSpec,
        state: PairDerState<bool, BytesDerState>,
    ) -> Seq<u8> {
        <Pair<U8, Tail> as DerOrd<(u8, &'a [u8])>>::der_remaining(
            &Pair(U8, Tail),
            (value.unused, value.bits),
            state,
        )
    }

    open spec fn der_state_valid(
        &self,
        value: BitStringSpec,
        state: PairDerState<bool, BytesDerState>,
    ) -> bool {
        <Pair<U8, Tail> as DerOrd<(u8, &'a [u8])>>::der_state_valid(
            &Pair(U8, Tail),
            (value.unused, value.bits),
            state,
        )
    }

    fn der_start(&self, b: &BitString<'a, true>) -> (state: PairDerState<bool, BytesDerState>) {
        let pair = (b.unused(), b.bits());
        proof {
            crate::asn1::bitstring::lemma_bit_string_fmt_serialization::<true>(b.deep_view());
        }
        let state = Pair(U8, Tail).der_start(&pair);
        proof {
            good_start!(self, b.deep_view(), state);
        }
        state
    }

    fn der_next(
        &self,
        b: &BitString<'a, true>,
        state: &mut PairDerState<bool, BytesDerState>,
    ) -> (next: Option<u8>) {
        let pair = (b.unused(), b.bits());
        let next = Pair(U8, Tail).der_next(&pair, state);
        next
    }
}

type AnyDerInnerFmt = Pair<TagFmt, Pair<LengthFmt<true>, Tail>>;

pub type AnyDerState = PairDerState<TagDerState, PairDerState<LengthDerState, BytesDerState>>;

impl DerState for AnyFmt<true> {
    type State = AnyDerState;
}

impl<'a> DerOrd<Any<'a>> for AnyFmt<true> {
    proof fn lemma_der_serialize_len(&self, value: AnySpec) {
        <AnyDerInnerFmt as DerOrd<(Tag, (usize, &'a [u8]))>>::lemma_der_serialize_len(
            &Pair(TagFmt, Pair(LengthFmt::<true>, Tail)),
            (value.tag, (value.content.len() as usize, value.content)),
        );
    }

    open spec fn der_remaining(&self, value: AnySpec, state: AnyDerState) -> Seq<u8> {
        <AnyDerInnerFmt as DerOrd<(Tag, (usize, &'a [u8]))>>::der_remaining(
            &Pair(TagFmt, Pair(LengthFmt::<true>, Tail)),
            (value.tag, (value.content.len() as usize, value.content)),
            state,
        )
    }

    open spec fn der_state_valid(&self, value: AnySpec, state: AnyDerState) -> bool {
        <AnyDerInnerFmt as DerOrd<(Tag, (usize, &'a [u8]))>>::der_state_valid(
            &Pair(TagFmt, Pair(LengthFmt::<true>, Tail)),
            (value.tag, (value.content.len() as usize, value.content)),
            state,
        )
    }

    fn der_start(&self, a: &Any<'a>) -> (state: AnyDerState) {
        let tag = a.tag();
        let content = a.content();
        let len = content.len();
        let pair = (tag, (len, content));
        let state = Pair(TagFmt, Pair(LengthFmt::<true>, Tail)).der_start(&pair);
        proof {
            good_start!(self, a.deep_view(), state);
        }
        state
    }

    fn der_next(&self, a: &Any<'a>, state: &mut AnyDerState) -> (next: Option<u8>) {
        let tag = a.tag();
        let content = a.content();
        let len = content.len();
        let pair = (tag, (len, content));
        let next = Pair(TagFmt, Pair(LengthFmt::<true>, Tail)).der_next(&pair, state);
        next
    }
}

/// Cursor for a binary choice.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Copy, Clone)]
pub enum ChoiceDerState<Left, Right> {
    Left(Left),
    Right(Right),
}

impl<Left: Default, Right> Default for ChoiceDerState<Left, Right> {
    fn default() -> (state: Self) {
        ChoiceDerState::Left(Left::default())
    }
}

impl<A: DerState, B: DerState> DerState for Choice<A, B> {
    type State = ChoiceDerState<A::State, B::State>;
}

impl<A, B, TA, TB> DerOrd<Sum<TA, TB>> for Choice<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: DerOrd<TA>,
    B: DerOrd<TB>,
 {
    proof fn lemma_der_serialize_len(&self, value: Sum<TA::V, TB::V>) {
        match value {
            Sum::Inl(value) => self.0.lemma_der_serialize_len(value),
            Sum::Inr(value) => self.1.lemma_der_serialize_len(value),
        }
    }

    open spec fn der_remaining(
        &self,
        value: Sum<TA::V, TB::V>,
        state: ChoiceDerState<A::State, B::State>,
    ) -> Seq<u8> {
        match (value, state) {
            (Sum::Inl(value), ChoiceDerState::Left(state)) => { self.0.der_remaining(value, state)
            },
            (Sum::Inr(value), ChoiceDerState::Right(state)) => { self.1.der_remaining(value, state)
            },
            _ => Seq::empty(),
        }
    }

    open spec fn der_state_valid(
        &self,
        value: Sum<TA::V, TB::V>,
        state: ChoiceDerState<A::State, B::State>,
    ) -> bool {
        match (value, state) {
            (Sum::Inl(value), ChoiceDerState::Left(state)) => { self.0.der_state_valid(value, state)
            },
            (Sum::Inr(value), ChoiceDerState::Right(state)) => {
                self.1.der_state_valid(value, state)
            },
            _ => false,
        }
    }

    fn der_start(&self, v: &Sum<TA, TB>) -> (state: ChoiceDerState<A::State, B::State>) {
        let state = match v {
            Sum::Inl(value) => ChoiceDerState::Left(self.0.der_start(value)),
            Sum::Inr(value) => ChoiceDerState::Right(self.1.der_start(value)),
        };
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &Sum<TA, TB>, state: &mut ChoiceDerState<A::State, B::State>) -> (next:
        Option<u8>) {
        let next = match (v, &mut *state) {
            (Sum::Inl(value), ChoiceDerState::Left(state)) => self.0.der_next(value, state),
            (Sum::Inr(value), ChoiceDerState::Right(state)) => self.1.der_next(value, state),
            _ => {
                proof {
                    assert(false);
                }
                None
            },
        };
        next
    }
}

/// Cursor for an optional value.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Copy, Clone)]
pub enum OptDerState<Inner> {
    Some(Inner),
    None,
}

impl<Inner> Default for OptDerState<Inner> {
    fn default() -> (state: Self) {
        OptDerState::None
    }
}

impl<A: DerState> DerState for Opt<A> {
    type State = OptDerState<A::State>;
}

impl<A, T> DerOrd<Option<T>> for Opt<A> where T: DeepView, A: DerOrd<T> {
    proof fn lemma_der_serialize_len(&self, value: Option<T::V>) {
        if let Some(value) = value {
            self.0.lemma_der_serialize_len(value);
        }
    }

    open spec fn der_remaining(&self, value: Option<T::V>, state: OptDerState<A::State>) -> Seq<
        u8,
    > {
        match (value, state) {
            (Some(value), OptDerState::Some(state)) => self.0.der_remaining(value, state),
            (None, OptDerState::None) => Seq::empty(),
            _ => Seq::empty(),
        }
    }

    open spec fn der_state_valid(&self, value: Option<T::V>, state: OptDerState<A::State>) -> bool {
        match (value, state) {
            (Some(value), OptDerState::Some(state)) => self.0.der_state_valid(value, state),
            (None, OptDerState::None) => true,
            _ => false,
        }
    }

    fn der_start(&self, o: &Option<T>) -> (state: OptDerState<A::State>) {
        let state = match o {
            Some(value) => OptDerState::Some(self.0.der_start(value)),
            None => OptDerState::None,
        };
        proof {
            good_start!(self, o.deep_view(), state);
        }
        state
    }

    fn der_next(&self, o: &Option<T>, state: &mut OptDerState<A::State>) -> (next: Option<u8>) {
        let next = match (o, &mut *state) {
            (Some(value), OptDerState::Some(state)) => self.0.der_next(value, state),
            (None, OptDerState::None) => None,
            _ => {
                proof {
                    assert(false);
                }
                None
            },
        };
        next
    }
}

impl<A: DerState, B: DerState> DerState for Optional<A, B> {
    type State = PairDerState<OptDerState<A::State>, B::State>;
}

impl<A, B, TA, TB> DerOrd<(Option<TA>, TB)> for Optional<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: DerOrd<TA>,
    B: DerOrd<TB>,
 {
    proof fn lemma_der_serialize_len(&self, value: (Option<TA::V>, TB::V)) {
        if let Some(left) = value.0 {
            self.0.lemma_der_serialize_len(left);
        }
        self.1.lemma_der_serialize_len(value.1);
    }

    open spec fn der_remaining(
        &self,
        value: (Option<TA::V>, TB::V),
        state: PairDerState<OptDerState<A::State>, B::State>,
    ) -> Seq<u8> {
        if state.in_left {
            (match (&value.0, &state.left) {
                (Some(value), OptDerState::Some(inner)) => { self.0.der_remaining(*value, *inner) },
                (None, OptDerState::None) => Seq::empty(),
                _ => Seq::empty(),
            }) + self.1.der_remaining(value.1, state.right)
        } else {
            self.1.der_remaining(value.1, state.right)
        }
    }

    open spec fn der_state_valid(
        &self,
        value: (Option<TA::V>, TB::V),
        state: PairDerState<OptDerState<A::State>, B::State>,
    ) -> bool {
        &&& match (&value.0, &state.left) {
            (Some(value), OptDerState::Some(inner)) => self.0.der_state_valid(*value, *inner),
            (None, OptDerState::None) => true,
            _ => false,
        }
        &&& self.1.der_state_valid(value.1, state.right)
        &&& !state.in_left ==> {
            match (&value.0, &state.left) {
                (Some(value), OptDerState::Some(inner)) => {
                    self.0.der_remaining(*value, *inner).len() == 0
                },
                (None, OptDerState::None) => true,
                _ => false,
            }
        }
    }

    fn der_start(&self, o: &(Option<TA>, TB)) -> (state: PairDerState<
        OptDerState<A::State>,
        B::State,
    >) {
        let left = match &o.0 {
            Some(value) => OptDerState::Some(self.0.der_start(value)),
            None => OptDerState::None,
        };
        let right = self.1.der_start(&o.1);
        let state = PairDerState { left, right, in_left: true };
        proof {
            good_start!(self, o.deep_view(), state);
        }
        state
    }

    fn der_next(
        &self,
        o: &(Option<TA>, TB),
        state: &mut PairDerState<OptDerState<A::State>, B::State>,
    ) -> (next: Option<u8>) {
        if state.in_left {
            let field = match (&o.0, &mut state.left) {
                (Some(value), OptDerState::Some(inner)) => self.0.der_next(value, inner),
                (None, OptDerState::None) => None,
                _ => {
                    proof {
                        assert(false);
                    }
                    None
                },
            };
            match field {
                Some(byte) => {
                    return Some(byte);
                },
                None => state.in_left = false,
            }
        }
        let next = self.1.der_next(&o.1, &mut state.right);
        next
    }
}

/// Cursor for a concatenated collection.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Copy, Clone, Default)]
pub struct StarDerState<Inner> {
    pub index: usize,
    pub current: Inner,
}

impl<A: DerState> DerState for Star<A> {
    type State = StarDerState<A::State>;
}

broadcast proof fn lemma_star_consistent_index<A: Consistency>(
    inner: A,
    values: Seq<A::Val>,
    index: int,
)
    requires
        Star(inner).consistent(values),
        0 <= index < values.len(),
    ensures
        #[trigger] inner.consistent(values[index]),
{
    reveal(<Star<_> as Consistency>::consistent);
}

proof fn lemma_star_der_serialize_len<A, T>(inner: A, values: Seq<T::V>) where
    T: DeepView,
    A: DerOrd<T> + Copy,

    requires
        Star(inner).consistent(values),
    ensures
        Star(inner).spec_serialize(values).len() == Star(inner).byte_len(values),
    decreases values.len(),
{
    reveal(<Star<_> as Consistency>::consistent);
    reveal(<Star<_> as SpecSerializer>::spec_serialize);
    reveal(<Star<_> as SpecByteLen>::byte_len);
    broadcast use lemma_star_consistent_index;

    if values.len() > 0 {
        let prefix = values.drop_last();
        let last = values.last();
        lemma_star_der_serialize_len::<A, T>(inner, prefix);
        inner.lemma_der_serialize_len(last);
    }
}

#[cfg(feature = "alloc")]
impl<A, T> DerOrd<Vec<T>> for Star<A> where T: DeepView, A: DerOrd<T> + Copy {
    proof fn lemma_der_serialize_len(&self, vs: Seq<T::V>) {
        lemma_star_der_serialize_len::<A, T>(self.0, vs);
    }

    open spec fn der_remaining(&self, vs: Seq<T::V>, state: StarDerState<A::State>) -> Seq<u8> {
        if state.index < vs.len() {
            self.0.der_remaining(vs[state.index as int], state.current) + Star(
                self.0,
            ).spec_serialize(vs.skip(state.index as int + 1))
        } else {
            Seq::empty()
        }
    }

    open spec fn der_state_valid(&self, vs: Seq<T::V>, state: StarDerState<A::State>) -> bool {
        &&& state.index <= vs.len()
        &&& state.index < vs.len() ==> {
            self.0.der_state_valid(vs[state.index as int], state.current)
        }
    }

    fn der_start(&self, v: &Vec<T>) -> (state: StarDerState<A::State>) {
        reveal(<Star<_> as SpecSerializer>::spec_serialize);

        let state = if v.len() == 0 {
            let current = A::State::default();
            StarDerState { index: 0, current }
        } else {
            proof {
                lemma_star_consistent_index(self.0, v.deep_view(), 0);
            }
            let state = StarDerState { index: 0, current: self.0.der_start(&v[0]) };
            proof {
                let vv = v.deep_view();
                Star(self.0).lemma_spec_serialize_suffix_step(vv, 0);
                assert(self.0.der_remaining(vv[0], state.current) == self.0.spec_serialize(vv[0]));
                assert(vv.skip(0) == vv);
            }
            state
        };
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    #[verifier::loop_isolation(false)]
    fn der_next(&self, v: &Vec<T>, state: &mut StarDerState<A::State>) -> (next: Option<u8>) {
        broadcast use lemma_star_consistent_index;

        let ghost vv = v.deep_view();

        loop
            invariant
                self.der_state_valid(vv, *state),
                self.der_remaining(vv, *state) == self.der_remaining(vv, *old(state)),
                state.index <= v.len(),
            decreases v.len() - state.index,
        {
            if state.index == v.len() {
                return None;
            }
            let idx = state.index;
            if let Some(byte) = self.0.der_next(&v[idx], &mut state.current) {
                return Some(byte);
            } else {
                let new_idx = idx + 1;
                state.index = new_idx;
                if new_idx < v.len() {
                    proof {
                        lemma_star_consistent_index(self.0, vv, new_idx as int);
                    }
                    state.current = self.0.der_start(&v[new_idx]);
                }
                proof {
                    if new_idx < vv.len() {
                        assert(self.0.der_remaining(vv[new_idx as int], state.current)
                            == self.0.spec_serialize(vv[new_idx as int]));
                        Star(self.0).lemma_spec_serialize_suffix_step(vv, new_idx as int);
                    } else {
                        reveal(<Star<_> as SpecSerializer>::spec_serialize);
                    }
                }
            }
        }
    }
}

impl<Inner: DerState, P> DerState for Refined<Inner, P> {
    type State = Inner::State;
}

impl<Inner, P, T> DerOrd<T> for Refined<Inner, P> where T: DeepView, Inner: DerOrd<T>, P: Pred<T> {
    proof fn lemma_der_serialize_len(&self, value: T::V) {
        self.0.lemma_der_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: T::V, state: Inner::State) -> Seq<u8> {
        self.0.der_remaining(value, state)
    }

    open spec fn der_state_valid(&self, value: T::V, state: Inner::State) -> bool {
        self.0.der_state_valid(value, state)
    }

    fn der_start(&self, v: &T) -> (state: Inner::State) {
        let state = self.0.der_start(v);
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &T, state: &mut Inner::State) -> (next: Option<u8>) {
        let next = self.0.der_next(v, state);
        next
    }
}

impl<Inner: DerState> DerState for Ref<Inner> {
    type State = Inner::State;
}

impl<Inner, T> DerOrd<&T> for Ref<Inner> where T: DeepView + ?Sized, Inner: DerOrd<T> {
    proof fn lemma_der_serialize_len(&self, value: T::V) {
        self.0.lemma_der_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: T::V, state: Inner::State) -> Seq<u8> {
        self.0.der_remaining(value, state)
    }

    open spec fn der_state_valid(&self, value: T::V, state: Inner::State) -> bool {
        self.0.der_state_valid(value, state)
    }

    fn der_start(&self, v: &&T) -> (state: Inner::State) {
        let state = self.0.der_start(*v);
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &&T, state: &mut Inner::State) -> (next: Option<u8>) {
        let next = self.0.der_next(*v, state);
        next
    }
}

impl<Inner: DerState, M, MRev> DerState for Mapped<Inner, BiMap<M, MRev>> {
    type State = Inner::State;
}

impl<Inner, M, MRev, T> DerOrd<T> for Mapped<Inner, BiMap<M, MRev>> where
    T: DeepView,
    M: SpecMap<Input = MRev::Output, Output = T::V>,
    MRev: SpecMap<Input = T::V> + for <'x>Map<&'x T>,
    Inner: DerState,
    for <'x>Inner: DerOrd<<MRev as Map<&'x T>>::O>,
 {
    proof fn lemma_der_serialize_len(&self, value: T::V) {
        let inner = self.mapper.1.spec_map(value);
        self.inner.lemma_der_serialize_len(inner);
    }

    open spec fn der_remaining(&self, value: T::V, state: Inner::State) -> Seq<u8> {
        self.inner.der_remaining(self.mapper.1.spec_map(value), state)
    }

    open spec fn der_state_valid(&self, value: T::V, state: Inner::State) -> bool {
        self.inner.der_state_valid(self.mapper.1.spec_map(value), state)
    }

    fn der_start(&self, v: &T) -> (state: Inner::State) {
        let inner = self.mapper.1.map(v);
        let state = self.inner.der_start(&inner);
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &T, state: &mut Inner::State) -> (next: Option<u8>) {
        let inner = self.mapper.1.map(v);
        let next = self.inner.der_next(&inner, state);
        next
    }
}

#[cfg(feature = "alloc")]
impl<A: DerState> DerState for RepeatTillEnd<A> {
    type State = StarDerState<A::State>;
}

#[cfg(feature = "alloc")]
impl<A, T> DerOrd<Vec<T>> for RepeatTillEnd<A> where T: DeepView, A: DerOrd<T> + Copy {
    proof fn lemma_der_serialize_len(&self, values: Seq<T::V>) {
        Star(self.0).lemma_der_serialize_len(values);
    }

    open spec fn der_remaining(&self, values: Seq<T::V>, state: StarDerState<A::State>) -> Seq<u8> {
        Star(self.0).der_remaining(values, state)
    }

    open spec fn der_state_valid(&self, values: Seq<T::V>, state: StarDerState<A::State>) -> bool {
        Star(self.0).der_state_valid(values, state)
    }

    fn der_start(&self, v: &Vec<T>) -> (state: StarDerState<A::State>) {
        let state = Star(self.0).der_start(v);
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &Vec<T>, state: &mut StarDerState<A::State>) -> (next: Option<u8>) {
        let next = Star(self.0).der_next(v, state);
        next
    }
}

#[cfg(feature = "alloc")]
#[derive(Copy, Clone, Default)]
pub struct BmpStringDerState {
    pub char_index: usize,
    pub second_octet: bool,
}

#[cfg(feature = "alloc")]
impl DerState for BmpStringFmt {
    type State = BmpStringDerState;
}

#[cfg(feature = "alloc")]
pub open spec fn bmp_string_der_position(state: BmpStringDerState) -> nat {
    state.char_index as nat * 2 + if state.second_octet {
        1nat
    } else {
        0nat
    }
}

#[cfg(feature = "alloc")]
impl DerOrd<BmpString> for BmpStringFmt {
    proof fn lemma_der_serialize_len(&self, value: BmpStringSpec) {
        crate::asn1::bmpstring::lemma_bmp_string_fmt_serialization(value);
    }

    open spec fn der_remaining(&self, value: BmpStringSpec, state: BmpStringDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(bmp_string_der_position(state) as int)
    }

    open spec fn der_state_valid(&self, value: BmpStringSpec, state: BmpStringDerState) -> bool {
        &&& state.char_index <= value.inner.len()
        &&& state.char_index == value.inner.len() ==> !state.second_octet
    }

    fn der_start(&self, s: &BmpString) -> (state: BmpStringDerState) {
        let state = BmpStringDerState { char_index: 0, second_octet: false };
        proof {
            crate::asn1::bmpstring::lemma_bmp_string_fmt_serialization(s.deep_view());
            good_start!(self, s.deep_view(), state);
        }
        state
    }

    fn der_next(&self, s: &BmpString, state: &mut BmpStringDerState) -> (next: Option<u8>) {
        proof {
            crate::asn1::bmpstring::lemma_bmp_string_fmt_serialization(s.deep_view());
        }
        let inner = s.inner();
        let len = inner.unicode_len();
        if state.char_index == len {
            None
        } else {
            let c = inner.get_char(state.char_index);
            let encoded = crate::combinators::uints::exec::u16_to_be_bytes(c as u16);
            let byte;
            if state.second_octet {
                byte = encoded[1];
                state.char_index += 1;
                state.second_octet = false;
            } else {
                byte = encoded[0];
                state.second_octet = true;
            }
            Some(byte)
        }
    }
}

#[cfg(feature = "alloc")]
#[derive(Copy, Clone, Default)]
pub struct UniversalStringDerState {
    pub char_index: usize,
    pub octet_index: u8,
}

#[cfg(feature = "alloc")]
impl DerState for UniversalStringFmt {
    type State = UniversalStringDerState;
}

#[cfg(feature = "alloc")]
pub open spec fn universal_string_der_position(state: UniversalStringDerState) -> nat {
    state.char_index as nat * 4 + state.octet_index as nat
}

#[cfg(feature = "alloc")]
impl DerOrd<UniversalString> for UniversalStringFmt {
    proof fn lemma_der_serialize_len(&self, value: Seq<char>) {
        crate::asn1::universalstring::lemma_universal_string_fmt_serialization(value);
    }

    open spec fn der_remaining(&self, value: Seq<char>, state: UniversalStringDerState) -> Seq<u8> {
        self.spec_serialize(value).skip(universal_string_der_position(state) as int)
    }

    open spec fn der_state_valid(&self, value: Seq<char>, state: UniversalStringDerState) -> bool {
        &&& state.char_index <= value.len()
        &&& state.octet_index < 4
        &&& state.char_index == value.len() ==> state.octet_index == 0
    }

    fn der_start(&self, value: &UniversalString) -> (state: UniversalStringDerState) {
        let state = UniversalStringDerState { char_index: 0, octet_index: 0 };
        proof {
            crate::asn1::universalstring::lemma_universal_string_fmt_serialization(
                value.deep_view(),
            );
            good_start!(self, value.deep_view(), state);
        }
        state
    }

    fn der_next(&self, value: &UniversalString, state: &mut UniversalStringDerState) -> (next:
        Option<u8>) {
        proof {
            crate::asn1::universalstring::lemma_universal_string_fmt_serialization(
                value.deep_view(),
            );
        }
        let inner = value.as_str();
        let len = inner.unicode_len();
        if state.char_index == len {
            None
        } else {
            let c = inner.get_char(state.char_index);
            let encoded = crate::combinators::uints::exec::u32_to_be_bytes(c as u32);
            let byte = encoded[state.octet_index as usize];
            if state.octet_index == 3 {
                state.char_index += 1;
                state.octet_index = 0;
            } else {
                state.octet_index += 1;
            }
            Some(byte)
        }
    }
}

#[cfg(feature = "alloc")]
pub type ObjectIdentifierDerState = PairDerState<Base128DerState, StarDerState<Base128DerState>>;

#[cfg(feature = "alloc")]
impl DerState for ObjectIdentifierFmt {
    type State = ObjectIdentifierDerState;
}

#[cfg(feature = "alloc")]
impl DerOrd<ObjectIdentifier> for ObjectIdentifierFmt {
    proof fn lemma_der_serialize_len(&self, value: ObjectIdentifierSpec) {
        <crate::asn1::oid::ObjectIdentifierInnerFmt as DerOrd<
            (u64, Vec<u64>),
        >>::lemma_der_serialize_len(
            &crate::asn1::oid::object_identifier_inner(),
            crate::asn1::oid::oid_to_subidentifiers(value),
        );
    }

    open spec fn der_remaining(
        &self,
        value: ObjectIdentifierSpec,
        state: ObjectIdentifierDerState,
    ) -> Seq<u8> {
        if state.in_left {
            Base128Fmt::<true>.der_remaining(
                crate::asn1::oid::oid_first_subidentifier(value),
                state.left,
            ) + RepeatTillEnd(Base128Fmt::<true>).der_remaining(value.rest, state.right)
        } else {
            RepeatTillEnd(Base128Fmt::<true>).der_remaining(value.rest, state.right)
        }
    }

    open spec fn der_state_valid(
        &self,
        value: ObjectIdentifierSpec,
        state: ObjectIdentifierDerState,
    ) -> bool {
        &&& Base128Fmt::<true>.der_state_valid(
            crate::asn1::oid::oid_first_subidentifier(value),
            state.left,
        )
        &&& RepeatTillEnd(Base128Fmt::<true>).der_state_valid(value.rest, state.right)
        &&& !state.in_left ==> Base128Fmt::<true>.der_remaining(
            crate::asn1::oid::oid_first_subidentifier(value),
            state.left,
        ).len() == 0
    }

    fn der_start(&self, o: &ObjectIdentifier) -> (state: ObjectIdentifierDerState) {
        let combined = o.combined_first_subidentifier();
        let rest = o.rest_vec();
        let left = Base128Fmt::<true>.der_start(&combined);
        let right = RepeatTillEnd(Base128Fmt::<true>).der_start(rest);
        let state = PairDerState { left, right, in_left: true };
        proof {
            good_start!(self, o.deep_view(), state);
        }
        state
    }

    fn der_next(&self, o: &ObjectIdentifier, state: &mut ObjectIdentifierDerState) -> (next: Option<
        u8,
    >) {
        let combined = o.combined_first_subidentifier();
        let rest = o.rest_vec();
        if state.in_left {
            match Base128Fmt::<true>.der_next(&combined, &mut state.left) {
                Some(byte) => {
                    return Some(byte);
                },
                None => state.in_left = false,
            }
        }
        let next = RepeatTillEnd(Base128Fmt::<true>).der_next(rest, &mut state.right);
        next
    }
}

#[cfg(feature = "alloc")]
impl<A: DerState> DerState for SetOfFmt<A> {
    type State = StarDerState<A::State>;
}

#[cfg(feature = "alloc")]
impl<A, T> DerOrd<Vec<T>> for SetOfFmt<A> where T: DeepView, A: DerOrd<T> + Copy {
    proof fn lemma_der_serialize_len(&self, values: Seq<T::V>) {
        Star(self.0).lemma_der_serialize_len(values);
    }

    open spec fn der_remaining(&self, values: Seq<T::V>, state: StarDerState<A::State>) -> Seq<u8> {
        Star(self.0).der_remaining(values, state)
    }

    open spec fn der_state_valid(&self, values: Seq<T::V>, state: StarDerState<A::State>) -> bool {
        Star(self.0).der_state_valid(values, state)
    }

    fn der_start(&self, v: &Vec<T>) -> (state: StarDerState<A::State>) {
        let state = Star(self.0).der_start(v);
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &Vec<T>, state: &mut StarDerState<A::State>) -> (next: Option<u8>) {
        let next = Star(self.0).der_next(v, state);
        next
    }
}

impl<F> DerState for ImplicitlyTaggedFmt<F> where F: Retaggable, F::Retagged: DerState {
    type State = <F::Retagged as DerState>::State;
}

impl<F, T> DerOrd<T> for ImplicitlyTaggedFmt<F> where
    T: DeepView + ?Sized,
    F: Retaggable,
    F::Retagged: DerOrd<T>,
 {
    proof fn lemma_der_serialize_len(&self, value: T::V) {
        self.1.spec_retagged(self.0).lemma_der_serialize_len(value);
    }

    open spec fn der_remaining(&self, value: T::V, state: <F::Retagged as DerState>::State) -> Seq<
        u8,
    > {
        self.1.spec_retagged(self.0).der_remaining(value, state)
    }

    open spec fn der_state_valid(
        &self,
        value: T::V,
        state: <F::Retagged as DerState>::State,
    ) -> bool {
        self.1.spec_retagged(self.0).der_state_valid(value, state)
    }

    fn der_start(&self, v: &T) -> (state: <F::Retagged as DerState>::State) {
        let retagged = self.1.retagged(self.0);
        let state = retagged.der_start(v);
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(&self, v: &T, state: &mut <F::Retagged as DerState>::State) -> (next: Option<u8>) {
        let retagged = self.1.retagged(self.0);
        let next = retagged.der_next(v, state);
        next
    }
}

impl<Field: DerState, Rest: DerState, Default> DerState for DefaultedFmt<
    Field,
    Default,
    Rest,
    true,
> {
    type State = PairDerState<OptDerState<Field::State>, Rest::State>;
}

impl<Field, Default, Rest, R> DerOrd<(Default, R)> for DefaultedFmt<
    Field,
    Default,
    Rest,
    true,
> where
    Default: DeepViewIdentity + PartialEq + Structural,
    R: DeepView,
    Field: DerOrd<Default>,
    Rest: DerOrd<R>,
 {
    proof fn lemma_der_serialize_len(&self, value: (Default, R::V)) {
        if value.0 != self.1 {
            self.0.lemma_der_serialize_len(value.0);
        }
        self.2.lemma_der_serialize_len(value.1);
    }

    open spec fn der_remaining(
        &self,
        value: (Default, R::V),
        state: PairDerState<OptDerState<Field::State>, Rest::State>,
    ) -> Seq<u8> {
        if state.in_left {
            (match (&value.0, &state.left) {
                (field, OptDerState::Some(inner)) if *field != self.1 => {
                    self.0.der_remaining(*field, *inner)
                },
                (field, OptDerState::None) if *field == self.1 => Seq::empty(),
                _ => Seq::empty(),
            }) + self.2.der_remaining(value.1, state.right)
        } else {
            self.2.der_remaining(value.1, state.right)
        }
    }

    open spec fn der_state_valid(
        &self,
        value: (Default, R::V),
        state: PairDerState<OptDerState<Field::State>, Rest::State>,
    ) -> bool {
        &&& match (&value.0, &state.left) {
            (field, OptDerState::Some(inner)) if *field != self.1 => {
                self.0.der_state_valid(*field, *inner)
            },
            (field, OptDerState::None) if *field == self.1 => true,
            _ => false,
        }
        &&& self.2.der_state_valid(value.1, state.right)
        &&& !state.in_left ==> {
            match (&value.0, &state.left) {
                (field, OptDerState::Some(inner)) if *field != self.1 => {
                    self.0.der_remaining(*field, *inner).len() == 0
                },
                (field, OptDerState::None) if *field == self.1 => true,
                _ => false,
            }
        }
    }

    fn der_start(&self, v: &(Default, R)) -> (state: PairDerState<
        OptDerState<Field::State>,
        Rest::State,
    >) {
        proof {
            v.0.lemma_deep_view_identity();
            self.1.lemma_deep_view_identity();
        }
        let left = if v.0 == self.1 {
            OptDerState::None
        } else {
            OptDerState::Some(self.0.der_start(&v.0))
        };
        let state = PairDerState { left, right: self.2.der_start(&v.1), in_left: true };
        proof {
            good_start!(self, v.deep_view(), state);
        }
        state
    }

    fn der_next(
        &self,
        v: &(Default, R),
        state: &mut PairDerState<OptDerState<Field::State>, Rest::State>,
    ) -> (next: Option<u8>) {
        proof {
            v.0.lemma_deep_view_identity();
            self.1.lemma_deep_view_identity();
        }
        if state.in_left {
            let next = match (&v.0, &mut state.left) {
                (field, OptDerState::Some(inner)) => self.0.der_next(field, inner),
                (_, OptDerState::None) => None,
            };
            match next {
                Some(byte) => {
                    return Some(byte);
                },
                None => state.in_left = false,
            }
        }
        let next = self.2.der_next(&v.1, &mut state.right);
        next
    }
}

} // verus!
