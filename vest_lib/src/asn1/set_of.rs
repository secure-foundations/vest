//! ASN.1 DER `SET OF` contents.
//!
//! The enclosing universal tag and DER length are supplied by [`ASN1Fmt`](crate::asn1::ASN1Fmt). Elements are
//! ordered by their complete encodings, as required by X.690 §11.6.
use super::DerOrd;
use crate::combinators::{star::spec::*, Star};
use crate::core::exec::output::*;
use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
        serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
        ParseError,
    },
    proof::*,
    spec::*,
};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::{prelude::*, relations::*};
use OutputBuf;

verus! {

/// DER `SET OF` contents whose elements are encoded by `C`.
///
/// `C` must encode a complete DER element, including its tag and length. The parsed value is a
/// `Vec<C::PT>` in canonical DER order. Duplicate encodings are permitted.
#[derive(Copy)]
pub struct SetOfFmt<C>(pub C);

impl<C: Clone> Clone for SetOfFmt<C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(C::clone, (&self.0,), cloned.0),
    {
        SetOfFmt(self.0.clone())
    }
}

/// The byte used at `i` when comparing DER encodings. X.690 §11.6 logically
/// pads the shorter encoding with zero octets at its trailing end.
pub open spec fn der_octet_at(bytes: Seq<u8>, i: nat) -> u8 {
    if i < bytes.len() {
        bytes[i as int]
    } else {
        0u8
    }
}

pub open spec fn der_octets_drop_head(bytes: Seq<u8>) -> Seq<u8> {
    if bytes.len() == 0 {
        bytes
    } else {
        bytes.skip(1)
    }
}

/// Whether complete element encodings are in nondecreasing DER order.
/// Uses the encoded-component ordering from X.690 §11.6.
pub open spec fn der_octets_leq(a: Seq<u8>, b: Seq<u8>) -> bool
    decreases a.len() + b.len(),
{
    if a.len() == 0 && b.len() == 0 {
        true
    } else {
        let left = der_octet_at(a, 0);
        let right = der_octet_at(b, 0);
        ||| left < right
        ||| (left == right && der_octets_leq(der_octets_drop_head(a), der_octets_drop_head(b)))
    }
}

pub open spec fn der_encodings_sorted(encodings: Seq<Seq<u8>>) -> bool {
    sorted_by(encodings, |a: Seq<u8>, b: Seq<u8>| der_octets_leq(a, b))
}

/// Whether values are in the canonical order required by DER `SET OF`.
pub open spec fn set_of_values_sorted<C: SpecSerializer>(inner: C, values: Seq<C::SVal>) -> bool {
    der_encodings_sorted(values.map_values(|v: C::SVal| inner.spec_serialize(v)))
}

/// Expose the one-octet transition used by executable DER cursors.
pub proof fn lemma_der_octets_leq_step(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() > 0 || b.len() > 0,
    ensures
        der_octet_at(a, 0) < der_octet_at(b, 0) ==> der_octets_leq(a, b),
        der_octet_at(a, 0) > der_octet_at(b, 0) ==> !der_octets_leq(a, b),
        der_octet_at(a, 0) == der_octet_at(b, 0) ==> {
            der_octets_leq(a, b) == der_octets_leq(der_octets_drop_head(a), der_octets_drop_head(b))
        },
{
}

/// Padded DER octet ordering is transitive.
pub proof fn lemma_der_octets_leq_transitive(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        der_octets_leq(a, b),
        der_octets_leq(b, c),
    ensures
        der_octets_leq(a, c),
    decreases a.len() + b.len() + c.len(),
{
    if a.len() > 0 || b.len() > 0 || c.len() > 0 {
        if a.len() > 0 || b.len() > 0 {
            lemma_der_octets_leq_step(a, b);
        }
        if b.len() > 0 || c.len() > 0 {
            lemma_der_octets_leq_step(b, c);
        }
        if a.len() > 0 || c.len() > 0 {
            lemma_der_octets_leq_step(a, c);
        }
        let ai = der_octet_at(a, 0);
        let bi = der_octet_at(b, 0);
        let ci = der_octet_at(c, 0);
        if ai == bi && bi == ci {
            lemma_der_octets_leq_transitive(
                der_octets_drop_head(a),
                der_octets_drop_head(b),
                der_octets_drop_head(c),
            );
        }
    }
}

proof fn lemma_sorted_by_index<T>(values: Seq<T>, leq: spec_fn(T, T) -> bool, i: int, j: int)
    requires
        sorted_by(values, leq),
        0 <= i < j < values.len(),
    ensures
        leq(values[i], values[j]),
{
}

pub proof fn lemma_der_encodings_sorted_index(encodings: Seq<Seq<u8>>, i: int, j: int)
    requires
        der_encodings_sorted(encodings),
        0 <= i < j < encodings.len(),
    ensures
        der_octets_leq(encodings[i], encodings[j]),
{
    lemma_sorted_by_index(encodings, |a: Seq<u8>, b: Seq<u8>| der_octets_leq(a, b), i, j);
}

pub proof fn lemma_der_encodings_sorted_take(encodings: Seq<Seq<u8>>, n: int)
    requires
        der_encodings_sorted(encodings),
        0 <= n <= encodings.len(),
    ensures
        der_encodings_sorted(encodings.take(n)),
{
    assert forall|i: int, j: int|
        0 <= i < j < encodings.take(n).len() implies #[trigger] der_octets_leq(
        encodings.take(n)[i],
        encodings.take(n)[j],
    ) by {
        lemma_der_encodings_sorted_index(encodings, i, j);
    }
}

/// Appending an encoding to a sorted prefix preserves sortedness exactly when it follows the
/// previous last encoding. This uses transitivity of padded DER ordering, so callers only need an
/// adjacent comparison.
pub proof fn lemma_der_encodings_sorted_push(encodings: Seq<Seq<u8>>, current: Seq<u8>)
    requires
        der_encodings_sorted(encodings),
    ensures
        der_encodings_sorted(encodings.push(current)) <==> (encodings.len() == 0 || der_octets_leq(
            encodings.last(),
            current,
        )),
{
    let extended = encodings.push(current);
    if encodings.len() > 0 {
        if der_octets_leq(encodings.last(), current) {
            assert forall|i: int, j: int|
                0 <= i < j < extended.len() implies #[trigger] der_octets_leq(
                extended[i],
                extended[j],
            ) by {
                if j < encodings.len() {
                    lemma_der_encodings_sorted_index(encodings, i, j);
                } else if i < encodings.len() - 1 {
                    lemma_der_encodings_sorted_index(encodings, i, encodings.len() as int - 1);
                    lemma_der_octets_leq_transitive(encodings[i], encodings.last(), current);
                }
            }
        } else {
            assert(!der_encodings_sorted(extended)) by {
                if der_encodings_sorted(extended) {
                    lemma_der_encodings_sorted_index(
                        extended,
                        encodings.len() as int - 1,
                        encodings.len() as int,
                    );
                }
            }
        }
    }
}

impl<C: SpecParser> SetOfFmt<C> {
    /// Parses all remaining elements while maintaining a canonically sorted encoding prefix.
    pub open spec fn parse_ordered(&self, ibuf: Seq<u8>, previous: Seq<Seq<u8>>) -> Option<
        Seq<C::PVal>,
    >
        decreases ibuf.len(),
    {
        if !der_encodings_sorted(previous) {
            None
        } else if ibuf.len() == 0 {
            Some(Seq::empty())
        } else {
            match self.0.spec_parse(ibuf) {
                Some((n, v)) if 0 < n <= ibuf.len() && der_encodings_sorted(
                    previous.push(ibuf.take(n)),
                ) => {
                    match self.parse_ordered(ibuf.skip(n), previous.push(ibuf.take(n))) {
                        Some(values) => Some(seq![v] + values),
                        None => None,
                    }
                },
                _ => None,
            }
        }
    }
}

impl<C: SoundParser> SetOfFmt<C> {
    proof fn lemma_parse_ordered_byte_len(&self, ibuf: Seq<u8>, previous: Seq<Seq<u8>>)
        requires
            self.0.sound_inv(),
            der_encodings_sorted(previous),
        ensures
            self.parse_ordered(ibuf, previous) matches Some(values) ==> {
                ibuf.len() == Star(self.0).byte_len(values)
            },
        decreases ibuf.len(),
    {
        reveal(<Star<_> as SpecByteLen>::byte_len);

        if ibuf.len() > 0 {
            match self.0.spec_parse(ibuf) {
                Some((n, value)) if 0 < n <= ibuf.len() && der_encodings_sorted(
                    previous.push(ibuf.take(n)),
                ) => {
                    self.0.lemma_parse_sound_consumption(ibuf);
                    self.lemma_parse_ordered_byte_len(ibuf.skip(n), previous.push(ibuf.take(n)));

                    if let Some(rest_values) = self.parse_ordered(
                        ibuf.skip(n),
                        previous.push(ibuf.take(n)),
                    ) {
                        Star(self.0).lemma_byte_len_cons(value, rest_values);
                    }
                },
                _ => {},
            }
        }
    }
}

impl<C: SoundParser + PSRoundTrip> SetOfFmt<C> {
    proof fn lemma_parse_ordered_consistent(&self, ibuf: Seq<u8>, previous: Seq<Seq<u8>>)
        requires
            self.0.sound_inv(),
            self.0.ps_roundtrip_inv(),
            der_encodings_sorted(previous),
        ensures
            self.parse_ordered(ibuf, previous) matches Some(values) ==> {
                &&& Star(self.0).consistent(values)
                &&& der_encodings_sorted(
                    previous + values.map_values(|v: C::PVal| self.0.spec_serialize(v)),
                )
            },
        decreases ibuf.len(),
    {
        reveal(<Star<_> as Consistency>::consistent);
        broadcast use vstd::seq::group_seq_axioms;

        if ibuf.len() > 0 {
            match self.0.spec_parse(ibuf) {
                Some((n, value)) if 0 < n <= ibuf.len() && der_encodings_sorted(
                    previous.push(ibuf.take(n)),
                ) => {
                    self.0.lemma_parse_sound_value(ibuf);
                    self.0.theorem_parse_serialize_roundtrip(ibuf);
                    self.lemma_parse_ordered_consistent(ibuf.skip(n), previous.push(ibuf.take(n)));

                    if let Some(rest_values) = self.parse_ordered(
                        ibuf.skip(n),
                        previous.push(ibuf.take(n)),
                    ) {
                        let values = seq![value] + rest_values;
                        let serialize = |v: C::PVal| self.0.spec_serialize(v);
                        assert(values.map_values(serialize) == seq![ibuf.take(n)]
                            + rest_values.map_values(serialize));
                        assert(previous + values.map_values(serialize) == previous.push(
                            ibuf.take(n),
                        ) + rest_values.map_values(serialize));
                    }
                },
                _ => {},
            }
        }
    }
}

impl<C: NonMalleable> SetOfFmt<C> {
    proof fn lemma_parse_ordered_non_malleable(
        &self,
        buf1: Seq<u8>,
        previous1: Seq<Seq<u8>>,
        buf2: Seq<u8>,
        previous2: Seq<Seq<u8>>,
    )
        requires
            self.0.nonmal_inv(),
            self.0.safe_inv(),
            der_encodings_sorted(previous1),
            der_encodings_sorted(previous2),
        ensures
            self.parse_ordered(buf1, previous1) matches Some(values1) ==> self.parse_ordered(
                buf2,
                previous2,
            ) matches Some(values2) ==> values1 == values2 ==> buf1 == buf2,
        decreases buf1.len(),
    {
        broadcast use vstd::seq_lib::group_seq_properties;

        if let Some(values1) = self.parse_ordered(buf1, previous1) {
            if let Some(values2) = self.parse_ordered(buf2, previous2) {
                if values1 == values2 && values1.len() > 0 {
                    let (n1, value1) = self.0.spec_parse(buf1)->0;
                    let (n2, value2) = self.0.spec_parse(buf2)->0;
                    let rest1 = self.parse_ordered(buf1.skip(n1), previous1.push(buf1.take(n1)))->0;
                    let rest2 = self.parse_ordered(buf2.skip(n2), previous2.push(buf2.take(n2)))->0;

                    assert(value1 == value2) by {
                        assert(value1 == values1[0]);
                        assert(value2 == values2[0]);
                    }
                    assert(rest1 == rest2) by {
                        assert(rest1 == values1.skip(1));
                        assert(rest2 == values2.skip(1));
                    }

                    self.0.lemma_parse_non_malleable(buf1, buf2);
                    self.lemma_parse_ordered_non_malleable(
                        buf1.skip(n1),
                        previous1.push(buf1.take(n1)),
                        buf2.skip(n2),
                        previous2.push(buf2.take(n2)),
                    );
                    assert(buf1 == buf1.take(n1) + buf1.skip(n1));
                    assert(buf2 == buf2.take(n2) + buf2.skip(n2));
                }
            }
        }
    }
}

impl<C> SetOfFmt<C> where
    C: SPRoundTripDps + NonTailFmt + EquivSerializersGeneral + Productive,
    C: SpecSerializer<SVal = C::T>,
 {
    proof fn lemma_serialize_parse_ordered(&self, values: Seq<C::T>, previous: Seq<Seq<u8>>)
        requires
            self.0.unambiguous(),
            self.0.serialize_dps_inv(),
            self.0.equiv_general_inv(),
            self.0.safe_inv(),
            self.0.productive_inv(),
            Star(self.0).consistent(values),
            der_encodings_sorted(previous + values.map_values(|v: C::T| self.0.spec_serialize(v))),
        ensures
            self.parse_ordered(Star(self.0).spec_serialize_dps(values, Seq::empty()), previous)
                == Some(values),
        decreases values.len(),
    {
        reveal(<Star<_> as Consistency>::consistent);
        reveal(<Star<_> as SpecSerializerDps>::spec_serialize_dps);
        broadcast use vstd::seq::group_seq_axioms;

        let encodings = values.map_values(|v: C::T| self.0.spec_serialize(v));
        lemma_der_encodings_sorted_take(previous + encodings, previous.len() as int);
        assert((previous + encodings).take(previous.len() as int) == previous);
        assert(der_encodings_sorted(previous));
        if values.len() > 0 {
            let value = values[0];
            let rest = values.skip(1);
            let rest_buf = Star(self.0).spec_serialize_dps(rest, Seq::empty());
            let serialized = Star(self.0).spec_serialize_dps(values, Seq::empty());
            let n = self.0.byte_len(value) as int;

            assert(values == seq![value] + rest);
            assert(encodings == seq![self.0.spec_serialize(value)] + rest.map_values(
                |v: C::T| self.0.spec_serialize(v),
            ));
            assert(serialized == self.0.spec_serialize_dps(value, rest_buf));
            self.0.theorem_serialize_dps_parse_roundtrip(value, rest_buf);
            self.0.lemma_serialize_dps_prepend(value, rest_buf);
            self.0.lemma_serialize_dps_len(value, rest_buf);
            self.0.lemma_serialize_equiv(value, rest_buf);
            self.0.lemma_productive(serialized);
            assert(serialized.take(n) == self.0.spec_serialize(value));
            assert(serialized.skip(n) == rest_buf);

            lemma_der_encodings_sorted_take(previous + encodings, previous.len() as int + 1);
            assert((previous + encodings).take(previous.len() as int + 1) == previous.push(
                self.0.spec_serialize(value),
            ));
            assert(previous.push(self.0.spec_serialize(value)) + rest.map_values(
                |v: C::T| self.0.spec_serialize(v),
            ) == previous + encodings);

            self.lemma_serialize_parse_ordered(rest, previous.push(self.0.spec_serialize(value)));
        }
    }
}

mod derived_specs {
    use super::*;

    impl<C: SpecParser> SpecParser for SetOfFmt<C> {
        type PVal = Seq<C::PVal>;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            match self.parse_ordered(ibuf, Seq::empty()) {
                Some(values) => Some((ibuf.len() as int, values)),
                _ => None,
            }
        }
    }

    impl<C> Consistency for SetOfFmt<C> where C: Consistency + SpecSerializer<SVal = C::Val> {
        type Val = Seq<C::Val>;

        open spec fn consistent(&self, values: Self::Val) -> bool {
            &&& Star(self.0).consistent(values)
            &&& set_of_values_sorted(self.0, values)
        }
    }

    impl<C: SpecSerializerDps> SpecSerializerDps for SetOfFmt<C> {
        type SValue = Seq<C::SValue>;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, _obuf: Seq<u8>) -> Seq<u8> {
            Star(self.0).spec_serialize_dps(v, Seq::empty())
        }
    }

    impl<C: SpecSerializer> SpecSerializer for SetOfFmt<C> {
        type SVal = Seq<C::SVal>;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Star(self.0).spec_serialize(v)
        }
    }

    impl<C: SpecByteLen> SpecByteLen for SetOfFmt<C> {
        type T = Seq<C::T>;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Star(self.0).byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<C: SafeParser> SafeParser for SetOfFmt<C> {
        open spec fn safe_inv(&self) -> bool {
            self.0.safe_inv()
        }

        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<SetOfFmt<_> as SpecParser>::spec_parse);
        }
    }

    impl<C: SoundParser + PSRoundTrip> SoundParser for SetOfFmt<C> {
        open spec fn sound_inv(&self) -> bool {
            self.0.sound_inv() && self.0.ps_roundtrip_inv()
        }

        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<SetOfFmt<_> as SpecParser>::spec_parse);
            reveal(<SetOfFmt<_> as SpecByteLen>::byte_len);
            self.lemma_parse_ordered_byte_len(ibuf, Seq::empty());
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<SetOfFmt<_> as SpecParser>::spec_parse);
            reveal(<SetOfFmt<_> as Consistency>::consistent);
            self.lemma_parse_ordered_consistent(ibuf, Seq::empty());
        }
    }

    impl<C: NonMalleable> NonMalleable for SetOfFmt<C> {
        open spec fn nonmal_inv(&self) -> bool {
            self.0.nonmal_inv() && self.0.safe_inv()
        }

        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<SetOfFmt<_> as SpecParser>::spec_parse);
            self.lemma_parse_ordered_non_malleable(buf1, Seq::empty(), buf2, Seq::empty());
        }
    }

    impl<C: SafeParser> Productive for SetOfFmt<C> {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, _ibuf: Seq<u8>) {
        }
    }

    impl<C: GoodSerializer> GoodSerializer for SetOfFmt<C> {
        open spec fn serialize_inv(&self) -> bool {
            self.0.serialize_inv()
        }

        proof fn lemma_serialize_len(&self, values: Self::SVal) {
            reveal(<SetOfFmt<_> as SpecSerializer>::spec_serialize);
            reveal(<SetOfFmt<_> as SpecByteLen>::byte_len);
            reveal(<Star<_> as SpecSerializer>::spec_serialize);
            reveal(<Star<_> as SpecByteLen>::byte_len);
            Star(self.0).lemma_serialize_len(values);
        }
    }

    impl<C: EquivSerializersGeneral> EquivSerializers for SetOfFmt<C> {
        open spec fn equiv_inv(&self) -> bool {
            self.0.equiv_general_inv()
        }

        proof fn lemma_serialize_equiv_on_empty(&self, values: Self::SVal) {
            reveal(<SetOfFmt<_> as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SetOfFmt<_> as SpecSerializer>::spec_serialize);
            reveal(<Star<_> as SpecSerializer>::spec_serialize);
            Star(self.0).lemma_serialize_equiv_on_empty(values);
        }
    }

    impl<C> SPRoundTripDps for SetOfFmt<C> where
        C: SPRoundTripDps + NonTailFmt + EquivSerializersGeneral + Productive,
        C: SpecSerializer<SVal = C::T>,
     {
        open spec fn unambiguous(&self) -> bool {
            &&& self.0.unambiguous()
            &&& self.0.serialize_dps_inv()
            &&& self.0.equiv_general_inv()
            &&& self.0.safe_inv()
            &&& self.0.productive_inv()
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, values: Self::T, _obuf: Seq<u8>) {
            reveal(<SetOfFmt<_> as Consistency>::consistent);
            reveal(<SetOfFmt<_> as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SetOfFmt<_> as SpecParser>::spec_parse);
            reveal(<SetOfFmt<_> as SpecByteLen>::byte_len);

            let star = Star(self.0);
            self.lemma_serialize_parse_ordered(values, Seq::empty());
            star.lemma_serialize_dps_len(values, Seq::empty());
            assert(star.spec_serialize_dps(values, Seq::empty()).len() == star.byte_len(values));
        }
    }

}

/// Executable octet comparison for X.690 §11.6 ordering.
pub fn der_leq(a: &[u8], b: &[u8]) -> (leq: bool)
    ensures
        leq == der_octets_leq(a.deep_view(), b.deep_view()),
{
    let mut left = 0usize;
    let mut right = 0usize;
    assert(a.deep_view().skip(0) == a.deep_view());
    assert(b.deep_view().skip(0) == b.deep_view());
    while left < a.len() || right < b.len()
        invariant
            left <= a.len(),
            right <= b.len(),
            der_octets_leq(a.deep_view(), b.deep_view()) == der_octets_leq(
                a.deep_view().skip(left as int),
                b.deep_view().skip(right as int),
            ),
        decreases a.len() - left + b.len() - right,
    {
        let ghost old_left = a.deep_view().skip(left as int);
        let ghost old_right = b.deep_view().skip(right as int);
        proof {
            lemma_der_octets_leq_step(old_left, old_right);
        }
        let ai = if left < a.len() {
            a[left]
        } else {
            0u8
        };
        let bi = if right < b.len() {
            b[right]
        } else {
            0u8
        };
        if ai < bi {
            return true;
        }
        if ai > bi {
            return false;
        }
        if left < a.len() {
            left += 1;
        }
        if right < b.len() {
            right += 1;
        }
        assert(der_octets_drop_head(old_left) == a.deep_view().skip(left as int));
        assert(der_octets_drop_head(old_right) == b.deep_view().skip(right as int));
    }
    true
}

#[cfg(feature = "alloc")]
impl<'i, C> Parser<&'i [u8]> for SetOfFmt<C> where
    C: Parser<&'i [u8]> + SafeParser + Productive + Copy,
 {
    type PT = Vec<C::PT>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.0.productive_inv()
    }

    fn parse(&self, ibuf: &&'i [u8]) -> (r: PResult<Self::PT>) {
        reveal(<SetOfFmt<_> as SpecParser>::spec_parse);
        broadcast use vstd::seq::group_seq_axioms;

        let _len = ibuf.len();
        let mut consumed = 0usize;
        let mut rest = *ibuf;
        let mut values = Vec::new();
        let mut encodings = Vec::new();

        assert(values.deep_view() == Seq::empty());
        assert(encodings.deep_view() == Seq::empty());

        while rest.len() > 0
            invariant
                self.exec_inv(),
                consumed + rest@.len() == _len,
                values.len() == encodings.len(),
                der_encodings_sorted(encodings.deep_view()),
                self.parse_ordered(rest@, encodings.deep_view()) matches Some(suffix)
                    ==> self.spec_parse(ibuf@) == Some((_len as int, values.deep_view() + suffix)),
                self.parse_ordered(rest@, encodings.deep_view()) is None ==> self.spec_parse(
                    ibuf@,
                ) is None,
            decreases rest.len(),
        {
            broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

            let (n, value): (usize, C::PT) = self.0.parse(&rest)?;
            proof {
                self.0.lemma_productive(rest@);
            }
            let encoding = &rest[0..n];

            proof {
                assert(encoding.deep_view() == rest@.take(n as int));
                lemma_der_encodings_sorted_push(encodings.deep_view(), encoding.deep_view());
            }
            if encodings.len() > 0 {
                let previous = encodings[encodings.len() - 1];
                if !der_leq(previous, encoding) {
                    return Err(ParseError::non_canonical());
                }
            }
            let ghost old_rest = rest@;
            let ghost old_encodings = encodings.deep_view();
            values.push(value);
            encodings.push(encoding);
            rest = &rest[n..rest.len()];
            consumed += n;

            assert(encodings.deep_view() == old_encodings.push(old_rest.take(n as int)));
        }

        Ok((consumed, values))
    }
}

impl<Output: OutputBuf, C, Elem> Serializer<Output, [Elem]> for SetOfFmt<C> where
    Elem: DeepView,
    C: SpecCombinator<T = <Elem as DeepView>::V> + Serializer<Output, Elem> + Copy,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &[Elem], obuf: &mut Output) {
        Star(self.0).serialize_into(v, obuf)
    }
}

impl<C, Elem> ByteLen<[Elem]> for SetOfFmt<C> where
    C: SpecByteLen<T = <Elem as DeepView>::V> + ByteLen<Elem> + Copy,
    Elem: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &[Elem]) -> (len: usize) {
        Star(self.0).length(v)
    }
}

impl<C, Elem> Prepare<[Elem]> for SetOfFmt<C> where
    Elem: DeepView,
    C: SpecCombinator<T = <Elem as DeepView>::V> + Prepare<Elem> + DerOrd<Elem> + Copy,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, values: &[Elem]) -> (checked: Result<usize, PreSerializeError>) {
        reveal(<Star<_> as Consistency>::consistent);
        let total = Star(self.0).prepare(values)?;

        for i in 0..values.len()
            invariant
                <Self as Prepare<[Elem]>>::exec_inv(self),
                forall|k: int|
                    0 <= k < values.deep_view().len() ==> self.0.consistent(
                        #[trigger] values.deep_view()[k],
                    ),
                total == Star(self.0).byte_len(values.deep_view()),
                set_of_values_sorted(self.0, values.deep_view().take(i as int)),
        {
            if i > 0 {
                assert(self.0.consistent(values.deep_view()[i as int - 1]));
                assert(self.0.consistent(values.deep_view()[i as int]));
                if !self.0.der_leq(&values[i - 1], &values[i]) {
                    return Err(
                        PreSerializeError::custom("SET OF elements are not in canonical DER order"),
                    );
                }
            }
            proof {
                let vs = values.deep_view();
                let serialize = |v: C::T| self.0.spec_serialize(v);
                let prefix_encodings = vs.take(i as int).map_values(serialize);
                let current_encoding = serialize(vs[i as int]);
                lemma_der_encodings_sorted_push(prefix_encodings, current_encoding);
                vs.lemma_map_take_succ(serialize, i as int);
            }
        }
        assert(values.deep_view().take(values.deep_view().len() as int) == values.deep_view());

        Ok(total)
    }
}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf, C, Elem> Serializer<Output, Vec<Elem>> for SetOfFmt<C> where
    Elem: DeepView,
    C: SpecCombinator<T = <Elem as DeepView>::V> + Serializer<Output, Elem> + Copy,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, values: &Vec<Elem>, obuf: &mut Output) {
        <Self as Serializer<Output, [Elem]>>::serialize_into(self, values.as_slice(), obuf)
    }
}

#[cfg(feature = "alloc")]
impl<C, Elem> ByteLen<Vec<Elem>> for SetOfFmt<C> where
    C: SpecByteLen<T = <Elem as DeepView>::V> + ByteLen<Elem> + Copy,
    Elem: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, values: &Vec<Elem>) -> (len: usize) {
        <Self as ByteLen<[Elem]>>::length(self, values.as_slice())
    }
}

#[cfg(feature = "alloc")]
impl<C, Elem> Prepare<Vec<Elem>> for SetOfFmt<C> where
    Elem: DeepView,
    C: SpecCombinator<T = <Elem as DeepView>::V> + Prepare<Elem> + DerOrd<Elem> + Copy,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, values: &Vec<Elem>) -> (checked: Result<usize, PreSerializeError>) {
        <Self as Prepare<[Elem]>>::prepare(self, values.as_slice())
    }
}

} // verus!
#[cfg(all(test, feature = "alloc"))]
mod tests {
    use crate::asn1::der::{INTEGER8, SET_OF};
    use crate::core::exec::{Parser, Prepare, SerializerExt};

    #[test]
    fn der_set_of_integer8_roundtrip_and_ordering() {
        let format = SET_OF(INTEGER8);
        let canonical = [0x31, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        let (consumed, values) = format.parse(&&canonical[..]).unwrap();
        assert_eq!(consumed, canonical.len());
        assert_eq!(values, vec![1, 2]);

        assert_eq!(format.prepare(&values), Ok(canonical.len()));
        let mut encoded = vec![0; format.prepare(&values).unwrap()];
        format.serialize(&values, &mut encoded);
        assert_eq!(encoded, canonical);

        let unordered = [0x31, 0x06, 0x02, 0x01, 0x02, 0x02, 0x01, 0x01];
        assert!(format.parse(&&unordered[..]).is_err());
        assert!(format.prepare(&vec![2, 1]).is_err());
    }

    #[test]
    fn der_set_of_allows_duplicate_encodings() {
        let format = SET_OF(INTEGER8);
        let duplicate = [0x31, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x01];
        let (_, values) = format.parse(&&duplicate[..]).unwrap();
        assert_eq!(values, vec![1, 1]);
        assert_eq!(format.prepare(&values), Ok(duplicate.len()));
    }
}
