//! Implementations for generated nominal ASN.1 format types.
//!
//! These macros are exported at the crate root as [`impl_der!`] and [`impl_ber!`]. A generated
//! nominal format supplies a duel spec-exec `schema()` constructor. Tagged formats
//! additionally store their outer tag class and number in tuple fields `0` and `1`; the macros
//! apply that effective tag when constructing the inner format.

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_inner {
    (tagged($constructed:expr), $fmt:ident, $inner:ty) => {
        verus! {

        impl $fmt {
            pub open spec fn spec_inner(&self) -> $inner {
                Self::schema().spec_retagged($crate::asn1::Tag {
                    class: self.0,
                    constructed: $constructed,
                    number: $crate::asn1::tag::tag_num_from_uint(self.1),
                })
            }

            fn exec_inner(&self) -> (fmt: $inner)
                ensures
                    fmt == self.spec_inner(),
            {
                Self::schema().retagged($crate::asn1::Tag {
                    class: self.0,
                    constructed: $constructed,
                    number: $crate::asn1::tag::tag_num_from_uint(self.1),
                })
            }
        }

        } // verus!
    };
    (untagged_start, $fmt:ident, $inner:ty) => {
        $crate::__impl_asn1_nominal_inner!(untagged, $fmt, $inner);
    };
    (untagged, $fmt:ident, $inner:ty) => {
        verus! {

        impl $fmt {
            pub open spec fn spec_inner(&self) -> $inner {
                Self::schema()
            }

            fn exec_inner(&self) -> (fmt: $inner)
                ensures
                    fmt == self.spec_inner(),
            {
                Self::schema()
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_specs_and_proofs {
    ($fmt:ident, $spec:ty $(, $forward:ty, $reverse:ty)?) => {
        verus! {

        impl SpecParser for $fmt {
            type PVal = $spec;

            #[verifier::opaque]
            open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
                self.spec_inner().spec_parse(ibuf)
            }
        }

        impl Consistency for $fmt {
            type Val = $spec;

            #[verifier::opaque]
            open spec fn consistent(&self, value: Self::Val) -> bool {
                self.spec_inner().consistent(value)
            }
        }

        impl SpecSerializerDps for $fmt {
            type SValue = $spec;

            #[verifier::opaque]
            open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
                self.spec_inner().spec_serialize_dps(value, obuf)
            }
        }

        impl SpecSerializer for $fmt {
            type SVal = $spec;

            #[verifier::opaque]
            open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
                self.spec_inner().spec_serialize(value)
            }
        }

        impl SpecByteLen for $fmt {
            type T = $spec;

            #[verifier::opaque]
            open spec fn byte_len(&self, value: Self::T) -> nat {
                self.spec_inner().byte_len(value)
            }
        }

        // The nominal boundary keeps the default `true` invariants. Each proof establishes the
        // concrete inner obligation locally before delegating.
        impl SafeParser for $fmt {
            proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                self.spec_inner().lemma_parse_safe(ibuf);
            }
        }

        impl Productive for $fmt {
            proof fn lemma_productive(&self, input: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                self.spec_inner().lemma_productive(input);
            }
        }

        impl NonTailFmt for $fmt {
            proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, obuf: Seq<u8>) {
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                self.spec_inner().lemma_serialize_dps_prepend(value, obuf);
            }

            proof fn lemma_serialize_dps_len(&self, value: Self::SValue, obuf: Seq<u8>) {
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                reveal(<$fmt as SpecByteLen>::byte_len);
                self.spec_inner().lemma_serialize_dps_len(value, obuf);
            }
        }

        impl GoodSerializer for $fmt {
            proof fn lemma_serialize_len(&self, value: Self::SVal) {
                reveal(<$fmt as SpecSerializer>::spec_serialize);
                reveal(<$fmt as SpecByteLen>::byte_len);
                self.spec_inner().lemma_serialize_len(value);
            }
        }

        impl SPRoundTripDps for $fmt {
            proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
                $(
                    reveal(<$forward as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                    reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                )?
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as Consistency>::consistent);
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                reveal(<$fmt as SpecByteLen>::byte_len);
                broadcast use $crate::combinators::disjoint::disjointness_lemmas;
                broadcast use $crate::asn1::disjoint::asn1_disjointness_lemmas;
                self.spec_inner().theorem_serialize_dps_parse_roundtrip(value, obuf);
            }
        }

        impl EquivSerializersGeneral for $fmt {
            proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
                reveal(<$fmt as SpecSerializer>::spec_serialize);
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                self.spec_inner().lemma_serialize_equiv(value, obuf);
            }
        }

        impl EquivSerializers for $fmt {
            proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
                reveal(<$fmt as SpecSerializer>::spec_serialize);
                reveal(<$fmt as SpecSerializerDps>::spec_serialize_dps);
                self.spec_inner().lemma_serialize_equiv_on_empty(value);
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_exec_borrowed {
    ($fmt:ident, $value:ident) => {
        verus! {

        impl<'i> Parser<&'i [u8]> for $fmt {
            type PT = $value<'i>;

            fn parse(&self, ibuf: &&'i [u8]) -> (result: PResult<Self::PT>) {
                proof {
                    reveal(<$fmt as SpecParser>::spec_parse);
                }
                let inner = self.exec_inner();
                inner.parse(ibuf)
            }
        }

        impl<'i, Output: OutputBuf> Serializer<Output, $value<'i>> for $fmt {
            fn serialize_into(&self, value: &$value<'i>, obuf: &mut Output) {
                proof {
                    reveal(<$fmt as Consistency>::consistent);
                    reveal(<$fmt as SpecSerializer>::spec_serialize);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                }
                let inner = self.exec_inner();
                inner.serialize_into(value, obuf)
            }
        }

        impl<'i> Prepare<$value<'i>> for $fmt {
            fn prepare(&self, value: &$value<'i>) -> (result: Result<usize, PreSerializeError>) {
                proof {
                    reveal(<$fmt as Consistency>::consistent);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                }
                let inner = self.exec_inner();
                inner.prepare(value)
            }
        }

        impl<'i> ByteLen<$value<'i>> for $fmt {
            fn length(&self, value: &$value<'i>) -> (result: usize) {
                proof {
                    reveal(<$fmt as SpecByteLen>::byte_len);
                }
                let inner = self.exec_inner();
                inner.length(value)
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_exec_owned {
    ($fmt:ident, $value:ty) => {
        verus! {

        impl<'i> Parser<&'i [u8]> for $fmt {
            type PT = $value;

            fn parse(&self, ibuf: &&'i [u8]) -> (result: PResult<Self::PT>) {
                proof {
                    reveal(<$fmt as SpecParser>::spec_parse);
                }
                let inner = self.exec_inner();
                inner.parse(ibuf)
            }
        }

        impl<Output: OutputBuf> Serializer<Output, $value> for $fmt {
            fn serialize_into(&self, value: &$value, obuf: &mut Output) {
                proof {
                    reveal(<$fmt as Consistency>::consistent);
                    reveal(<$fmt as SpecSerializer>::spec_serialize);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                }
                let inner = self.exec_inner();
                inner.serialize_into(value, obuf)
            }
        }

        impl Prepare<$value> for $fmt {
            fn prepare(&self, value: &$value) -> (result: Result<usize, PreSerializeError>) {
                proof {
                    reveal(<$fmt as Consistency>::consistent);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                }
                let inner = self.exec_inner();
                inner.prepare(value)
            }
        }

        impl ByteLen<$value> for $fmt {
            fn length(&self, value: &$value) -> (result: usize) {
                proof {
                    reveal(<$fmt as SpecByteLen>::byte_len);
                }
                let inner = self.exec_inner();
                inner.length(value)
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_has_start {
    ($fmt:ident) => {
        verus! {

        impl $crate::asn1::disjoint::HasAsn1Start for $fmt {
            #[verifier::inline]
            open spec fn asn1_start(&self) -> $crate::asn1::disjoint::Asn1StartDomain {
                self.spec_inner().asn1_start()
            }

            proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal($fmt::spec_inner);
                self.spec_inner().lemma_parse_implies_asn1_start(input);
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_tagged {
    ($fmt:ident) => {
        $crate::__impl_asn1_nominal_has_start!($fmt);

        verus! {

        impl Retaggable for $fmt {
            #[verifier::inline]
            open spec fn spec_retagged(&self, tag: Tag) -> Self {
                Self(tag.class, $crate::asn1::tag::tag_num_to_uint(tag.number))
            }

            fn retagged(&self, tag: Tag) -> Self {
                Self(tag.class, $crate::asn1::tag::tag_number_value(tag.number))
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_der_tagged_proofs {
    ($fmt:ident $(, $forward:ty, $reverse:ty)?) => {
        verus! {

        impl $fmt {
            proof fn lemma_successful_parse_inner_invariants(&self, input: Seq<u8>)
                requires
                    self.spec_parse(input) is Some,
                ensures
                    self.spec_inner().safe_inv(),
                    self.spec_inner().sound_inv(),
                    self.spec_inner().nonmal_inv(),
            {
                $(
                    reveal(<$forward as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                    reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                )?
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal($fmt::spec_inner);
                broadcast use $crate::asn1::tag::lemma_tag_wf_implies_tag_consistent;
                self.spec_inner().lemma_parse_implies_asn1_start(input);
                reveal($crate::asn1::disjoint::input_starts_with);
                TagFmt.lemma_parse_sound_value(input);
            }
        }

        impl SoundParser for $fmt {
            proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as SpecByteLen>::byte_len);
                broadcast use $crate::asn1::tag::lemma_tag_wf_implies_tag_consistent;
                if self.spec_parse(ibuf) is Some {
                    self.lemma_successful_parse_inner_invariants(ibuf);
                    self.spec_inner().lemma_parse_sound_consumption(ibuf);
                }
            }

            proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as Consistency>::consistent);
                broadcast use $crate::asn1::tag::lemma_tag_wf_implies_tag_consistent;
                if self.spec_parse(ibuf) is Some {
                    self.lemma_successful_parse_inner_invariants(ibuf);
                    self.spec_inner().lemma_parse_sound_value(ibuf);
                }
            }
        }

        impl NonMalleable for $fmt {
            proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                broadcast use $crate::asn1::tag::lemma_tag_wf_implies_tag_consistent;
                if self.spec_parse(buf1) is Some && self.spec_parse(buf2) is Some {
                    self.lemma_successful_parse_inner_invariants(buf1);
                    self.spec_inner().lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_der_fixed_proofs {
    ($fmt:ident $(, $forward:ty, $reverse:ty)?) => {
        verus! {

        impl $fmt {
            proof fn lemma_sound_nonmal_inv(&self)
                ensures
                    self.spec_inner().sound_inv(),
                    self.spec_inner().nonmal_inv(),
            {
                $(
                    reveal(<$forward as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                    reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                )?
                broadcast use $crate::asn1::tag::lemma_tag_wf_implies_tag_consistent;
            }
        }

        impl SoundParser for $fmt {
            proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as SpecByteLen>::byte_len);
                self.lemma_sound_nonmal_inv();
                self.spec_inner().lemma_parse_sound_consumption(ibuf);
            }

            proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                reveal(<$fmt as Consistency>::consistent);
                self.lemma_sound_nonmal_inv();
                self.spec_inner().lemma_parse_sound_value(ibuf);
            }
        }

        impl NonMalleable for $fmt {
            proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
                reveal(<$fmt as SpecParser>::spec_parse);
                self.lemma_sound_nonmal_inv();
                self.spec_inner().lemma_parse_non_malleable(buf1, buf2);
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_der_ord_borrowed {
    ($fmt:ident, $inner:ty, $spec:ty, $value:ident $(, $forward:ty, $reverse:ty)?) => {
        verus! {

        impl DerState for $fmt {
            type State = <$inner as DerState>::State;
        }

        impl<'i> DerOrd<$value<'i>> for $fmt {
            proof fn lemma_der_serialize_len(&self, value: $spec) {
                $(
                    reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                )?
                reveal(<$fmt as Consistency>::consistent);
                reveal(<$fmt as SpecSerializer>::spec_serialize);
                reveal(<$fmt as SpecByteLen>::byte_len);
                <$inner as DerOrd<$value<'i>>>::lemma_der_serialize_len(
                    &self.spec_inner(),
                    value,
                );
            }

            open spec fn der_remaining(
                &self,
                value: $spec,
                state: <Self as DerState>::State,
            ) -> Seq<u8> {
                <$inner as DerOrd<$value<'i>>>::der_remaining(&self.spec_inner(), value, state)
            }

            open spec fn der_state_valid(
                &self,
                value: $spec,
                state: <Self as DerState>::State,
            ) -> bool {
                <$inner as DerOrd<$value<'i>>>::der_state_valid(&self.spec_inner(), value, state)
            }

            fn der_start(&self, value: &$value<'i>) -> (state: <Self as DerState>::State) {
                proof {
                    $(
                        reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                    )?
                    reveal(<$fmt as Consistency>::consistent);
                    reveal(<$fmt as SpecSerializer>::spec_serialize);
                }
                let inner = self.exec_inner();
                <$inner as DerOrd<$value<'i>>>::der_start(&inner, value)
            }

            fn der_next(
                &self,
                value: &$value<'i>,
                state: &mut <Self as DerState>::State,
            ) -> (next: Option<u8>) {
                proof {
                    $(
                        reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                    )?
                    reveal(<$fmt as Consistency>::consistent);
                }
                let inner = self.exec_inner();
                <$inner as DerOrd<$value<'i>>>::der_next(&inner, value, state)
            }
        }

        } // verus!
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_der_ord_owned {
    ($fmt:ident, $inner:ty, $spec:ty, $value:ty $(, $forward:ty, $reverse:ty)?) => {
        verus! {

        impl DerState for $fmt {
            type State = <$inner as DerState>::State;
        }

        impl DerOrd<$value> for $fmt {
            proof fn lemma_der_serialize_len(&self, value: $spec) {
                $(
                    reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                )?
                reveal(<$fmt as Consistency>::consistent);
                reveal(<$fmt as SpecSerializer>::spec_serialize);
                reveal(<$fmt as SpecByteLen>::byte_len);
                <$inner as DerOrd<$value>>::lemma_der_serialize_len(&self.spec_inner(), value);
            }

            open spec fn der_remaining(
                &self,
                value: $spec,
                state: <Self as DerState>::State,
            ) -> Seq<u8> {
                <$inner as DerOrd<$value>>::der_remaining(&self.spec_inner(), value, state)
            }

            open spec fn der_state_valid(
                &self,
                value: $spec,
                state: <Self as DerState>::State,
            ) -> bool {
                <$inner as DerOrd<$value>>::der_state_valid(&self.spec_inner(), value, state)
            }

            fn der_start(&self, value: &$value) -> (state: <Self as DerState>::State) {
                proof {
                    $(
                        reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                    )?
                    reveal(<$fmt as Consistency>::consistent);
                    reveal(<$fmt as SpecSerializer>::spec_serialize);
                }
                let inner = self.exec_inner();
                <$inner as DerOrd<$value>>::der_start(&inner, value)
            }

            fn der_next(
                &self,
                value: &$value,
                state: &mut <Self as DerState>::State,
            ) -> (next: Option<u8>) {
                proof {
                    $(
                        reveal(<$reverse as $crate::combinators::mapped::spec::SpecMap>::spec_map);
                    )?
                    reveal(<$fmt as Consistency>::consistent);
                }
                let inner = self.exec_inner();
                <$inner as DerOrd<$value>>::der_next(&inner, value, state)
            }
        }

        } // verus!
    };
}

/// Implements the verified DER traits and executable APIs for a generated nominal format.
#[macro_export]
macro_rules! impl_der {
    ($kind:ident $(($constructed:expr))?, borrowed, $fmt:ident, $inner:ty, $spec:ty, $value:ident $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_inner!($kind $(($constructed))?, $fmt, $inner);
        $crate::__impl_asn1_nominal_specs_and_proofs!($fmt, $spec $(, $forward, $reverse)?);
        $crate::__impl_asn1_nominal_exec_borrowed!($fmt, $value);
        $crate::__impl_asn1_nominal_der_ord_borrowed!($fmt, $inner, $spec, $value $(, $forward, $reverse)?);
        $crate::impl_der!(@kind $kind, $fmt $(, $forward, $reverse)?);
    };
    ($kind:ident $(($constructed:expr))?, owned, $fmt:ident, $inner:ty, $spec:ty, $value:ty $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_inner!($kind $(($constructed))?, $fmt, $inner);
        $crate::__impl_asn1_nominal_specs_and_proofs!($fmt, $spec $(, $forward, $reverse)?);
        $crate::__impl_asn1_nominal_exec_owned!($fmt, $value);
        $crate::__impl_asn1_nominal_der_ord_owned!($fmt, $inner, $spec, $value $(, $forward, $reverse)?);
        $crate::impl_der!(@kind $kind, $fmt $(, $forward, $reverse)?);
    };
    (@kind tagged, $fmt:ident $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_tagged!($fmt);
        $crate::__impl_asn1_nominal_der_tagged_proofs!($fmt $(, $forward, $reverse)?);
    };
    (@kind untagged_start, $fmt:ident $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_has_start!($fmt);
        $crate::__impl_asn1_nominal_der_fixed_proofs!($fmt $(, $forward, $reverse)?);
    };
    (@kind untagged, $fmt:ident $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_der_fixed_proofs!($fmt $(, $forward, $reverse)?);
    };
}

/// Implements the verified BER traits and executable APIs for a generated nominal format.
///
/// BER formats deliberately do not implement `SoundParser`, `NonMalleable`, or DER ordering.
#[macro_export]
macro_rules! impl_ber {
    ($kind:ident $(($constructed:expr))?, borrowed, $fmt:ident, $inner:ty, $spec:ty, $value:ident $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_inner!($kind $(($constructed))?, $fmt, $inner);
        $crate::__impl_asn1_nominal_specs_and_proofs!($fmt, $spec $(, $forward, $reverse)?);
        $crate::__impl_asn1_nominal_exec_borrowed!($fmt, $value);
        $crate::impl_ber!(@kind $kind, $fmt);
    };
    ($kind:ident $(($constructed:expr))?, owned, $fmt:ident, $inner:ty, $spec:ty, $value:ty $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_inner!($kind $(($constructed))?, $fmt, $inner);
        $crate::__impl_asn1_nominal_specs_and_proofs!($fmt, $spec $(, $forward, $reverse)?);
        $crate::__impl_asn1_nominal_exec_owned!($fmt, $value);
        $crate::impl_ber!(@kind $kind, $fmt);
    };
    (@kind tagged, $fmt:ident) => {
        $crate::__impl_asn1_nominal_tagged!($fmt);
    };
    (@kind untagged_start, $fmt:ident) => {
        $crate::__impl_asn1_nominal_has_start!($fmt);
    };
    (@kind untagged, $fmt:ident) => {};
}

// `#[macro_export]` places macros at the crate root. Re-export them here as well so callers can
// discover and import them through `vest_lib2::asn1::macros`.
pub use crate::{impl_ber, impl_der};
