//! Allocation-free DER ordering, delegated to the inner format's cursor.
//!
//! Borrowed and owned values differ only in the impl lifetime. Only the reverse
//! mapper is revealed: ordering observes serialization, never parsing.
#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_der_ord {
    (borrowed, $fmt:ident, $inner:ty, $spec:ty, $value:ident $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_der_ord!(@impl ['i], $fmt, $inner, $spec, $value<'i> $(, $forward, $reverse)?);
    };
    (owned, $fmt:ident, $inner:ty, $spec:ty, $value:ty $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_der_ord!(@impl [], $fmt, $inner, $spec, $value $(, $forward, $reverse)?);
    };
    // [value lifetime] is empty for owned values; the delegated cursor is unchanged.
    (@impl [$($value_lt:lifetime)?], $fmt:ident, $inner:ty, $spec:ty, $value:ty $(, $forward:ty, $reverse:ty)?) => {
        verus! {

        impl DerState for $fmt {
            type State = <$inner as DerState>::State;
        }

        impl$(<$value_lt>)? DerOrd<$value> for $fmt {
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
