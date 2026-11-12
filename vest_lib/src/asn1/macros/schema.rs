//! Schema construction, outer-tag replacement, and start-domain certificates.
//!
//! `tag(form)` formats store the effective class and number. `starts(domain)`
//! formats instead expose a fixed start domain, without a replaceable outer tag.
//! `lemma_schema_unambiguous` connects each compact domain to the inner format.
// DER and BER share the same tagging interface; only their parser proofs differ.
#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_tag_support {
    (tag($form:ident), $fmt:ident) => {
        $crate::__impl_asn1_nominal_has_start!(tag($form), $fmt);
        $crate::__impl_asn1_nominal_tagged!($fmt);
    };
    (starts($domain:expr), $fmt:ident) => {
        $crate::__impl_asn1_nominal_has_start!(starts($domain), $fmt);
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_inner {
    (tag(primitive), $fmt:ident, $inner:ty) => {
        $crate::__impl_asn1_nominal_inner!(@tagged false, $fmt, $inner);
    };
    (tag(constructed), $fmt:ident, $inner:ty) => {
        $crate::__impl_asn1_nominal_inner!(@tagged true, $fmt, $inner);
    };
    (tag(either), $fmt:ident, $inner:ty) => {
        // BER strings normalize replacement tags to primitive form themselves;
        // their parser accepts both forms. This is not a parser restriction.
        $crate::__impl_asn1_nominal_inner!(@tagged false, $fmt, $inner);
    };
    (@tagged $constructed:literal, $fmt:ident, $inner:ty) => {
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
    (starts($domain:expr), $fmt:ident, $inner:ty) => {
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
macro_rules! __impl_asn1_nominal_has_start {
    (tag(primitive), $fmt:ident) => {
        $crate::__impl_asn1_nominal_has_start!(@certified $fmt, _this,
            $crate::asn1::disjoint::asn1_start_exact_uint(_this.0, false, _this.1));
    };
    (tag(constructed), $fmt:ident) => {
        $crate::__impl_asn1_nominal_has_start!(@certified $fmt, _this,
            $crate::asn1::disjoint::asn1_start_exact_uint(_this.0, true, _this.1));
    };
    (tag(either), $fmt:ident) => {
        $crate::__impl_asn1_nominal_has_start!(@certified $fmt, _this,
            $crate::asn1::disjoint::asn1_start_identity_uint(_this.0, _this.1));
    };
    (starts($domain:expr), $fmt:ident) => {
        $crate::__impl_asn1_nominal_has_start!(@certified $fmt, _this, $domain);
    };
    (@certified $fmt:ident, $this:ident, $domain:expr) => {
        verus! {

        impl $crate::asn1::disjoint::HasAsn1Start for $fmt {
            #[verifier::inline]
            open spec fn asn1_start(&self) -> $crate::asn1::disjoint::Asn1StartDomain {
                let $this = self;
                $domain
            }

            proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
                self.lemma_schema_unambiguous();
                reveal(<$fmt as SpecParser>::spec_parse);
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
