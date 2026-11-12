//! Executable delegation. Normalize ownership once; all four APIs share the same proof bodies.
//!
//! Only mapped BER entry points request the wire-parser hide. It targets the
//! closure-backed wire mapper, not the generated structural `BiMap` or a child
//! nominal parser. A broader hide regresses depth and CMS verification.
#[doc(hidden)]
#[macro_export]
macro_rules! __impl_asn1_nominal_exec {
    // Mappers are a marker here: their types are used by the proof macros, not by these APIs.
    (borrowed, $fmt:ident, $value:ident, $_forward:ty, $_reverse:ty) => {
        $crate::__impl_asn1_nominal_exec!(@impl ['i] input('i), $fmt, $value<'i>,
            $crate::combinators::Mapped<_, $crate::combinators::mapped::spec::FnSpecMapper<_, _>>);
    };
    (borrowed, $fmt:ident, $value:ident) => {
        $crate::__impl_asn1_nominal_exec!(@impl ['i] input('i), $fmt, $value<'i>);
    };
    (owned, $fmt:ident, $value:ty, $_forward:ty, $_reverse:ty) => {
        $crate::__impl_asn1_nominal_exec!(@impl [] input('i), $fmt, $value,
            $crate::combinators::Mapped<_, $crate::combinators::mapped::spec::FnSpecMapper<_, _>>);
    };
    (owned, $fmt:ident, $value:ty) => {
        $crate::__impl_asn1_nominal_exec!(@impl [] input('i), $fmt, $value);
    };
    // [value lifetime] is empty for owned values. Parsing always has an input lifetime.
    (@impl [$($value_lt:lifetime)?] input($input_lt:lifetime), $fmt:ident, $value:ty $(, $wire_parser:ty)?) => {
        verus! {

        impl<$input_lt> Parser<&$input_lt [u8]> for $fmt {
            type PT = $value;

            fn min_byte_len(&self) -> usize {
                <_ as Parser<&$input_lt [u8]>>::min_byte_len(&self.exec_inner())
            }

            fn parse(&self, ibuf: &&$input_lt [u8]) -> (result: PResult<Self::PT>) {
                $(hide(<$wire_parser as SpecParser>::spec_parse);)?
                let inner = self.exec_inner();
                proof {
                    assert(self.spec_parse(ibuf@) == inner.spec_parse(ibuf@)) by {
                        reveal(<$fmt as SpecParser>::spec_parse);
                    }
                }
                inner.parse(ibuf)
            }
        }

        impl<$($value_lt,)? Output: OutputBuf> Serializer<Output, $value> for $fmt {
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

        impl$(<$value_lt>)? Prepare<$value> for $fmt {
            fn prepare(&self, value: &$value) -> (result: Result<usize, PreSerializeError>) {
                proof {
                    reveal(<$fmt as Consistency>::consistent);
                    reveal(<$fmt as SpecByteLen>::byte_len);
                }
                let inner = self.exec_inner();
                inner.prepare(value)
            }
        }

        impl$(<$value_lt>)? ByteLen<$value> for $fmt {
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
