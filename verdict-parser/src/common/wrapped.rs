use super::*;
use std::marker::PhantomData;
use vstd::prelude::*;

verus! {

/// Sometimes it is useful to wrap an existing combinator
/// within a Mapped combinator so that the SpecFrom trait
/// works better
pub type Wrapped<C> = Mapped<C, IdentityMapper<C>>;

pub open spec fn spec_new_wrapped<C: for<'a> Combinator<'a>>(c: C) -> Wrapped<C> where
    C::V: SecureSpecCombinator,
{
    Mapped {
        inner: c,
        mapper: IdentityMapper(PhantomData),
    }
}

pub fn new_wrapped<C: for<'a> Combinator<'a>>(c: C) -> Wrapped<C> where
    C::V: SecureSpecCombinator,
{
    Mapped {
        inner: c,
        mapper: IdentityMapper::new(),
    }
}

/// An identity mapper that does not change the parsed object
/// Used in situations when we need prove U: DisjointFrom<Mapped<...>>
/// in which case we can wrap U in Mapped and use existing impls
#[derive(Debug)]
pub struct IdentityMapper<C>(pub PhantomData<C>);

impl<C: View> View for IdentityMapper<C> {
    type V = IdentityMapper<C::V>;

    open spec fn view(&self) -> Self::V {
        IdentityMapper(PhantomData)
    }
}

impl<C> IdentityMapper<C> {
    pub fn new() -> Self {
        IdentityMapper(PhantomData)
    }
}

impl<C: SpecCombinator> SpecIso for IdentityMapper<C> {
    type Src = C::Type;
    type Dst = C::Type;
}

impl<C: SpecCombinator> SpecIsoProof for IdentityMapper<C> {
    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl<'a, C> Iso<'a> for IdentityMapper<C> where
    C: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <C as View>::V: SecureSpecCombinator,
{
    type Src = <C as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type Dst = <C as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type RefSrc = <C as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
}

/// Wrap a non-parametric combinator in a new unit struct
/// e.g.
/// wrap_combinator! {
///     struct AlgorithmIdentifier: AlgorithmIdentifierInner =
///         Mapped {
///             inner: ASN1(ExplicitTag(TagValue {
///                 class: TagClass::Universal,
///                 form: TagForm::Constructed,
///                 num: 0x10,
///             }, (ASN1(ObjectIdentifier), Tail))),
///             mapper: AlgorithmIdentifierMapper,
///         }
/// }
///
/// TODO: Due to a Verus issue, everything here is unproved
/// NOTE: $inner_expr is used both in exec and spec mode
#[allow(unused_macros)]
macro_rules! wrap_combinator {
    // NOTE: use the other alternative to reduce type checking time
    ($vis:vis struct $name:ident $({ $($field_vis:vis $field_name:ident: $field_type:ty),* $(,)? })?: $inner_type:ty = $inner_expr:expr ;) => {
        wrap_combinator! {
           $vis struct $name $({ $($field_vis $field_name: $field_type),* })?: $inner_type =>
                spec <<$inner_type as View>::V as SpecCombinator>::SpecResult,
                exec<'a> <$inner_type as Combinator>::Result<'a>,
                owned <$inner_type as Combinator>::Owned,
            = $inner_expr;
        }
    };

    ($vis:vis struct $name:ident: $inner_type:ty =>
        spec $spec_result:ty,
        exec<$lt:lifetime> $result:ty,
        owned $owned:ty $(,)?
        = $inner_expr:expr ;) => {
        ::vstd::prelude::verus! {
            #[derive(Debug, View)]
            $vis struct $name;

            wrap_combinator_impls! {
                $vis struct $name {} : $inner_type =>
                    spec $spec_result,
                    exec<$lt> $result,
                    owned $owned
                = $inner_expr;
            }
        }
    };

    ($vis:vis struct $name:ident { $($field_vis:vis $field_name:ident: $field_type:ty),* $(,)? } : $inner_type:ty =>
        spec $spec_result:ty,
        exec<$lt:lifetime> $result:ty,
        owned $owned:ty $(,)?
        = $inner_expr:expr ;) => {
        ::vstd::prelude::verus! {
            #[derive(Debug, View)]
            $vis struct $name { $($field_vis $field_name: $field_type),* }

            wrap_combinator_impls! {
                $vis struct $name { $($field_vis $field_name: $field_type),* } : $inner_type =>
                    spec $spec_result,
                    exec<$lt> $result,
                    owned $owned
                = $inner_expr;
            }
        }
    };
}
pub(crate) use wrap_combinator;

#[allow(unused_macros)]
macro_rules! wrap_combinator_impls {
    ($vis:vis struct $name:ident { $($field_vis:vis $field_name:ident: $field_type:ty),* } : $inner_type:ty =>
        spec $spec_result:ty,
        exec<$lt:lifetime> $result:ty,
        owned $owned:ty $(,)?
        = $inner_expr:expr ;) => {
        ::vstd::prelude::verus! {
            impl $name {
                /// Due to a Verus/SMT instability issue,
                /// specifying the actual definitions of, e.g., spec_parse
                /// results in proof failures in a large number of irrelevant places
                ///
                /// So instead, we just separately check a number of sufficient conditions
                /// for the wrapped combinator in this function
                ///
                /// TODO: remove this once the Verus issue is fixed
                #[allow(dead_code)]
                fn check_valid_inner_combinator() {
                    // Type check
                    #[allow(unused_variables)]
                    let c: $inner_type = $inner_expr;

                    // For future compatibility, check that $inner_expr is also a valid spec expr
                    let ghost _ = $inner_expr.view();

                    // Check that $inner_expr is a Combinator
                    let _ = $inner_expr.length();

                    // The inner combinator has to be prefix secure
                    assert(<<$inner_type as View>::V as SecureSpecCombinator>::is_prefix_secure());

                    // Check that parse_requires and serialize_requires are satisfied
                    assert(c.parse_requires());
                    assert(c.serialize_requires());
                }
            }

            impl SpecCombinator for $name {
                type Type = $spec_result;

                open spec fn wf(&self, v: Self::Type) -> bool {
                    true
                }
                
                open spec fn requires(&self) -> bool {
                    true
                }

                // $inner_expr.view().spec_parse(s)
                uninterp spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>;

                // $inner_expr.view().spec_serialize(v)
                uninterp spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;
            }

            impl SecureSpecCombinator for $name {
                // $inner_type::is_prefix_secure()
                open spec fn is_prefix_secure() -> bool {
                    true // sound since it's checked in check_valid_inner_combinator
                }
                
                spec fn is_productive() -> bool {
                    true
                }

                #[verifier::external_body]
                proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
                    // $inner_expr.view().theorem_serialize_parse_roundtrip(v)
                }

                #[verifier::external_body]
                proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
                    // $inner_expr.view().theorem_parse_serialize_roundtrip(buf)
                }

                #[verifier::external_body]
                proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
                    // $inner_expr.view().lemma_prefix_secure(s1, s2)
                }
                
                #[verifier::external_body]
                proof fn lemma_parse_length(&self, s: Seq<u8>) {}
                
                #[verifier::external_body]
                proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
            }

            impl<$lt> Combinator<$lt, &$lt [u8], Vec<u8>> for $name {
                type Type = $result;
                type SType =  $owned;

                #[verifier::external_body]
                fn length(&self, v: Self::SType) -> usize {
                    $(let $field_name: $field_type = self.$field_name;)*
                    $inner_expr.length(v)
                }

                #[verifier::external_body]
                #[inline(always)]
                #[allow(unexpected_cfgs)]
                fn parse(&self, s: &$lt [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
                    $(let $field_name: $field_type = self.$field_name;)*
                    let res = $inner_expr.parse(s);
                    #[cfg(feature = "trace")] {
                        use verdict_polyfill::*;
                        eprintln_join!("[", stringify!($name), "] ", format_dbg(&res));
                    }
                    res
                }

                #[verifier::external_body]
                #[inline(always)]
                fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
                    $(let $field_name: $field_type = self.$field_name;)*
                    $inner_expr.serialize(v, data, pos)
                }
            }
        }
    };
}
pub(crate) use wrap_combinator_impls;

}
