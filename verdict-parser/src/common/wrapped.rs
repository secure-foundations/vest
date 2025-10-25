use super::*;
use std::marker::PhantomData;
use vstd::prelude::*;

verus! {

/// Sometimes it is useful to wrap an existing combinator
/// within a Mapped combinator so that the SpecFrom trait
/// works better
pub type Wrapped<C> = Mapped<C, IdentityMapper<C>>;

pub open spec fn spec_new_wrapped<C: Combinator>(c: C) -> Wrapped<C> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    Mapped {
        inner: c,
        mapper: IdentityMapper(PhantomData),
    }
}

pub fn new_wrapped<C: Combinator>(c: C) -> Wrapped<C> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
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
    type Src = C::SpecResult;
    type Dst = C::SpecResult;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl<C: Combinator> Iso for IdentityMapper<C> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    type Src<'a> = C::Result<'a>;
    type Dst<'a> = C::Result<'a>;

    type SrcOwned = C::Owned;
    type DstOwned = C::Owned;
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
        ::builtin_macros::verus! {
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
        ::builtin_macros::verus! {
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
        ::builtin_macros::verus! {
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
                type SpecResult = $spec_result;

                // $inner_expr.view().spec_parse(s)
                uninterp spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>;

                // $inner_expr.view().spec_parse_wf(s)
                #[verifier::external_body]
                proof fn spec_parse_wf(&self, s: Seq<u8>) {}

                // $inner_expr.view().spec_serialize(v)
                uninterp spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>;
            }

            impl SecureSpecCombinator for $name {
                // $inner_type::is_prefix_secure()
                open spec fn is_prefix_secure() -> bool {
                    true // sound since it's checked in check_valid_inner_combinator
                }

                #[verifier::external_body]
                proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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
            }

            impl Combinator for $name {
                type Result<$lt> = $result;
                type Owned =  $owned;

                uninterp spec fn spec_length(&self) -> Option<usize>;

                #[verifier::external_body]
                fn length(&self) -> Option<usize> {
                    $(let $field_name: $field_type = self.$field_name;)*
                    $inner_expr.length()
                }

                open spec fn parse_requires(&self) -> bool {
                    true // sound since it's checked in check_valid_inner_combinator
                }

                #[verifier::external_body]
                #[inline(always)]
                #[allow(unexpected_cfgs)]
                fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
                    $(let $field_name: $field_type = self.$field_name;)*
                    let res = $inner_expr.parse(s);
                    #[cfg(feature = "trace")] {
                        use verdict_polyfill::*;
                        eprintln_join!("[", stringify!($name), "] ", format_dbg(&res));
                    }
                    res
                }

                open spec fn serialize_requires(&self) -> bool {
                    true // sound since it's checked in check_valid_inner_combinator
                }

                #[verifier::external_body]
                #[inline(always)]
                fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
                    $(let $field_name: $field_type = self.$field_name;)*
                    $inner_expr.serialize(v, data, pos)
                }
            }
        }
    };
}
pub(crate) use wrap_combinator_impls;

}
