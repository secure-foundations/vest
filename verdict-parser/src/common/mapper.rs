use super::*;
use vstd::prelude::*;

verus! {

/// Macro for generating a mapper
/// ```text
/// mapper! {
///     struct ValidityMapper;
///
///     for <A, B>
///     from ValidityFrom where type ValidityFrom = Pair<A, B>;
///     to ValidityPoly where struct ValidityPoly<A, B> {
///         a: A,
///         b: B,
///     }
///
///     forward(s) {
///         ...
///     } [by { ... }]
///
///     backward(s) {
///         ...
///     } [by { ... }]
///
///     spec <SpecTimeValue, SpecTimeValue>
///     exec<'a> <TimeValue<'a>, TimeValue<'a>>
///     owned <TimeValueOwned, TimeValueOwned>
/// }
/// ```
#[allow(unused_macros)]
macro_rules! mapper {
    (
        $vis:vis struct $name:ident $(;)?

        for <$($param:ident),*$(,)?> $(;)?
        from $from:ident where $from_defn:item
        to $to:ident where $to_defn:item

        spec $spec_alias:ident with <$($spec_type:ty),*$(,)?> $(;)?
        exec $exec_alias:ident<$lt:lifetime> with <$($exec_type:ty),*$(,)?> $(;)?
        owned $owned_alias:ident with <$($owned_type:ty),*$(,)?> $(;)?

        forward($forward_var:ident) $forward_body:block $(by $forward_proof:block)?
        backward($backward_var:ident) $backward_body:block $(by $backward_proof:block)?
    ) => {
        ::builtin_macros::verus! {
            #[derive(Debug, View, PolyfillClone)]
            $to_defn

            pub type $spec_alias = $to<$($spec_type),*>;
            pub type $exec_alias<$lt> = $to<$($exec_type),*>;
            pub type $owned_alias = $to<$($owned_type),*>;

            $from_defn

            mapper_from_impls!(
                $from, $to, <$($param),*>,
                $forward_var, $forward_body,
                $backward_var, $backward_body
            );

            mapper_iso_impls!(
                $vis, $name, $from, $to,
                $forward_var, { $($forward_proof)? },
                $backward_var, { $($backward_proof)? },
                <$($spec_type),*>,
                <$lt> <$($exec_type),*>,
                <$($owned_type),*>
            );
        }
    };
}
pub(crate) use mapper;

#[allow(unused_macros)]
macro_rules! mapper_from_impls {
    (
        $from:ident, $to:ident, <$($param:ident),*>,
        $forward_var:ident, $forward_body:block,
        $backward_var:ident, $backward_body:block
    ) => {
        ::builtin_macros::verus! {
            impl<$($param),*> SpecFrom<$from<$($param),*>> for $to<$($param),*> {
                closed spec fn spec_from($forward_var: $from<$($param),*>) -> Self
                    $forward_body
            }

            impl<$($param),*> SpecFrom<$to<$($param),*>> for $from<$($param),*> {
                closed spec fn spec_from($backward_var: $to<$($param),*>) -> Self
                    $backward_body
            }

            impl<$($param: View),*> From<$from<$($param),*>> for $to<$($param),*> {
                #[inline(always)]
                fn ex_from($forward_var: $from<$($param),*>) -> Self
                    $forward_body
            }

            impl<$($param: View),*> From<$to<$($param),*>> for $from<$($param),*> {
                #[inline(always)]
                fn ex_from($backward_var: $to<$($param),*>) -> Self
                    $backward_body
            }
        }
    };
}
pub(crate) use mapper_from_impls;

#[allow(unused_macros)]
macro_rules! mapper_iso_impls {
    (
        $vis:vis, $name:ident, $from:ident, $to:ident,
        $forward_var:ident, $forward_proof:block,
        $backward_var:ident, $backward_proof:block,
        <$($spec_type:ty),*>,
        <$lt:lifetime> <$($exec_type:ty),*>,
        <$($owned_type:ty),*>
    ) => {
        ::builtin_macros::verus! {
            #[derive(Debug, View)]
            $vis struct $name;

            impl SpecIso for $name {
                type Src = $from<$($spec_type),*>;
                type Dst = $to<$($spec_type),*>;

                proof fn spec_iso($forward_var: Self::Src) $forward_proof
                proof fn spec_iso_rev($backward_var: Self::Dst) $backward_proof
            }

            impl Iso for $name {
                type Src<$lt> = $from<$($exec_type),*>;
                type Dst<$lt> = $to<$($exec_type),*>;

                type SrcOwned = $from<$($owned_type),*>;
                type DstOwned = $to<$($owned_type),*>;
            }
        }
    }
}
pub(crate) use mapper_iso_impls;

}
