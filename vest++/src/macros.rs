//! Utility macros.

#[doc(hidden)]
#[macro_export]
macro_rules! __vest_build_tuple_ty {
    ($ty:ty) => { $ty };
    ($ty:ty, $($rest:ty),+) => { ($ty, $crate::__vest_build_tuple_ty!($($rest),+)) };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __vest_build_tuple_pat {
    ($id:ident) => { $id };
    ($id:ident, $($rest:ident),+) => { ($id, $crate::__vest_build_tuple_pat!($($rest),+)) };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __vest_build_tuple_expr {
    ($i:expr, $id:ident) => { $i.$id };
    ($i:expr, $id:ident, $($rest:ident),+) => { ($i.$id, $crate::__vest_build_tuple_expr!($i, $($rest),+)) };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __vest_build_sum_ty {
    ($ty:ty) => { $ty };
    ($ty1:ty, $ty2:ty) => { $crate::combinators::Sum<$ty1, $ty2> };
    ($ty:ty, $($rest:ty),+) => { $crate::combinators::Sum<$ty, $crate::__vest_build_sum_ty!($($rest),+)> };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __vest_build_sum_map {
    ($i:expr, $spec_name:ident, $variant:ident) => {
        $spec_name::$variant($i)
    };
    ($i:expr, $spec_name:ident, $variant:ident, $($rest:ident),+) => {
        match $i {
            $crate::combinators::Sum::Inl(v) => $spec_name::$variant(v),
            $crate::combinators::Sum::Inr(rest) => $crate::__vest_build_sum_map!(rest, $spec_name, $($rest),+),
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __vest_build_sum_map_rev {
    ($i:expr, $spec_name:ident, $variant:ident) => {
        match $i {
            $spec_name::$variant(v) => v,
            _ => ::vstd::prelude::arbitrary(),
        }
    };
    ($i:expr, $spec_name:ident, $variant:ident, $($rest:ident),+) => {
        match $i {
            $spec_name::$variant(v) => $crate::combinators::Sum::Inl(v),
            _ => $crate::combinators::Sum::Inr($crate::__vest_build_sum_map_rev!($i, $spec_name, $($rest),+)),
        }
    };
}

/// Defines paired executable/spec nominal value types and corresponding `DeepView` and `SpecMapper` impls.
///
/// The generated `DeepView` and `SpecMapper` implementations assume the exec and spec fields or
/// variants are aligned by name and order.
#[macro_export]
macro_rules! with_deep_view_and_mapper {
    (
        $(#[$exec_attr:meta])*
        pub struct $exec_name:ident <$lt:lifetime> {
            $(pub $exec_field:ident: $exec_ty:ty,)*
        }

        $(#[$spec_attr:meta])*
        pub struct $spec_name:ident {
            $(pub $spec_field:ident: $spec_ty:ty,)*
        }

        type $inner_name:ident;
        pub struct $mapper_name:ident;
    ) => {
        verus! {
            $(#[$exec_attr])*
            pub struct $exec_name<$lt> {
                $(pub $exec_field: $exec_ty,)*
            }

            $(#[$spec_attr])*
            pub struct $spec_name {
                $(pub $spec_field: $spec_ty,)*
            }

            impl<$lt> ::vstd::prelude::DeepView for $exec_name<$lt> {
                type V = $spec_name;

                open spec fn deep_view(&self) -> Self::V {
                    $spec_name {
                        $($exec_field: self.$exec_field.deep_view(),)*
                    }
                }
            }

            type $inner_name = $crate::__vest_build_tuple_ty!($($spec_ty),*);
            pub struct $mapper_name;

            impl $crate::combinators::mapped::spec::SpecMapper for $mapper_name {
                type In = $inner_name;
                type Out = $spec_name;

                open spec fn spec_map(&self, i: Self::In) -> Self::Out {
                    let $crate::__vest_build_tuple_pat!($($spec_field),*) = i;
                    $spec_name {
                        $($spec_field,)*
                    }
                }

                open spec fn spec_map_rev(&self, i: Self::Out) -> Self::In {
                    $crate::__vest_build_tuple_expr!(i, $($spec_field),*)
                }
            }
        }
    };
    (
        $(#[$exec_attr:meta])*
        pub enum $exec_name:ident <$lt:lifetime> {
            $($exec_variant:ident($exec_ty:ty),)*
        }

        $(#[$spec_attr:meta])*
        pub enum $spec_name:ident {
            $($spec_variant:ident($spec_ty:ty),)*
        }

        type $inner_name:ident;
        pub struct $mapper_name:ident;
    ) => {
        verus! {
            $(#[$exec_attr])*
            pub enum $exec_name<$lt> {
                $($exec_variant($exec_ty),)*
            }

            $(#[$spec_attr])*
            pub enum $spec_name {
                $($spec_variant($spec_ty),)*
            }

            impl<$lt> ::vstd::prelude::DeepView for $exec_name<$lt> {
                type V = $spec_name;

                open spec fn deep_view(&self) -> Self::V {
                    match self {
                        $($exec_name::$exec_variant(v) => $spec_name::$spec_variant(v.deep_view()),)*
                    }
                }
            }

            type $inner_name = $crate::__vest_build_sum_ty!($($spec_ty),*);
            pub struct $mapper_name;

            impl $crate::combinators::mapped::spec::SpecMapper for $mapper_name {
                type In = $inner_name;
                type Out = $spec_name;

                open spec fn spec_map(&self, i: Self::In) -> Self::Out {
                    $crate::__vest_build_sum_map!(i, $spec_name, $($spec_variant),*)
                }

                open spec fn spec_map_rev(&self, i: Self::Out) -> Self::In {
                    $crate::__vest_build_sum_map_rev!(i, $spec_name, $($spec_variant),*)
                }
            }
        }
    };
}

pub use crate::with_deep_view_and_mapper;
