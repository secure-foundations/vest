#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::*;
use vest_lib2::core::exec::input::{InputBuf, InputSlice};
use vest_lib2::core::exec::parser::*;
use vest_lib2::core::exec::serializer::*;
use vest_lib2::core::exec::ParseError;
use vest_lib2::core::exec::{DeepEq, SelfView};
use vest_lib2::core::{proof::*, spec::*};
use vest_lib2::macros::impl_self_view_for;
use vest_lib2::primitives::btcvarint::VarInt;
use vest_lib2::primitives::leb128::ULeb128;
use vstd::prelude::*;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `a_typed_choose`."]
# [derive (Debug , PartialEq , Eq , Clone , Copy)]
pub enum ATypedChoose {
    X(u8),
    Y(u16),
    Z(u32),
}

# [verifier :: ext_equal]
pub enum ATypedChooseSpec {
    X(u8),
    Y(u16),
    Z(u32),
}

pub type ATypedChooseInner = Sum<u8, Sum<u16, u32>>;

impl DeepView for ATypedChoose {
    type V = ATypedChooseSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ATypedChoose::X(v) => ATypedChooseSpec::X(v.deep_view()),
            ATypedChoose::Y(v) => ATypedChooseSpec::Y(v.deep_view()),
            ATypedChoose::Z(v) => ATypedChooseSpec::Z(v.deep_view()),
        }
    }
}

# [doc = "data type for `a_typed_open_enum`."]
# [repr (u32)]
# [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
pub enum ATypedOpenEnum {
    P = 0,
    Q = 1,
    R = 2,
    Unknown(u32),
}

pub type ATypedOpenEnumSpec = ATypedOpenEnum;

pub type ATypedOpenEnumInner = Sum<u32, u32>;

impl DeepView for ATypedOpenEnum {
    type V = ATypedOpenEnumSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            ATypedOpenEnum::P => ATypedOpenEnumSpec::P,
            ATypedOpenEnum::Q => ATypedOpenEnumSpec::Q,
            ATypedOpenEnum::R => ATypedOpenEnumSpec::R,
            ATypedOpenEnum::Unknown(v) => ATypedOpenEnumSpec::Unknown(v),
        }
    }
}

impl DeepEq for ATypedOpenEnum {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for ATypedOpenEnum {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `a_non_dependent_choose`."]
# [derive (Debug , PartialEq , Eq , Clone , Copy)]
pub enum ANonDependentChoose {
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
}

# [verifier :: ext_equal]
pub enum ANonDependentChooseSpec {
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
}

pub type ANonDependentChooseInner = Sum<u8, Sum<u8, u8>>;

impl DeepView for ANonDependentChoose {
    type V = ANonDependentChooseSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ANonDependentChoose::Variant1(v) => ANonDependentChooseSpec::Variant1(v.deep_view()),
            ANonDependentChoose::Variant2(v) => ANonDependentChooseSpec::Variant2(v.deep_view()),
            ANonDependentChoose::Variant3(v) => ANonDependentChooseSpec::Variant3(v.deep_view()),
        }
    }
}

# [doc = "data type for `a_regular_choose`."]
# [derive (Debug , PartialEq , Eq , Clone , Copy)]
pub enum ARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

# [verifier :: ext_equal]
pub enum ARegularChooseSpec {
    A(u8),
    B(u16),
    C(u32),
}

pub type ARegularChooseInner = Sum<u8, Sum<u16, u32>>;

impl DeepView for ARegularChoose {
    type V = ARegularChooseSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ARegularChoose::A(v) => ARegularChooseSpec::A(v.deep_view()),
            ARegularChoose::B(v) => ARegularChooseSpec::B(v.deep_view()),
            ARegularChoose::C(v) => ARegularChooseSpec::C(v.deep_view()),
        }
    }
}

# [doc = "data type for `a_mixed_typed_enum`."]
# [repr (u8)]
# [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
pub enum AMixedTypedEnum {
    M = 0,
    N = 1,
    O = 2,
}

pub type AMixedTypedEnumSpec = AMixedTypedEnum;

pub type AMixedTypedEnumInner = u8;

impl DeepView for AMixedTypedEnum {
    type V = AMixedTypedEnumSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            AMixedTypedEnum::M => AMixedTypedEnumSpec::M,
            AMixedTypedEnum::N => AMixedTypedEnumSpec::N,
            AMixedTypedEnum::O => AMixedTypedEnumSpec::O,
        }
    }
}

impl DeepEq for AMixedTypedEnum {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for AMixedTypedEnum {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `a_closed_enum`."]
# [repr (u8)]
# [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
pub enum AClosedEnum {
    A = 0,
    B = 1,
    C = 2,
}

pub type AClosedEnumSpec = AClosedEnum;

pub type AClosedEnumInner = u8;

impl DeepView for AClosedEnum {
    type V = AClosedEnumSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            AClosedEnum::A => AClosedEnumSpec::A,
            AClosedEnum::B => AClosedEnumSpec::B,
            AClosedEnum::C => AClosedEnumSpec::C,
        }
    }
}

impl DeepEq for AClosedEnum {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for AClosedEnum {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `a_typed_closed_enum`."]
# [repr (u16)]
# [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
pub enum ATypedClosedEnum {
    X = 0,
    Y = 1,
    Z = 2,
}

pub type ATypedClosedEnumSpec = ATypedClosedEnum;

pub type ATypedClosedEnumInner = u16;

impl DeepView for ATypedClosedEnum {
    type V = ATypedClosedEnumSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            ATypedClosedEnum::X => ATypedClosedEnumSpec::X,
            ATypedClosedEnum::Y => ATypedClosedEnumSpec::Y,
            ATypedClosedEnum::Z => ATypedClosedEnumSpec::Z,
        }
    }
}

impl DeepEq for ATypedClosedEnum {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for ATypedClosedEnum {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `an_open_enum`."]
# [repr (u8)]
# [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
pub enum AnOpenEnum {
    A = 0,
    B = 1,
    C = 2,
    Unknown(u8),
}

pub type AnOpenEnumSpec = AnOpenEnum;

pub type AnOpenEnumInner = Sum<u8, u8>;

impl DeepView for AnOpenEnum {
    type V = AnOpenEnumSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            AnOpenEnum::A => AnOpenEnumSpec::A,
            AnOpenEnum::B => AnOpenEnumSpec::B,
            AnOpenEnum::C => AnOpenEnumSpec::C,
            AnOpenEnum::Unknown(v) => AnOpenEnumSpec::Unknown(v),
        }
    }
}

impl DeepEq for AnOpenEnum {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for AnOpenEnum {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `a_typed_choose_with_default`."]
# [derive (Debug , PartialEq , Eq , Clone , Copy)]
pub enum ATypedChooseWithDefault<'i> {
    P(u8),
    Q(u16),
    R(u32),
    Default(&'i [u8]),
}

# [verifier :: ext_equal]
pub enum ATypedChooseWithDefaultSpec {
    P(u8),
    Q(u16),
    R(u32),
    Default(Seq<u8>),
}

pub type ATypedChooseWithDefaultInner = Sum<u8, Sum<u16, Sum<u32, Seq<u8>>>>;

impl<'i> DeepView for ATypedChooseWithDefault<'i> {
    type V = ATypedChooseWithDefaultSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ATypedChooseWithDefault::P(v) => ATypedChooseWithDefaultSpec::P(v.deep_view()),
            ATypedChooseWithDefault::Q(v) => ATypedChooseWithDefaultSpec::Q(v.deep_view()),
            ATypedChooseWithDefault::R(v) => ATypedChooseWithDefaultSpec::R(v.deep_view()),
            ATypedChooseWithDefault::Default(v) => ATypedChooseWithDefaultSpec::Default(
                v.deep_view(),
            ),
        }
    }
}

# [doc = "data type for `a_choose_with_default`."]
# [derive (Debug , PartialEq , Eq , Clone , Copy)]
pub enum AChooseWithDefault<'i> {
    A(u8),
    B(u16),
    C(u32),
    Default(&'i [u8]),
}

# [verifier :: ext_equal]
pub enum AChooseWithDefaultSpec {
    A(u8),
    B(u16),
    C(u32),
    Default(Seq<u8>),
}

pub type AChooseWithDefaultInner = Sum<u8, Sum<u16, Sum<u32, Seq<u8>>>>;

impl<'i> DeepView for AChooseWithDefault<'i> {
    type V = AChooseWithDefaultSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            AChooseWithDefault::A(v) => AChooseWithDefaultSpec::A(v.deep_view()),
            AChooseWithDefault::B(v) => AChooseWithDefaultSpec::B(v.deep_view()),
            AChooseWithDefault::C(v) => AChooseWithDefaultSpec::C(v.deep_view()),
            AChooseWithDefault::Default(v) => AChooseWithDefaultSpec::Default(v.deep_view()),
        }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `a_typed_choose`."]
# [derive (Clone , Copy)]
pub struct ATypedChooseFmt {
    pub e: ATypedClosedEnum,
}

pub type ATypedChooseFmtSpec = Named<
    Mapped<Sum<U8, Sum<U16Le, U32Le>>, FnSpecMapper<ATypedChooseInner, ATypedChooseSpec>>,
>;

# [doc = "specification constructor for `a_typed_choose`."]
pub open spec fn a_typed_choose_fmt(e: ATypedClosedEnumSpec) -> ATypedChooseFmtSpec {
    Named(
        "a_typed_choose",
        Mapped {
            inner: match e {
                ATypedClosedEnumSpec::X => Sum::Inl(U8),
                ATypedClosedEnumSpec::Y => Sum::Inr(Sum::Inl(U16Le)),
                ATypedClosedEnumSpec::Z => Sum::Inr(Sum::Inr(U32Le)),
            },
            mapper: (
                |parsed: ATypedChooseInner| -> ATypedChooseSpec
                    {
                        match parsed {
                            Sum::Inl(v) => ATypedChooseSpec::X(v),
                            Sum::Inr(Sum::Inl(v)) => ATypedChooseSpec::Y(v),
                            Sum::Inr(Sum::Inr(v)) => ATypedChooseSpec::Z(v),
                        }
                    },
                |value: ATypedChooseSpec| -> ATypedChooseInner
                    {
                        match value {
                            ATypedChooseSpec::X(v) => Sum::Inl(v),
                            ATypedChooseSpec::Y(v) => Sum::Inr(Sum::Inl(v)),
                            ATypedChooseSpec::Z(v) => Sum::Inr(Sum::Inr(v)),
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `a_typed_open_enum`."]
# [derive (Clone , Copy)]
pub struct ATypedOpenEnumFmt;

pub type ATypedOpenEnumFmtSpec = Named<
    Mapped<
        Choice<Refined<U32Le, PredFnSpec<u32>>, Refined<U32Le, PredFnSpec<u32>>>,
        FnSpecMapper<ATypedOpenEnumInner, ATypedOpenEnumSpec>,
    >,
>;

# [doc = "specification constructor for `a_typed_open_enum`."]
pub open spec fn a_typed_open_enum_fmt() -> ATypedOpenEnumFmtSpec {
    Named(
        "a_typed_open_enum",
        Mapped {
            inner: Choice(
                Refined(U32Le, |x: u32| x == 0 || x == 1 || x == 2),
                Refined(U32Le, |x: u32| x != 0 && x != 1 && x != 2),
            ),
            mapper: (
                |parsed: ATypedOpenEnumInner| -> ATypedOpenEnumSpec
                    {
                        match parsed {
                            Sum::Inl(x) => match x {
                                0 => ATypedOpenEnumSpec::P,
                                1 => ATypedOpenEnumSpec::Q,
                                2 => ATypedOpenEnumSpec::R,
                                _ => arbitrary(),
                            },
                            Sum::Inr(x) => ATypedOpenEnumSpec::Unknown(x),
                        }
                    },
                |value: ATypedOpenEnumSpec| -> ATypedOpenEnumInner
                    {
                        match value {
                            ATypedOpenEnumSpec::P => Sum::Inl(0),
                            ATypedOpenEnumSpec::Q => Sum::Inl(1),
                            ATypedOpenEnumSpec::R => Sum::Inl(2),
                            ATypedOpenEnumSpec::Unknown(x) => Sum::Inr(x),
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `a_non_dependent_choose`."]
# [derive (Clone , Copy)]
pub struct ANonDependentChooseFmt;

pub type ANonDependentChooseFmtSpec = Named<
    Mapped<
        Choice<
            Refined<U8, PredFnSpec<u8>>,
            Choice<Refined<U8, PredFnSpec<u8>>, Refined<U8, PredFnSpec<u8>>>,
        >,
        FnSpecMapper<ANonDependentChooseInner, ANonDependentChooseSpec>,
    >,
>;

# [doc = "specification constructor for `a_non_dependent_choose`."]
pub open spec fn a_non_dependent_choose_fmt() -> ANonDependentChooseFmtSpec {
    Named(
        "a_non_dependent_choose",
        Mapped {
            inner: Choice(
                Refined(U8, |x: u8| x >= 0 && x <= 10),
                Choice(Refined(U8, |x: u8| x >= 11 && x <= 20), Refined(U8, |x: u8| x >= 21)),
            ),
            mapper: (
                |parsed: ANonDependentChooseInner| -> ANonDependentChooseSpec
                    {
                        match parsed {
                            Sum::Inl(v) => ANonDependentChooseSpec::Variant1(v),
                            Sum::Inr(Sum::Inl(v)) => ANonDependentChooseSpec::Variant2(v),
                            Sum::Inr(Sum::Inr(v)) => ANonDependentChooseSpec::Variant3(v),
                        }
                    },
                |value: ANonDependentChooseSpec| -> ANonDependentChooseInner
                    {
                        match value {
                            ANonDependentChooseSpec::Variant1(v) => Sum::Inl(v),
                            ANonDependentChooseSpec::Variant2(v) => Sum::Inr(Sum::Inl(v)),
                            ANonDependentChooseSpec::Variant3(v) => Sum::Inr(Sum::Inr(v)),
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `a_regular_choose`."]
# [derive (Clone , Copy)]
pub struct ARegularChooseFmt {
    pub e: AClosedEnum,
}

pub type ARegularChooseFmtSpec = Named<
    Mapped<Sum<U8, Sum<U16Le, U32Le>>, FnSpecMapper<ARegularChooseInner, ARegularChooseSpec>>,
>;

# [doc = "specification constructor for `a_regular_choose`."]
pub open spec fn a_regular_choose_fmt(e: AClosedEnumSpec) -> ARegularChooseFmtSpec {
    Named(
        "a_regular_choose",
        Mapped {
            inner: match e {
                AClosedEnumSpec::A => Sum::Inl(U8),
                AClosedEnumSpec::B => Sum::Inr(Sum::Inl(U16Le)),
                AClosedEnumSpec::C => Sum::Inr(Sum::Inr(U32Le)),
            },
            mapper: (
                |parsed: ARegularChooseInner| -> ARegularChooseSpec
                    {
                        match parsed {
                            Sum::Inl(v) => ARegularChooseSpec::A(v),
                            Sum::Inr(Sum::Inl(v)) => ARegularChooseSpec::B(v),
                            Sum::Inr(Sum::Inr(v)) => ARegularChooseSpec::C(v),
                        }
                    },
                |value: ARegularChooseSpec| -> ARegularChooseInner
                    {
                        match value {
                            ARegularChooseSpec::A(v) => Sum::Inl(v),
                            ARegularChooseSpec::B(v) => Sum::Inr(Sum::Inl(v)),
                            ARegularChooseSpec::C(v) => Sum::Inr(Sum::Inr(v)),
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `a_mixed_typed_enum`."]
# [derive (Clone , Copy)]
pub struct AMixedTypedEnumFmt;

pub type AMixedTypedEnumFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<AMixedTypedEnumInner, AMixedTypedEnumSpec>>,
>;

# [doc = "specification constructor for `a_mixed_typed_enum`."]
pub open spec fn a_mixed_typed_enum_fmt() -> AMixedTypedEnumFmtSpec {
    Named(
        "a_mixed_typed_enum",
        Mapped {
            inner: Refined(U8, |x: u8| x == 0 || x == 1 || x == 2),
            mapper: (
                |parsed: AMixedTypedEnumInner| -> AMixedTypedEnumSpec
                    {
                        match parsed {
                            0 => AMixedTypedEnumSpec::M,
                            1 => AMixedTypedEnumSpec::N,
                            2 => AMixedTypedEnumSpec::O,
                            _ => arbitrary(),
                        }
                    },
                |value: AMixedTypedEnumSpec| -> AMixedTypedEnumInner
                    {
                        match value {
                            AMixedTypedEnumSpec::M => 0,
                            AMixedTypedEnumSpec::N => 1,
                            AMixedTypedEnumSpec::O => 2,
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `a_closed_enum`."]
# [derive (Clone , Copy)]
pub struct AClosedEnumFmt;

pub type AClosedEnumFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<AClosedEnumInner, AClosedEnumSpec>>,
>;

# [doc = "specification constructor for `a_closed_enum`."]
pub open spec fn a_closed_enum_fmt() -> AClosedEnumFmtSpec {
    Named(
        "a_closed_enum",
        Mapped {
            inner: Refined(U8, |x: u8| x == 0 || x == 1 || x == 2),
            mapper: (
                |parsed: AClosedEnumInner| -> AClosedEnumSpec
                    {
                        match parsed {
                            0 => AClosedEnumSpec::A,
                            1 => AClosedEnumSpec::B,
                            2 => AClosedEnumSpec::C,
                            _ => arbitrary(),
                        }
                    },
                |value: AClosedEnumSpec| -> AClosedEnumInner
                    {
                        match value {
                            AClosedEnumSpec::A => 0,
                            AClosedEnumSpec::B => 1,
                            AClosedEnumSpec::C => 2,
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `a_typed_closed_enum`."]
# [derive (Clone , Copy)]
pub struct ATypedClosedEnumFmt;

pub type ATypedClosedEnumFmtSpec = Named<
    Mapped<
        Refined<U16Le, PredFnSpec<u16>>,
        FnSpecMapper<ATypedClosedEnumInner, ATypedClosedEnumSpec>,
    >,
>;

# [doc = "specification constructor for `a_typed_closed_enum`."]
pub open spec fn a_typed_closed_enum_fmt() -> ATypedClosedEnumFmtSpec {
    Named(
        "a_typed_closed_enum",
        Mapped {
            inner: Refined(U16Le, |x: u16| x == 0 || x == 1 || x == 2),
            mapper: (
                |parsed: ATypedClosedEnumInner| -> ATypedClosedEnumSpec
                    {
                        match parsed {
                            0 => ATypedClosedEnumSpec::X,
                            1 => ATypedClosedEnumSpec::Y,
                            2 => ATypedClosedEnumSpec::Z,
                            _ => arbitrary(),
                        }
                    },
                |value: ATypedClosedEnumSpec| -> ATypedClosedEnumInner
                    {
                        match value {
                            ATypedClosedEnumSpec::X => 0,
                            ATypedClosedEnumSpec::Y => 1,
                            ATypedClosedEnumSpec::Z => 2,
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `an_open_enum`."]
# [derive (Clone , Copy)]
pub struct AnOpenEnumFmt;

pub type AnOpenEnumFmtSpec = Named<
    Mapped<
        Choice<Refined<U8, PredFnSpec<u8>>, Refined<U8, PredFnSpec<u8>>>,
        FnSpecMapper<AnOpenEnumInner, AnOpenEnumSpec>,
    >,
>;

# [doc = "specification constructor for `an_open_enum`."]
pub open spec fn an_open_enum_fmt() -> AnOpenEnumFmtSpec {
    Named(
        "an_open_enum",
        Mapped {
            inner: Choice(
                Refined(U8, |x: u8| x == 0 || x == 1 || x == 2),
                Refined(U8, |x: u8| x != 0 && x != 1 && x != 2),
            ),
            mapper: (
                |parsed: AnOpenEnumInner| -> AnOpenEnumSpec
                    {
                        match parsed {
                            Sum::Inl(x) => match x {
                                0 => AnOpenEnumSpec::A,
                                1 => AnOpenEnumSpec::B,
                                2 => AnOpenEnumSpec::C,
                                _ => arbitrary(),
                            },
                            Sum::Inr(x) => AnOpenEnumSpec::Unknown(x),
                        }
                    },
                |value: AnOpenEnumSpec| -> AnOpenEnumInner
                    {
                        match value {
                            AnOpenEnumSpec::A => Sum::Inl(0),
                            AnOpenEnumSpec::B => Sum::Inl(1),
                            AnOpenEnumSpec::C => Sum::Inl(2),
                            AnOpenEnumSpec::Unknown(x) => Sum::Inr(x),
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `a_typed_choose_with_default`."]
# [derive (Clone , Copy)]
pub struct ATypedChooseWithDefaultFmt {
    pub e: ATypedOpenEnum,
}

pub type ATypedChooseWithDefaultFmtSpec = Named<
    Mapped<
        Sum<U8, Sum<U16Le, Sum<U32Le, Tail>>>,
        FnSpecMapper<ATypedChooseWithDefaultInner, ATypedChooseWithDefaultSpec>,
    >,
>;

# [doc = "specification constructor for `a_typed_choose_with_default`."]
pub open spec fn a_typed_choose_with_default_fmt(
    e: ATypedOpenEnumSpec,
) -> ATypedChooseWithDefaultFmtSpec {
    Named(
        "a_typed_choose_with_default",
        Mapped {
            inner: match e {
                ATypedOpenEnumSpec::P => Sum::Inl(U8),
                ATypedOpenEnumSpec::Q => Sum::Inr(Sum::Inl(U16Le)),
                ATypedOpenEnumSpec::R => Sum::Inr(Sum::Inr(Sum::Inl(U32Le))),
                _ => Sum::Inr(Sum::Inr(Sum::Inr(Tail))),
            },
            mapper: (
                |parsed: ATypedChooseWithDefaultInner| -> ATypedChooseWithDefaultSpec
                    {
                        match parsed {
                            Sum::Inl(v) => ATypedChooseWithDefaultSpec::P(v),
                            Sum::Inr(Sum::Inl(v)) => ATypedChooseWithDefaultSpec::Q(v),
                            Sum::Inr(Sum::Inr(Sum::Inl(v))) => ATypedChooseWithDefaultSpec::R(v),
                            Sum::Inr(Sum::Inr(Sum::Inr(v))) => ATypedChooseWithDefaultSpec::Default(
                                v,
                            ),
                        }
                    },
                |value: ATypedChooseWithDefaultSpec| -> ATypedChooseWithDefaultInner
                    {
                        match value {
                            ATypedChooseWithDefaultSpec::P(v) => Sum::Inl(v),
                            ATypedChooseWithDefaultSpec::Q(v) => Sum::Inr(Sum::Inl(v)),
                            ATypedChooseWithDefaultSpec::R(v) => Sum::Inr(Sum::Inr(Sum::Inl(v))),
                            ATypedChooseWithDefaultSpec::Default(v) => Sum::Inr(
                                Sum::Inr(Sum::Inr(v)),
                            ),
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `a_choose_with_default`."]
# [derive (Clone , Copy)]
pub struct AChooseWithDefaultFmt {
    pub e: AnOpenEnum,
}

pub type AChooseWithDefaultFmtSpec = Named<
    Mapped<
        Sum<U8, Sum<U16Le, Sum<U32Le, Tail>>>,
        FnSpecMapper<AChooseWithDefaultInner, AChooseWithDefaultSpec>,
    >,
>;

# [doc = "specification constructor for `a_choose_with_default`."]
pub open spec fn a_choose_with_default_fmt(e: AnOpenEnumSpec) -> AChooseWithDefaultFmtSpec {
    Named(
        "a_choose_with_default",
        Mapped {
            inner: match e {
                AnOpenEnumSpec::A => Sum::Inl(U8),
                AnOpenEnumSpec::B => Sum::Inr(Sum::Inl(U16Le)),
                AnOpenEnumSpec::C => Sum::Inr(Sum::Inr(Sum::Inl(U32Le))),
                _ => Sum::Inr(Sum::Inr(Sum::Inr(Tail))),
            },
            mapper: (
                |parsed: AChooseWithDefaultInner| -> AChooseWithDefaultSpec
                    {
                        match parsed {
                            Sum::Inl(v) => AChooseWithDefaultSpec::A(v),
                            Sum::Inr(Sum::Inl(v)) => AChooseWithDefaultSpec::B(v),
                            Sum::Inr(Sum::Inr(Sum::Inl(v))) => AChooseWithDefaultSpec::C(v),
                            Sum::Inr(Sum::Inr(Sum::Inr(v))) => AChooseWithDefaultSpec::Default(v),
                        }
                    },
                |value: AChooseWithDefaultSpec| -> AChooseWithDefaultInner
                    {
                        match value {
                            AChooseWithDefaultSpec::A(v) => Sum::Inl(v),
                            AChooseWithDefaultSpec::B(v) => Sum::Inr(Sum::Inl(v)),
                            AChooseWithDefaultSpec::C(v) => Sum::Inr(Sum::Inr(Sum::Inl(v))),
                            AChooseWithDefaultSpec::Default(v) => Sum::Inr(Sum::Inr(Sum::Inr(v))),
                        }
                    },
            ),
        },
    )
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ATypedChooseFmt {
        type PVal = ATypedChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_typed_choose_fmt(self.e.deep_view()).spec_parse(ibuf)
        }
    }

    impl Consistency for ATypedChooseFmt {
        type Val = ATypedChooseSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_typed_choose_fmt(self.e.deep_view()).consistent(v)
        }
    }

    impl SpecSerializerDps for ATypedChooseFmt {
        type SValue = ATypedChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_typed_choose_fmt(self.e.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypedChooseFmt {
        type SVal = ATypedChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_typed_choose_fmt(self.e.deep_view()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypedChooseFmt {
        type T = ATypedChooseSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_typed_choose_fmt(self.e.deep_view()).byte_len(v)
        }
    }

    impl SpecParser for ATypedOpenEnumFmt {
        type PVal = ATypedOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_typed_open_enum_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for ATypedOpenEnumFmt {
        type Val = ATypedOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_typed_open_enum_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for ATypedOpenEnumFmt {
        type SValue = ATypedOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_typed_open_enum_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypedOpenEnumFmt {
        type SVal = ATypedOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_typed_open_enum_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypedOpenEnumFmt {
        type T = ATypedOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_typed_open_enum_fmt().byte_len(v)
        }
    }

    impl SpecParser for ANonDependentChooseFmt {
        type PVal = ANonDependentChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_non_dependent_choose_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for ANonDependentChooseFmt {
        type Val = ANonDependentChooseSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_non_dependent_choose_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for ANonDependentChooseFmt {
        type SValue = ANonDependentChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_non_dependent_choose_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ANonDependentChooseFmt {
        type SVal = ANonDependentChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_non_dependent_choose_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for ANonDependentChooseFmt {
        type T = ANonDependentChooseSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_non_dependent_choose_fmt().byte_len(v)
        }
    }

    impl SpecParser for ARegularChooseFmt {
        type PVal = ARegularChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_regular_choose_fmt(self.e.deep_view()).spec_parse(ibuf)
        }
    }

    impl Consistency for ARegularChooseFmt {
        type Val = ARegularChooseSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_regular_choose_fmt(self.e.deep_view()).consistent(v)
        }
    }

    impl SpecSerializerDps for ARegularChooseFmt {
        type SValue = ARegularChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_regular_choose_fmt(self.e.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ARegularChooseFmt {
        type SVal = ARegularChooseSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_regular_choose_fmt(self.e.deep_view()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ARegularChooseFmt {
        type T = ARegularChooseSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_regular_choose_fmt(self.e.deep_view()).byte_len(v)
        }
    }

    impl SpecParser for AMixedTypedEnumFmt {
        type PVal = AMixedTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_mixed_typed_enum_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for AMixedTypedEnumFmt {
        type Val = AMixedTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_mixed_typed_enum_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for AMixedTypedEnumFmt {
        type SValue = AMixedTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_mixed_typed_enum_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AMixedTypedEnumFmt {
        type SVal = AMixedTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_mixed_typed_enum_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for AMixedTypedEnumFmt {
        type T = AMixedTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_mixed_typed_enum_fmt().byte_len(v)
        }
    }

    impl SpecParser for AClosedEnumFmt {
        type PVal = AClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_closed_enum_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for AClosedEnumFmt {
        type Val = AClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_closed_enum_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for AClosedEnumFmt {
        type SValue = AClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_closed_enum_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AClosedEnumFmt {
        type SVal = AClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_closed_enum_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for AClosedEnumFmt {
        type T = AClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_closed_enum_fmt().byte_len(v)
        }
    }

    impl SpecParser for ATypedClosedEnumFmt {
        type PVal = ATypedClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_typed_closed_enum_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for ATypedClosedEnumFmt {
        type Val = ATypedClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_typed_closed_enum_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for ATypedClosedEnumFmt {
        type SValue = ATypedClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_typed_closed_enum_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypedClosedEnumFmt {
        type SVal = ATypedClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_typed_closed_enum_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypedClosedEnumFmt {
        type T = ATypedClosedEnumSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_typed_closed_enum_fmt().byte_len(v)
        }
    }

    impl SpecParser for AnOpenEnumFmt {
        type PVal = AnOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            an_open_enum_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for AnOpenEnumFmt {
        type Val = AnOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            an_open_enum_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for AnOpenEnumFmt {
        type SValue = AnOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            an_open_enum_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AnOpenEnumFmt {
        type SVal = AnOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            an_open_enum_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for AnOpenEnumFmt {
        type T = AnOpenEnumSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            an_open_enum_fmt().byte_len(v)
        }
    }

    impl SpecParser for ATypedChooseWithDefaultFmt {
        type PVal = ATypedChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_typed_choose_with_default_fmt(self.e.deep_view()).spec_parse(ibuf)
        }
    }

    impl Consistency for ATypedChooseWithDefaultFmt {
        type Val = ATypedChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_typed_choose_with_default_fmt(self.e.deep_view()).consistent(v)
        }
    }

    impl SpecSerializerDps for ATypedChooseWithDefaultFmt {
        type SValue = ATypedChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_typed_choose_with_default_fmt(self.e.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypedChooseWithDefaultFmt {
        type SVal = ATypedChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_typed_choose_with_default_fmt(self.e.deep_view()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypedChooseWithDefaultFmt {
        type T = ATypedChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_typed_choose_with_default_fmt(self.e.deep_view()).byte_len(v)
        }
    }

    impl SpecParser for AChooseWithDefaultFmt {
        type PVal = AChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            a_choose_with_default_fmt(self.e.deep_view()).spec_parse(ibuf)
        }
    }

    impl Consistency for AChooseWithDefaultFmt {
        type Val = AChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            a_choose_with_default_fmt(self.e.deep_view()).consistent(v)
        }
    }

    impl SpecSerializerDps for AChooseWithDefaultFmt {
        type SValue = AChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            a_choose_with_default_fmt(self.e.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AChooseWithDefaultFmt {
        type SVal = AChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            a_choose_with_default_fmt(self.e.deep_view()).spec_serialize(v)
        }
    }

    impl SpecByteLen for AChooseWithDefaultFmt {
        type T = AChooseWithDefaultSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            a_choose_with_default_fmt(self.e.deep_view()).byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for ATypedChooseFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            a_typed_choose_fmt(self.e.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypedChooseFmt {
        open spec fn productive_inv(&self) -> bool {
            a_typed_choose_fmt(self.e.deep_view()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypedChooseFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseFmt as Consistency>::consistent);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ATypedChooseFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ATypedChooseFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypedChooseFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypedChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ATypedChooseFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseFmt as Consistency>::consistent);
            reveal(<ATypedChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypedChooseFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ATypedChooseFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ATypedChooseFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = a_typed_choose_fmt(self.e.deep_view());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ATypedOpenEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            a_typed_open_enum_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypedOpenEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            a_typed_open_enum_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypedOpenEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedOpenEnumFmt as Consistency>::consistent);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ATypedOpenEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ATypedOpenEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypedOpenEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypedOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ATypedOpenEnumFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedOpenEnumFmt as Consistency>::consistent);
            reveal(<ATypedOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypedOpenEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ATypedOpenEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedOpenEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ATypedOpenEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedOpenEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = a_typed_open_enum_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ANonDependentChooseFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            a_non_dependent_choose_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ANonDependentChooseFmt {
        open spec fn productive_inv(&self) -> bool {
            a_non_dependent_choose_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ANonDependentChooseFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            reveal(<ANonDependentChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            reveal(<ANonDependentChooseFmt as Consistency>::consistent);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ANonDependentChooseFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ANonDependentChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ANonDependentChooseFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ANonDependentChooseFmt as SpecSerializer>::spec_serialize);
            reveal(<ANonDependentChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ANonDependentChooseFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ANonDependentChooseFmt as Consistency>::consistent);
            reveal(<ANonDependentChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ANonDependentChooseFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ANonDependentChooseFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ANonDependentChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ANonDependentChooseFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ANonDependentChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = a_non_dependent_choose_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ARegularChooseFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            a_regular_choose_fmt(self.e.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ARegularChooseFmt {
        open spec fn productive_inv(&self) -> bool {
            a_regular_choose_fmt(self.e.deep_view()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ARegularChooseFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            reveal(<ARegularChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            reveal(<ARegularChooseFmt as Consistency>::consistent);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ARegularChooseFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ARegularChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ARegularChooseFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ARegularChooseFmt as SpecSerializer>::spec_serialize);
            reveal(<ARegularChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ARegularChooseFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ARegularChooseFmt as Consistency>::consistent);
            reveal(<ARegularChooseFmt as SpecByteLen>::byte_len);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ARegularChooseFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ARegularChooseFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ARegularChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ARegularChooseFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ARegularChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = a_regular_choose_fmt(self.e.deep_view());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AMixedTypedEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            a_mixed_typed_enum_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AMixedTypedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            a_mixed_typed_enum_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AMixedTypedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<AMixedTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<AMixedTypedEnumFmt as Consistency>::consistent);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AMixedTypedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AMixedTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AMixedTypedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AMixedTypedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<AMixedTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for AMixedTypedEnumFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AMixedTypedEnumFmt as Consistency>::consistent);
            reveal(<AMixedTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AMixedTypedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AMixedTypedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AMixedTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AMixedTypedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AMixedTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = a_mixed_typed_enum_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AClosedEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            a_closed_enum_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AClosedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            a_closed_enum_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            let fmt = a_closed_enum_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AClosedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<AClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_closed_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<AClosedEnumFmt as Consistency>::consistent);
            let fmt = a_closed_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AClosedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = a_closed_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_closed_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AClosedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AClosedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<AClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_closed_enum_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for AClosedEnumFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AClosedEnumFmt as Consistency>::consistent);
            reveal(<AClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_closed_enum_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AClosedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            let fmt = a_closed_enum_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AClosedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AClosedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = a_closed_enum_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AClosedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AClosedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = a_closed_enum_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ATypedClosedEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            a_typed_closed_enum_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypedClosedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            a_typed_closed_enum_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypedClosedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedClosedEnumFmt as Consistency>::consistent);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ATypedClosedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ATypedClosedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypedClosedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypedClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ATypedClosedEnumFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedClosedEnumFmt as Consistency>::consistent);
            reveal(<ATypedClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypedClosedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ATypedClosedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedClosedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ATypedClosedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedClosedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = a_typed_closed_enum_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AnOpenEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            an_open_enum_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AnOpenEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            an_open_enum_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            let fmt = an_open_enum_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AnOpenEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<AnOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = an_open_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<AnOpenEnumFmt as Consistency>::consistent);
            let fmt = an_open_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AnOpenEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = an_open_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = an_open_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AnOpenEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AnOpenEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<AnOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = an_open_enum_fmt();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for AnOpenEnumFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnOpenEnumFmt as Consistency>::consistent);
            reveal(<AnOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = an_open_enum_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AnOpenEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            let fmt = an_open_enum_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AnOpenEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnOpenEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = an_open_enum_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AnOpenEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnOpenEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = an_open_enum_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ATypedChooseWithDefaultFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            a_typed_choose_with_default_fmt(self.e.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypedChooseWithDefaultFmt {
        open spec fn productive_inv(&self) -> bool {
            a_typed_choose_with_default_fmt(self.e.deep_view()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            let fmt = a_typed_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypedChooseWithDefaultFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseWithDefaultFmt as Consistency>::consistent);
            let fmt = a_typed_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for ATypedChooseWithDefaultFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypedChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypedChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ATypedChooseWithDefaultFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseWithDefaultFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseWithDefaultFmt as Consistency>::consistent);
            reveal(<ATypedChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = a_typed_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypedChooseWithDefaultFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            let fmt = a_typed_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for ATypedChooseWithDefaultFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypedChooseWithDefaultFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            let fmt = a_typed_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AChooseWithDefaultFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            a_choose_with_default_fmt(self.e.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AChooseWithDefaultFmt {
        open spec fn productive_inv(&self) -> bool {
            a_choose_with_default_fmt(self.e.deep_view()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            let fmt = a_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AChooseWithDefaultFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<AChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = a_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<AChooseWithDefaultFmt as Consistency>::consistent);
            let fmt = a_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for AChooseWithDefaultFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            reveal(<AChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = a_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for AChooseWithDefaultFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<AChooseWithDefaultFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AChooseWithDefaultFmt as Consistency>::consistent);
            reveal(<AChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = a_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AChooseWithDefaultFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            let fmt = a_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for AChooseWithDefaultFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AChooseWithDefaultFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            let fmt = a_choose_with_default_fmt(self.e.deep_view());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
impl<'i> Parser<&'i [u8]> for ATypedChooseFmt {
    type PT = ATypedChoose;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = match self.e {
            ATypedClosedEnum::X => {
                let (n, v) = (U8).parse(&rest)?;
                (n, ATypedChoose::X(v))
            },
            ATypedClosedEnum::Y => {
                let (n, v) = (U16Le).parse(&rest)?;
                (n, ATypedChoose::Y(v))
            },
            ATypedClosedEnum::Z => {
                let (n, v) = (U32Le).parse(&rest)?;
                (n, ATypedChoose::Z(v))
            },
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
        Ok((n, v))
    }
}

impl<'i> Parser<&'i [u8]> for ATypedOpenEnumFmt {
    type PT = ATypedOpenEnum;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = U32Le.parse(&rest)?;
        let enum_val = match v {
            0 => ATypedOpenEnum::P,
            1 => ATypedOpenEnum::Q,
            2 => ATypedOpenEnum::R,
            x => ATypedOpenEnum::Unknown(x),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        Ok((n, enum_val))
    }
}

impl<'i> Parser<&'i [u8]> for ANonDependentChooseFmt {
    type PT = ANonDependentChoose;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = match (U8).parse(&rest) {
            Ok((n, va)) if va >= 0 && va <= 10 => Ok((n, ANonDependentChoose::Variant1(va))),
            _ => match (U8).parse(&rest) {
                Ok((n, va)) if va >= 11 && va <= 20 => Ok((n, ANonDependentChoose::Variant2(va))),
                _ => match (U8).parse(&rest) {
                    Ok((n, va)) if va >= 21 => Ok((n, ANonDependentChoose::Variant3(va))),
                    _ => Err(ParseError::invalid_tag()),
                },
            },
        }?;
        assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
        Ok((n, v))
    }
}

impl<'i> Parser<&'i [u8]> for ARegularChooseFmt {
    type PT = ARegularChoose;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = match self.e {
            AClosedEnum::A => {
                let (n, v) = (U8).parse(&rest)?;
                (n, ARegularChoose::A(v))
            },
            AClosedEnum::B => {
                let (n, v) = (U16Le).parse(&rest)?;
                (n, ARegularChoose::B(v))
            },
            AClosedEnum::C => {
                let (n, v) = (U32Le).parse(&rest)?;
                (n, ARegularChoose::C(v))
            },
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
        Ok((n, v))
    }
}

impl<'i> Parser<&'i [u8]> for AMixedTypedEnumFmt {
    type PT = AMixedTypedEnum;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = U8.parse(&rest)?;
        let enum_val = match v {
            0 => AMixedTypedEnum::M,
            1 => AMixedTypedEnum::N,
            2 => AMixedTypedEnum::O,
            _ => return Err(ParseError::invalid_tag()),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        Ok((n, enum_val))
    }
}

impl<'i> Parser<&'i [u8]> for AClosedEnumFmt {
    type PT = AClosedEnum;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = U8.parse(&rest)?;
        let enum_val = match v {
            0 => AClosedEnum::A,
            1 => AClosedEnum::B,
            2 => AClosedEnum::C,
            _ => return Err(ParseError::invalid_tag()),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        Ok((n, enum_val))
    }
}

impl<'i> Parser<&'i [u8]> for ATypedClosedEnumFmt {
    type PT = ATypedClosedEnum;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = U16Le.parse(&rest)?;
        let enum_val = match v {
            0 => ATypedClosedEnum::X,
            1 => ATypedClosedEnum::Y,
            2 => ATypedClosedEnum::Z,
            _ => return Err(ParseError::invalid_tag()),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        Ok((n, enum_val))
    }
}

impl<'i> Parser<&'i [u8]> for AnOpenEnumFmt {
    type PT = AnOpenEnum;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = U8.parse(&rest)?;
        let enum_val = match v {
            0 => AnOpenEnum::A,
            1 => AnOpenEnum::B,
            2 => AnOpenEnum::C,
            x => AnOpenEnum::Unknown(x),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        Ok((n, enum_val))
    }
}

impl<'i> Parser<&'i [u8]> for ATypedChooseWithDefaultFmt {
    type PT = ATypedChooseWithDefault<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = match self.e {
            ATypedOpenEnum::P => {
                let (n, v) = (U8).parse(&rest)?;
                (n, ATypedChooseWithDefault::P(v))
            },
            ATypedOpenEnum::Q => {
                let (n, v) = (U16Le).parse(&rest)?;
                (n, ATypedChooseWithDefault::Q(v))
            },
            ATypedOpenEnum::R => {
                let (n, v) = (U32Le).parse(&rest)?;
                (n, ATypedChooseWithDefault::R(v))
            },
            _ => {
                let (n, v) = (Tail).parse(&rest)?;
                (n, ATypedChooseWithDefault::Default(v))
            },
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
        Ok((n, v))
    }
}

impl<'i> Parser<&'i [u8]> for AChooseWithDefaultFmt {
    type PT = AChooseWithDefault<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = match self.e {
            AnOpenEnum::A => {
                let (n, v) = (U8).parse(&rest)?;
                (n, AChooseWithDefault::A(v))
            },
            AnOpenEnum::B => {
                let (n, v) = (U16Le).parse(&rest)?;
                (n, AChooseWithDefault::B(v))
            },
            AnOpenEnum::C => {
                let (n, v) = (U32Le).parse(&rest)?;
                (n, AChooseWithDefault::C(v))
            },
            _ => {
                let (n, v) = (Tail).parse(&rest)?;
                (n, AChooseWithDefault::Default(v))
            },
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
        Ok((n, v))
    }
}

} // verus!
