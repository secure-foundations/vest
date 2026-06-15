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
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `a_typed_choose`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum ATypedChoose {
    X(u8),
    Y(u16),
    Z(u32),
}

pub type ATypedChooseSpec = ATypedChoose;

pub type ATypedChooseInner = Sum<u8, Sum<u16, u32>>;

impl DeepView for ATypedChoose {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `a_typed_open_enum`."]
# [repr (u32)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum ATypedOpenEnum {
    P = 0,
    Q = 1,
    R = 2,
    Unknown(u32),
}

pub type ATypedOpenEnumSpec = ATypedOpenEnum;

pub type ATypedOpenEnumInner = Sum<u32, u32>;

impl DeepView for ATypedOpenEnum {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
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
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum ANonDependentChoose {
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
}

pub type ANonDependentChooseSpec = ANonDependentChoose;

pub type ANonDependentChooseInner = Sum<u8, Sum<u8, u8>>;

impl DeepView for ANonDependentChoose {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `a_regular_choose`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum ARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type ARegularChooseSpec = ARegularChoose;

pub type ARegularChooseInner = Sum<u8, Sum<u16, u32>>;

impl DeepView for ARegularChoose {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `a_mixed_typed_enum`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum AMixedTypedEnum {
    M = 0,
    N = 1,
    O = 2,
}

pub type AMixedTypedEnumSpec = AMixedTypedEnum;

pub type AMixedTypedEnumInner = u8;

impl DeepView for AMixedTypedEnum {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
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
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum AClosedEnum {
    A = 0,
    B = 1,
    C = 2,
}

pub type AClosedEnumSpec = AClosedEnum;

pub type AClosedEnumInner = u8;

impl DeepView for AClosedEnum {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
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
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum ATypedClosedEnum {
    X = 0,
    Y = 1,
    Z = 2,
}

pub type ATypedClosedEnumSpec = ATypedClosedEnum;

pub type ATypedClosedEnumInner = u16;

impl DeepView for ATypedClosedEnum {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
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
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum AnOpenEnum {
    A = 0,
    B = 1,
    C = 2,
    Unknown(u8),
}

pub type AnOpenEnumSpec = AnOpenEnum;

pub type AnOpenEnumInner = Sum<u8, u8>;

impl DeepView for AnOpenEnum {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
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
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum ATypedChooseWithDefault<'i> {
    P(u8),
    Q(u16),
    R(u32),
    Default(&'i [u8]),
}

# [verifier::ext_equal]
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
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum AChooseWithDefault<'i> {
    A(u8),
    B(u16),
    C(u32),
    Default(&'i [u8]),
}

# [verifier::ext_equal]
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
# [derive (Clone, Copy)]
pub struct ATypedChooseFmt {
    e: ATypedClosedEnum,
}

impl ATypedChooseFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        ATypedClosedEnumFmt.consistent(self.e.deep_view())
    }

    pub closed spec fn e_spec(&self) -> ATypedClosedEnumSpec {
        self.e.deep_view()
    }

    pub closed spec fn spec(e: ATypedClosedEnum) -> Self {
        ATypedChooseFmt { e }
    }
}

pub type ATypedChooseFmtSpec = Named<
    Mapped<Sum<U8, Sum<U16Le, U32Le>>, FnSpecMapper<ATypedChooseInner, ATypedChooseSpec>>,
>;

impl ATypedChooseFmt {
    # [doc = "specification constructor for `a_typed_choose`."]
    pub open spec fn spec_inner(e: ATypedClosedEnumSpec) -> ATypedChooseFmtSpec {
        Named(
            "a_typed_choose",
            Mapped {
                inner: match e {
                    ATypedClosedEnumSpec::X => L(U8),
                    ATypedClosedEnumSpec::Y => R(L(U16Le)),
                    ATypedClosedEnumSpec::Z => R(R(U32Le)),
                },
                mapper: (
                    |parsed: ATypedChooseInner| -> ATypedChooseSpec
                        {
                            match parsed {
                                L(v) => ATypedChooseSpec::X(v),
                                R(L(v)) => ATypedChooseSpec::Y(v),
                                R(R(v)) => ATypedChooseSpec::Z(v),
                            }
                        },
                    |value: ATypedChooseSpec| -> ATypedChooseInner
                        {
                            match value {
                                ATypedChooseSpec::X(v) => L(v),
                                ATypedChooseSpec::Y(v) => R(L(v)),
                                ATypedChooseSpec::Z(v) => R(R(v)),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `a_typed_open_enum`."]
# [derive (Clone, Copy)]
pub struct ATypedOpenEnumFmt;

pub type ATypedOpenEnumFmtSpec = Named<
    Mapped<
        Choice<Refined<U32Le, PredFnSpec<u32>>, Refined<U32Le, PredFnSpec<u32>>>,
        FnSpecMapper<ATypedOpenEnumInner, ATypedOpenEnumSpec>,
    >,
>;

impl ATypedOpenEnumFmt {
    # [doc = "specification constructor for `a_typed_open_enum`."]
    pub open spec fn spec_inner() -> ATypedOpenEnumFmtSpec {
        Named(
            "a_typed_open_enum",
            Mapped {
                inner: Choice(
                    Refined(U32Le, |x: u32| ((x == 0) || (x == 1)) || (x == 2)),
                    Refined(U32Le, |x: u32| ((x != 0) && (x != 1)) && (x != 2)),
                ),
                mapper: (
                    |parsed: ATypedOpenEnumInner| -> ATypedOpenEnumSpec
                        {
                            match parsed {
                                L(x) => match x {
                                    0 => ATypedOpenEnumSpec::P,
                                    1 => ATypedOpenEnumSpec::Q,
                                    2 => ATypedOpenEnumSpec::R,
                                    _ => arbitrary(),
                                },
                                R(x) => ATypedOpenEnumSpec::Unknown(x),
                            }
                        },
                    |value: ATypedOpenEnumSpec| -> ATypedOpenEnumInner
                        {
                            match value {
                                ATypedOpenEnumSpec::P => L(0),
                                ATypedOpenEnumSpec::Q => L(1),
                                ATypedOpenEnumSpec::R => L(2),
                                ATypedOpenEnumSpec::Unknown(x) => R(x),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `a_non_dependent_choose`."]
# [derive (Clone, Copy)]
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

impl ANonDependentChooseFmt {
    # [doc = "specification constructor for `a_non_dependent_choose`."]
    pub open spec fn spec_inner() -> ANonDependentChooseFmtSpec {
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
                                L(v) => ANonDependentChooseSpec::Variant1(v),
                                R(L(v)) => ANonDependentChooseSpec::Variant2(v),
                                R(R(v)) => ANonDependentChooseSpec::Variant3(v),
                            }
                        },
                    |value: ANonDependentChooseSpec| -> ANonDependentChooseInner
                        {
                            match value {
                                ANonDependentChooseSpec::Variant1(v) => L(v),
                                ANonDependentChooseSpec::Variant2(v) => R(L(v)),
                                ANonDependentChooseSpec::Variant3(v) => R(R(v)),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `a_regular_choose`."]
# [derive (Clone, Copy)]
pub struct ARegularChooseFmt {
    e: AClosedEnum,
}

impl ARegularChooseFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        AClosedEnumFmt.consistent(self.e.deep_view())
    }

    pub closed spec fn e_spec(&self) -> AClosedEnumSpec {
        self.e.deep_view()
    }

    pub closed spec fn spec(e: AClosedEnum) -> Self {
        ARegularChooseFmt { e }
    }
}

pub type ARegularChooseFmtSpec = Named<
    Mapped<Sum<U8, Sum<U16Le, U32Le>>, FnSpecMapper<ARegularChooseInner, ARegularChooseSpec>>,
>;

impl ARegularChooseFmt {
    # [doc = "specification constructor for `a_regular_choose`."]
    pub open spec fn spec_inner(e: AClosedEnumSpec) -> ARegularChooseFmtSpec {
        Named(
            "a_regular_choose",
            Mapped {
                inner: match e {
                    AClosedEnumSpec::A => L(U8),
                    AClosedEnumSpec::B => R(L(U16Le)),
                    AClosedEnumSpec::C => R(R(U32Le)),
                },
                mapper: (
                    |parsed: ARegularChooseInner| -> ARegularChooseSpec
                        {
                            match parsed {
                                L(v) => ARegularChooseSpec::A(v),
                                R(L(v)) => ARegularChooseSpec::B(v),
                                R(R(v)) => ARegularChooseSpec::C(v),
                            }
                        },
                    |value: ARegularChooseSpec| -> ARegularChooseInner
                        {
                            match value {
                                ARegularChooseSpec::A(v) => L(v),
                                ARegularChooseSpec::B(v) => R(L(v)),
                                ARegularChooseSpec::C(v) => R(R(v)),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `a_mixed_typed_enum`."]
# [derive (Clone, Copy)]
pub struct AMixedTypedEnumFmt;

pub type AMixedTypedEnumFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<AMixedTypedEnumInner, AMixedTypedEnumSpec>>,
>;

impl AMixedTypedEnumFmt {
    # [doc = "specification constructor for `a_mixed_typed_enum`."]
    pub open spec fn spec_inner() -> AMixedTypedEnumFmtSpec {
        Named(
            "a_mixed_typed_enum",
            Mapped {
                inner: Refined(U8, |x: u8| ((x == 0) || (x == 1)) || (x == 2)),
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
}

# [doc = "named format combinator for `a_closed_enum`."]
# [derive (Clone, Copy)]
pub struct AClosedEnumFmt;

pub type AClosedEnumFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<AClosedEnumInner, AClosedEnumSpec>>,
>;

impl AClosedEnumFmt {
    # [doc = "specification constructor for `a_closed_enum`."]
    pub open spec fn spec_inner() -> AClosedEnumFmtSpec {
        Named(
            "a_closed_enum",
            Mapped {
                inner: Refined(U8, |x: u8| ((x == 0) || (x == 1)) || (x == 2)),
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
}

# [doc = "named format combinator for `a_typed_closed_enum`."]
# [derive (Clone, Copy)]
pub struct ATypedClosedEnumFmt;

pub type ATypedClosedEnumFmtSpec = Named<
    Mapped<
        Refined<U16Le, PredFnSpec<u16>>,
        FnSpecMapper<ATypedClosedEnumInner, ATypedClosedEnumSpec>,
    >,
>;

impl ATypedClosedEnumFmt {
    # [doc = "specification constructor for `a_typed_closed_enum`."]
    pub open spec fn spec_inner() -> ATypedClosedEnumFmtSpec {
        Named(
            "a_typed_closed_enum",
            Mapped {
                inner: Refined(U16Le, |x: u16| ((x == 0) || (x == 1)) || (x == 2)),
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
}

# [doc = "named format combinator for `an_open_enum`."]
# [derive (Clone, Copy)]
pub struct AnOpenEnumFmt;

pub type AnOpenEnumFmtSpec = Named<
    Mapped<
        Choice<Refined<U8, PredFnSpec<u8>>, Refined<U8, PredFnSpec<u8>>>,
        FnSpecMapper<AnOpenEnumInner, AnOpenEnumSpec>,
    >,
>;

impl AnOpenEnumFmt {
    # [doc = "specification constructor for `an_open_enum`."]
    pub open spec fn spec_inner() -> AnOpenEnumFmtSpec {
        Named(
            "an_open_enum",
            Mapped {
                inner: Choice(
                    Refined(U8, |x: u8| ((x == 0) || (x == 1)) || (x == 2)),
                    Refined(U8, |x: u8| ((x != 0) && (x != 1)) && (x != 2)),
                ),
                mapper: (
                    |parsed: AnOpenEnumInner| -> AnOpenEnumSpec
                        {
                            match parsed {
                                L(x) => match x {
                                    0 => AnOpenEnumSpec::A,
                                    1 => AnOpenEnumSpec::B,
                                    2 => AnOpenEnumSpec::C,
                                    _ => arbitrary(),
                                },
                                R(x) => AnOpenEnumSpec::Unknown(x),
                            }
                        },
                    |value: AnOpenEnumSpec| -> AnOpenEnumInner
                        {
                            match value {
                                AnOpenEnumSpec::A => L(0),
                                AnOpenEnumSpec::B => L(1),
                                AnOpenEnumSpec::C => L(2),
                                AnOpenEnumSpec::Unknown(x) => R(x),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `a_typed_choose_with_default`."]
# [derive (Clone, Copy)]
pub struct ATypedChooseWithDefaultFmt {
    e: ATypedOpenEnum,
}

impl ATypedChooseWithDefaultFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        ATypedOpenEnumFmt.consistent(self.e.deep_view())
    }

    pub closed spec fn e_spec(&self) -> ATypedOpenEnumSpec {
        self.e.deep_view()
    }

    pub closed spec fn spec(e: ATypedOpenEnum) -> Self {
        ATypedChooseWithDefaultFmt { e }
    }
}

pub type ATypedChooseWithDefaultFmtSpec = Named<
    Mapped<
        Sum<U8, Sum<U16Le, Sum<U32Le, Tail>>>,
        FnSpecMapper<ATypedChooseWithDefaultInner, ATypedChooseWithDefaultSpec>,
    >,
>;

impl ATypedChooseWithDefaultFmt {
    # [doc = "specification constructor for `a_typed_choose_with_default`."]
    pub open spec fn spec_inner(e: ATypedOpenEnumSpec) -> ATypedChooseWithDefaultFmtSpec {
        Named(
            "a_typed_choose_with_default",
            Mapped {
                inner: match e {
                    ATypedOpenEnumSpec::P => L(U8),
                    ATypedOpenEnumSpec::Q => R(L(U16Le)),
                    ATypedOpenEnumSpec::R => R(R(L(U32Le))),
                    _ => R(R(R(Tail))),
                },
                mapper: (
                    |parsed: ATypedChooseWithDefaultInner| -> ATypedChooseWithDefaultSpec
                        {
                            match parsed {
                                L(v) => ATypedChooseWithDefaultSpec::P(v),
                                R(L(v)) => ATypedChooseWithDefaultSpec::Q(v),
                                R(R(L(v))) => ATypedChooseWithDefaultSpec::R(v),
                                R(R(R(v))) => ATypedChooseWithDefaultSpec::Default(v),
                            }
                        },
                    |value: ATypedChooseWithDefaultSpec| -> ATypedChooseWithDefaultInner
                        {
                            match value {
                                ATypedChooseWithDefaultSpec::P(v) => L(v),
                                ATypedChooseWithDefaultSpec::Q(v) => R(L(v)),
                                ATypedChooseWithDefaultSpec::R(v) => R(R(L(v))),
                                ATypedChooseWithDefaultSpec::Default(v) => R(R(R(v))),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `a_choose_with_default`."]
# [derive (Clone, Copy)]
pub struct AChooseWithDefaultFmt {
    e: AnOpenEnum,
}

impl AChooseWithDefaultFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        AnOpenEnumFmt.consistent(self.e.deep_view())
    }

    pub closed spec fn e_spec(&self) -> AnOpenEnumSpec {
        self.e.deep_view()
    }

    pub closed spec fn spec(e: AnOpenEnum) -> Self {
        AChooseWithDefaultFmt { e }
    }
}

pub type AChooseWithDefaultFmtSpec = Named<
    Mapped<
        Sum<U8, Sum<U16Le, Sum<U32Le, Tail>>>,
        FnSpecMapper<AChooseWithDefaultInner, AChooseWithDefaultSpec>,
    >,
>;

impl AChooseWithDefaultFmt {
    # [doc = "specification constructor for `a_choose_with_default`."]
    pub open spec fn spec_inner(e: AnOpenEnumSpec) -> AChooseWithDefaultFmtSpec {
        Named(
            "a_choose_with_default",
            Mapped {
                inner: match e {
                    AnOpenEnumSpec::A => L(U8),
                    AnOpenEnumSpec::B => R(L(U16Le)),
                    AnOpenEnumSpec::C => R(R(L(U32Le))),
                    _ => R(R(R(Tail))),
                },
                mapper: (
                    |parsed: AChooseWithDefaultInner| -> AChooseWithDefaultSpec
                        {
                            match parsed {
                                L(v) => AChooseWithDefaultSpec::A(v),
                                R(L(v)) => AChooseWithDefaultSpec::B(v),
                                R(R(L(v))) => AChooseWithDefaultSpec::C(v),
                                R(R(R(v))) => AChooseWithDefaultSpec::Default(v),
                            }
                        },
                    |value: AChooseWithDefaultSpec| -> AChooseWithDefaultInner
                        {
                            match value {
                                AChooseWithDefaultSpec::A(v) => L(v),
                                AChooseWithDefaultSpec::B(v) => R(L(v)),
                                AChooseWithDefaultSpec::C(v) => R(R(L(v))),
                                AChooseWithDefaultSpec::Default(v) => R(R(R(v))),
                            }
                        },
                ),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ATypedChooseFmt {
        type PVal = ATypedChooseSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ATypedChooseFmt::spec_inner(self.e_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for ATypedChooseFmt {
        type Val = ATypedChooseSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ATypedChooseFmt::spec_inner(self.e_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for ATypedChooseFmt {
        type SValue = ATypedChooseSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ATypedChooseFmt::spec_inner(self.e_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypedChooseFmt {
        type SVal = ATypedChooseSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ATypedChooseFmt::spec_inner(self.e_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypedChooseFmt {
        type T = ATypedChooseSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ATypedChooseFmt::spec_inner(self.e_spec()).byte_len(v)
        }
    }

    impl SpecParser for ATypedOpenEnumFmt {
        type PVal = ATypedOpenEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ATypedOpenEnumFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ATypedOpenEnumFmt {
        type Val = ATypedOpenEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ATypedOpenEnumFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ATypedOpenEnumFmt {
        type SValue = ATypedOpenEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ATypedOpenEnumFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypedOpenEnumFmt {
        type SVal = ATypedOpenEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ATypedOpenEnumFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypedOpenEnumFmt {
        type T = ATypedOpenEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ATypedOpenEnumFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ANonDependentChooseFmt {
        type PVal = ANonDependentChooseSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ANonDependentChooseFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ANonDependentChooseFmt {
        type Val = ANonDependentChooseSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ANonDependentChooseFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ANonDependentChooseFmt {
        type SValue = ANonDependentChooseSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ANonDependentChooseFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ANonDependentChooseFmt {
        type SVal = ANonDependentChooseSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ANonDependentChooseFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ANonDependentChooseFmt {
        type T = ANonDependentChooseSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ANonDependentChooseFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ARegularChooseFmt {
        type PVal = ARegularChooseSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ARegularChooseFmt::spec_inner(self.e_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for ARegularChooseFmt {
        type Val = ARegularChooseSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ARegularChooseFmt::spec_inner(self.e_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for ARegularChooseFmt {
        type SValue = ARegularChooseSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ARegularChooseFmt::spec_inner(self.e_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ARegularChooseFmt {
        type SVal = ARegularChooseSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ARegularChooseFmt::spec_inner(self.e_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ARegularChooseFmt {
        type T = ARegularChooseSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ARegularChooseFmt::spec_inner(self.e_spec()).byte_len(v)
        }
    }

    impl SpecParser for AMixedTypedEnumFmt {
        type PVal = AMixedTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            AMixedTypedEnumFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for AMixedTypedEnumFmt {
        type Val = AMixedTypedEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            AMixedTypedEnumFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for AMixedTypedEnumFmt {
        type SValue = AMixedTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            AMixedTypedEnumFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AMixedTypedEnumFmt {
        type SVal = AMixedTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            AMixedTypedEnumFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for AMixedTypedEnumFmt {
        type T = AMixedTypedEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            AMixedTypedEnumFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for AClosedEnumFmt {
        type PVal = AClosedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            AClosedEnumFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for AClosedEnumFmt {
        type Val = AClosedEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            AClosedEnumFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for AClosedEnumFmt {
        type SValue = AClosedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            AClosedEnumFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AClosedEnumFmt {
        type SVal = AClosedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            AClosedEnumFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for AClosedEnumFmt {
        type T = AClosedEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            AClosedEnumFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ATypedClosedEnumFmt {
        type PVal = ATypedClosedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ATypedClosedEnumFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ATypedClosedEnumFmt {
        type Val = ATypedClosedEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ATypedClosedEnumFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ATypedClosedEnumFmt {
        type SValue = ATypedClosedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ATypedClosedEnumFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypedClosedEnumFmt {
        type SVal = ATypedClosedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ATypedClosedEnumFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypedClosedEnumFmt {
        type T = ATypedClosedEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ATypedClosedEnumFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for AnOpenEnumFmt {
        type PVal = AnOpenEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            AnOpenEnumFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for AnOpenEnumFmt {
        type Val = AnOpenEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            AnOpenEnumFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for AnOpenEnumFmt {
        type SValue = AnOpenEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            AnOpenEnumFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AnOpenEnumFmt {
        type SVal = AnOpenEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            AnOpenEnumFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for AnOpenEnumFmt {
        type T = AnOpenEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            AnOpenEnumFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ATypedChooseWithDefaultFmt {
        type PVal = ATypedChooseWithDefaultSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ATypedChooseWithDefaultFmt::spec_inner(self.e_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for ATypedChooseWithDefaultFmt {
        type Val = ATypedChooseWithDefaultSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ATypedChooseWithDefaultFmt::spec_inner(self.e_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for ATypedChooseWithDefaultFmt {
        type SValue = ATypedChooseWithDefaultSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ATypedChooseWithDefaultFmt::spec_inner(self.e_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypedChooseWithDefaultFmt {
        type SVal = ATypedChooseWithDefaultSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ATypedChooseWithDefaultFmt::spec_inner(self.e_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypedChooseWithDefaultFmt {
        type T = ATypedChooseWithDefaultSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ATypedChooseWithDefaultFmt::spec_inner(self.e_spec()).byte_len(v)
        }
    }

    impl SpecParser for AChooseWithDefaultFmt {
        type PVal = AChooseWithDefaultSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            AChooseWithDefaultFmt::spec_inner(self.e_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for AChooseWithDefaultFmt {
        type Val = AChooseWithDefaultSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            AChooseWithDefaultFmt::spec_inner(self.e_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for AChooseWithDefaultFmt {
        type SValue = AChooseWithDefaultSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            AChooseWithDefaultFmt::spec_inner(self.e_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AChooseWithDefaultFmt {
        type SVal = AChooseWithDefaultSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            AChooseWithDefaultFmt::spec_inner(self.e_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for AChooseWithDefaultFmt {
        type T = AChooseWithDefaultSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            AChooseWithDefaultFmt::spec_inner(self.e_spec()).byte_len(v)
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
            ATypedChooseFmt::spec_inner(self.e_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypedChooseFmt {
        open spec fn productive_inv(&self) -> bool {
            ATypedChooseFmt::spec_inner(self.e_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypedChooseFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseFmt as SpecByteLen>::byte_len);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseFmt as Consistency>::consistent);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ATypedChooseFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseFmt as SpecByteLen>::byte_len);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ATypedChooseFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypedChooseFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypedChooseFmt as SpecByteLen>::byte_len);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
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
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypedChooseFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ATypedChooseFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ATypedChooseFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypedChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypedChooseFmt::spec_inner(self.e_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ATypedOpenEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            ATypedOpenEnumFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypedOpenEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            ATypedOpenEnumFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypedOpenEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedOpenEnumFmt as Consistency>::consistent);
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ATypedOpenEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ATypedOpenEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypedOpenEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypedOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = ATypedOpenEnumFmt::spec_inner();
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
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypedOpenEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecParser>::spec_parse);
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ATypedOpenEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedOpenEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ATypedOpenEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypedOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedOpenEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypedOpenEnumFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ANonDependentChooseFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            ANonDependentChooseFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ANonDependentChooseFmt {
        open spec fn productive_inv(&self) -> bool {
            ANonDependentChooseFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ANonDependentChooseFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            reveal(<ANonDependentChooseFmt as SpecByteLen>::byte_len);
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            reveal(<ANonDependentChooseFmt as Consistency>::consistent);
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ANonDependentChooseFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ANonDependentChooseFmt as SpecByteLen>::byte_len);
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ANonDependentChooseFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ANonDependentChooseFmt as SpecSerializer>::spec_serialize);
            reveal(<ANonDependentChooseFmt as SpecByteLen>::byte_len);
            let fmt = ANonDependentChooseFmt::spec_inner();
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
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ANonDependentChooseFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ANonDependentChooseFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ANonDependentChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ANonDependentChooseFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ANonDependentChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ANonDependentChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = ANonDependentChooseFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ARegularChooseFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            ARegularChooseFmt::spec_inner(self.e_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ARegularChooseFmt {
        open spec fn productive_inv(&self) -> bool {
            ARegularChooseFmt::spec_inner(self.e_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ARegularChooseFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            reveal(<ARegularChooseFmt as SpecByteLen>::byte_len);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            reveal(<ARegularChooseFmt as Consistency>::consistent);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ARegularChooseFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ARegularChooseFmt as SpecByteLen>::byte_len);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ARegularChooseFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ARegularChooseFmt as SpecSerializer>::spec_serialize);
            reveal(<ARegularChooseFmt as SpecByteLen>::byte_len);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
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
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ARegularChooseFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ARegularChooseFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ARegularChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ARegularChooseFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ARegularChooseFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ARegularChooseFmt as SpecSerializer>::spec_serialize);
            let fmt = ARegularChooseFmt::spec_inner(self.e_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AMixedTypedEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            AMixedTypedEnumFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AMixedTypedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            AMixedTypedEnumFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AMixedTypedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<AMixedTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<AMixedTypedEnumFmt as Consistency>::consistent);
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AMixedTypedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AMixedTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AMixedTypedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AMixedTypedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<AMixedTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = AMixedTypedEnumFmt::spec_inner();
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
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AMixedTypedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AMixedTypedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AMixedTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AMixedTypedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AMixedTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AMixedTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = AMixedTypedEnumFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AClosedEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            AClosedEnumFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AClosedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            AClosedEnumFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AClosedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<AClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<AClosedEnumFmt as Consistency>::consistent);
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AClosedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AClosedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AClosedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<AClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = AClosedEnumFmt::spec_inner();
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
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AClosedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecParser>::spec_parse);
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AClosedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AClosedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AClosedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AClosedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = AClosedEnumFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ATypedClosedEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            ATypedClosedEnumFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypedClosedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            ATypedClosedEnumFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypedClosedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            reveal(<ATypedClosedEnumFmt as Consistency>::consistent);
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ATypedClosedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ATypedClosedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypedClosedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypedClosedEnumFmt as SpecByteLen>::byte_len);
            let fmt = ATypedClosedEnumFmt::spec_inner();
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
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypedClosedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecParser>::spec_parse);
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ATypedClosedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedClosedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ATypedClosedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypedClosedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedClosedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypedClosedEnumFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AnOpenEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            AnOpenEnumFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AnOpenEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            AnOpenEnumFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AnOpenEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<AnOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            reveal(<AnOpenEnumFmt as Consistency>::consistent);
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AnOpenEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AnOpenEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AnOpenEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<AnOpenEnumFmt as SpecByteLen>::byte_len);
            let fmt = AnOpenEnumFmt::spec_inner();
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
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AnOpenEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecParser>::spec_parse);
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AnOpenEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnOpenEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AnOpenEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AnOpenEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnOpenEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = AnOpenEnumFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ATypedChooseWithDefaultFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            ATypedChooseWithDefaultFmt::spec_inner(self.e_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypedChooseWithDefaultFmt {
        open spec fn productive_inv(&self) -> bool {
            ATypedChooseWithDefaultFmt::spec_inner(self.e_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            let fmt = ATypedChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypedChooseWithDefaultFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = ATypedChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<ATypedChooseWithDefaultFmt as Consistency>::consistent);
            let fmt = ATypedChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for ATypedChooseWithDefaultFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypedChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypedChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = ATypedChooseWithDefaultFmt::spec_inner(self.e_spec());
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
            let fmt = ATypedChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypedChooseWithDefaultFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            let fmt = ATypedChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for ATypedChooseWithDefaultFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypedChooseWithDefaultFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypedChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypedChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AChooseWithDefaultFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            AChooseWithDefaultFmt::spec_inner(self.e_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AChooseWithDefaultFmt {
        open spec fn productive_inv(&self) -> bool {
            AChooseWithDefaultFmt::spec_inner(self.e_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            let fmt = AChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AChooseWithDefaultFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<AChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = AChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            reveal(<AChooseWithDefaultFmt as Consistency>::consistent);
            let fmt = AChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for AChooseWithDefaultFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            reveal(<AChooseWithDefaultFmt as SpecByteLen>::byte_len);
            let fmt = AChooseWithDefaultFmt::spec_inner(self.e_spec());
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
            let fmt = AChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AChooseWithDefaultFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            let fmt = AChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for AChooseWithDefaultFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AChooseWithDefaultFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            let fmt = AChooseWithDefaultFmt::spec_inner(self.e_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for ATypedChooseFmt {
        type PT = ATypedChoose;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ATypedChooseFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

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

    impl<'i> Serializer<ATypedChoose> for ATypedChooseFmt {
        fn serialize(&self, v: &ATypedChoose, obuf: &mut Vec<u8>) {
            reveal(<ATypedChooseFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.e, v) {
                (ATypedClosedEnum::X, ATypedChoose::X(v)) => {
                    (U8).serialize(v, obuf);
                },
                (ATypedClosedEnum::Y, ATypedChoose::Y(v)) => {
                    (U16Le).serialize(v, obuf);
                },
                (ATypedClosedEnum::Z, ATypedChoose::Z(v)) => {
                    (U32Le).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ATypedChoose> for ATypedChooseFmt {
        fn prepare(&self, v: &ATypedChoose) -> Result<usize, PreSerializeError> {
            reveal(<ATypedChooseFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.e, v) {
                (ATypedClosedEnum::X, ATypedChoose::X(v)) => (U8).prepare(v),
                (ATypedClosedEnum::Y, ATypedChoose::Y(v)) => (U16Le).prepare(v),
                (ATypedClosedEnum::Z, ATypedChoose::Z(v)) => (U32Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for ATypedOpenEnumFmt {
        type PT = ATypedOpenEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
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

    impl<'i> Serializer<ATypedOpenEnum> for ATypedOpenEnumFmt {
        fn serialize(&self, v: &ATypedOpenEnum, obuf: &mut Vec<u8>) {
            reveal(<ATypedOpenEnumFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                ATypedOpenEnum::P => 0,
                ATypedOpenEnum::Q => 1,
                ATypedOpenEnum::R => 2,
                ATypedOpenEnum::Unknown(x) => x,
            };
            U32Le.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ATypedOpenEnum> for ATypedOpenEnumFmt {
        fn prepare(&self, v: &ATypedOpenEnum) -> Result<usize, PreSerializeError> {
            reveal(<ATypedOpenEnumFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                ATypedOpenEnum::P => 0,
                ATypedOpenEnum::Q => 1,
                ATypedOpenEnum::R => 2,
                ATypedOpenEnum::Unknown(x) if x != 0 && x != 1 && x != 2 => x,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U32Le.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for ANonDependentChooseFmt {
        type PT = ANonDependentChoose;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ANonDependentChooseFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U8).parse(&rest) {
                Ok((n, va)) if va >= 0 && va <= 10 => { Ok((n, ANonDependentChoose::Variant1(va)))
                },
                _ => match (U8).parse(&rest) {
                    Ok((n, va)) if va >= 11 && va <= 20 => {
                        Ok((n, ANonDependentChoose::Variant2(va)))
                    },
                    _ => match (U8).parse(&rest) {
                        Ok((n, va)) if va >= 21 => { Ok((n, ANonDependentChoose::Variant3(va))) },
                        _ => Err(ParseError::invalid_choice()),
                    },
                },
            }?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<ANonDependentChoose> for ANonDependentChooseFmt {
        fn serialize(&self, v: &ANonDependentChoose, obuf: &mut Vec<u8>) {
            reveal(<ANonDependentChooseFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            match v {
                ANonDependentChoose::Variant1(v) => {
                    (U8).serialize(v, obuf);
                },
                ANonDependentChoose::Variant2(v) => {
                    (U8).serialize(v, obuf);
                },
                ANonDependentChoose::Variant3(v) => {
                    (U8).serialize(v, obuf);
                },
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ANonDependentChoose> for ANonDependentChooseFmt {
        fn prepare(&self, v: &ANonDependentChoose) -> Result<usize, PreSerializeError> {
            reveal(<ANonDependentChooseFmt as SpecByteLen>::byte_len);
            match v {
                ANonDependentChoose::Variant1(v) => {
                    if !(*v >= 0 && *v <= 10) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U8).prepare(v)
                    }
                },
                ANonDependentChoose::Variant2(v) => {
                    if !(*v >= 11 && *v <= 20) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U8).prepare(v)
                    }
                },
                ANonDependentChoose::Variant3(v) => {
                    if !(*v >= 21) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U8).prepare(v)
                    }
                },
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for ARegularChooseFmt {
        type PT = ARegularChoose;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ARegularChooseFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

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

    impl<'i> Serializer<ARegularChoose> for ARegularChooseFmt {
        fn serialize(&self, v: &ARegularChoose, obuf: &mut Vec<u8>) {
            reveal(<ARegularChooseFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.e, v) {
                (AClosedEnum::A, ARegularChoose::A(v)) => {
                    (U8).serialize(v, obuf);
                },
                (AClosedEnum::B, ARegularChoose::B(v)) => {
                    (U16Le).serialize(v, obuf);
                },
                (AClosedEnum::C, ARegularChoose::C(v)) => {
                    (U32Le).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ARegularChoose> for ARegularChooseFmt {
        fn prepare(&self, v: &ARegularChoose) -> Result<usize, PreSerializeError> {
            reveal(<ARegularChooseFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.e, v) {
                (AClosedEnum::A, ARegularChoose::A(v)) => (U8).prepare(v),
                (AClosedEnum::B, ARegularChoose::B(v)) => (U16Le).prepare(v),
                (AClosedEnum::C, ARegularChoose::C(v)) => (U32Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for AMixedTypedEnumFmt {
        type PT = AMixedTypedEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
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

    impl<'i> Serializer<AMixedTypedEnum> for AMixedTypedEnumFmt {
        fn serialize(&self, v: &AMixedTypedEnum, obuf: &mut Vec<u8>) {
            reveal(<AMixedTypedEnumFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                AMixedTypedEnum::M => 0,
                AMixedTypedEnum::N => 1,
                AMixedTypedEnum::O => 2,
            };
            U8.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AMixedTypedEnum> for AMixedTypedEnumFmt {
        fn prepare(&self, v: &AMixedTypedEnum) -> Result<usize, PreSerializeError> {
            reveal(<AMixedTypedEnumFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                AMixedTypedEnum::M => 0,
                AMixedTypedEnum::N => 1,
                AMixedTypedEnum::O => 2,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for AClosedEnumFmt {
        type PT = AClosedEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
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

    impl<'i> Serializer<AClosedEnum> for AClosedEnumFmt {
        fn serialize(&self, v: &AClosedEnum, obuf: &mut Vec<u8>) {
            reveal(<AClosedEnumFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                AClosedEnum::A => 0,
                AClosedEnum::B => 1,
                AClosedEnum::C => 2,
            };
            U8.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AClosedEnum> for AClosedEnumFmt {
        fn prepare(&self, v: &AClosedEnum) -> Result<usize, PreSerializeError> {
            reveal(<AClosedEnumFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                AClosedEnum::A => 0,
                AClosedEnum::B => 1,
                AClosedEnum::C => 2,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for ATypedClosedEnumFmt {
        type PT = ATypedClosedEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
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

    impl<'i> Serializer<ATypedClosedEnum> for ATypedClosedEnumFmt {
        fn serialize(&self, v: &ATypedClosedEnum, obuf: &mut Vec<u8>) {
            reveal(<ATypedClosedEnumFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                ATypedClosedEnum::X => 0,
                ATypedClosedEnum::Y => 1,
                ATypedClosedEnum::Z => 2,
            };
            U16Le.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ATypedClosedEnum> for ATypedClosedEnumFmt {
        fn prepare(&self, v: &ATypedClosedEnum) -> Result<usize, PreSerializeError> {
            reveal(<ATypedClosedEnumFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                ATypedClosedEnum::X => 0,
                ATypedClosedEnum::Y => 1,
                ATypedClosedEnum::Z => 2,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U16Le.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for AnOpenEnumFmt {
        type PT = AnOpenEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
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

    impl<'i> Serializer<AnOpenEnum> for AnOpenEnumFmt {
        fn serialize(&self, v: &AnOpenEnum, obuf: &mut Vec<u8>) {
            reveal(<AnOpenEnumFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                AnOpenEnum::A => 0,
                AnOpenEnum::B => 1,
                AnOpenEnum::C => 2,
                AnOpenEnum::Unknown(x) => x,
            };
            U8.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AnOpenEnum> for AnOpenEnumFmt {
        fn prepare(&self, v: &AnOpenEnum) -> Result<usize, PreSerializeError> {
            reveal(<AnOpenEnumFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                AnOpenEnum::A => 0,
                AnOpenEnum::B => 1,
                AnOpenEnum::C => 2,
                AnOpenEnum::Unknown(x) if x != 0 && x != 1 && x != 2 => x,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for ATypedChooseWithDefaultFmt {
        type PT = ATypedChooseWithDefault<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ATypedChooseWithDefaultFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

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

    impl<'i> Serializer<ATypedChooseWithDefault<'i>> for ATypedChooseWithDefaultFmt {
        fn serialize(&self, v: &ATypedChooseWithDefault<'i>, obuf: &mut Vec<u8>) {
            reveal(<ATypedChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.e, v) {
                (ATypedOpenEnum::P, ATypedChooseWithDefault::P(v)) => {
                    (U8).serialize(v, obuf);
                },
                (ATypedOpenEnum::Q, ATypedChooseWithDefault::Q(v)) => {
                    (U16Le).serialize(v, obuf);
                },
                (ATypedOpenEnum::R, ATypedChooseWithDefault::R(v)) => {
                    (U32Le).serialize(v, obuf);
                },
                (_, ATypedChooseWithDefault::Default(v)) => {
                    (Tail).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ATypedChooseWithDefault<'i>> for ATypedChooseWithDefaultFmt {
        fn prepare(&self, v: &ATypedChooseWithDefault<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ATypedChooseWithDefaultFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.e, v) {
                (ATypedOpenEnum::P, ATypedChooseWithDefault::P(v)) => (U8).prepare(v),
                (ATypedOpenEnum::Q, ATypedChooseWithDefault::Q(v)) => (U16Le).prepare(v),
                (ATypedOpenEnum::R, ATypedChooseWithDefault::R(v)) => (U32Le).prepare(v),
                (ATypedOpenEnum::Unknown(x), ATypedChooseWithDefault::Default(v)) if x != 0 && x
                    != 1 && x != 2 => (Tail).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for AChooseWithDefaultFmt {
        type PT = AChooseWithDefault<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<AChooseWithDefaultFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

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

    impl<'i> Serializer<AChooseWithDefault<'i>> for AChooseWithDefaultFmt {
        fn serialize(&self, v: &AChooseWithDefault<'i>, obuf: &mut Vec<u8>) {
            reveal(<AChooseWithDefaultFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.e, v) {
                (AnOpenEnum::A, AChooseWithDefault::A(v)) => {
                    (U8).serialize(v, obuf);
                },
                (AnOpenEnum::B, AChooseWithDefault::B(v)) => {
                    (U16Le).serialize(v, obuf);
                },
                (AnOpenEnum::C, AChooseWithDefault::C(v)) => {
                    (U32Le).serialize(v, obuf);
                },
                (_, AChooseWithDefault::Default(v)) => {
                    (Tail).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AChooseWithDefault<'i>> for AChooseWithDefaultFmt {
        fn prepare(&self, v: &AChooseWithDefault<'i>) -> Result<usize, PreSerializeError> {
            reveal(<AChooseWithDefaultFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.e, v) {
                (AnOpenEnum::A, AChooseWithDefault::A(v)) => (U8).prepare(v),
                (AnOpenEnum::B, AChooseWithDefault::B(v)) => (U16Le).prepare(v),
                (AnOpenEnum::C, AChooseWithDefault::C(v)) => (U32Le).prepare(v),
                (AnOpenEnum::Unknown(x), AChooseWithDefault::Default(v)) if x != 0 && x != 1 && x
                    != 2 => (Tail).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

} // verus!
