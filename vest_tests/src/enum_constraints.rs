#![allow(warnings)]
use vest_lib::combinators::mapped::spec::*;
use vest_lib::combinators::recursive::*;
use vest_lib::combinators::*;
use vest_lib::core::exec::bytes_eq;
use vest_lib::core::exec::input::{InputBuf, InputSlice};
use vest_lib::core::exec::output::OutputBuf;
use vest_lib::core::exec::parser::*;
use vest_lib::core::exec::serializer::*;
use vest_lib::core::exec::ParseError;
use vest_lib::core::{proof::*, spec::*};
use vest_lib::primitives::btcvarint::VarInt;
use vest_lib::primitives::leb128::ULeb128;
use vest_lib::Never;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `my_enum`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum MyEnum {
    A = 1,
    B = 2,
    C = 3,
}

pub type MyEnumSpec = MyEnum;

pub type MyEnumInner = u8;

impl DeepView for MyEnum {
    type V = Self;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl MyEnum {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<MyEnum as DeepView>::deep_view);
    }

    pub open spec fn structural_valid(input: MyEnumInner) -> bool {
        {
            let x = input;
            x == 1 || x == 2 || x == 3
        }
    }

    # [verifier::opaque]
    pub open spec fn from_structural(input: MyEnumInner) -> Self {
        match input {
            1 => Self::A,
            2 => Self::B,
            3 => Self::C,
            _ => arbitrary(),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> MyEnumInner {
        match self {
            Self::A => 1,
            Self::B => 2,
            Self::C => 3,
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(MyEnum::from_structural);
        reveal(MyEnum::into_structural);
        match self {
            Self::A => {},
            Self::B => {},
            Self::C => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: MyEnumInner)
        requires
            Self::structural_valid(input),
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(MyEnum::from_structural);
        reveal(MyEnum::into_structural);
        match input {
            1 => {},
            2 => {},
            3 => {},
            _ => {
                assert(false);
            },
        }
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MyEnumForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MyEnumReverse;

impl SpecMap for MyEnumForward {
    type Input = MyEnumInner;

    type Output = MyEnumSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        MyEnum::from_structural(input)
    }
}

impl SpecMap for MyEnumReverse {
    type Input = MyEnumSpec;

    type Output = MyEnumInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for MyEnum {

}

# [doc = "data type for `enum_constraints`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct EnumConstraints {
    pub foo: MyEnum,
    pub bar: MyEnum,
    pub baz: MyEnum,
    pub tag: MyEnum,
}

# [verifier::ext_equal]
pub struct EnumConstraintsSpec<T0 = MyEnumSpec, T1 = MyEnumSpec, T2 = MyEnumSpec, T3 = MyEnumSpec> {
    pub foo: T0,
    pub bar: T1,
    pub baz: T2,
    pub tag: T3,
}

pub type EnumConstraintsInner = (MyEnumSpec, (MyEnumSpec, (MyEnumSpec, MyEnumSpec)));

impl DeepView for EnumConstraints {
    type V = EnumConstraintsSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        EnumConstraintsSpec {
            foo: self.foo.deep_view(),
            bar: self.bar.deep_view(),
            baz: self.baz.deep_view(),
            tag: self.tag.deep_view(),
        }
    }
}

impl EnumConstraints {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().foo == self.foo.deep_view(),
            self.deep_view().bar == self.bar.deep_view(),
            self.deep_view().baz == self.baz.deep_view(),
            self.deep_view().tag == self.tag.deep_view(),
    {
        reveal(<EnumConstraints as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3> EnumConstraintsSpec<T0, T1, T2, T3> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, T3)))) -> Self {
        let (foo, (bar, (baz, tag))) = input;
        Self { foo, bar, baz, tag }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, T3))) {
        let Self { foo, bar, baz, tag } = self;
        (foo, (bar, (baz, tag)))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(EnumConstraintsSpec::from_structural);
        reveal(EnumConstraintsSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, T3))))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(EnumConstraintsSpec::from_structural);
        reveal(EnumConstraintsSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { foo, bar, baz, tag } => (foo, (bar, (baz, tag))),
            },
    {
        reveal(EnumConstraintsSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct EnumConstraintsForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct EnumConstraintsReverse;

impl SpecMap for EnumConstraintsForward {
    type Input = EnumConstraintsInner;

    type Output = EnumConstraintsSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        EnumConstraintsSpec::from_structural(input)
    }
}

impl SpecMap for EnumConstraintsReverse {
    type Input = EnumConstraintsSpec;

    type Output = EnumConstraintsInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `my_typed_enum`."]
# [repr (u16)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum MyTypedEnum {
    X = 1,
    Y = 2,
    Z = 3,
}

pub type MyTypedEnumSpec = MyTypedEnum;

pub type MyTypedEnumInner = u16;

impl DeepView for MyTypedEnum {
    type V = Self;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl MyTypedEnum {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<MyTypedEnum as DeepView>::deep_view);
    }

    pub open spec fn structural_valid(input: MyTypedEnumInner) -> bool {
        {
            let x = input;
            x == 1 || x == 2 || x == 3
        }
    }

    # [verifier::opaque]
    pub open spec fn from_structural(input: MyTypedEnumInner) -> Self {
        match input {
            1 => Self::X,
            2 => Self::Y,
            3 => Self::Z,
            _ => arbitrary(),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> MyTypedEnumInner {
        match self {
            Self::X => 1,
            Self::Y => 2,
            Self::Z => 3,
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(MyTypedEnum::from_structural);
        reveal(MyTypedEnum::into_structural);
        match self {
            Self::X => {},
            Self::Y => {},
            Self::Z => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: MyTypedEnumInner)
        requires
            Self::structural_valid(input),
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(MyTypedEnum::from_structural);
        reveal(MyTypedEnum::into_structural);
        match input {
            1 => {},
            2 => {},
            3 => {},
            _ => {
                assert(false);
            },
        }
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MyTypedEnumForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MyTypedEnumReverse;

impl SpecMap for MyTypedEnumForward {
    type Input = MyTypedEnumInner;

    type Output = MyTypedEnumSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        MyTypedEnum::from_structural(input)
    }
}

impl SpecMap for MyTypedEnumReverse {
    type Input = MyTypedEnumSpec;

    type Output = MyTypedEnumInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for MyTypedEnum {

}

# [doc = "data type for `typed_enum_constraints`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct TypedEnumConstraints {
    pub foo: MyTypedEnum,
    pub bar: MyTypedEnum,
    pub baz: MyTypedEnum,
    pub tag: MyTypedEnum,
}

# [verifier::ext_equal]
pub struct TypedEnumConstraintsSpec<
    T0 = MyTypedEnumSpec,
    T1 = MyTypedEnumSpec,
    T2 = MyTypedEnumSpec,
    T3 = MyTypedEnumSpec,
> {
    pub foo: T0,
    pub bar: T1,
    pub baz: T2,
    pub tag: T3,
}

pub type TypedEnumConstraintsInner = (
    MyTypedEnumSpec,
    (MyTypedEnumSpec, (MyTypedEnumSpec, MyTypedEnumSpec)),
);

impl DeepView for TypedEnumConstraints {
    type V = TypedEnumConstraintsSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TypedEnumConstraintsSpec {
            foo: self.foo.deep_view(),
            bar: self.bar.deep_view(),
            baz: self.baz.deep_view(),
            tag: self.tag.deep_view(),
        }
    }
}

impl TypedEnumConstraints {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().foo == self.foo.deep_view(),
            self.deep_view().bar == self.bar.deep_view(),
            self.deep_view().baz == self.baz.deep_view(),
            self.deep_view().tag == self.tag.deep_view(),
    {
        reveal(<TypedEnumConstraints as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3> TypedEnumConstraintsSpec<T0, T1, T2, T3> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, T3)))) -> Self {
        let (foo, (bar, (baz, tag))) = input;
        Self { foo, bar, baz, tag }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, T3))) {
        let Self { foo, bar, baz, tag } = self;
        (foo, (bar, (baz, tag)))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TypedEnumConstraintsSpec::from_structural);
        reveal(TypedEnumConstraintsSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, T3))))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TypedEnumConstraintsSpec::from_structural);
        reveal(TypedEnumConstraintsSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { foo, bar, baz, tag } => (foo, (bar, (baz, tag))),
            },
    {
        reveal(TypedEnumConstraintsSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TypedEnumConstraintsForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TypedEnumConstraintsReverse;

impl SpecMap for TypedEnumConstraintsForward {
    type Input = TypedEnumConstraintsInner;

    type Output = TypedEnumConstraintsSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TypedEnumConstraintsSpec::from_structural(input)
    }
}

impl SpecMap for TypedEnumConstraintsReverse {
    type Input = TypedEnumConstraintsSpec;

    type Output = TypedEnumConstraintsInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `my_enum`."]
# [derive (Clone, Copy)]
pub struct MyEnumFmt;

pub type MyEnumFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, BiMap<MyEnumForward, MyEnumReverse>>,
>;

impl MyEnumFmt {
    # [doc = "specification constructor for `my_enum`."]
    pub open spec fn spec_inner() -> MyEnumFmtSpec {
        Named(
            "my_enum",
            Mapped {
                inner: Refined(U8, |x: u8| ((x == 1) || (x == 2)) || (x == 3)),
                mapper: BiMap(MyEnumForward, MyEnumReverse),
            },
        )
    }
}

# [doc = "named format combinator for `enum_constraints`."]
# [derive (Clone, Copy)]
pub struct EnumConstraintsFmt;

pub type EnumConstraintsFmtSpec = Named<
    Mapped<
        Pair<
            Refined<MyEnumFmt, PredFnSpec<MyEnumSpec>>,
            Pair<
                Refined<MyEnumFmt, PredFnSpec<MyEnumSpec>>,
                Pair<Refined<MyEnumFmt, PredFnSpec<MyEnumSpec>>, Const<MyEnumFmt, MyEnumSpec>>,
            >,
        >,
        BiMap<EnumConstraintsForward, EnumConstraintsReverse>,
    >,
>;

impl EnumConstraintsFmt {
    # [doc = "specification constructor for `enum_constraints`."]
    pub open spec fn spec_inner() -> EnumConstraintsFmtSpec {
        Named(
            "enum_constraints",
            Mapped {
                inner: Pair(
                    Refined(MyEnumFmt, |x: MyEnumSpec| x == MyEnumSpec::A),
                    Pair(
                        Refined(MyEnumFmt, |x: MyEnumSpec| !(x == MyEnumSpec::B)),
                        Pair(
                            Refined(
                                MyEnumFmt,
                                |x: MyEnumSpec| x == MyEnumSpec::A || x == MyEnumSpec::C,
                            ),
                            Const(MyEnumFmt, MyEnumSpec::A),
                        ),
                    ),
                ),
                mapper: BiMap(EnumConstraintsForward, EnumConstraintsReverse),
            },
        )
    }
}

# [doc = "named format combinator for `my_typed_enum`."]
# [derive (Clone, Copy)]
pub struct MyTypedEnumFmt;

pub type MyTypedEnumFmtSpec = Named<
    Mapped<Refined<U16Le, PredFnSpec<u16>>, BiMap<MyTypedEnumForward, MyTypedEnumReverse>>,
>;

impl MyTypedEnumFmt {
    # [doc = "specification constructor for `my_typed_enum`."]
    pub open spec fn spec_inner() -> MyTypedEnumFmtSpec {
        Named(
            "my_typed_enum",
            Mapped {
                inner: Refined(U16Le, |x: u16| ((x == 1) || (x == 2)) || (x == 3)),
                mapper: BiMap(MyTypedEnumForward, MyTypedEnumReverse),
            },
        )
    }
}

# [doc = "named format combinator for `typed_enum_constraints`."]
# [derive (Clone, Copy)]
pub struct TypedEnumConstraintsFmt;

pub type TypedEnumConstraintsFmtSpec = Named<
    Mapped<
        Pair<
            Refined<MyTypedEnumFmt, PredFnSpec<MyTypedEnumSpec>>,
            Pair<
                Refined<MyTypedEnumFmt, PredFnSpec<MyTypedEnumSpec>>,
                Pair<
                    Refined<MyTypedEnumFmt, PredFnSpec<MyTypedEnumSpec>>,
                    Const<MyTypedEnumFmt, MyTypedEnumSpec>,
                >,
            >,
        >,
        BiMap<TypedEnumConstraintsForward, TypedEnumConstraintsReverse>,
    >,
>;

impl TypedEnumConstraintsFmt {
    # [doc = "specification constructor for `typed_enum_constraints`."]
    pub open spec fn spec_inner() -> TypedEnumConstraintsFmtSpec {
        Named(
            "typed_enum_constraints",
            Mapped {
                inner: Pair(
                    Refined(MyTypedEnumFmt, |x: MyTypedEnumSpec| x == MyTypedEnumSpec::X),
                    Pair(
                        Refined(MyTypedEnumFmt, |x: MyTypedEnumSpec| !(x == MyTypedEnumSpec::Y)),
                        Pair(
                            Refined(
                                MyTypedEnumFmt,
                                |x: MyTypedEnumSpec|
                                    x == MyTypedEnumSpec::X || x == MyTypedEnumSpec::Z,
                            ),
                            Const(MyTypedEnumFmt, MyTypedEnumSpec::X),
                        ),
                    ),
                ),
                mapper: BiMap(TypedEnumConstraintsForward, TypedEnumConstraintsReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for MyEnumFmt {
        type PVal = MyEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MyEnumFmt {
        type Val = MyEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MyEnumFmt {
        type SValue = MyEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MyEnumFmt {
        type SVal = MyEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MyEnumFmt {
        type T = MyEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for EnumConstraintsFmt {
        type PVal = EnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for EnumConstraintsFmt {
        type Val = EnumConstraintsSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for EnumConstraintsFmt {
        type SValue = EnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for EnumConstraintsFmt {
        type SVal = EnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for EnumConstraintsFmt {
        type T = EnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MyTypedEnumFmt {
        type PVal = MyTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MyTypedEnumFmt {
        type Val = MyTypedEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MyTypedEnumFmt {
        type SValue = MyTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MyTypedEnumFmt {
        type SVal = MyTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MyTypedEnumFmt {
        type T = MyTypedEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TypedEnumConstraintsFmt {
        type PVal = TypedEnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TypedEnumConstraintsFmt {
        type Val = TypedEnumConstraintsSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TypedEnumConstraintsFmt {
        type SValue = TypedEnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TypedEnumConstraintsFmt {
        type SVal = TypedEnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TypedEnumConstraintsFmt {
        type T = TypedEnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use {
        vest_lib::combinators::disjoint::disjointness_lemmas,
        MyEnum::lemma_from_into,
        MyEnum::lemma_into_from,
        EnumConstraintsSpec::lemma_from_into,
        EnumConstraintsSpec::lemma_into_from,
        MyTypedEnum::lemma_from_into,
        MyTypedEnum::lemma_into_from,
        TypedEnumConstraintsSpec::lemma_from_into,
        TypedEnumConstraintsSpec::lemma_into_from,
    };

    impl SafeParser for MyEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MyEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MyEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: MyEnumInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(MyEnum::structural_valid(input));
                MyEnum::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            reveal(<MyEnumFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: MyEnumInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(MyEnum::structural_valid(input));
                MyEnum::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MyEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MyEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MyEnumFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as Consistency>::consistent);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: MyEnumSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                MyEnum::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MyEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: MyEnumInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(MyEnum::structural_valid(input));
                MyEnum::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MyEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MyEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for EnumConstraintsFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for EnumConstraintsFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for EnumConstraintsFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: EnumConstraintsInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                EnumConstraintsSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<EnumConstraintsFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: EnumConstraintsInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                EnumConstraintsSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for EnumConstraintsFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for EnumConstraintsFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for EnumConstraintsFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as Consistency>::consistent);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: EnumConstraintsSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                EnumConstraintsSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for EnumConstraintsFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: EnumConstraintsInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                EnumConstraintsSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for EnumConstraintsFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for EnumConstraintsFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MyTypedEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MyTypedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MyTypedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: MyTypedEnumInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(MyTypedEnum::structural_valid(input));
                MyTypedEnum::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<MyTypedEnumFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: MyTypedEnumInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(MyTypedEnum::structural_valid(input));
                MyTypedEnum::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MyTypedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MyTypedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MyTypedEnumFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as Consistency>::consistent);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: MyTypedEnumSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                MyTypedEnum::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MyTypedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: MyTypedEnumInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(MyTypedEnum::structural_valid(input));
                MyTypedEnum::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MyTypedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MyTypedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TypedEnumConstraintsFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TypedEnumConstraintsFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TypedEnumConstraintsFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: TypedEnumConstraintsInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TypedEnumConstraintsSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<TypedEnumConstraintsFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TypedEnumConstraintsInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TypedEnumConstraintsSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TypedEnumConstraintsFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as Consistency>::consistent);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: TypedEnumConstraintsSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TypedEnumConstraintsSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TypedEnumConstraintsFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TypedEnumConstraintsInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TypedEnumConstraintsSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
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

    impl<'i> Parser<&'i [u8]> for MyEnumFmt {
        type PT = MyEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            reveal(<MyEnum as DeepView>::deep_view);
            reveal(MyEnum::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                1 => MyEnum::A,
                2 => MyEnum::B,
                3 => MyEnum::C,
                _ => return Err(ParseError::invalid_tag()),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MyEnum> for MyEnumFmt {
        fn serialize_into(&self, v: &MyEnum, obuf: &mut Output) {
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            reveal(<MyEnum as DeepView>::deep_view);
            reveal(MyEnum::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                MyEnum::A => 1,
                MyEnum::B => 2,
                MyEnum::C => 3,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MyEnum> for MyEnumFmt {
        fn prepare(&self, v: &MyEnum) -> Result<usize, PreSerializeError> {
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            reveal(<MyEnum as DeepView>::deep_view);
            reveal(MyEnum::into_structural);
            let tag = match *v {
                MyEnum::A => 1,
                MyEnum::B => 2,
                MyEnum::C => 3,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for EnumConstraintsFmt {
        type PT = EnumConstraints;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<EnumConstraints as DeepView>::deep_view);
            reveal(EnumConstraintsSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, foo) = (Named("my_enum", MyEnumFmt)).parse(&rest)?;
            proof {
                foo.lemma_deep_view();
            }
            if !(foo == MyEnum::A) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, bar) = (Named("my_enum", MyEnumFmt)).parse(&rest)?;
            proof {
                bar.lemma_deep_view();
            }
            if !(!(bar == MyEnum::B)) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n2);
            let (n3, baz) = (Named("my_enum", MyEnumFmt)).parse(&rest)?;
            proof {
                baz.lemma_deep_view();
            }
            if !(baz == MyEnum::A || baz == MyEnum::C) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n3);
            let (n4, tag) = MyEnumFmt.parse(&rest)?;
            proof {
                tag.lemma_deep_view();
            }
            if !(tag == MyEnum::A) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = EnumConstraints { foo, bar, baz, tag };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, EnumConstraints> for EnumConstraintsFmt {
        fn serialize_into(&self, v: &EnumConstraints, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            reveal(<EnumConstraints as DeepView>::deep_view);
            reveal(EnumConstraintsSpec::into_structural);
            let ghost old_obuf = obuf@;

            let EnumConstraints { foo, bar, baz, tag } = v;
            proof {
                tag.lemma_deep_view();
            }
            proof {
                foo.lemma_deep_view();
                bar.lemma_deep_view();
                baz.lemma_deep_view();
            }

            MyEnumFmt.serialize_into(foo, obuf);
            MyEnumFmt.serialize_into(bar, obuf);
            MyEnumFmt.serialize_into(baz, obuf);
            MyEnumFmt.serialize_into(tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<EnumConstraints> for EnumConstraintsFmt {
        fn prepare(&self, v: &EnumConstraints) -> Result<usize, PreSerializeError> {
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            reveal(<EnumConstraints as DeepView>::deep_view);
            reveal(EnumConstraintsSpec::into_structural);
            let EnumConstraints { foo, bar, baz, tag } = v;
            proof {
                tag.lemma_deep_view();
            }
            proof {
                foo.lemma_deep_view();
                bar.lemma_deep_view();
                baz.lemma_deep_view();
            }

            let l1 = {
                if !(*foo == MyEnum::A) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (Named("my_enum", MyEnumFmt)).prepare(foo)
                }
            }?;
            let l2 = {
                if !(!(*bar == MyEnum::B)) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (Named("my_enum", MyEnumFmt)).prepare(bar)
                }
            }?;
            let l3 = {
                if !(*baz == MyEnum::A || *baz == MyEnum::C) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (Named("my_enum", MyEnumFmt)).prepare(baz)
                }
            }?;
            let l4 = {
                if !(*tag == MyEnum::A) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (MyEnumFmt).prepare(tag)
                }
            }?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?.checked_add(l4).ok_or(
                PreSerializeError::length_too_large(),
            )?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for MyTypedEnumFmt {
        type PT = MyTypedEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<MyTypedEnum as DeepView>::deep_view);
            reveal(MyTypedEnum::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U16Le.parse(&rest)?;
            let enum_val = match v {
                1 => MyTypedEnum::X,
                2 => MyTypedEnum::Y,
                3 => MyTypedEnum::Z,
                _ => return Err(ParseError::invalid_tag()),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MyTypedEnum> for MyTypedEnumFmt {
        fn serialize_into(&self, v: &MyTypedEnum, obuf: &mut Output) {
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            reveal(<MyTypedEnum as DeepView>::deep_view);
            reveal(MyTypedEnum::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                MyTypedEnum::X => 1,
                MyTypedEnum::Y => 2,
                MyTypedEnum::Z => 3,
            };
            U16Le.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MyTypedEnum> for MyTypedEnumFmt {
        fn prepare(&self, v: &MyTypedEnum) -> Result<usize, PreSerializeError> {
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            reveal(<MyTypedEnum as DeepView>::deep_view);
            reveal(MyTypedEnum::into_structural);
            let tag = match *v {
                MyTypedEnum::X => 1,
                MyTypedEnum::Y => 2,
                MyTypedEnum::Z => 3,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U16Le.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for TypedEnumConstraintsFmt {
        type PT = TypedEnumConstraints;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<TypedEnumConstraints as DeepView>::deep_view);
            reveal(TypedEnumConstraintsSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, foo) = (Named("my_typed_enum", MyTypedEnumFmt)).parse(&rest)?;
            proof {
                foo.lemma_deep_view();
            }
            if !(foo == MyTypedEnum::X) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, bar) = (Named("my_typed_enum", MyTypedEnumFmt)).parse(&rest)?;
            proof {
                bar.lemma_deep_view();
            }
            if !(!(bar == MyTypedEnum::Y)) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n2);
            let (n3, baz) = (Named("my_typed_enum", MyTypedEnumFmt)).parse(&rest)?;
            proof {
                baz.lemma_deep_view();
            }
            if !(baz == MyTypedEnum::X || baz == MyTypedEnum::Z) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n3);
            let (n4, tag) = MyTypedEnumFmt.parse(&rest)?;
            proof {
                tag.lemma_deep_view();
            }
            if !(tag == MyTypedEnum::X) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = TypedEnumConstraints { foo, bar, baz, tag };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        TypedEnumConstraints,
    > for TypedEnumConstraintsFmt {
        fn serialize_into(&self, v: &TypedEnumConstraints, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            reveal(<TypedEnumConstraints as DeepView>::deep_view);
            reveal(TypedEnumConstraintsSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TypedEnumConstraints { foo, bar, baz, tag } = v;
            proof {
                tag.lemma_deep_view();
            }
            proof {
                foo.lemma_deep_view();
                bar.lemma_deep_view();
                baz.lemma_deep_view();
            }

            MyTypedEnumFmt.serialize_into(foo, obuf);
            MyTypedEnumFmt.serialize_into(bar, obuf);
            MyTypedEnumFmt.serialize_into(baz, obuf);
            MyTypedEnumFmt.serialize_into(tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TypedEnumConstraints> for TypedEnumConstraintsFmt {
        fn prepare(&self, v: &TypedEnumConstraints) -> Result<usize, PreSerializeError> {
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            reveal(<TypedEnumConstraints as DeepView>::deep_view);
            reveal(TypedEnumConstraintsSpec::into_structural);
            let TypedEnumConstraints { foo, bar, baz, tag } = v;
            proof {
                tag.lemma_deep_view();
            }
            proof {
                foo.lemma_deep_view();
                bar.lemma_deep_view();
                baz.lemma_deep_view();
            }

            let l1 = {
                if !(*foo == MyTypedEnum::X) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (Named("my_typed_enum", MyTypedEnumFmt)).prepare(foo)
                }
            }?;
            let l2 = {
                if !(!(*bar == MyTypedEnum::Y)) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (Named("my_typed_enum", MyTypedEnumFmt)).prepare(bar)
                }
            }?;
            let l3 = {
                if !(*baz == MyTypedEnum::X || *baz == MyTypedEnum::Z) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (Named("my_typed_enum", MyTypedEnumFmt)).prepare(baz)
                }
            }?;
            let l4 = {
                if !(*tag == MyTypedEnum::X) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (MyTypedEnumFmt).prepare(tag)
                }
            }?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?.checked_add(l4).ok_or(
                PreSerializeError::length_too_large(),
            )?;
            Ok(total_len)
        }
    }

}

} // verus!
