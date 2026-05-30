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
# [doc = "data type for `my_typed_enum`."]
# [repr (u16)]
# [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
pub enum MyTypedEnum {
    X = 1,
    Y = 2,
    Z = 3,
}

pub type MyTypedEnumSpec = MyTypedEnum;

pub type MyTypedEnumInner = u16;

impl DeepView for MyTypedEnum {
    type V = MyTypedEnumSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            MyTypedEnum::X => MyTypedEnumSpec::X,
            MyTypedEnum::Y => MyTypedEnumSpec::Y,
            MyTypedEnum::Z => MyTypedEnumSpec::Z,
        }
    }
}

impl DeepEq for MyTypedEnum {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for MyTypedEnum {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `my_enum`."]
# [repr (u8)]
# [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
pub enum MyEnum {
    A = 1,
    B = 2,
    C = 3,
}

pub type MyEnumSpec = MyEnum;

pub type MyEnumInner = u8;

impl DeepView for MyEnum {
    type V = MyEnumSpec;

    open spec fn deep_view(&self) -> Self::V {
        match *self {
            MyEnum::A => MyEnumSpec::A,
            MyEnum::B => MyEnumSpec::B,
            MyEnum::C => MyEnumSpec::C,
        }
    }
}

impl DeepEq for MyEnum {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for MyEnum {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `typed_enum_constraints`."]
# [derive (Debug , PartialEq , Eq)]
pub struct TypedEnumConstraints {
    pub foo: MyTypedEnum,
    pub bar: MyTypedEnum,
    pub baz: MyTypedEnum,
    pub tag: MyTypedEnum,
}

# [verifier :: ext_equal]
pub struct TypedEnumConstraintsSpec {
    pub foo: MyTypedEnumSpec,
    pub bar: MyTypedEnumSpec,
    pub baz: MyTypedEnumSpec,
    pub tag: MyTypedEnumSpec,
}

pub type TypedEnumConstraintsInner = (
    MyTypedEnumSpec,
    (MyTypedEnumSpec, (MyTypedEnumSpec, MyTypedEnumSpec)),
);

impl DeepView for TypedEnumConstraints {
    type V = TypedEnumConstraintsSpec;

    open spec fn deep_view(&self) -> Self::V {
        TypedEnumConstraintsSpec {
            foo: self.foo.deep_view(),
            bar: self.bar.deep_view(),
            baz: self.baz.deep_view(),
            tag: self.tag.deep_view(),
        }
    }
}

# [doc = "data type for `enum_constraints`."]
# [derive (Debug , PartialEq , Eq)]
pub struct EnumConstraints {
    pub foo: MyEnum,
    pub bar: MyEnum,
    pub baz: MyEnum,
    pub tag: MyEnum,
}

# [verifier :: ext_equal]
pub struct EnumConstraintsSpec {
    pub foo: MyEnumSpec,
    pub bar: MyEnumSpec,
    pub baz: MyEnumSpec,
    pub tag: MyEnumSpec,
}

pub type EnumConstraintsInner = (MyEnumSpec, (MyEnumSpec, (MyEnumSpec, MyEnumSpec)));

impl DeepView for EnumConstraints {
    type V = EnumConstraintsSpec;

    open spec fn deep_view(&self) -> Self::V {
        EnumConstraintsSpec {
            foo: self.foo.deep_view(),
            bar: self.bar.deep_view(),
            baz: self.baz.deep_view(),
            tag: self.tag.deep_view(),
        }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `my_typed_enum`."]
pub struct MyTypedEnumFmt;

pub type MyTypedEnumFmtSpec = Named<
    Mapped<Refined<U16Le, PredFnSpec<u16>>, FnSpecMapper<MyTypedEnumInner, MyTypedEnumSpec>>,
>;

# [doc = "specification constructor for `my_typed_enum`."]
pub open spec fn my_typed_enum_fmt() -> MyTypedEnumFmtSpec {
    Named(
        "my_typed_enum",
        Mapped {
            inner: Refined(U16Le, |x: u16| x == 1 || x == 2 || x == 3),
            mapper: (
                |parsed: MyTypedEnumInner| -> MyTypedEnumSpec
                    {
                        match parsed {
                            1 => MyTypedEnumSpec::X,
                            2 => MyTypedEnumSpec::Y,
                            3 => MyTypedEnumSpec::Z,
                            _ => arbitrary(),
                        }
                    },
                |value: MyTypedEnumSpec| -> MyTypedEnumInner
                    {
                        match value {
                            MyTypedEnumSpec::X => 1,
                            MyTypedEnumSpec::Y => 2,
                            MyTypedEnumSpec::Z => 3,
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `my_enum`."]
pub struct MyEnumFmt;

pub type MyEnumFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<MyEnumInner, MyEnumSpec>>,
>;

# [doc = "specification constructor for `my_enum`."]
pub open spec fn my_enum_fmt() -> MyEnumFmtSpec {
    Named(
        "my_enum",
        Mapped {
            inner: Refined(U8, |x: u8| x == 1 || x == 2 || x == 3),
            mapper: (
                |parsed: MyEnumInner| -> MyEnumSpec
                    {
                        match parsed {
                            1 => MyEnumSpec::A,
                            2 => MyEnumSpec::B,
                            3 => MyEnumSpec::C,
                            _ => arbitrary(),
                        }
                    },
                |value: MyEnumSpec| -> MyEnumInner
                    {
                        match value {
                            MyEnumSpec::A => 1,
                            MyEnumSpec::B => 2,
                            MyEnumSpec::C => 3,
                        }
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `typed_enum_constraints`."]
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
        FnSpecMapper<TypedEnumConstraintsInner, TypedEnumConstraintsSpec>,
    >,
>;

# [doc = "specification constructor for `typed_enum_constraints`."]
pub open spec fn typed_enum_constraints_fmt() -> TypedEnumConstraintsFmtSpec {
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
                            |x: MyTypedEnumSpec| x == MyTypedEnumSpec::X || x == MyTypedEnumSpec::Z,
                        ),
                        Const(MyTypedEnumFmt, MyTypedEnumSpec::X),
                    ),
                ),
            ),
            mapper: (
                |parsed: TypedEnumConstraintsInner| -> TypedEnumConstraintsSpec
                    {
                        let (foo, (bar, (baz, tag))) = parsed;
                        TypedEnumConstraintsSpec { foo, bar, baz, tag }
                    },
                |value: TypedEnumConstraintsSpec| -> TypedEnumConstraintsInner
                    {
                        let TypedEnumConstraintsSpec { foo, bar, baz, tag } = value;
                        (foo, (bar, (baz, tag)))
                    },
            ),
        },
    )
}

# [doc = "named format combinator for `enum_constraints`."]
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
        FnSpecMapper<EnumConstraintsInner, EnumConstraintsSpec>,
    >,
>;

# [doc = "specification constructor for `enum_constraints`."]
pub open spec fn enum_constraints_fmt() -> EnumConstraintsFmtSpec {
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
            mapper: (
                |parsed: EnumConstraintsInner| -> EnumConstraintsSpec
                    {
                        let (foo, (bar, (baz, tag))) = parsed;
                        EnumConstraintsSpec { foo, bar, baz, tag }
                    },
                |value: EnumConstraintsSpec| -> EnumConstraintsInner
                    {
                        let EnumConstraintsSpec { foo, bar, baz, tag } = value;
                        (foo, (bar, (baz, tag)))
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

    impl SpecParser for MyTypedEnumFmt {
        type PVal = MyTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            my_typed_enum_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for MyTypedEnumFmt {
        type Val = MyTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            my_typed_enum_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for MyTypedEnumFmt {
        type SValue = MyTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            my_typed_enum_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MyTypedEnumFmt {
        type SVal = MyTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            my_typed_enum_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for MyTypedEnumFmt {
        type T = MyTypedEnumSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            my_typed_enum_fmt().byte_len(v)
        }
    }

    impl SpecParser for MyEnumFmt {
        type PVal = MyEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            my_enum_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for MyEnumFmt {
        type Val = MyEnumSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            my_enum_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for MyEnumFmt {
        type SValue = MyEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            my_enum_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MyEnumFmt {
        type SVal = MyEnumSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            my_enum_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for MyEnumFmt {
        type T = MyEnumSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            my_enum_fmt().byte_len(v)
        }
    }

    impl SpecParser for TypedEnumConstraintsFmt {
        type PVal = TypedEnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            typed_enum_constraints_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for TypedEnumConstraintsFmt {
        type Val = TypedEnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            typed_enum_constraints_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for TypedEnumConstraintsFmt {
        type SValue = TypedEnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            typed_enum_constraints_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TypedEnumConstraintsFmt {
        type SVal = TypedEnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            typed_enum_constraints_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for TypedEnumConstraintsFmt {
        type T = TypedEnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            typed_enum_constraints_fmt().byte_len(v)
        }
    }

    impl SpecParser for EnumConstraintsFmt {
        type PVal = EnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            enum_constraints_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for EnumConstraintsFmt {
        type Val = EnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn consistent(&self, v: Self::Val) -> bool {
            enum_constraints_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for EnumConstraintsFmt {
        type SValue = EnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            enum_constraints_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for EnumConstraintsFmt {
        type SVal = EnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            enum_constraints_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for EnumConstraintsFmt {
        type T = EnumConstraintsSpec;

        # [verifier :: opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            enum_constraints_fmt().byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for MyTypedEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            my_typed_enum_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MyTypedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            my_typed_enum_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = my_typed_enum_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MyTypedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = my_typed_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<MyTypedEnumFmt as Consistency>::consistent);
            let fmt = my_typed_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MyTypedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = my_typed_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = my_typed_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MyTypedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = my_typed_enum_fmt();
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
            let fmt = my_typed_enum_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MyTypedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = my_typed_enum_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MyTypedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = my_typed_enum_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MyTypedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = my_typed_enum_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MyEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            my_enum_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MyEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            my_enum_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            let fmt = my_enum_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MyEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = my_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            reveal(<MyEnumFmt as Consistency>::consistent);
            let fmt = my_enum_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MyEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = my_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = my_enum_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MyEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = my_enum_fmt();
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
            let fmt = my_enum_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MyEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            let fmt = my_enum_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MyEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = my_enum_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MyEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = my_enum_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TypedEnumConstraintsFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            typed_enum_constraints_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TypedEnumConstraintsFmt {
        open spec fn productive_inv(&self) -> bool {
            typed_enum_constraints_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TypedEnumConstraintsFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<TypedEnumConstraintsFmt as Consistency>::consistent);
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = typed_enum_constraints_fmt();
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
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TypedEnumConstraintsFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = typed_enum_constraints_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for EnumConstraintsFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            enum_constraints_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for EnumConstraintsFmt {
        open spec fn productive_inv(&self) -> bool {
            enum_constraints_fmt().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = enum_constraints_fmt();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for EnumConstraintsFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = enum_constraints_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<EnumConstraintsFmt as Consistency>::consistent);
            let fmt = enum_constraints_fmt();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for EnumConstraintsFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = enum_constraints_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = enum_constraints_fmt();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for EnumConstraintsFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = enum_constraints_fmt();
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
            let fmt = enum_constraints_fmt();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for EnumConstraintsFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = enum_constraints_fmt();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for EnumConstraintsFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = enum_constraints_fmt();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for EnumConstraintsFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = enum_constraints_fmt();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
impl<'i> Parser<&'i [u8]> for MyTypedEnumFmt {
    type PT = MyTypedEnum;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
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

impl<'i> Parser<&'i [u8]> for MyEnumFmt {
    type PT = MyEnum;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<MyEnumFmt as SpecParser>::spec_parse);
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

impl<'i> Parser<&'i [u8]> for TypedEnumConstraintsFmt {
    type PT = TypedEnumConstraints;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, foo) = (MyTypedEnumFmt).parse(&rest)?;
        if !(foo == MyTypedEnum::X) {
            return Err(ParseError::predicate_failed());
        }
        let rest = rest.skip(n1);
        let (n2, bar) = (MyTypedEnumFmt).parse(&rest)?;
        if !(!(bar == MyTypedEnum::Y)) {
            return Err(ParseError::predicate_failed());
        }
        let rest = rest.skip(n2);
        let (n3, baz) = (MyTypedEnumFmt).parse(&rest)?;
        if !(baz == MyTypedEnum::X || baz == MyTypedEnum::Z) {
            return Err(ParseError::predicate_failed());
        }
        let rest = rest.skip(n3);
        let (n4, tag) = (Const(MyTypedEnumFmt, MyTypedEnum::X)).parse(&rest)?;
        let rest = rest.skip(n4);
        let total_n = n1 + n2 + n3 + n4;
        let final_v = TypedEnumConstraints { foo, bar, baz, tag };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

impl<'i> Parser<&'i [u8]> for EnumConstraintsFmt {
    type PT = EnumConstraints;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

        reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n1, foo) = (MyEnumFmt).parse(&rest)?;
        if !(foo == MyEnum::A) {
            return Err(ParseError::predicate_failed());
        }
        let rest = rest.skip(n1);
        let (n2, bar) = (MyEnumFmt).parse(&rest)?;
        if !(!(bar == MyEnum::B)) {
            return Err(ParseError::predicate_failed());
        }
        let rest = rest.skip(n2);
        let (n3, baz) = (MyEnumFmt).parse(&rest)?;
        if !(baz == MyEnum::A || baz == MyEnum::C) {
            return Err(ParseError::predicate_failed());
        }
        let rest = rest.skip(n3);
        let (n4, tag) = (Const(MyEnumFmt, MyEnum::A)).parse(&rest)?;
        let rest = rest.skip(n4);
        let total_n = n1 + n2 + n3 + n4;
        let final_v = EnumConstraints { foo, bar, baz, tag };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        Ok((total_n, final_v))
    }
}

} // verus!
