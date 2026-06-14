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
# [doc = "data type for `my_typed_enum`."]
# [repr (u16)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum MyTypedEnum {
    X = 1,
    Y = 2,
    Z = 3,
}

pub type MyTypedEnumSpec = MyTypedEnum;

pub type MyTypedEnumInner = u16;

impl DeepView for MyTypedEnum {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
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
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum MyEnum {
    A = 1,
    B = 2,
    C = 3,
}

pub type MyEnumSpec = MyEnum;

pub type MyEnumInner = u8;

impl DeepView for MyEnum {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
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
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct TypedEnumConstraints {
    pub foo: MyTypedEnum,
    pub bar: MyTypedEnum,
    pub baz: MyTypedEnum,
    pub tag: MyTypedEnum,
}

pub type TypedEnumConstraintsSpec = TypedEnumConstraints;

pub type TypedEnumConstraintsInner = (
    MyTypedEnumSpec,
    (MyTypedEnumSpec, (MyTypedEnumSpec, MyTypedEnumSpec)),
);

impl DeepView for TypedEnumConstraints {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `enum_constraints`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct EnumConstraints {
    pub foo: MyEnum,
    pub bar: MyEnum,
    pub baz: MyEnum,
    pub tag: MyEnum,
}

pub type EnumConstraintsSpec = EnumConstraints;

pub type EnumConstraintsInner = (MyEnumSpec, (MyEnumSpec, (MyEnumSpec, MyEnumSpec)));

impl DeepView for EnumConstraints {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `my_typed_enum`."]
# [derive (Clone, Copy)]
pub struct MyTypedEnumFmt;

pub type MyTypedEnumFmtSpec = Named<
    Mapped<Refined<U16Le, PredFnSpec<u16>>, FnSpecMapper<MyTypedEnumInner, MyTypedEnumSpec>>,
>;

impl MyTypedEnumFmt {
    # [doc = "specification constructor for `my_typed_enum`."]
    pub open spec fn spec_inner() -> MyTypedEnumFmtSpec {
        Named(
            "my_typed_enum",
            Mapped {
                inner: Refined(U16Le, |x: u16| ((x == 1) || (x == 2)) || (x == 3)),
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
}

# [doc = "named format combinator for `my_enum`."]
# [derive (Clone, Copy)]
pub struct MyEnumFmt;

pub type MyEnumFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<MyEnumInner, MyEnumSpec>>,
>;

impl MyEnumFmt {
    # [doc = "specification constructor for `my_enum`."]
    pub open spec fn spec_inner() -> MyEnumFmtSpec {
        Named(
            "my_enum",
            Mapped {
                inner: Refined(U8, |x: u8| ((x == 1) || (x == 2)) || (x == 3)),
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
        FnSpecMapper<TypedEnumConstraintsInner, TypedEnumConstraintsSpec>,
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
        FnSpecMapper<EnumConstraintsInner, EnumConstraintsSpec>,
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
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for MyTypedEnumFmt {
        type PVal = MyTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            MyTypedEnumFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MyTypedEnumFmt {
        type Val = MyTypedEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            MyTypedEnumFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MyTypedEnumFmt {
        type SValue = MyTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            MyTypedEnumFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MyTypedEnumFmt {
        type SVal = MyTypedEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            MyTypedEnumFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MyTypedEnumFmt {
        type T = MyTypedEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            MyTypedEnumFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MyEnumFmt {
        type PVal = MyEnumSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            MyEnumFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MyEnumFmt {
        type Val = MyEnumSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            MyEnumFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MyEnumFmt {
        type SValue = MyEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            MyEnumFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MyEnumFmt {
        type SVal = MyEnumSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            MyEnumFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MyEnumFmt {
        type T = MyEnumSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            MyEnumFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TypedEnumConstraintsFmt {
        type PVal = TypedEnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            TypedEnumConstraintsFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TypedEnumConstraintsFmt {
        type Val = TypedEnumConstraintsSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            TypedEnumConstraintsFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TypedEnumConstraintsFmt {
        type SValue = TypedEnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            TypedEnumConstraintsFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TypedEnumConstraintsFmt {
        type SVal = TypedEnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            TypedEnumConstraintsFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TypedEnumConstraintsFmt {
        type T = TypedEnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            TypedEnumConstraintsFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for EnumConstraintsFmt {
        type PVal = EnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            EnumConstraintsFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for EnumConstraintsFmt {
        type Val = EnumConstraintsSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            EnumConstraintsFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for EnumConstraintsFmt {
        type SValue = EnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            EnumConstraintsFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for EnumConstraintsFmt {
        type SVal = EnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            EnumConstraintsFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for EnumConstraintsFmt {
        type T = EnumConstraintsSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            EnumConstraintsFmt::spec_inner().byte_len(v)
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
            MyTypedEnumFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MyTypedEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            MyTypedEnumFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MyTypedEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            reveal(<MyTypedEnumFmt as Consistency>::consistent);
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MyTypedEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MyTypedEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let fmt = MyTypedEnumFmt::spec_inner();
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
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MyTypedEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecParser>::spec_parse);
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MyTypedEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MyTypedEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MyTypedEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = MyTypedEnumFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MyEnumFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            MyEnumFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MyEnumFmt {
        open spec fn productive_inv(&self) -> bool {
            MyEnumFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MyEnumFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            reveal(<MyEnumFmt as Consistency>::consistent);
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MyEnumFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MyEnumFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let fmt = MyEnumFmt::spec_inner();
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
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MyEnumFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MyEnumFmt as SpecParser>::spec_parse);
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MyEnumFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MyEnumFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MyEnumFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            let fmt = MyEnumFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TypedEnumConstraintsFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            TypedEnumConstraintsFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TypedEnumConstraintsFmt {
        open spec fn productive_inv(&self) -> bool {
            TypedEnumConstraintsFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TypedEnumConstraintsFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<TypedEnumConstraintsFmt as Consistency>::consistent);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
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
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TypedEnumConstraintsFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TypedEnumConstraintsFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = TypedEnumConstraintsFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for EnumConstraintsFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            EnumConstraintsFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for EnumConstraintsFmt {
        open spec fn productive_inv(&self) -> bool {
            EnumConstraintsFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = EnumConstraintsFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for EnumConstraintsFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = EnumConstraintsFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            reveal(<EnumConstraintsFmt as Consistency>::consistent);
            let fmt = EnumConstraintsFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for EnumConstraintsFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = EnumConstraintsFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = EnumConstraintsFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for EnumConstraintsFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let fmt = EnumConstraintsFmt::spec_inner();
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
            let fmt = EnumConstraintsFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for EnumConstraintsFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            let fmt = EnumConstraintsFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for EnumConstraintsFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = EnumConstraintsFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for EnumConstraintsFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<EnumConstraintsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let fmt = EnumConstraintsFmt::spec_inner();
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

    impl<'i> Parser<&'i [u8]> for MyTypedEnumFmt {
        type PT = MyTypedEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
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

    impl<'i> Serializer<MyTypedEnum> for MyTypedEnumFmt {
        fn serialize(&self, v: &MyTypedEnum, obuf: &mut Vec<u8>) {
            reveal(<MyTypedEnumFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                MyTypedEnum::X => 1,
                MyTypedEnum::Y => 2,
                MyTypedEnum::Z => 3,
            };
            U16Le.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MyTypedEnum> for MyTypedEnumFmt {
        fn prepare(&self, v: &MyTypedEnum) -> Result<usize, PreSerializeError> {
            reveal(<MyTypedEnumFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                MyTypedEnum::X => 1,
                MyTypedEnum::Y => 2,
                MyTypedEnum::Z => 3,
                _ => return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
            };
            U16Le.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for MyEnumFmt {
        type PT = MyEnum;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
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

    impl<'i> Serializer<MyEnum> for MyEnumFmt {
        fn serialize(&self, v: &MyEnum, obuf: &mut Vec<u8>) {
            reveal(<MyEnumFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                MyEnum::A => 1,
                MyEnum::B => 2,
                MyEnum::C => 3,
            };
            U8.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MyEnum> for MyEnumFmt {
        fn prepare(&self, v: &MyEnum) -> Result<usize, PreSerializeError> {
            reveal(<MyEnumFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                MyEnum::A => 1,
                MyEnum::B => 2,
                MyEnum::C => 3,
                _ => return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for TypedEnumConstraintsFmt {
        type PT = TypedEnumConstraints;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TypedEnumConstraintsFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, foo) = MyTypedEnumFmt.parse(&rest)?;
            if !(foo == MyTypedEnum::X) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, bar) = MyTypedEnumFmt.parse(&rest)?;
            if !(!(bar == MyTypedEnum::Y)) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n2);
            let (n3, baz) = MyTypedEnumFmt.parse(&rest)?;
            if !(baz == MyTypedEnum::X || baz == MyTypedEnum::Z) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n3);
            let (n4, tag) = Const(MyTypedEnumFmt, MyTypedEnum::X).parse(&rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = TypedEnumConstraints { foo, bar, baz, tag };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<TypedEnumConstraints> for TypedEnumConstraintsFmt {
        fn serialize(&self, v: &TypedEnumConstraints, obuf: &mut Vec<u8>) {
            reveal(<TypedEnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let TypedEnumConstraints { foo, bar, baz, tag } = v;
            MyTypedEnumFmt.serialize(foo, obuf);
            MyTypedEnumFmt.serialize(bar, obuf);
            MyTypedEnumFmt.serialize(baz, obuf);
            Const(MyTypedEnumFmt, MyTypedEnum::X).serialize(tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TypedEnumConstraints> for TypedEnumConstraintsFmt {
        fn prepare(&self, v: &TypedEnumConstraints) -> Result<usize, PreSerializeError> {
            reveal(<TypedEnumConstraintsFmt as SpecByteLen>::byte_len);
            let TypedEnumConstraints { foo, bar, baz, tag } = v;
            let l1 = {
                if !(*foo == MyTypedEnum::X) {
                    Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (MyTypedEnumFmt).prepare(foo)
                }
            }?;
            let l2 = {
                if !(!(*bar == MyTypedEnum::Y)) {
                    Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (MyTypedEnumFmt).prepare(bar)
                }
            }?;
            let l3 = {
                if !(*baz == MyTypedEnum::X || *baz == MyTypedEnum::Z) {
                    Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (MyTypedEnumFmt).prepare(baz)
                }
            }?;
            let l4 = (Const(MyTypedEnumFmt, MyTypedEnum::X)).prepare(tag)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::LengthTooLarge,
            )?.checked_add(l3).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(l4).ok_or(
                PreSerializeError::LengthTooLarge,
            )?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for EnumConstraintsFmt {
        type PT = EnumConstraints;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<EnumConstraintsFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, foo) = MyEnumFmt.parse(&rest)?;
            if !(foo == MyEnum::A) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, bar) = MyEnumFmt.parse(&rest)?;
            if !(!(bar == MyEnum::B)) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n2);
            let (n3, baz) = MyEnumFmt.parse(&rest)?;
            if !(baz == MyEnum::A || baz == MyEnum::C) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n3);
            let (n4, tag) = Const(MyEnumFmt, MyEnum::A).parse(&rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = EnumConstraints { foo, bar, baz, tag };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<EnumConstraints> for EnumConstraintsFmt {
        fn serialize(&self, v: &EnumConstraints, obuf: &mut Vec<u8>) {
            reveal(<EnumConstraintsFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let EnumConstraints { foo, bar, baz, tag } = v;
            MyEnumFmt.serialize(foo, obuf);
            MyEnumFmt.serialize(bar, obuf);
            MyEnumFmt.serialize(baz, obuf);
            Const(MyEnumFmt, MyEnum::A).serialize(tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<EnumConstraints> for EnumConstraintsFmt {
        fn prepare(&self, v: &EnumConstraints) -> Result<usize, PreSerializeError> {
            reveal(<EnumConstraintsFmt as SpecByteLen>::byte_len);
            let EnumConstraints { foo, bar, baz, tag } = v;
            let l1 = {
                if !(*foo == MyEnum::A) {
                    Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (MyEnumFmt).prepare(foo)
                }
            }?;
            let l2 = {
                if !(!(*bar == MyEnum::B)) {
                    Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (MyEnumFmt).prepare(bar)
                }
            }?;
            let l3 = {
                if !(*baz == MyEnum::A || *baz == MyEnum::C) {
                    Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (MyEnumFmt).prepare(baz)
                }
            }?;
            let l4 = (Const(MyEnumFmt, MyEnum::A)).prepare(tag)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::LengthTooLarge,
            )?.checked_add(l3).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(l4).ok_or(
                PreSerializeError::LengthTooLarge,
            )?;
            Ok(total_len)
        }
    }

}

} // verus!
