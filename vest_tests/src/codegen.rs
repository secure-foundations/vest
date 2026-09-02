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
# [doc = "data type for `msg1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg1<'i> {
    pub a: u8,
    pub b: u16,
    pub c: &'i [u8],
}

# [verifier::ext_equal]
pub struct Msg1Spec<T0 = u8, T1 = u16, T2 = Seq<u8>> {
    pub a: T0,
    pub b: T1,
    pub c: T2,
}

pub type Msg1Inner = (u8, (u16, Seq<u8>));

impl<'i> DeepView for Msg1<'i> {
    type V = Msg1Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Msg1Spec { a: self.a.deep_view(), b: self.b.deep_view(), c: self.c.deep_view() }
    }
}

impl<'i> Msg1<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().a == self.a.deep_view(),
            self.deep_view().b == self.b.deep_view(),
            self.deep_view().c == self.c.deep_view(),
    {
        reveal(<Msg1 as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> Msg1Spec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (a, (b, c)) = input;
        Self { a, b, c }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { a, b, c } = self;
        (a, (b, c))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg1Spec::from_structural);
        reveal(Msg1Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg1Spec::from_structural);
        reveal(Msg1Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { a, b, c } => (a, (b, c)),
            },
    {
        reveal(Msg1Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg1Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg1Reverse;

impl SpecMap for Msg1Forward {
    type Input = Msg1Inner;

    type Output = Msg1Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg1Spec::from_structural(input)
    }
}

impl SpecMap for Msg1Reverse {
    type Input = Msg1Spec;

    type Output = Msg1Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg2`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg2 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

# [verifier::ext_equal]
pub struct Msg2Spec<T0 = u8, T1 = u16, T2 = u32> {
    pub a: T0,
    pub b: T1,
    pub c: T2,
}

pub type Msg2Inner = (u8, (u16, u32));

impl DeepView for Msg2 {
    type V = Msg2Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Msg2Spec { a: self.a.deep_view(), b: self.b.deep_view(), c: self.c.deep_view() }
    }
}

impl Msg2 {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().a == self.a.deep_view(),
            self.deep_view().b == self.b.deep_view(),
            self.deep_view().c == self.c.deep_view(),
    {
        reveal(<Msg2 as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> Msg2Spec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (a, (b, c)) = input;
        Self { a, b, c }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { a, b, c } = self;
        (a, (b, c))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg2Spec::from_structural);
        reveal(Msg2Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg2Spec::from_structural);
        reveal(Msg2Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { a, b, c } => (a, (b, c)),
            },
    {
        reveal(Msg2Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg2Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg2Reverse;

impl SpecMap for Msg2Forward {
    type Input = Msg2Inner;

    type Output = Msg2Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg2Spec::from_structural(input)
    }
}

impl SpecMap for Msg2Reverse {
    type Input = Msg2Spec;

    type Output = Msg2Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg3`."]
pub type Msg3<'i> = &'i [u8];

pub type Msg3Spec = Seq<u8>;

# [doc = "data type for `a_type`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum AType {
    A = 0,
    B = 1,
    C = 2,
}

pub type ATypeSpec = AType;

pub type ATypeInner = u8;

impl DeepView for AType {
    type V = Self;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl AType {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<AType as DeepView>::deep_view);
    }

    pub open spec fn structural_valid(input: ATypeInner) -> bool {
        {
            let x = input;
            x == 0 || x == 1 || x == 2
        }
    }

    # [verifier::opaque]
    pub open spec fn from_structural(input: ATypeInner) -> Self {
        match input {
            0 => Self::A,
            1 => Self::B,
            2 => Self::C,
            _ => arbitrary(),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> ATypeInner {
        match self {
            Self::A => 0,
            Self::B => 1,
            Self::C => 2,
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(AType::from_structural);
        reveal(AType::into_structural);
        match self {
            Self::A => {},
            Self::B => {},
            Self::C => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: ATypeInner)
        requires
            Self::structural_valid(input),
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(AType::from_structural);
        reveal(AType::into_structural);
        match input {
            0 => {},
            1 => {},
            2 => {},
            _ => {
                assert(false);
            },
        }
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ATypeForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ATypeReverse;

impl SpecMap for ATypeForward {
    type Input = ATypeInner;

    type Output = ATypeSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        AType::from_structural(input)
    }
}

impl SpecMap for ATypeReverse {
    type Input = ATypeSpec;

    type Output = ATypeInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for AType {

}

# [doc = "data type for `msg4`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg4<'i> {
    pub t: AType,
    pub val: Msg4Val<'i>,
    pub tail: &'i [u8],
}

# [verifier::ext_equal]
pub struct Msg4Spec<T0 = ATypeSpec, T1 = Msg4ValSpec, T2 = Seq<u8>> {
    pub t: T0,
    pub val: T1,
    pub tail: T2,
}

pub type Msg4Inner = (ATypeSpec, (Msg4ValSpec, Seq<u8>));

impl<'i> DeepView for Msg4<'i> {
    type V = Msg4Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Msg4Spec { t: self.t.deep_view(), val: self.val.deep_view(), tail: self.tail.deep_view() }
    }
}

impl<'i> Msg4<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().t == self.t.deep_view(),
            self.deep_view().val == self.val.deep_view(),
            self.deep_view().tail == self.tail.deep_view(),
    {
        reveal(<Msg4 as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> Msg4Spec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (t, (val, tail)) = input;
        Self { t, val, tail }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { t, val, tail } = self;
        (t, (val, tail))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg4Spec::from_structural);
        reveal(Msg4Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg4Spec::from_structural);
        reveal(Msg4Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { t, val, tail } => (t, (val, tail)),
            },
    {
        reveal(Msg4Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg4Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg4Reverse;

impl SpecMap for Msg4Forward {
    type Input = Msg4Inner;

    type Output = Msg4Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg4Spec::from_structural(input)
    }
}

impl SpecMap for Msg4Reverse {
    type Input = Msg4Spec;

    type Output = Msg4Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg4_val`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Msg4Val<'i> {
    A(Msg1<'i>),
    B(Msg2),
    C(Msg3<'i>),
}

# [verifier::ext_equal]
pub enum Msg4ValSpec<T0 = Msg1Spec, T1 = Msg2Spec, T2 = Msg3Spec> {
    A(T0),
    B(T1),
    C(T2),
}

pub type Msg4ValInner = Sum<Msg1Spec, Sum<Msg2Spec, Msg3Spec>>;

impl<'i> DeepView for Msg4Val<'i> {
    type V = Msg4ValSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Msg4Val::A(v) => Msg4ValSpec::A(v.deep_view()),
            Msg4Val::B(v) => Msg4ValSpec::B(v.deep_view()),
            Msg4Val::C(v) => Msg4ValSpec::C(v.deep_view()),
        }
    }
}

impl<'i> Msg4Val<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                Msg4Val::A(v) => Msg4ValSpec::A(v.deep_view()),
                Msg4Val::B(v) => Msg4ValSpec::B(v.deep_view()),
                Msg4Val::C(v) => Msg4ValSpec::C(v.deep_view()),
            },
    {
        reveal(<Msg4Val as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> Msg4ValSpec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, Sum<T1, T2>>) -> Self {
        match input {
            L(value) => Self::A(value),
            R(L(value)) => Self::B(value),
            R(R(value)) => Self::C(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, Sum<T1, T2>> {
        match self {
            Self::A(value) => L(value),
            Self::B(value) => R(L(value)),
            Self::C(value) => R(R(value)),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg4ValSpec::from_structural);
        reveal(Msg4ValSpec::into_structural);
        match self {
            Self::A(_) => {},
            Self::B(_) => {},
            Self::C(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, Sum<T1, T2>>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg4ValSpec::from_structural);
        reveal(Msg4ValSpec::into_structural);
        match input {
            L(_) => {},
            R(L(_)) => {},
            R(R(_)) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::A(value) => L(value),
                Self::B(value) => R(L(value)),
                Self::C(value) => R(R(value)),
            },
    {
        reveal(Msg4ValSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg4ValForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg4ValReverse;

impl SpecMap for Msg4ValForward {
    type Input = Msg4ValInner;

    type Output = Msg4ValSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg4ValSpec::from_structural(input)
    }
}

impl SpecMap for Msg4ValReverse {
    type Input = Msg4ValSpec;

    type Output = Msg4ValInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `msg1`."]
# [derive (Clone, Copy)]
pub struct Msg1Fmt;

pub type Msg1FmtSpec = Named<
    Mapped<
        Pair<Refined<U8, PredFnSpec<u8>>, Pair<U16Le, Fixed<3>>>,
        BiMap<Msg1Forward, Msg1Reverse>,
    >,
>;

impl Msg1Fmt {
    # [doc = "specification constructor for `msg1`."]
    pub open spec fn spec_inner() -> Msg1FmtSpec {
        Named(
            "msg1",
            Mapped {
                inner: Pair(
                    Refined(U8, |x: u8| x >= 0 && x <= 10 || x == 32 || x >= 100),
                    Pair(U16Le, Fixed::<3>),
                ),
                mapper: BiMap(Msg1Forward, Msg1Reverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg2`."]
# [derive (Clone, Copy)]
pub struct Msg2Fmt;

pub type Msg2FmtSpec = Named<Mapped<Pair<U8, Pair<U16Le, U32Le>>, BiMap<Msg2Forward, Msg2Reverse>>>;

impl Msg2Fmt {
    # [doc = "specification constructor for `msg2`."]
    pub open spec fn spec_inner() -> Msg2FmtSpec {
        Named(
            "msg2",
            Mapped { inner: Pair(U8, Pair(U16Le, U32Le)), mapper: BiMap(Msg2Forward, Msg2Reverse) },
        )
    }
}

# [doc = "named format combinator for `msg3`."]
# [derive (Clone, Copy)]
pub struct Msg3Fmt;

pub type Msg3FmtSpec = Named<Fixed<6>>;

impl Msg3Fmt {
    # [doc = "specification constructor for `msg3`."]
    pub open spec fn spec_inner() -> Msg3FmtSpec {
        Named("msg3", Fixed::<6>)
    }
}

# [doc = "named format combinator for `a_type`."]
# [derive (Clone, Copy)]
pub struct ATypeFmt;

pub type ATypeFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, BiMap<ATypeForward, ATypeReverse>>,
>;

impl ATypeFmt {
    # [doc = "specification constructor for `a_type`."]
    pub open spec fn spec_inner() -> ATypeFmtSpec {
        Named(
            "a_type",
            Mapped {
                inner: Refined(U8, |x: u8| ((x == 0) || (x == 1)) || (x == 2)),
                mapper: BiMap(ATypeForward, ATypeReverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg4`."]
# [derive (Clone, Copy)]
pub struct Msg4Fmt;

pub type Msg4FmtSpec = Named<
    Mapped<
        Bind<ATypeFmt, spec_fn(ATypeSpec) -> Pair<Msg4ValFmt, Tail>>,
        BiMap<Msg4Forward, Msg4Reverse>,
    >,
>;

impl Msg4Fmt {
    # [doc = "specification constructor for `msg4`."]
    pub open spec fn spec_inner() -> Msg4FmtSpec {
        Named(
            "msg4",
            Mapped {
                inner: Bind(ATypeFmt, |t: ATypeSpec| Pair(Msg4ValFmt::spec(t), Tail)),
                mapper: BiMap(Msg4Forward, Msg4Reverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg4_val`."]
# [derive (Clone, Copy)]
pub struct Msg4ValFmt {
    t: AType,
}

impl Msg4ValFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        ATypeFmt.consistent(self.t.deep_view())
    }

    pub closed spec fn t_spec(&self) -> ATypeSpec {
        self.t.deep_view()
    }

    pub closed spec fn spec(t: AType) -> Self {
        Msg4ValFmt { t }
    }
}

pub type Msg4ValFmtSpec = Named<
    Mapped<Sum<Msg1Fmt, Sum<Msg2Fmt, Msg3Fmt>>, BiMap<Msg4ValForward, Msg4ValReverse>>,
>;

impl Msg4ValFmt {
    # [doc = "specification constructor for `msg4_val`."]
    pub open spec fn spec_inner(t: ATypeSpec) -> Msg4ValFmtSpec {
        Named(
            "msg4_val",
            Mapped {
                inner: match t {
                    ATypeSpec::A => L(Msg1Fmt),
                    ATypeSpec::B => R(L(Msg2Fmt)),
                    ATypeSpec::C => R(R(Msg3Fmt)),
                },
                mapper: BiMap(Msg4ValForward, Msg4ValReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for Msg1Fmt {
        type PVal = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg1Fmt {
        type Val = Msg1Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg1Fmt {
        type SValue = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg1Fmt {
        type SVal = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg1Fmt {
        type T = Msg1Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg2Fmt {
        type PVal = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg2Fmt {
        type Val = Msg2Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg2Fmt {
        type SValue = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg2Fmt {
        type SVal = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg2Fmt {
        type T = Msg2Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg3Fmt {
        type PVal = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg3Fmt {
        type Val = Msg3Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg3Fmt {
        type SValue = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg3Fmt {
        type SVal = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg3Fmt {
        type T = Msg3Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ATypeFmt {
        type PVal = ATypeSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ATypeFmt {
        type Val = ATypeSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ATypeFmt {
        type SValue = ATypeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypeFmt {
        type SVal = ATypeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypeFmt {
        type T = ATypeSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg4Fmt {
        type PVal = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg4Fmt {
        type Val = Msg4Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg4Fmt {
        type SValue = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg4Fmt {
        type SVal = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg4Fmt {
        type T = Msg4Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg4ValFmt {
        type PVal = Msg4ValSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.t_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for Msg4ValFmt {
        type Val = Msg4ValSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.t_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for Msg4ValFmt {
        type SValue = Msg4ValSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.t_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg4ValFmt {
        type SVal = Msg4ValSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.t_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg4ValFmt {
        type T = Msg4ValSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.t_spec()).byte_len(v)
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
        Msg1Spec::lemma_from_into,
        Msg1Spec::lemma_into_from,
        Msg2Spec::lemma_from_into,
        Msg2Spec::lemma_into_from,
        AType::lemma_from_into,
        AType::lemma_into_from,
        Msg4Spec::lemma_from_into,
        Msg4Spec::lemma_into_from,
        Msg4ValSpec::lemma_from_into,
        Msg4ValSpec::lemma_into_from,
    };

    impl SafeParser for Msg1Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg1Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg1Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: Msg1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Msg1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg1Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg1Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg1Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as Consistency>::consistent);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: Msg1Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg1Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg1Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Msg1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg1Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg1Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg2Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg2Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg2Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: Msg2Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Msg2Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg2Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg2Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg2Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as Consistency>::consistent);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: Msg2Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg2Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg2Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Msg2Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg2Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg2Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg3Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg3Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg3Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg3Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg3Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg3Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as Consistency>::consistent);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg3Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg3Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg3Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ATypeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypeFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: ATypeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(AType::structural_valid(input));
                AType::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            reveal(<ATypeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ATypeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(AType::structural_valid(input));
                AType::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ATypeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ATypeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypeFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ATypeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypeFmt as Consistency>::consistent);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: ATypeSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                AType::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: ATypeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(AType::structural_valid(input));
                AType::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ATypeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ATypeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg4Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg4Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg4Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: Msg4Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Msg4Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for Msg4Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg4Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4Fmt as Consistency>::consistent);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: Msg4Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg4Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg4Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Msg4Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for Msg4Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg4ValFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.t_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg4ValFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.t_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg4ValFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.t_spec());
            assert forall|input: Msg4ValInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4ValSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            reveal(<Msg4ValFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.t_spec());
            assert forall|input: Msg4ValInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4ValSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg4ValFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg4ValFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg4ValFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg4ValFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ValFmt as Consistency>::consistent);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.t_spec());
            assert forall|output: Msg4ValSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg4ValSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg4ValFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.t_spec());
            assert forall|input: Msg4ValInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4ValSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg4ValFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ValFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg4ValFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ValFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.t_spec());
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

    impl<'i> Parser<&'i [u8]> for Msg1Fmt {
        type PT = Msg1<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1 as DeepView>::deep_view);
            reveal(Msg1Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, a) = (U8).parse(&rest)?;
            if !(a >= 0 && a <= 10 || a == 32 || a >= 100) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, b) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, c) = (Fixed::<3>).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Msg1 { a, b, c };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg1<'i>> for Msg1Fmt {
        fn serialize_into(&self, v: &Msg1<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            reveal(<Msg1 as DeepView>::deep_view);
            reveal(Msg1Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg1 { a, b, c } = v;
            U8.serialize_into(a, obuf);
            U16Le.serialize_into(b, obuf);
            Fixed::<3>.serialize_into(*c, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg1<'i>> for Msg1Fmt {
        fn prepare(&self, v: &Msg1<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            reveal(<Msg1 as DeepView>::deep_view);
            reveal(Msg1Spec::into_structural);
            let Msg1 { a, b, c } = v;
            let l1 = {
                if !(*a >= 0 && *a <= 10 || *a == 32 || *a >= 100) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (U8).prepare(a)
                }
            }?;
            let l2 = (U16Le).prepare(b)?;
            let l3 = (Fixed::<3>).prepare(c)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg2Fmt {
        type PT = Msg2;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2 as DeepView>::deep_view);
            reveal(Msg2Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, a) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, b) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, c) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Msg2 { a, b, c };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg2> for Msg2Fmt {
        fn serialize_into(&self, v: &Msg2, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            reveal(<Msg2 as DeepView>::deep_view);
            reveal(Msg2Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg2 { a, b, c } = v;
            U8.serialize_into(a, obuf);
            U16Le.serialize_into(b, obuf);
            U32Le.serialize_into(c, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg2> for Msg2Fmt {
        fn prepare(&self, v: &Msg2) -> Result<usize, PreSerializeError> {
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            reveal(<Msg2 as DeepView>::deep_view);
            reveal(Msg2Spec::into_structural);
            let Msg2 { a, b, c } = v;
            let l1 = (U8).prepare(a)?;
            let l2 = (U16Le).prepare(b)?;
            let l3 = (U32Le).prepare(c)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg3Fmt {
        type PT = Msg3<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Fixed::<6>.parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg3<'i>> for Msg3Fmt {
        fn serialize_into(&self, v: &Msg3<'i>, obuf: &mut Output) {
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            Fixed::<6>.serialize_into(*v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg3<'i>> for Msg3Fmt {
        fn prepare(&self, v: &Msg3<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            (Fixed::<6>).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for ATypeFmt {
        type PT = AType;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            reveal(<AType as DeepView>::deep_view);
            reveal(AType::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                0 => AType::A,
                1 => AType::B,
                2 => AType::C,
                _ => return Err(ParseError::invalid_tag()),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, AType> for ATypeFmt {
        fn serialize_into(&self, v: &AType, obuf: &mut Output) {
            reveal(<ATypeFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            reveal(<AType as DeepView>::deep_view);
            reveal(AType::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                AType::A => 0,
                AType::B => 1,
                AType::C => 2,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AType> for ATypeFmt {
        fn prepare(&self, v: &AType) -> Result<usize, PreSerializeError> {
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            reveal(<AType as DeepView>::deep_view);
            reveal(AType::into_structural);
            let tag = match *v {
                AType::A => 0,
                AType::B => 1,
                AType::C => 2,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg4Fmt {
        type PT = Msg4<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4 as DeepView>::deep_view);
            reveal(Msg4Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, t) = (Named("a_type", ATypeFmt)).parse(&rest)?;
            proof {
                t.lemma_deep_view();
            }
            let rest = rest.skip(n1);
            proof {
                t.lemma_deep_view();
            }

            let (n2, val) = (Named("msg4_val", Msg4ValFmt { t: t })).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, tail) = (Tail).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Msg4 { t, val, tail };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg4<'i>> for Msg4Fmt {
        fn serialize_into(&self, v: &Msg4<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            reveal(<Msg4 as DeepView>::deep_view);
            reveal(Msg4Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg4 { t, val, tail } = v;
            proof {
                t.lemma_deep_view();
            }

            ATypeFmt.serialize_into(t, obuf);
            Msg4ValFmt { t: *t }.serialize_into(val, obuf);
            Tail.serialize_into(tail, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg4<'i>> for Msg4Fmt {
        fn prepare(&self, v: &Msg4<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            reveal(<Msg4 as DeepView>::deep_view);
            reveal(Msg4Spec::into_structural);
            let Msg4 { t, val, tail } = v;
            proof {
                t.lemma_deep_view();
            }

            let l1 = (Named("a_type", ATypeFmt)).prepare(t)?;
            let l2 = (Named("msg4_val", Msg4ValFmt { t: *t })).prepare(val)?;
            let l3 = (Tail).prepare(tail)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg4ValFmt {
        type PT = Msg4Val<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            reveal(<Msg4Val as DeepView>::deep_view);
            reveal(Msg4ValSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.t.lemma_deep_view();
            }

            proof {
                self.t.lemma_deep_view();
            }

            let (n, v) = match self.t {
                AType::A => {
                    let (n, v) = (Named("msg1", Msg1Fmt)).parse(&rest)?;
                    (n, Msg4Val::A(v))
                },
                AType::B => {
                    let (n, v) = (Named("msg2", Msg2Fmt)).parse(&rest)?;
                    (n, Msg4Val::B(v))
                },
                AType::C => {
                    let (n, v) = (Named("msg3", Msg3Fmt)).parse(&rest)?;
                    (n, Msg4Val::C(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg4Val<'i>> for Msg4ValFmt {
        fn serialize_into(&self, v: &Msg4Val<'i>, obuf: &mut Output) {
            reveal(<Msg4ValFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            reveal(<Msg4Val as DeepView>::deep_view);
            reveal(Msg4ValSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.t.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            proof {
                self.t.lemma_deep_view();
            }

            match (self.t, v) {
                (AType::A, Msg4Val::A(v)) => {
                    (Msg1Fmt).serialize_into(v, obuf);
                },
                (AType::B, Msg4Val::B(v)) => {
                    (Msg2Fmt).serialize_into(v, obuf);
                },
                (AType::C, Msg4Val::C(v)) => {
                    (Msg3Fmt).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg4Val<'i>> for Msg4ValFmt {
        fn prepare(&self, v: &Msg4Val<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            reveal(<Msg4Val as DeepView>::deep_view);
            reveal(Msg4ValSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.t.lemma_deep_view();
            }

            proof {
                self.t.lemma_deep_view();
            }

            match (self.t, v) {
                (AType::A, Msg4Val::A(v)) => (Named("msg1", Msg1Fmt)).prepare(v),
                (AType::B, Msg4Val::B(v)) => (Named("msg2", Msg2Fmt)).prepare(v),
                (AType::C, Msg4Val::C(v)) => (Named("msg3", Msg3Fmt)).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

} // verus!
