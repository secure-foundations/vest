#![allow(warnings)]
use vps_lib::combinators::mapped::spec::*;
use vps_lib::combinators::recursive::*;
use vps_lib::combinators::*;
use vps_lib::core::exec::bytes_eq;
use vps_lib::core::exec::input::{InputBuf, InputSlice};
use vps_lib::core::exec::output::OutputBuf;
use vps_lib::core::exec::parser::*;
use vps_lib::core::exec::serializer::*;
use vps_lib::core::exec::ParseError;
use vps_lib::core::{proof::*, spec::*};
use vps_lib::primitives::btcvarint::VarInt;
use vps_lib::primitives::leb128::ULeb128;
use vps_lib::Never;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `msg`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg {
    pub a: u8,
    pub b: [u8; 2],
}

# [verifier::ext_equal]
pub struct MsgSpec<T0 = u8, T1 = Seq<u8>> {
    pub a: T0,
    pub b: T1,
}

pub type MsgInner = (u8, Seq<u8>);

impl DeepView for Msg {
    type V = MsgSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        MsgSpec { a: self.a.deep_view(), b: self.b.deep_view() }
    }
}

impl Msg {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().a == self.a.deep_view(),
            self.deep_view().b == self.b.deep_view(),
    {
        reveal(<Msg as DeepView>::deep_view);
    }
}

impl<T0, T1> MsgSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (a, b) = input;
        Self { a, b }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { a, b } = self;
        (a, b)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(MsgSpec::from_structural);
        reveal(MsgSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(MsgSpec::from_structural);
        reveal(MsgSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { a, b } => (a, b),
            },
    {
        reveal(MsgSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MsgForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MsgReverse;

impl SpecMap for MsgForward {
    type Input = MsgInner;

    type Output = MsgSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        MsgSpec::from_structural(input)
    }
}

impl SpecMap for MsgReverse {
    type Input = MsgSpec;

    type Output = MsgInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `optmsg`."]
pub type Optmsg = Option<Msg>;

pub type OptmsgSpec = Option<MsgSpec>;

# [doc = "data type for `const_10`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Const10<'i> {
    pub reserved: &'i [u8],
}

# [verifier::ext_equal]
pub struct Const10Spec<T0 = Seq<u8>> {
    pub reserved: T0,
}

pub type Const10Inner = Seq<u8>;

impl<'i> DeepView for Const10<'i> {
    type V = Const10Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Const10Spec { reserved: self.reserved.deep_view() }
    }
}

impl<'i> Const10<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().reserved == self.reserved.deep_view(),
    {
        reveal(<Const10 as DeepView>::deep_view);
    }
}

impl<T0> Const10Spec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let reserved = input;
        Self { reserved }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { reserved } = self;
        reserved
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Const10Spec::from_structural);
        reveal(Const10Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Const10Spec::from_structural);
        reveal(Const10Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { reserved } => reserved,
            },
    {
        reveal(Const10Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Const10Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Const10Reverse;

impl SpecMap for Const10Forward {
    type Input = Const10Inner;

    type Output = Const10Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Const10Spec::from_structural(input)
    }
}

impl SpecMap for Const10Reverse {
    type Input = Const10Spec;

    type Output = Const10Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `a`."]
pub type A<'i> = Const10<'i>;

pub type ASpec = Const10Spec;

# [doc = "data type for `b`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct B<'i> {
    pub x: &'i [u8],
    pub y: A<'i>,
}

# [verifier::ext_equal]
pub struct BSpec<T0 = Seq<u8>, T1 = ASpec> {
    pub x: T0,
    pub y: T1,
}

pub type BInner = (Seq<u8>, ASpec);

impl<'i> DeepView for B<'i> {
    type V = BSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        BSpec { x: self.x.deep_view(), y: self.y.deep_view() }
    }
}

impl<'i> B<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().x == self.x.deep_view(),
            self.deep_view().y == self.y.deep_view(),
    {
        reveal(<B as DeepView>::deep_view);
    }
}

impl<T0, T1> BSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (x, y) = input;
        Self { x, y }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { x, y } = self;
        (x, y)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(BSpec::from_structural);
        reveal(BSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(BSpec::from_structural);
        reveal(BSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { x, y } => (x, y),
            },
    {
        reveal(BSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BReverse;

impl SpecMap for BForward {
    type Input = BInner;

    type Output = BSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        BSpec::from_structural(input)
    }
}

impl SpecMap for BReverse {
    type Input = BSpec;

    type Output = BInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tagged_mix`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct TaggedMix<'i> {
    pub x: Option<Const10<'i>>,
    pub y: Vec<A<'i>>,
    pub z: Option<B<'i>>,
    pub w: Vec<Msg>,
}

# [verifier::ext_equal]
pub struct TaggedMixSpec<
    T0 = Option<Const10Spec>,
    T1 = Seq<ASpec>,
    T2 = Option<BSpec>,
    T3 = Seq<MsgSpec>,
> {
    pub x: T0,
    pub y: T1,
    pub z: T2,
    pub w: T3,
}

pub type TaggedMixInner = (Option<Const10Spec>, (Seq<ASpec>, (Option<BSpec>, Seq<MsgSpec>)));

impl<'i> DeepView for TaggedMix<'i> {
    type V = TaggedMixSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TaggedMixSpec {
            x: self.x.deep_view(),
            y: self.y.deep_view(),
            z: self.z.deep_view(),
            w: self.w.deep_view(),
        }
    }
}

impl<'i> TaggedMix<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().x == self.x.deep_view(),
            self.deep_view().y == self.y.deep_view(),
            self.deep_view().z == self.z.deep_view(),
            self.deep_view().w == self.w.deep_view(),
    {
        reveal(<TaggedMix as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3> TaggedMixSpec<T0, T1, T2, T3> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, T3)))) -> Self {
        let (x, (y, (z, w))) = input;
        Self { x, y, z, w }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, T3))) {
        let Self { x, y, z, w } = self;
        (x, (y, (z, w)))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TaggedMixSpec::from_structural);
        reveal(TaggedMixSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, T3))))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TaggedMixSpec::from_structural);
        reveal(TaggedMixSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { x, y, z, w } => (x, (y, (z, w))),
            },
    {
        reveal(TaggedMixSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TaggedMixForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TaggedMixReverse;

impl SpecMap for TaggedMixForward {
    type Input = TaggedMixInner;

    type Output = TaggedMixSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TaggedMixSpec::from_structural(input)
    }
}

impl SpecMap for TaggedMixReverse {
    type Input = TaggedMixSpec;

    type Output = TaggedMixInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `msg`."]
# [derive (Clone, Copy)]
pub struct MsgFmt;

pub type MsgFmtSpec = Named<
    Mapped<Pair<Const<U8, u8>, Const<Fixed<2>, [u8; 2]>>, BiMap<MsgForward, MsgReverse>>,
>;

impl MsgFmt {
    # [doc = "specification constructor for `msg`."]
    pub open spec fn spec_inner() -> MsgFmtSpec {
        Named(
            "msg",
            Mapped {
                inner: Pair(Const(U8, 1), Const(Fixed::<2>, [0x01u8, 0x02u8])),
                mapper: BiMap(MsgForward, MsgReverse),
            },
        )
    }
}

# [doc = "named format combinator for `optmsg`."]
# [derive (Clone, Copy)]
pub struct OptmsgFmt;

pub type OptmsgFmtSpec = Named<OptionalEnd<MsgFmt>>;

impl OptmsgFmt {
    # [doc = "specification constructor for `optmsg`."]
    pub open spec fn spec_inner() -> OptmsgFmtSpec {
        Named("optmsg", OptionalEnd(MsgFmt))
    }
}

# [doc = "named format combinator for `const_10`."]
# [derive (Clone, Copy)]
pub struct Const10Fmt;

pub type Const10FmtSpec = Named<Mapped<Fixed<10>, BiMap<Const10Forward, Const10Reverse>>>;

impl Const10Fmt {
    # [doc = "specification constructor for `const_10`."]
    pub open spec fn spec_inner() -> Const10FmtSpec {
        Named(
            "const_10",
            Mapped { inner: Fixed::<10>, mapper: BiMap(Const10Forward, Const10Reverse) },
        )
    }
}

# [doc = "named format combinator for `a`."]
# [derive (Clone, Copy)]
pub struct AFmt;

pub type AFmtSpec = Named<
    PrefixTagged<U8, u8, PrefixTagged<U8, u8, SuffixTagged<Const10Fmt, U8, u8>>>,
>;

impl AFmt {
    # [doc = "specification constructor for `a`."]
    pub open spec fn spec_inner() -> AFmtSpec {
        Named("a", PrefixTagged(U8, 1, PrefixTagged(U8, 2, SuffixTagged(Const10Fmt, U8, 3))))
    }
}

# [doc = "named format combinator for `b`."]
# [derive (Clone, Copy)]
pub struct BFmt;

pub type BFmtSpec = Named<
    Mapped<
        Pair<Fixed<10>, PrefixTagged<U16Le, u16, SuffixTagged<AFmt, U8, u8>>>,
        BiMap<BForward, BReverse>,
    >,
>;

impl BFmt {
    # [doc = "specification constructor for `b`."]
    pub open spec fn spec_inner() -> BFmtSpec {
        Named(
            "b",
            Mapped {
                inner: Pair(Fixed::<10>, PrefixTagged(U16Le, 65535, SuffixTagged(AFmt, U8, 1))),
                mapper: BiMap(BForward, BReverse),
            },
        )
    }
}

# [doc = "named format combinator for `tagged_mix`."]
# [derive (Clone, Copy)]
pub struct TaggedMixFmt;

pub type TaggedMixFmtSpec = Named<
    Mapped<
        Optional<
            PrefixTagged<U8, u8, Const10Fmt>,
            Repeat<
                PrefixTagged<U8, u8, AFmt>,
                Optional<PrefixTagged<U8, u8, BFmt>, RepeatTillEnd<PrefixTagged<U8, u8, MsgFmt>>>,
            >,
        >,
        BiMap<TaggedMixForward, TaggedMixReverse>,
    >,
>;

impl TaggedMixFmt {
    # [doc = "specification constructor for `tagged_mix`."]
    pub open spec fn spec_inner() -> TaggedMixFmtSpec {
        Named(
            "tagged_mix",
            Mapped {
                inner: Optional(
                    PrefixTagged(U8, 10, Const10Fmt),
                    Repeat(
                        PrefixTagged(U8, 11, AFmt),
                        Optional(
                            PrefixTagged(U8, 12, BFmt),
                            RepeatTillEnd(PrefixTagged(U8, 13, MsgFmt)),
                        ),
                    ),
                ),
                mapper: BiMap(TaggedMixForward, TaggedMixReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for MsgFmt {
        type PVal = MsgSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MsgFmt {
        type Val = MsgSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MsgFmt {
        type SValue = MsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgFmt {
        type SVal = MsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgFmt {
        type T = MsgSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for OptmsgFmt {
        type PVal = OptmsgSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for OptmsgFmt {
        type Val = OptmsgSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for OptmsgFmt {
        type SValue = OptmsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OptmsgFmt {
        type SVal = OptmsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for OptmsgFmt {
        type T = OptmsgSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Const10Fmt {
        type PVal = Const10Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Const10Fmt {
        type Val = Const10Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Const10Fmt {
        type SValue = Const10Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Const10Fmt {
        type SVal = Const10Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Const10Fmt {
        type T = Const10Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for AFmt {
        type PVal = ASpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for AFmt {
        type Val = ASpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for AFmt {
        type SValue = ASpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AFmt {
        type SVal = ASpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for AFmt {
        type T = ASpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for BFmt {
        type PVal = BSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for BFmt {
        type Val = BSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for BFmt {
        type SValue = BSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for BFmt {
        type SVal = BSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for BFmt {
        type T = BSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TaggedMixFmt {
        type PVal = TaggedMixSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TaggedMixFmt {
        type Val = TaggedMixSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TaggedMixFmt {
        type SValue = TaggedMixSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TaggedMixFmt {
        type SVal = TaggedMixSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TaggedMixFmt {
        type T = TaggedMixSpec;

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
        vps_lib::combinators::disjoint::disjointness_lemmas,
        MsgSpec::lemma_from_into,
        MsgSpec::lemma_into_from,
        Const10Spec::lemma_from_into,
        Const10Spec::lemma_into_from,
        BSpec::lemma_from_into,
        BSpec::lemma_into_from,
        TaggedMixSpec::lemma_from_into,
        TaggedMixSpec::lemma_into_from,
    };

    impl SafeParser for MsgFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: MsgInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MsgSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            reveal(<MsgFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: MsgInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MsgSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MsgFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MsgFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgFmt as Consistency>::consistent);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: MsgSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                MsgSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: MsgInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MsgSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MsgFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MsgFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for OptmsgFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<OptmsgFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for OptmsgFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<OptmsgFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for OptmsgFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<OptmsgFmt as SpecParser>::spec_parse);
            reveal(<OptmsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OptmsgFmt as SpecParser>::spec_parse);
            reveal(<OptmsgFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for OptmsgFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<OptmsgFmt as SpecSerializer>::spec_serialize);
            reveal(<OptmsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for OptmsgFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<OptmsgFmt as SpecParser>::spec_parse);
            reveal(<OptmsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OptmsgFmt as Consistency>::consistent);
            reveal(<OptmsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OptmsgFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OptmsgFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for OptmsgFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<OptmsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OptmsgFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Const10Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Const10Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Const10Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Const10Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Const10Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Const10Fmt as SpecParser>::spec_parse);
            reveal(<Const10Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: Const10Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Const10Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Const10Fmt as SpecParser>::spec_parse);
            reveal(<Const10Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Const10Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Const10Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Const10Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Const10Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Const10Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Const10Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Const10Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Const10Fmt as SpecSerializer>::spec_serialize);
            reveal(<Const10Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Const10Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Const10Fmt as SpecParser>::spec_parse);
            reveal(<Const10Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Const10Fmt as Consistency>::consistent);
            reveal(<Const10Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: Const10Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Const10Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Const10Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Const10Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Const10Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Const10Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Const10Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Const10Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Const10Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Const10Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Const10Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Const10Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AFmt as SpecParser>::spec_parse);
            reveal(<AFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AFmt as SpecParser>::spec_parse);
            reveal(<AFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AFmt as SpecSerializer>::spec_serialize);
            reveal(<AFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for AFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<AFmt as SpecParser>::spec_parse);
            reveal(<AFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AFmt as Consistency>::consistent);
            reveal(<AFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for BFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<BFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for BFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<BFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for BFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<BFmt as SpecParser>::spec_parse);
            reveal(<BFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: BInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<BFmt as SpecParser>::spec_parse);
            reveal(<BFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: BInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for BFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for BFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<BFmt as SpecSerializer>::spec_serialize);
            reveal(<BFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for BFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<BFmt as SpecParser>::spec_parse);
            reveal(<BFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BFmt as Consistency>::consistent);
            reveal(<BFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: BSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                BSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for BFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<BFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: BInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for BFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<BFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for BFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<BFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TaggedMixFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TaggedMixFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TaggedMixFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TaggedMixFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TaggedMixFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TaggedMixFmt as SpecParser>::spec_parse);
            reveal(<TaggedMixFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: TaggedMixInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TaggedMixSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TaggedMixFmt as SpecParser>::spec_parse);
            reveal(<TaggedMixFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TaggedMixInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TaggedMixSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for TaggedMixFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TaggedMixFmt as SpecSerializer>::spec_serialize);
            reveal(<TaggedMixFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TaggedMixFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TaggedMixFmt as SpecParser>::spec_parse);
            reveal(<TaggedMixFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TaggedMixFmt as Consistency>::consistent);
            reveal(<TaggedMixFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: TaggedMixSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TaggedMixSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TaggedMixFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TaggedMixFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TaggedMixInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TaggedMixSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for TaggedMixFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TaggedMixFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TaggedMixFmt as SpecSerializer>::spec_serialize);
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

    impl<'i> Parser<&'i [u8]> for MsgFmt {
        type PT = Msg;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MsgFmt as SpecParser>::spec_parse);
            reveal(<Msg as DeepView>::deep_view);
            reveal(MsgSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, a) = Const(U8, 1).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, b) = Const(Fixed::<2>, [0x01, 0x02]).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Msg { a, b };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg> for MsgFmt {
        fn serialize_into(&self, v: &Msg, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<MsgFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            reveal(<Msg as DeepView>::deep_view);
            reveal(MsgSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg { a, b } = v;
            U8.serialize_into(a, obuf);
            Fixed::<2>.serialize_into(b, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg> for MsgFmt {
        fn prepare(&self, v: &Msg) -> Result<usize, PreSerializeError> {
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            reveal(<Msg as DeepView>::deep_view);
            reveal(MsgSpec::into_structural);
            let Msg { a, b } = v;
            let l1 = (Const(U8, 1)).prepare(a)?;
            let l2 = (Const(Fixed::<2>, [0x01, 0x02])).prepare(b)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for OptmsgFmt {
        type PT = Optmsg;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<OptmsgFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Opt(MsgFmt).parse(ibuf)?;
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let rest = ibuf.skip(n);
            let _ = Eof.parse(&rest)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Optmsg> for OptmsgFmt {
        fn serialize_into(&self, v: &Optmsg, obuf: &mut Output) {
            reveal(<OptmsgFmt as SpecSerializer>::spec_serialize);
            reveal(<OptmsgFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            Opt(MsgFmt).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Optmsg> for OptmsgFmt {
        fn prepare(&self, v: &Optmsg) -> Result<usize, PreSerializeError> {
            reveal(<OptmsgFmt as SpecByteLen>::byte_len);
            (Opt(MsgFmt)).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for Const10Fmt {
        type PT = Const10<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Const10Fmt as SpecParser>::spec_parse);
            reveal(<Const10 as DeepView>::deep_view);
            reveal(Const10Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, reserved) = (Fixed::<10>).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Const10 { reserved };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Const10<'i>> for Const10Fmt {
        fn serialize_into(&self, v: &Const10<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<Const10Fmt as SpecSerializer>::spec_serialize);
            reveal(<Const10Fmt as SpecByteLen>::byte_len);
            reveal(<Const10 as DeepView>::deep_view);
            reveal(Const10Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Const10 { reserved } = v;
            Fixed::<10>.serialize_into(*reserved, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Const10<'i>> for Const10Fmt {
        fn prepare(&self, v: &Const10<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Const10Fmt as SpecByteLen>::byte_len);
            reveal(<Const10 as DeepView>::deep_view);
            reveal(Const10Spec::into_structural);
            let Const10 { reserved } = v;
            let l1 = (Fixed::<10>).prepare(reserved)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for AFmt {
        type PT = A<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<AFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = PrefixTagged(
                U8,
                1,
                PrefixTagged(U8, 2, SuffixTagged(Const10Fmt, U8, 3)),
            ).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, A<'i>> for AFmt {
        fn serialize_into(&self, v: &A<'i>, obuf: &mut Output) {
            reveal(<AFmt as SpecSerializer>::spec_serialize);
            reveal(<AFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            PrefixTagged(
                U8,
                1,
                PrefixTagged(U8, 2, SuffixTagged(Const10Fmt, U8, 3)),
            ).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<A<'i>> for AFmt {
        fn prepare(&self, v: &A<'i>) -> Result<usize, PreSerializeError> {
            reveal(<AFmt as SpecByteLen>::byte_len);
            (PrefixTagged(U8, 1, PrefixTagged(U8, 2, SuffixTagged(Const10Fmt, U8, 3)))).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for BFmt {
        type PT = B<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<BFmt as SpecParser>::spec_parse);
            reveal(<B as DeepView>::deep_view);
            reveal(BSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, x) = (Fixed::<10>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, y) = (PrefixTagged(U16Le, 65535, SuffixTagged(AFmt, U8, 1))).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = B { x, y };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, B<'i>> for BFmt {
        fn serialize_into(&self, v: &B<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<BFmt as SpecSerializer>::spec_serialize);
            reveal(<BFmt as SpecByteLen>::byte_len);
            reveal(<B as DeepView>::deep_view);
            reveal(BSpec::into_structural);
            let ghost old_obuf = obuf@;

            let B { x, y } = v;
            Fixed::<10>.serialize_into(*x, obuf);
            PrefixTagged(U16Le, 65535, SuffixTagged(AFmt, U8, 1)).serialize_into(y, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<B<'i>> for BFmt {
        fn prepare(&self, v: &B<'i>) -> Result<usize, PreSerializeError> {
            reveal(<BFmt as SpecByteLen>::byte_len);
            reveal(<B as DeepView>::deep_view);
            reveal(BSpec::into_structural);
            let B { x, y } = v;
            let l1 = (Fixed::<10>).prepare(x)?;
            let l2 = (PrefixTagged(U16Le, 65535, SuffixTagged(AFmt, U8, 1))).prepare(y)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for TaggedMixFmt {
        type PT = TaggedMix<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TaggedMixFmt as SpecParser>::spec_parse);
            reveal(<TaggedMix as DeepView>::deep_view);
            reveal(TaggedMixSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, x) = (Opt(PrefixTagged(U8, 10, Const10Fmt))).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, y) = (Star(PrefixTagged(U8, 11, AFmt))).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, z) = (Opt(PrefixTagged(U8, 12, BFmt))).parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, w) = (RepeatTillEnd(PrefixTagged(U8, 13, MsgFmt))).parse(&rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = TaggedMix { x, y, z, w };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TaggedMix<'i>> for TaggedMixFmt {
        fn serialize_into(&self, v: &TaggedMix<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<TaggedMixFmt as SpecSerializer>::spec_serialize);
            reveal(<TaggedMixFmt as SpecByteLen>::byte_len);
            reveal(<TaggedMix as DeepView>::deep_view);
            reveal(TaggedMixSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TaggedMix { x, y, z, w } = v;
            Opt(PrefixTagged(U8, 10, Const10Fmt)).serialize_into(x, obuf);
            Star(PrefixTagged(U8, 11, AFmt)).serialize_into(y, obuf);
            Opt(PrefixTagged(U8, 12, BFmt)).serialize_into(z, obuf);
            Star(PrefixTagged(U8, 13, MsgFmt)).serialize_into(w, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TaggedMix<'i>> for TaggedMixFmt {
        fn prepare(&self, v: &TaggedMix<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TaggedMixFmt as SpecByteLen>::byte_len);
            reveal(<TaggedMix as DeepView>::deep_view);
            reveal(TaggedMixSpec::into_structural);
            let TaggedMix { x, y, z, w } = v;
            let l1 = (Opt(PrefixTagged(U8, 10, Const10Fmt))).prepare(x)?;
            let l2 = (Star(PrefixTagged(U8, 11, AFmt))).prepare(y)?;
            let l3 = (Opt(PrefixTagged(U8, 12, BFmt))).prepare(z)?;
            let l4 = (Star(PrefixTagged(U8, 13, MsgFmt))).prepare(w)?;
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
