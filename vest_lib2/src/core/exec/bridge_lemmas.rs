use crate::combinators::bytes::{AndThen, ExactLen};
use crate::combinators::mapped::spec::{BiMap, SpecMap};
use crate::combinators::named::Named;
use crate::combinators::reference::Ref;
use crate::combinators::tail::{RepeatTillEnd, Tail};
use crate::combinators::AsLen;
use crate::combinators::Optional;
use crate::combinators::OptionalEnd;
use crate::combinators::{
    Alt, Array, Bind, Choice, Cond, Const, Mapped, Opt, Pair, Preceded, PrefixTagged, Refined,
    Repeat, RepeatN, Star, SuffixTagged, Sum, Terminated,
};
use crate::core::exec::fns::{Map, MapRef, Pred};
use crate::core::exec::input::InputBuf;
use crate::core::exec::{OutputBuf, Parser, Prepare, Serializer};
use crate::core::proof::Productive;
use crate::core::spec::{
    BytesCombinator, Consistency, SafeParser, SpecByteLen, SpecParser, SpecPred, SpecSerializer,
    SpecSerializerDps,
};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

// ----------------------------------------------------
// ExactLen
// ----------------------------------------------------
pub proof fn lemma_exact_len_parser_exec_inv<I, Len, Inner>(fmt: &ExactLen<Inner, Len>) where
    I: InputBuf,
    Len: AsLen,
    Inner: Parser<I> + SafeParser,

    ensures
        fmt.1.exec_inv() && fmt.1.safe_inv() ==> fmt.exec_inv() && fmt.safe_inv(),
{
}

pub proof fn lemma_exact_len_serializer_exec_inv<Output, Inner, Len, T>(
    fmt: &ExactLen<Inner, Len>,
) where
    Output: OutputBuf,
    Len: AsLen,
    Inner: Serializer<Output, T> + SpecByteLen<T = T::V>,
    T: DeepView + ?Sized,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_exact_len_prepare_exec_inv<Inner, Len, T>(fmt: &ExactLen<Inner, Len>) where
    Len: AsLen,
    Inner: Prepare<T>,
    T: DeepView + ?Sized,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// AndThen
// ----------------------------------------------------
pub proof fn lemma_and_then_parser_exec_inv<I, TailType, Then>(fmt: &AndThen<TailType, Then>) where
    I: InputBuf,
    TailType: Parser<I, PT = I, PVal = Seq<u8>>,
    Then: Parser<I>,

    ensures
        fmt.0.exec_inv() && fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_and_then_serializer_exec_inv<Output, Then, T>(fmt: &AndThen<Tail, Then>) where
    Output: OutputBuf,
    Then: Serializer<Output, T>,
    T: DeepView + ?Sized,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_and_then_prepare_exec_inv<Then, T>(fmt: &AndThen<Tail, Then>) where
    Then: Prepare<T>,
    T: DeepView + ?Sized,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Mapped
// ----------------------------------------------------
pub proof fn lemma_mapped_parser_exec_inv<I, Inner, M, MRev>(
    fmt: &Mapped<Inner, BiMap<M, MRev>>,
) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,
    M: Map<Inner::PT, Input = Inner::PVal>,
    MRev: SpecMap<Input = M::Output, Output = M::Input>,

    ensures
        fmt.inner.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_mapped_serializer_exec_inv<Output, Inner, M, MRev, T, InnerT>(
    fmt: &Mapped<Inner, BiMap<M, MRev>>,
) where
    Output: OutputBuf,
    Inner: Serializer<Output, InnerT>,
    T: DeepView,
    InnerT: DeepView,
    M: SpecMap<Input = Inner::T, Output = T::V>,
    MRev: for <'x>Map<&'x T, O = InnerT, Input = T::V, Output = Inner::T>,

    ensures
        fmt.inner.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_mapped_prepare_exec_inv<Inner, M, MRev, T, InnerT>(
    fmt: &Mapped<Inner, BiMap<M, MRev>>,
) where
    Inner: Prepare<InnerT>,
    T: DeepView,
    InnerT: DeepView,
    M: SpecMap<Input = Inner::T, Output = T::V>,
    MRev: for <'x>Map<&'x T, O = InnerT, Input = T::V, Output = Inner::T>,

    ensures
        fmt.inner.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Refined
// ----------------------------------------------------
pub proof fn lemma_refined_parser_exec_inv<I, A, PredFn>(fmt: &Refined<A, PredFn>) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    PredFn: Pred<A::PT>,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_refined_serializer_exec_inv<Output, A, PredFn, T>(
    fmt: &Refined<A, PredFn>,
) where Output: OutputBuf, A: Serializer<Output, T>, PredFn: SpecPred<T::V>, T: DeepView
    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_refined_prepare_exec_inv<A, PredFn, T>(fmt: &Refined<A, PredFn>) where
    A: Prepare<T>,
    PredFn: Pred<T>,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Const
// ----------------------------------------------------
pub proof fn lemma_const_parser_exec_inv<I, Inner, T>(fmt: &Const<Inner, T>) where
    I: InputBuf,
    Inner: Parser<I, PT = T, PVal = T> + Prepare<T>,
    T: DeepView<V = T> + PartialEq + Structural,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && (forall|v: T| v.deep_view() == v)) ==> Parser::<
            I,
        >::exec_inv(fmt),
{
}

pub proof fn lemma_const_serializer_exec_inv<Output, Inner, T>(fmt: &Const<Inner, T>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView<V = T>,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_const_prepare_exec_inv<Inner, T>(fmt: &Const<Inner, T>) where
    Inner: Prepare<T>,
    T: DeepView<V = T> + PartialEq + Structural,

    ensures
        (fmt.0.exec_inv() && (forall|v: T| v.deep_view() == v)) ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Repeat
// ----------------------------------------------------
#[cfg(feature = "alloc")]
pub proof fn lemma_repeat_parser_exec_inv<I, A, B>(fmt: &Repeat<A, B>) where
    I: InputBuf,
    A: Parser<I> + SafeParser + Productive + Copy,
    B: Parser<I> + SafeParser + Copy,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv() && fmt.0.productive_inv() && fmt.1.exec_inv()
            && fmt.1.safe_inv()) ==> (fmt.exec_inv() && fmt.safe_inv()),
{
}

// ----------------------------------------------------
// RepeatTillEnd
// ----------------------------------------------------
#[cfg(feature = "alloc")]
pub proof fn lemma_repeat_till_end_parser_exec_inv<I, A>(fmt: &RepeatTillEnd<A>) where
    I: InputBuf,
    A: Parser<I> + SafeParser + Productive + Copy,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv() && fmt.0.productive_inv()) ==> (fmt.exec_inv()
            && fmt.safe_inv()),
{
}

// ----------------------------------------------------
// Cond
// ----------------------------------------------------
pub proof fn lemma_cond_parser_exec_inv<I, Inner>(fmt: &Cond<Inner>) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_cond_serializer_exec_inv<Output, Inner, T>(fmt: &Cond<Inner>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_cond_prepare_exec_inv<Inner, T>(fmt: &Cond<Inner>) where
    Inner: Prepare<T>,
    T: DeepView,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Choice
// ----------------------------------------------------
pub proof fn lemma_choice_parser_exec_inv<I, A, B>(fmt: &Choice<A, B>) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I>,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_choice_serializer_exec_inv<Output, A, B, TA, TB>(fmt: &Choice<A, B>) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_choice_prepare_exec_inv<A, B, TA, TB>(fmt: &Choice<A, B>) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Alt
// ----------------------------------------------------
pub proof fn lemma_alt_parser_exec_inv<const NONDETERMINISTIC: bool, I, A, B>(
    fmt: &Alt<A, B, NONDETERMINISTIC>,
) where I: View<V = Seq<u8>>, A: Parser<I>, B: Parser<I, PVal = A::PVal, PT = A::PT>
    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Sum
// ----------------------------------------------------
pub proof fn lemma_sum_inl_parser_exec_inv<I, A, B>(a: A) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I>,

    ensures
        a.exec_inv() ==> (&Sum::<A, B>::Inl(a)).exec_inv(),
{
}

pub proof fn lemma_sum_inr_parser_exec_inv<I, A, B>(b: B) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I>,

    ensures
        b.exec_inv() ==> (&Sum::<A, B>::Inr(b)).exec_inv(),
{
}

pub proof fn lemma_sum_inl_serializer_exec_inv<Output, A, B, TA, TB>(a: A) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        a.exec_inv() ==> (&Sum::<A, B>::Inl(a)).exec_inv(),
{
}

pub proof fn lemma_sum_inr_serializer_exec_inv<Output, A, B, TA, TB>(b: B) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        b.exec_inv() ==> (&Sum::<A, B>::Inr(b)).exec_inv(),
{
}

pub proof fn lemma_sum_inl_prepare_exec_inv<A, B, TA, TB>(a: A) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        a.exec_inv() ==> (&Sum::<A, B>::Inl(a)).exec_inv(),
{
}

pub proof fn lemma_sum_inr_prepare_exec_inv<A, B, TA, TB>(b: B) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        b.exec_inv() ==> (&Sum::<A, B>::Inr(b)).exec_inv(),
{
}

// ----------------------------------------------------
// Opt
// ----------------------------------------------------
pub proof fn lemma_opt_parser_exec_inv<I, A>(fmt: &Opt<A>) where I: View<V = Seq<u8>>, A: Parser<I>
    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_opt_serializer_exec_inv<Output, A, T>(fmt: &Opt<A>) where
    Output: OutputBuf,
    A: Serializer<Output, T>,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_opt_prepare_exec_inv<A, T>(fmt: &Opt<A>) where A: Prepare<T>, T: DeepView
    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Optional
// ----------------------------------------------------
pub proof fn lemma_optional_parser_exec_inv<I, A, B>(fmt: &Optional<A, B>) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv() && fmt.1.exec_inv() && fmt.1.safe_inv())
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_optional_serializer_exec_inv<Output, A, B, TA, TB>(fmt: &Optional<A, B>) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_optional_prepare_exec_inv<A, B, TA, TB>(fmt: &Optional<A, B>) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// OptionalEnd
// ----------------------------------------------------
pub proof fn lemma_optional_end_parser_exec_inv<I, A>(fmt: &OptionalEnd<A>) where
    I: InputBuf,
    A: Parser<I> + SafeParser,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv()) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_optional_end_serializer_exec_inv<Output, A, T>(fmt: &OptionalEnd<A>) where
    Output: OutputBuf,
    A: Serializer<Output, T>,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_optional_end_prepare_exec_inv<A, T>(fmt: &OptionalEnd<A>) where
    A: Prepare<T>,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Preceded
// ----------------------------------------------------
pub proof fn lemma_preceded_parser_exec_inv<I, A, B, AVal>(fmt: &Preceded<A, AVal, B, false>) where
    I: InputBuf,
    A: Parser<I, PT = AVal> + SafeParser<PVal = AVal>,
    B: Parser<I> + SafeParser,
    AVal: DeepView<V = AVal>,

    ensures
        (fmt.a.exec_inv() && fmt.a.safe_inv() && fmt.b.exec_inv() && fmt.b.safe_inv())
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_preceded_checked_parser_exec_inv<I, A, B, AVal>(
    fmt: &Preceded<A, AVal, B, true>,
) where
    I: InputBuf,
    A: Parser<I, PT = AVal> + SafeParser<PVal = AVal>,
    B: Parser<I> + SafeParser,
    AVal: DeepView<V = AVal> + PartialEq + Structural,

    ensures
        (fmt.a.exec_inv() && fmt.a.safe_inv() && fmt.b.exec_inv() && fmt.b.safe_inv() && (forall|
            v: AVal,
        |
            v.deep_view() == v)) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_preceded_serializer_exec_inv<Output, A, B, AVal, T, const CHECK: bool>(
    fmt: &Preceded<A, AVal, B, CHECK>,
) where
    Output: OutputBuf,
    A: Serializer<Output, AVal>,
    B: Serializer<Output, T>,
    AVal: DeepView<V = AVal>,
    T: DeepView,

    ensures
        (fmt.a.exec_inv() && fmt.b.exec_inv() && (forall|v: AVal| v.deep_view() == v))
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_preceded_prepare_exec_inv<A, B, AVal, T, const CHECK: bool>(
    fmt: &Preceded<A, AVal, B, CHECK>,
) where A: Prepare<AVal>, B: Prepare<T>, AVal: DeepView<V = AVal>, T: DeepView
    ensures
        (fmt.a.exec_inv() && fmt.b.exec_inv() && (forall|v: AVal| v.deep_view() == v))
            ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Terminated
// ----------------------------------------------------
pub proof fn lemma_terminated_parser_exec_inv<I, A, B, BVal>(
    fmt: &Terminated<A, B, BVal, false>,
) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I, PT = BVal> + SafeParser<PVal = BVal>,
    BVal: DeepView<V = BVal>,

    ensures
        (fmt.a.exec_inv() && fmt.a.safe_inv() && fmt.b.exec_inv() && fmt.b.safe_inv())
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_terminated_checked_parser_exec_inv<I, A, B, BVal>(
    fmt: &Terminated<A, B, BVal, true>,
) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I, PT = BVal> + SafeParser<PVal = BVal>,
    BVal: DeepView<V = BVal> + PartialEq + Structural,

    ensures
        (fmt.a.exec_inv() && fmt.a.safe_inv() && fmt.b.exec_inv() && fmt.b.safe_inv() && (forall|
            v: BVal,
        |
            v.deep_view() == v)) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_terminated_serializer_exec_inv<Output, A, B, BVal, T, const CHECK: bool>(
    fmt: &Terminated<A, B, BVal, CHECK>,
) where
    Output: OutputBuf,
    A: Serializer<Output, T>,
    B: Serializer<Output, BVal>,
    BVal: DeepView<V = BVal>,
    T: DeepView,

    ensures
        (fmt.a.exec_inv() && fmt.b.exec_inv() && (forall|v: BVal| v.deep_view() == v))
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_terminated_prepare_exec_inv<A, B, BVal, T, const CHECK: bool>(
    fmt: &Terminated<A, B, BVal, CHECK>,
) where A: Prepare<T>, B: Prepare<BVal>, BVal: DeepView<V = BVal>, T: DeepView
    ensures
        (fmt.a.exec_inv() && fmt.b.exec_inv() && (forall|v: BVal| v.deep_view() == v))
            ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// PrefixTagged / SuffixTagged
// ----------------------------------------------------
pub proof fn lemma_prefix_tagged_parser_exec_inv<I, Tg, TagVal, Of>(
    fmt: &PrefixTagged<Tg, TagVal, Of>,
) where
    I: InputBuf,
    Tg: SpecByteLen<T = TagVal> + Parser<I, PT = TagVal, PVal = TagVal> + SafeParser,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Parser<I> + SafeParser,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv() && fmt.2.exec_inv() && fmt.2.safe_inv() && (forall|
            v: TagVal,
        |
            v.deep_view() == v)) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_prefix_tagged_serializer_exec_inv<Output, Tg, TagVal, Of, T>(
    fmt: &PrefixTagged<Tg, TagVal, Of>,
) where
    Output: OutputBuf,
    Tg: SpecByteLen<T = TagVal> + Serializer<Output, TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Serializer<Output, T>,
    T: DeepView,

    ensures
        (fmt.0.exec_inv() && fmt.2.exec_inv() && (forall|v: TagVal| v.deep_view() == v))
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_prefix_tagged_prepare_exec_inv<Tg, TagVal, Of, T>(
    fmt: &PrefixTagged<Tg, TagVal, Of>,
) where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Prepare<T>,
    T: DeepView,

    ensures
        (fmt.0.exec_inv() && fmt.2.exec_inv() && (forall|v: TagVal| v.deep_view() == v))
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_suffix_tagged_parser_exec_inv<I, Of, Tg, TagVal>(
    fmt: &SuffixTagged<Of, Tg, TagVal>,
) where
    I: InputBuf,
    Tg: SpecByteLen<T = TagVal> + Parser<I, PT = TagVal, PVal = TagVal> + SafeParser,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Parser<I> + SafeParser,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv() && fmt.1.exec_inv() && fmt.1.safe_inv() && (forall|
            v: TagVal,
        |
            v.deep_view() == v)) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_suffix_tagged_serializer_exec_inv<Output, Of, Tg, TagVal, T>(
    fmt: &SuffixTagged<Of, Tg, TagVal>,
) where
    Output: OutputBuf,
    Tg: SpecByteLen<T = TagVal> + Serializer<Output, TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Serializer<Output, T>,
    T: DeepView,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv() && (forall|v: TagVal| v.deep_view() == v))
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_suffix_tagged_prepare_exec_inv<Of, Tg, TagVal, T>(
    fmt: &SuffixTagged<Of, Tg, TagVal>,
) where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Prepare<T>,
    T: DeepView,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv() && (forall|v: TagVal| v.deep_view() == v))
            ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Pair
// ----------------------------------------------------
pub proof fn lemma_pair_parser_exec_inv<I, A, B>(fmt: &Pair<A, B>) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv() && fmt.1.exec_inv() && fmt.1.safe_inv())
            ==> fmt.exec_inv(),
{
}

pub proof fn lemma_pair_serializer_exec_inv<Output, A, B, TA, TB>(fmt: &Pair<A, B>) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_pair_prepare_exec_inv<A, B, TA, TB>(fmt: &Pair<A, B>) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Bind
// ----------------------------------------------------
pub proof fn lemma_bind_parser_exec_inv<I, A, B>(fmt: &Bind<A, B>) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: MapRef<A::PT, Input = A::PVal>,
    B::O: Parser<I> + SafeParser,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv() && (forall|pb: B::O| #[trigger]
            pb.exec_inv() && pb.safe_inv())) ==> (#[trigger] fmt.exec_inv() && fmt.safe_inv()),
{
    if fmt.0.exec_inv() && fmt.0.safe_inv() && (forall|pb: B::O| #[trigger]
        pb.exec_inv() && pb.safe_inv()) {
        assert(Parser::<I>::exec_inv(fmt));
        assert forall|key: A::PVal| #[trigger] fmt.1.spec_map(key).safe_inv() by {
            let pb = fmt.1.spec_map(key);
            assert(pb.exec_inv());
            assert(pb.exec_inv());
        };
        assert(fmt.safe_inv());
    }
}

pub proof fn lemma_bind_serializer_exec_inv<Output, A, B, TA, TB>(fmt: &Bind<A, B>) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B::O: Serializer<Output, TB>,
    B: MapRef<TA, Input = TA::V>,

    ensures
        (fmt.0.exec_inv() && (forall|pb: B::O| pb.exec_inv())) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_bind_prepare_exec_inv<A, B, TA, TB>(fmt: &Bind<A, B>) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B::O: Prepare<TB>,
    B: MapRef<TA, Input = TA::V>,

    ensures
        (fmt.0.exec_inv() && (forall|pb: B::O| pb.exec_inv())) ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Rust shared references
// ----------------------------------------------------
pub proof fn lemma_ref_parser_exec_inv<I, P>(parser: &P) where I: View<V = Seq<u8>>, P: Parser<I>
    ensures
        parser.exec_inv() ==> (&parser).exec_inv(),
{
}

pub proof fn lemma_ref_serializer_exec_inv<Output, S, T>(serializer: &S) where
    Output: OutputBuf,
    S: Serializer<Output, T>,
    T: DeepView + ?Sized,

    ensures
        serializer.exec_inv() ==> (&serializer).exec_inv(),
{
}

pub proof fn lemma_ref_prepare_exec_inv<S, T>(serializer: &S) where
    S: Prepare<T>,
    T: DeepView + ?Sized,

    ensures
        serializer.exec_inv() ==> (&serializer).exec_inv(),
{
}

// ----------------------------------------------------
// Ref
// ----------------------------------------------------
pub proof fn lemma_reference_parser_exec_inv<I, Inner>(fmt: &Ref<Inner>) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_reference_serializer_exec_inv<Output, Inner, T>(fmt: &Ref<Inner>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView + ?Sized,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_reference_prepare_exec_inv<Inner, T>(fmt: &Ref<Inner>) where
    Inner: Prepare<T>,
    T: DeepView + ?Sized,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Named
// ----------------------------------------------------
pub proof fn lemma_named_parser_exec_inv<I, Inner>(fmt: &Named<Inner>) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_named_serializer_exec_inv<Output, Inner, T>(fmt: &Named<Inner>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_named_prepare_exec_inv<Inner, T>(fmt: &Named<Inner>) where
    Inner: Prepare<T>,
    T: DeepView,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Star
// ----------------------------------------------------
#[cfg(feature = "alloc")]
pub proof fn lemma_star_parser_exec_inv<I, Inner>(fmt: &Star<Inner>) where
    I: InputBuf,
    Inner: Parser<I> + SafeParser + Productive + Copy,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv() && fmt.0.productive_inv()) ==> (fmt.exec_inv()
            && fmt.safe_inv()),
{
}

pub proof fn lemma_star_serializer_exec_inv<Output, Inner, T>(fmt: &Star<Inner>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_star_prepare_exec_inv<Inner, T>(fmt: &Star<Inner>) where
    Inner: Prepare<T>,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_repeat_serializer_exec_inv<Output, A, B, TA, TB>(fmt: &Repeat<A, B>) where
    Output: OutputBuf,
    A: Serializer<Output, TA> + Copy,
    B: Serializer<Output, TB>,
    TA: DeepView,
    TB: DeepView,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_repeat_prepare_exec_inv<A, B, TA, TB>(fmt: &Repeat<A, B>) where
    A: Prepare<TA> + Copy,
    B: Prepare<TB>,
    TA: DeepView,
    TB: DeepView,

    ensures
        (fmt.0.exec_inv() && fmt.1.exec_inv()) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_repeat_till_end_slice_serializer_exec_inv<Output, A, T>(
    fmt: &RepeatTillEnd<A>,
) where Output: OutputBuf, A: Serializer<Output, T> + Copy, T: DeepView
    ensures
        fmt.0.exec_inv() ==> Serializer::<Output, &[T]>::exec_inv(fmt),
{
}

pub proof fn lemma_repeat_till_end_slice_prepare_exec_inv<A, T>(fmt: &RepeatTillEnd<A>) where
    A: Prepare<T> + Copy,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> Prepare::<&[T]>::exec_inv(fmt),
{
}

#[cfg(feature = "alloc")]
pub proof fn lemma_repeat_till_end_vec_serializer_exec_inv<Output, A, T>(
    fmt: &RepeatTillEnd<A>,
) where Output: OutputBuf, A: Serializer<Output, T> + Copy, T: DeepView
    ensures
        fmt.0.exec_inv() ==> Serializer::<Output, Vec<T>>::exec_inv(fmt),
{
}

#[cfg(feature = "alloc")]
pub proof fn lemma_repeat_till_end_vec_prepare_exec_inv<A, T>(fmt: &RepeatTillEnd<A>) where
    A: Prepare<T> + Copy,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> Prepare::<Vec<T>>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// RepeatN
// ----------------------------------------------------
#[cfg(feature = "alloc")]
pub proof fn lemma_repeat_n_parser_exec_inv<I, Inner, N>(fmt: &RepeatN<Inner, N>) where
    I: InputBuf,
    Inner: Parser<I> + SafeParser,
    N: AsLen,

    ensures
        (fmt.1.exec_inv() && fmt.1.safe_inv()) ==> (fmt.exec_inv()),
{
}

pub proof fn lemma_repeat_n_serializer_exec_inv<Output, Inner, N, T>(fmt: &RepeatN<Inner, N>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    N: AsLen,
    T: DeepView,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_repeat_n_prepare_exec_inv<Inner, N, T>(fmt: &RepeatN<Inner, N>) where
    Inner: Prepare<T>,
    N: AsLen,
    T: DeepView,

    ensures
        fmt.1.exec_inv() ==> fmt.exec_inv(),
{
}

// ----------------------------------------------------
// Array
// ----------------------------------------------------
pub proof fn lemma_array_parser_exec_inv<I, Inner, const N: usize>(fmt: &Array<N, Inner>) where
    I: InputBuf,
    Inner: Parser<I> + SafeParser,

    ensures
        (fmt.0.exec_inv() && fmt.0.safe_inv()) ==> fmt.exec_inv(),
{
}

pub proof fn lemma_array_serializer_exec_inv<Output, Inner, T, const N: usize>(
    fmt: &Array<N, Inner>,
) where Output: OutputBuf, Inner: Serializer<Output, T>, T: DeepView
    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

pub proof fn lemma_array_prepare_exec_inv<Inner, T, const N: usize>(fmt: &Array<N, Inner>) where
    Inner: Prepare<T>,
    T: DeepView,

    ensures
        fmt.0.exec_inv() ==> fmt.exec_inv(),
{
}

} // verus!
