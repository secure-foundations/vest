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
use vstd::prelude::*;

verus! {

// ----------------------------------------------------
// ExactLen
// ----------------------------------------------------
pub broadcast proof fn lemma_exact_len_parser_exec_inv<I, Len, Inner>(
    fmt: &ExactLen<Inner, Len>,
) where I: InputBuf, Len: AsLen, Inner: Parser<I> + SafeParser
    ensures
        Inner::exec_inv(&fmt.1) && SafeParser::safe_inv(&fmt.1) ==> #[trigger] Parser::<
            I,
        >::exec_inv(fmt) && SafeParser::safe_inv(fmt),
{
}

pub broadcast proof fn lemma_exact_len_serializer_exec_inv<Output, Inner, Len, T>(
    fmt: &ExactLen<Inner, Len>,
) where
    Output: OutputBuf,
    Len: AsLen,
    Inner: Serializer<Output, T> + SpecByteLen<T = T::V>,
    T: DeepView + ?Sized,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.1) ==> #[trigger] Serializer::<Output, T>::exec_inv(
            fmt,
        ),
{
}

pub broadcast proof fn lemma_exact_len_prepare_exec_inv<Inner, Len, T>(
    fmt: &ExactLen<Inner, Len>,
) where Len: AsLen, Inner: Prepare<T>, T: DeepView + ?Sized
    ensures
        Prepare::<T>::exec_inv(&fmt.1) ==> #[trigger] Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// AndThen
// ----------------------------------------------------
pub broadcast proof fn lemma_and_then_parser_exec_inv<I, TailType, Then>(
    fmt: &AndThen<TailType, Then>,
) where I: InputBuf, TailType: Parser<I, PT = I, PVal = Seq<u8>>, Then: Parser<I>
    ensures
        Parser::<I>::exec_inv(&fmt.0) && Parser::<I>::exec_inv(&fmt.1) ==> #[trigger] Parser::<
            I,
        >::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_and_then_serializer_exec_inv<Output, Then, T>(
    fmt: &AndThen<Tail, Then>,
) where Output: OutputBuf, Then: Serializer<Output, T>, T: DeepView + ?Sized
    ensures
        Serializer::<Output, T>::exec_inv(&fmt.1) ==> #[trigger] Serializer::<Output, T>::exec_inv(
            fmt,
        ),
{
}

pub broadcast proof fn lemma_and_then_prepare_exec_inv<Then, T>(fmt: &AndThen<Tail, Then>) where
    Then: Prepare<T>,
    T: DeepView + ?Sized,

    ensures
        Prepare::<T>::exec_inv(&fmt.1) ==> #[trigger] Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Mapped
// ----------------------------------------------------
pub broadcast proof fn lemma_mapped_parser_exec_inv<I, Inner, M, MRev>(
    fmt: &Mapped<Inner, BiMap<M, MRev>>,
) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,
    M: Map<Inner::PT, Input = Inner::PVal>,
    MRev: SpecMap<Input = M::Output, Output = M::Input>,

    ensures
        Parser::<I>::exec_inv(&fmt.inner) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_mapped_serializer_exec_inv<Output, Inner, M, MRev, T, InnerT>(
    fmt: &Mapped<Inner, BiMap<M, MRev>>,
) where
    Output: OutputBuf,
    Inner: Serializer<Output, InnerT>,
    T: DeepView,
    InnerT: DeepView,
    M: SpecMap<Input = Inner::T, Output = T::V>,
    MRev: for <'x>Map<&'x T, O = InnerT, Input = T::V, Output = Inner::T>,

    ensures
        #[trigger] Serializer::<Output, InnerT>::exec_inv(&fmt.inner) ==> #[trigger]
            Serializer::<Output, T>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_mapped_prepare_exec_inv<Inner, M, MRev, T, InnerT>(
    fmt: &Mapped<Inner, BiMap<M, MRev>>,
) where
    Inner: Prepare<InnerT>,
    T: DeepView,
    InnerT: DeepView,
    M: SpecMap<Input = Inner::T, Output = T::V>,
    MRev: for <'x>Map<&'x T, O = InnerT, Input = T::V, Output = Inner::T>,

    ensures
        #[trigger] Prepare::<InnerT>::exec_inv(&fmt.inner) ==> #[trigger]
            Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Refined
// ----------------------------------------------------
pub broadcast proof fn lemma_refined_parser_exec_inv<I, A, PredFn>(fmt: &Refined<A, PredFn>) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    PredFn: Pred<A::PT>,

    ensures
        Parser::<I>::exec_inv(&fmt.0) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_refined_serializer_exec_inv<Output, A, PredFn, T>(
    fmt: &Refined<A, PredFn>,
) where Output: OutputBuf, A: Serializer<Output, T>, PredFn: SpecPred<T::V>, T: DeepView
    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger] Serializer::<Output, T>::exec_inv(
            fmt,
        ),
{
}

pub broadcast proof fn lemma_refined_prepare_exec_inv<A, PredFn, T>(fmt: &Refined<A, PredFn>) where
    A: Prepare<T>,
    PredFn: Pred<T>,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.0) ==> #[trigger] Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Const
// ----------------------------------------------------
pub broadcast proof fn lemma_const_parser_exec_inv<I, Inner, T>(fmt: &Const<Inner, T>) where
    I: InputBuf,
    Inner: Parser<I, PT = T, PVal = T> + Prepare<T>,
    T: DeepView<V = T> + PartialEq + Structural,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && (forall|v: T| #[trigger] v.deep_view() == v))
            ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_const_serializer_exec_inv<Output, Inner, T>(fmt: &Const<Inner, T>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView<V = T>,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger]
            Serializer::<Output, T>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_const_prepare_exec_inv<Inner, T>(fmt: &Const<Inner, T>) where
    Inner: Prepare<T>,
    T: DeepView<V = T> + PartialEq + Structural,

    ensures
        (Prepare::<T>::exec_inv(&fmt.0) && (forall|v: T| #[trigger] v.deep_view() == v))
            ==> #[trigger] Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Repeat
// ----------------------------------------------------
pub broadcast proof fn lemma_repeat_parser_exec_inv<I, A, B>(fmt: &Repeat<A, B>) where
    I: InputBuf,
    A: Parser<I> + SafeParser + Productive + Copy,
    B: Parser<I> + SafeParser + Copy,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0)
            && Productive::productive_inv(&fmt.0) && Parser::<I>::exec_inv(&fmt.1)
            && SafeParser::safe_inv(&fmt.1)) ==> (#[trigger] Parser::<I>::exec_inv(fmt)
            && SafeParser::safe_inv(fmt)),
{
}

// ----------------------------------------------------
// RepeatTillEnd
// ----------------------------------------------------
pub broadcast proof fn lemma_repeat_till_end_parser_exec_inv<I, A>(fmt: &RepeatTillEnd<A>) where
    I: InputBuf,
    A: Parser<I> + SafeParser + Productive + Copy,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0)
            && Productive::productive_inv(&fmt.0)) ==> (#[trigger] Parser::<I>::exec_inv(fmt)
            && SafeParser::safe_inv(fmt)),
{
}

// ----------------------------------------------------
// Cond
// ----------------------------------------------------
pub broadcast proof fn lemma_cond_parser_exec_inv<I, Inner>(fmt: &Cond<Inner>) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,

    ensures
        Parser::<I>::exec_inv(&fmt.1) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_cond_serializer_exec_inv<Output, Inner, T>(fmt: &Cond<Inner>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.1) ==> #[trigger] Serializer::<Output, T>::exec_inv(
            fmt,
        ),
{
}

pub broadcast proof fn lemma_cond_prepare_exec_inv<Inner, T>(fmt: &Cond<Inner>) where
    Inner: Prepare<T>,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.1) ==> #[trigger] Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Choice
// ----------------------------------------------------
pub broadcast proof fn lemma_choice_parser_exec_inv<I, A, B>(fmt: &Choice<A, B>) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I>,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && Parser::<I>::exec_inv(&fmt.1)) ==> #[trigger] Parser::<
            I,
        >::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_choice_serializer_exec_inv<Output, A, B, TA, TB>(
    fmt: &Choice<A, B>,
) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        (Serializer::<Output, TA>::exec_inv(&fmt.0) && Serializer::<Output, TB>::exec_inv(&fmt.1))
            ==> #[trigger] Serializer::<Output, Sum<TA, TB>>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_choice_prepare_exec_inv<A, B, TA, TB>(fmt: &Choice<A, B>) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        (Prepare::<TA>::exec_inv(&fmt.0) && Prepare::<TB>::exec_inv(&fmt.1))
            ==> #[trigger] Prepare::<Sum<TA, TB>>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Alt
// ----------------------------------------------------
pub broadcast proof fn lemma_alt_parser_exec_inv<const NONDETERMINISTIC: bool, I, A, B>(
    fmt: &Alt<A, B, NONDETERMINISTIC>,
) where I: View<V = Seq<u8>>, A: Parser<I>, B: Parser<I, PVal = A::PVal, PT = A::PT>
    ensures
        (Parser::<I>::exec_inv(&fmt.0) && Parser::<I>::exec_inv(&fmt.1)) ==> #[trigger] Parser::<
            I,
        >::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Sum
// ----------------------------------------------------
pub broadcast proof fn lemma_sum_inl_parser_exec_inv<I, A, B>(a: A) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I>,

    ensures
        Parser::<I>::exec_inv(&a) ==> #[trigger] Parser::<I>::exec_inv(&Sum::<A, B>::Inl(a)),
{
}

pub broadcast proof fn lemma_sum_inr_parser_exec_inv<I, A, B>(b: B) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I>,

    ensures
        Parser::<I>::exec_inv(&b) ==> #[trigger] Parser::<I>::exec_inv(&Sum::<A, B>::Inr(b)),
{
}

pub broadcast proof fn lemma_sum_inl_serializer_exec_inv<Output, A, B, TA, TB>(a: A) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        Serializer::<Output, TA>::exec_inv(&a) ==> #[trigger] Serializer::<
            Output,
            Sum<TA, TB>,
        >::exec_inv(&Sum::<A, B>::Inl(a)),
{
}

pub broadcast proof fn lemma_sum_inr_serializer_exec_inv<Output, A, B, TA, TB>(b: B) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        Serializer::<Output, TB>::exec_inv(&b) ==> #[trigger] Serializer::<
            Output,
            Sum<TA, TB>,
        >::exec_inv(&Sum::<A, B>::Inr(b)),
{
}

pub broadcast proof fn lemma_sum_inl_prepare_exec_inv<A, B, TA, TB>(a: A) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        Prepare::<TA>::exec_inv(&a) ==> #[trigger] Prepare::<Sum<TA, TB>>::exec_inv(
            &Sum::<A, B>::Inl(a),
        ),
{
}

pub broadcast proof fn lemma_sum_inr_prepare_exec_inv<A, B, TA, TB>(b: B) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        Prepare::<TB>::exec_inv(&b) ==> #[trigger] Prepare::<Sum<TA, TB>>::exec_inv(
            &Sum::<A, B>::Inr(b),
        ),
{
}

// ----------------------------------------------------
// Opt
// ----------------------------------------------------
pub broadcast proof fn lemma_opt_parser_exec_inv<I, A>(fmt: &Opt<A>) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,

    ensures
        Parser::<I>::exec_inv(&fmt.0) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_opt_serializer_exec_inv<Output, A, T>(fmt: &Opt<A>) where
    Output: OutputBuf,
    A: Serializer<Output, T>,
    T: DeepView,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger]
            Serializer::<Output, Option<T>>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_opt_prepare_exec_inv<A, T>(fmt: &Opt<A>) where
    A: Prepare<T>,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.0) ==> #[trigger] Prepare::<Option<T>>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Optional
// ----------------------------------------------------
pub broadcast proof fn lemma_optional_parser_exec_inv<I, A, B>(fmt: &Optional<A, B>) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0) && Parser::<I>::exec_inv(
            &fmt.1,
        ) && SafeParser::safe_inv(&fmt.1)) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_optional_serializer_exec_inv<Output, A, B, TA, TB>(
    fmt: &Optional<A, B>,
) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        (Serializer::<Output, TA>::exec_inv(&fmt.0) && Serializer::<Output, TB>::exec_inv(&fmt.1))
            ==> #[trigger] Serializer::<Output, (Option<TA>, TB)>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_optional_prepare_exec_inv<A, B, TA, TB>(fmt: &Optional<A, B>) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        (Prepare::<TA>::exec_inv(&fmt.0) && Prepare::<TB>::exec_inv(&fmt.1))
            ==> #[trigger] Prepare::<(Option<TA>, TB)>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// OptionalEnd
// ----------------------------------------------------
pub broadcast proof fn lemma_optional_end_parser_exec_inv<I, A>(fmt: &OptionalEnd<A>) where
    I: InputBuf,
    A: Parser<I> + SafeParser,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0)) ==> #[trigger] Parser::<
            I,
        >::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_optional_end_serializer_exec_inv<Output, A, T>(
    fmt: &OptionalEnd<A>,
) where Output: OutputBuf, A: Serializer<Output, T>, T: DeepView
    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger] Serializer::<
            Output,
            Option<T>,
        >::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_optional_end_prepare_exec_inv<A, T>(fmt: &OptionalEnd<A>) where
    A: Prepare<T>,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.0) ==> #[trigger] Prepare::<Option<T>>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Preceded
// ----------------------------------------------------
pub broadcast proof fn lemma_preceded_parser_exec_inv<I, A, B, AVal>(
    fmt: &Preceded<A, AVal, B, false>,
) where
    I: InputBuf,
    A: Parser<I, PT = AVal> + SafeParser<PVal = AVal>,
    B: Parser<I> + SafeParser,
    AVal: DeepView<V = AVal>,

    ensures
        (Parser::<I>::exec_inv(&fmt.a) && SafeParser::safe_inv(&fmt.a) && Parser::<I>::exec_inv(
            &fmt.b,
        ) && SafeParser::safe_inv(&fmt.b)) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_preceded_checked_parser_exec_inv<I, A, B, AVal>(
    fmt: &Preceded<A, AVal, B, true>,
) where
    I: InputBuf,
    A: Parser<I, PT = AVal> + SafeParser<PVal = AVal>,
    B: Parser<I> + SafeParser,
    AVal: DeepView<V = AVal> + PartialEq + Structural,

    ensures
        (Parser::<I>::exec_inv(&fmt.a) && SafeParser::safe_inv(&fmt.a)
            && Parser::<I>::exec_inv(&fmt.b) && SafeParser::safe_inv(&fmt.b)
            && (forall|v: AVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_preceded_serializer_exec_inv<
    Output,
    A,
    B,
    AVal,
    T,
    const CHECK: bool,
>(fmt: &Preceded<A, AVal, B, CHECK>) where
    Output: OutputBuf,
    A: Serializer<Output, AVal>,
    B: Serializer<Output, T>,
    AVal: DeepView<V = AVal>,
    T: DeepView,

    ensures
        (Serializer::<Output, AVal>::exec_inv(&fmt.a)
            && Serializer::<Output, T>::exec_inv(&fmt.b)
            && (forall|v: AVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Serializer::<Output, T>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_preceded_prepare_exec_inv<A, B, AVal, T, const CHECK: bool>(
    fmt: &Preceded<A, AVal, B, CHECK>,
) where
    A: Prepare<AVal>,
    B: Prepare<T>,
    AVal: DeepView<V = AVal>,
    T: DeepView,

    ensures
        (Prepare::<AVal>::exec_inv(&fmt.a) && Prepare::<T>::exec_inv(&fmt.b)
            && (forall|v: AVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Terminated
// ----------------------------------------------------
pub broadcast proof fn lemma_terminated_parser_exec_inv<I, A, B, BVal>(
    fmt: &Terminated<A, B, BVal, false>,
) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I, PT = BVal> + SafeParser<PVal = BVal>,
    BVal: DeepView<V = BVal>,

    ensures
        (Parser::<I>::exec_inv(&fmt.a) && SafeParser::safe_inv(&fmt.a) && Parser::<I>::exec_inv(
            &fmt.b,
        ) && SafeParser::safe_inv(&fmt.b)) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_terminated_checked_parser_exec_inv<I, A, B, BVal>(
    fmt: &Terminated<A, B, BVal, true>,
) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I, PT = BVal> + SafeParser<PVal = BVal>,
    BVal: DeepView<V = BVal> + PartialEq + Structural,

    ensures
        (Parser::<I>::exec_inv(&fmt.a) && SafeParser::safe_inv(&fmt.a)
            && Parser::<I>::exec_inv(&fmt.b) && SafeParser::safe_inv(&fmt.b)
            && (forall|v: BVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_terminated_serializer_exec_inv<
    Output,
    A,
    B,
    BVal,
    T,
    const CHECK: bool,
>(fmt: &Terminated<A, B, BVal, CHECK>) where
    Output: OutputBuf,
    A: Serializer<Output, T>,
    B: Serializer<Output, BVal>,
    BVal: DeepView<V = BVal>,
    T: DeepView,

    ensures
        (Serializer::<Output, T>::exec_inv(&fmt.a)
            && Serializer::<Output, BVal>::exec_inv(&fmt.b)
            && (forall|v: BVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Serializer::<Output, T>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_terminated_prepare_exec_inv<A, B, BVal, T, const CHECK: bool>(
    fmt: &Terminated<A, B, BVal, CHECK>,
) where
    A: Prepare<T>,
    B: Prepare<BVal>,
    BVal: DeepView<V = BVal>,
    T: DeepView,

    ensures
        (Prepare::<T>::exec_inv(&fmt.a) && Prepare::<BVal>::exec_inv(&fmt.b)
            && (forall|v: BVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// PrefixTagged / SuffixTagged
// ----------------------------------------------------
pub broadcast proof fn lemma_prefix_tagged_parser_exec_inv<I, Tg, TagVal, Of>(
    fmt: &PrefixTagged<Tg, TagVal, Of>,
) where
    I: InputBuf,
    Tg: SpecByteLen<T = TagVal> + Parser<I, PT = TagVal, PVal = TagVal> + SafeParser,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Parser<I> + SafeParser,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0)
            && Parser::<I>::exec_inv(&fmt.2) && SafeParser::safe_inv(&fmt.2)
            && (forall|v: TagVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_prefix_tagged_serializer_exec_inv<Output, Tg, TagVal, Of, T>(
    fmt: &PrefixTagged<Tg, TagVal, Of>,
) where
    Output: OutputBuf,
    Tg: SpecByteLen<T = TagVal> + Serializer<Output, TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Serializer<Output, T>,
    T: DeepView,

    ensures
        (Serializer::<Output, TagVal>::exec_inv(&fmt.0)
            && Serializer::<Output, T>::exec_inv(&fmt.2)
            && (forall|v: TagVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Serializer::<Output, T>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_prefix_tagged_prepare_exec_inv<Tg, TagVal, Of, T>(
    fmt: &PrefixTagged<Tg, TagVal, Of>,
) where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Prepare<T>,
    T: DeepView,

    ensures
        (Prepare::<TagVal>::exec_inv(&fmt.0) && Prepare::<T>::exec_inv(&fmt.2)
            && (forall|v: TagVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Prepare::<T>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_suffix_tagged_parser_exec_inv<I, Of, Tg, TagVal>(
    fmt: &SuffixTagged<Of, Tg, TagVal>,
) where
    I: InputBuf,
    Tg: SpecByteLen<T = TagVal> + Parser<I, PT = TagVal, PVal = TagVal> + SafeParser,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Parser<I> + SafeParser,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0)
            && Parser::<I>::exec_inv(&fmt.1) && SafeParser::safe_inv(&fmt.1)
            && (forall|v: TagVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_suffix_tagged_serializer_exec_inv<Output, Of, Tg, TagVal, T>(
    fmt: &SuffixTagged<Of, Tg, TagVal>,
) where
    Output: OutputBuf,
    Tg: SpecByteLen<T = TagVal> + Serializer<Output, TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Serializer<Output, T>,
    T: DeepView,

    ensures
        (Serializer::<Output, T>::exec_inv(&fmt.0)
            && Serializer::<Output, TagVal>::exec_inv(&fmt.1)
            && (forall|v: TagVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Serializer::<Output, T>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_suffix_tagged_prepare_exec_inv<Of, Tg, TagVal, T>(
    fmt: &SuffixTagged<Of, Tg, TagVal>,
) where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    Of: Prepare<T>,
    T: DeepView,

    ensures
        (Prepare::<T>::exec_inv(&fmt.0) && Prepare::<TagVal>::exec_inv(&fmt.1)
            && (forall|v: TagVal| #[trigger] v.deep_view() == v)) ==> #[trigger]
            Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Pair
// ----------------------------------------------------
pub broadcast proof fn lemma_pair_parser_exec_inv<I, A, B>(fmt: &Pair<A, B>) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0) && Parser::<I>::exec_inv(
            &fmt.1,
        ) && SafeParser::safe_inv(&fmt.1)) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_pair_serializer_exec_inv<Output, A, B, TA, TB>(fmt: &Pair<A, B>) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,

    ensures
        (Serializer::<Output, TA>::exec_inv(&fmt.0) && Serializer::<Output, TB>::exec_inv(&fmt.1))
            ==> #[trigger] Serializer::<Output, (TA, TB)>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_pair_prepare_exec_inv<A, B, TA, TB>(fmt: &Pair<A, B>) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,

    ensures
        (Prepare::<TA>::exec_inv(&fmt.0) && Prepare::<TB>::exec_inv(&fmt.1))
            ==> #[trigger] Prepare::<(TA, TB)>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Bind
// ----------------------------------------------------
pub broadcast proof fn lemma_bind_parser_exec_inv<I, A, B>(fmt: &Bind<A, B>) where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: MapRef<A::PT, Input = A::PVal>,
    B::O: Parser<I> + SafeParser,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0) &&
         (forall|pb: B::O| #[trigger] pb.exec_inv() && pb.safe_inv())) ==>
        (#[trigger] Parser::<I>::exec_inv(fmt) && SafeParser::safe_inv(fmt)),
{
    if Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0) &&
       (forall|pb: B::O| #[trigger] pb.exec_inv() && pb.safe_inv()) {
        assert(Parser::<I>::exec_inv(fmt));
        assert forall|key: A::PVal| #[trigger] fmt.1.spec_map(key).safe_inv() by {
            let pb = fmt.1.spec_map(key);
            assert(pb.exec_inv() && pb.safe_inv());
        };
        assert(SafeParser::safe_inv(fmt));
    }
}

pub broadcast proof fn lemma_bind_serializer_exec_inv<Output, A, B, TA, TB>(fmt: &Bind<A, B>) where
    Output: OutputBuf,
    TA: DeepView,
    TB: DeepView,
    A: Serializer<Output, TA>,
    B::O: Serializer<Output, TB>,
    B: MapRef<TA, Input = TA::V>,

    ensures
        (Serializer::<Output, TA>::exec_inv(&fmt.0) && (forall|pb: B::O| #[trigger]
            Serializer::<Output, TB>::exec_inv(&pb))) ==> #[trigger] Serializer::<
            Output,
            (TA, TB),
        >::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_bind_prepare_exec_inv<A, B, TA, TB>(fmt: &Bind<A, B>) where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B::O: Prepare<TB>,
    B: MapRef<TA, Input = TA::V>,

    ensures
        (Prepare::<TA>::exec_inv(&fmt.0) && (forall|pb: B::O| #[trigger]
            Prepare::<TB>::exec_inv(&pb))) ==> #[trigger] Prepare::<(TA, TB)>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Rust shared references
// ----------------------------------------------------
pub broadcast proof fn lemma_ref_parser_exec_inv<I, P>(parser: &P) where
    I: View<V = Seq<u8>>,
    P: Parser<I>,

    ensures
        <P as Parser<I>>::exec_inv(parser) ==> #[trigger]
            <&P as Parser<I>>::exec_inv(&parser),
{
}

pub broadcast proof fn lemma_ref_serializer_exec_inv<Output, S, T>(serializer: &S) where
    Output: OutputBuf,
    S: Serializer<Output, T>,
    T: DeepView + ?Sized,

    ensures
        <S as Serializer<Output, T>>::exec_inv(serializer) ==> #[trigger]
            <&S as Serializer<Output, T>>::exec_inv(&serializer),
{
}

pub broadcast proof fn lemma_ref_prepare_exec_inv<S, T>(serializer: &S) where
    S: Prepare<T>,
    T: DeepView + ?Sized,

    ensures
        <S as Prepare<T>>::exec_inv(serializer) ==> #[trigger]
            <&S as Prepare<T>>::exec_inv(&serializer),
{
}

// ----------------------------------------------------
// Ref
// ----------------------------------------------------
pub broadcast proof fn lemma_reference_parser_exec_inv<I, Inner>(fmt: &Ref<Inner>) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,

    ensures
        Parser::<I>::exec_inv(&fmt.0) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_reference_serializer_exec_inv<Output, Inner, T>(
    fmt: &Ref<Inner>,
) where Output: OutputBuf, Inner: Serializer<Output, T>, T: DeepView + ?Sized
    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger] Serializer::<Output, &T>::exec_inv(
            fmt,
        ),
{
}

pub broadcast proof fn lemma_reference_prepare_exec_inv<Inner, T>(fmt: &Ref<Inner>) where
    Inner: Prepare<T>,
    T: DeepView + ?Sized,

    ensures
        Prepare::<T>::exec_inv(&fmt.0) ==> #[trigger] Prepare::<&T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Named
// ----------------------------------------------------
pub broadcast proof fn lemma_named_parser_exec_inv<I, Inner>(fmt: &Named<Inner>) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,

    ensures
        Parser::<I>::exec_inv(&fmt.1) ==> #[trigger] Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_named_serializer_exec_inv<Output, Inner, T>(fmt: &Named<Inner>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.1) ==> #[trigger] Serializer::<Output, T>::exec_inv(
            fmt,
        ),
{
}

pub broadcast proof fn lemma_named_prepare_exec_inv<Inner, T>(fmt: &Named<Inner>) where
    Inner: Prepare<T>,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.1) ==> #[trigger] Prepare::<T>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Star
// ----------------------------------------------------
pub broadcast proof fn lemma_star_parser_exec_inv<I, Inner>(fmt: &Star<Inner>) where
    I: InputBuf,
    Inner: Parser<I> + SafeParser + Productive + Copy,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0)
            && Productive::productive_inv(&fmt.0)) ==> (#[trigger] Parser::<I>::exec_inv(fmt)
            && SafeParser::safe_inv(fmt)),
{
}

pub broadcast proof fn lemma_star_serializer_exec_inv<Output, Inner, T>(fmt: &Star<Inner>) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger]
            Serializer::<Output, [T]>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_star_prepare_exec_inv<Inner, T>(fmt: &Star<Inner>) where
    Inner: Prepare<T>,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.0) ==> #[trigger] Prepare::<[T]>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_repeat_serializer_exec_inv<Output, A, B, TA, TB>(
    fmt: &Repeat<A, B>,
) where
    Output: OutputBuf,
    A: Serializer<Output, TA> + Copy,
    B: Serializer<Output, TB>,
    TA: DeepView,
    TB: DeepView,

    ensures
        (Serializer::<Output, TA>::exec_inv(&fmt.0)
            && Serializer::<Output, TB>::exec_inv(&fmt.1)) ==> #[trigger]
            Serializer::<Output, (&[TA], TB)>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_repeat_prepare_exec_inv<A, B, TA, TB>(fmt: &Repeat<A, B>) where
    A: Prepare<TA> + Copy,
    B: Prepare<TB>,
    TA: DeepView,
    TB: DeepView,

    ensures
        (Prepare::<TA>::exec_inv(&fmt.0) && Prepare::<TB>::exec_inv(&fmt.1)) ==> #[trigger]
            Prepare::<(&[TA], TB)>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_repeat_till_end_slice_serializer_exec_inv<Output, A, T>(
    fmt: &RepeatTillEnd<A>,
) where
    Output: OutputBuf,
    A: Serializer<Output, T> + Copy,
    T: DeepView,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger]
            Serializer::<Output, &[T]>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_repeat_till_end_slice_prepare_exec_inv<A, T>(
    fmt: &RepeatTillEnd<A>,
) where
    A: Prepare<T> + Copy,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.0) ==> #[trigger] Prepare::<&[T]>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_repeat_till_end_vec_serializer_exec_inv<Output, A, T>(
    fmt: &RepeatTillEnd<A>,
) where
    Output: OutputBuf,
    A: Serializer<Output, T> + Copy,
    T: DeepView,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger]
            Serializer::<Output, Vec<T>>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_repeat_till_end_vec_prepare_exec_inv<A, T>(
    fmt: &RepeatTillEnd<A>,
) where
    A: Prepare<T> + Copy,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.0) ==> #[trigger] Prepare::<Vec<T>>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// RepeatN
// ----------------------------------------------------
pub broadcast proof fn lemma_repeat_n_parser_exec_inv<I, Inner, N>(fmt: &RepeatN<Inner, N>) where
    I: InputBuf,
    Inner: Parser<I> + SafeParser,
    N: AsLen,

    ensures
        (Parser::<I>::exec_inv(&fmt.1) && SafeParser::safe_inv(&fmt.1)) ==> (#[trigger] Parser::<
            I,
        >::exec_inv(fmt)),
{
}

pub broadcast proof fn lemma_repeat_n_serializer_exec_inv<Output, Inner, N, T>(
    fmt: &RepeatN<Inner, N>,
) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    N: AsLen,
    T: DeepView,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.1) ==> #[trigger]
            Serializer::<Output, [T]>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_repeat_n_prepare_exec_inv<Inner, N, T>(
    fmt: &RepeatN<Inner, N>,
) where
    Inner: Prepare<T>,
    N: AsLen,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.1) ==> #[trigger] Prepare::<[T]>::exec_inv(fmt),
{
}

// ----------------------------------------------------
// Array
// ----------------------------------------------------
pub broadcast proof fn lemma_array_parser_exec_inv<I, Inner, const N: usize>(
    fmt: &Array<N, Inner>,
) where
    I: InputBuf,
    Inner: Parser<I> + SafeParser,

    ensures
        (Parser::<I>::exec_inv(&fmt.0) && SafeParser::safe_inv(&fmt.0)) ==> #[trigger]
            Parser::<I>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_array_serializer_exec_inv<Output, Inner, T, const N: usize>(
    fmt: &Array<N, Inner>,
) where
    Output: OutputBuf,
    Inner: Serializer<Output, T>,
    T: DeepView,

    ensures
        Serializer::<Output, T>::exec_inv(&fmt.0) ==> #[trigger]
            Serializer::<Output, [T; N]>::exec_inv(fmt),
{
}

pub broadcast proof fn lemma_array_prepare_exec_inv<Inner, T, const N: usize>(
    fmt: &Array<N, Inner>,
) where
    Inner: Prepare<T>,
    T: DeepView,

    ensures
        Prepare::<T>::exec_inv(&fmt.0) ==> #[trigger] Prepare::<[T; N]>::exec_inv(fmt),
{
}

// ====================================================
// Broadcast Groups
// ====================================================
pub broadcast group parser_exec_inv_lemmas {
    lemma_exact_len_parser_exec_inv,
    lemma_and_then_parser_exec_inv,
    lemma_mapped_parser_exec_inv,
    lemma_refined_parser_exec_inv,
    lemma_const_parser_exec_inv,
    lemma_repeat_parser_exec_inv,
    lemma_repeat_till_end_parser_exec_inv,
    lemma_cond_parser_exec_inv,
    lemma_choice_parser_exec_inv,
    lemma_alt_parser_exec_inv,
    lemma_sum_inl_parser_exec_inv,
    lemma_sum_inr_parser_exec_inv,
    lemma_optional_parser_exec_inv,
    lemma_optional_end_parser_exec_inv,
    lemma_preceded_parser_exec_inv,
    lemma_preceded_checked_parser_exec_inv,
    lemma_terminated_parser_exec_inv,
    lemma_terminated_checked_parser_exec_inv,
    lemma_prefix_tagged_parser_exec_inv,
    lemma_suffix_tagged_parser_exec_inv,
    lemma_pair_parser_exec_inv,
    lemma_bind_parser_exec_inv,
    lemma_ref_parser_exec_inv,
    lemma_reference_parser_exec_inv,
    lemma_named_parser_exec_inv,
    lemma_star_parser_exec_inv,
    lemma_repeat_n_parser_exec_inv,
    lemma_opt_parser_exec_inv,
    lemma_array_parser_exec_inv,
}

pub broadcast group serializer_exec_inv_lemmas {
    lemma_exact_len_serializer_exec_inv,
    lemma_and_then_serializer_exec_inv,
    lemma_mapped_serializer_exec_inv,
    lemma_refined_serializer_exec_inv,
    lemma_const_serializer_exec_inv,
    lemma_cond_serializer_exec_inv,
    lemma_choice_serializer_exec_inv,
    lemma_sum_inl_serializer_exec_inv,
    lemma_sum_inr_serializer_exec_inv,
    lemma_opt_serializer_exec_inv,
    lemma_optional_serializer_exec_inv,
    lemma_optional_end_serializer_exec_inv,
    lemma_preceded_serializer_exec_inv,
    lemma_terminated_serializer_exec_inv,
    lemma_prefix_tagged_serializer_exec_inv,
    lemma_suffix_tagged_serializer_exec_inv,
    lemma_pair_serializer_exec_inv,
    lemma_bind_serializer_exec_inv,
    lemma_ref_serializer_exec_inv,
    lemma_reference_serializer_exec_inv,
    lemma_named_serializer_exec_inv,
    lemma_star_serializer_exec_inv,
    lemma_repeat_serializer_exec_inv,
    lemma_repeat_till_end_slice_serializer_exec_inv,
    lemma_repeat_till_end_vec_serializer_exec_inv,
    lemma_repeat_n_serializer_exec_inv,
    lemma_array_serializer_exec_inv,
}

pub broadcast group prepare_exec_inv_lemmas {
    lemma_exact_len_prepare_exec_inv,
    lemma_and_then_prepare_exec_inv,
    lemma_mapped_prepare_exec_inv,
    lemma_refined_prepare_exec_inv,
    lemma_const_prepare_exec_inv,
    lemma_cond_prepare_exec_inv,
    lemma_choice_prepare_exec_inv,
    lemma_sum_inl_prepare_exec_inv,
    lemma_sum_inr_prepare_exec_inv,
    lemma_opt_prepare_exec_inv,
    lemma_optional_prepare_exec_inv,
    lemma_optional_end_prepare_exec_inv,
    lemma_preceded_prepare_exec_inv,
    lemma_terminated_prepare_exec_inv,
    lemma_prefix_tagged_prepare_exec_inv,
    lemma_suffix_tagged_prepare_exec_inv,
    lemma_pair_prepare_exec_inv,
    lemma_bind_prepare_exec_inv,
    lemma_ref_prepare_exec_inv,
    lemma_reference_prepare_exec_inv,
    lemma_named_prepare_exec_inv,
    lemma_star_prepare_exec_inv,
    lemma_repeat_prepare_exec_inv,
    lemma_repeat_till_end_slice_prepare_exec_inv,
    lemma_repeat_till_end_vec_prepare_exec_inv,
    lemma_repeat_n_prepare_exec_inv,
    lemma_array_prepare_exec_inv,
}

} // verus!
