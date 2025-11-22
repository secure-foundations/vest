use super::disjoint::DisjointFrom;
use crate::properties::*;
use vstd::prelude::*;

verus! {

#[allow(missing_docs)]
#[derive(Debug)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A: View, B: View> View for Either<A, B> {
    type V = Either<A::V, B::V>;

    open spec fn view(&self) -> Either<A::V, B::V> {
        match self {
            Either::Left(v) => Either::Left(v@),
            Either::Right(v) => Either::Right(v@),
        }
    }
}

/// Combinator that tries the `Fst` combinator and if it fails, tries the `Snd` combinator.
pub struct Choice<Fst, Snd>(pub Fst, pub Snd);

impl<Fst, Snd> Choice<Fst, Snd> where
    Fst: View,
    Snd: View,
    Fst::V: SpecCombinator,
    Snd::V: SpecCombinator,
    Snd::V: DisjointFrom<Fst::V>,
 {
    pub fn new(fst: Fst, snd: Snd) -> (o: Self)
        requires
            snd@.disjoint_from(&fst@),
        ensures
            o == Choice(fst, snd),
    {
        Choice(fst, snd)
    }
}

impl<Fst: View, Snd: View> View for Choice<Fst, Snd> where  {
    type V = Choice<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        Choice(self.0@, self.1@)
    }
}

impl<Fst, Snd> SpecCombinator for Choice<Fst, Snd> where
    Fst: SpecCombinator,
    Snd: SpecCombinator + DisjointFrom<Fst>,
 {
    type Type = Either<Fst::Type, Snd::Type>;

    open spec fn requires(&self) -> bool {
        self.0.requires() && self.1.requires() && self.1.disjoint_from(&self.0)
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            Either::Left(v) => self.0.wf(v),
            Either::Right(v) => self.1.wf(v),
        }
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if let Some((n, v)) = self.0.spec_parse(s) {
            Some((n, Either::Left(v)))
        } else {
            if let Some((n, v)) = self.1.spec_parse(s) {
                Some((n, Either::Right(v)))
            } else {
                None
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        match v {
            Either::Left(v) => self.0.spec_serialize(v),
            Either::Right(v) => self.1.spec_serialize(v),
        }
    }
}

impl<Fst, Snd> SecureSpecCombinator for Choice<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator + DisjointFrom<Fst>,
 {
    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        self.0.is_productive() && self.1.is_productive()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.1.disjoint_from(&self.0) {
            // must also explicitly state that parser1 will fail on anything that parser2 will succeed on
            self.1.parse_disjoint_on(&self.0, s1.add(s2));
            if Self::is_prefix_secure() {
                self.0.lemma_prefix_secure(s1, s2);
                self.1.lemma_prefix_secure(s1, s2);
            }
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        match v {
            Either::Left(v) => {
                self.0.theorem_serialize_parse_roundtrip(v);
            },
            Either::Right(v) => {
                self.1.theorem_serialize_parse_roundtrip(v);
                let buf = self.1.spec_serialize(v);
                if self.1.disjoint_from(&self.0) {
                    self.1.parse_disjoint_on(&self.0, buf);
                }
            },
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((n, v)) = self.0.spec_parse(buf) {
            self.0.theorem_parse_serialize_roundtrip(buf);
        } else {
            if let Some((n, v)) = self.1.spec_parse(buf) {
                self.1.theorem_parse_serialize_roundtrip(buf);
            }
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Some((n, v)) = self.0.spec_parse(s) {
            self.0.lemma_parse_length(s);
        } else {
            if let Some((n, v)) = self.1.spec_parse(s) {
                self.1.lemma_parse_length(s);
            }
        }
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        if let Some((n, v)) = self.0.spec_parse(s) {
            self.0.lemma_parse_productive(s);
        } else {
            if let Some((n, v)) = self.1.spec_parse(s) {
                self.1.lemma_parse_productive(s);
            }
        }
    }
}

impl<'x, I, O, Fst, Snd> Combinator<'x, I, O> for Choice<Fst, Snd> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<'x, I, O>,
    Snd: Combinator<'x, I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
    Snd::V: DisjointFrom<Fst::V>,
 {
    type Type = Either<Fst::Type, Snd::Type>;

    type SType = Either<Fst::SType, Snd::SType>;

    fn length(&self, v: Self::SType) -> usize {
        match v {
            Either::Left(v) => self.0.length(v),
            Either::Right(v) => self.1.length(v),
        }
    }

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires() && self.1.ex_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        if let Ok((n, v)) = self.0.parse(s.clone()) {
            Ok((n, Either::Left(v)))
        } else {
            if let Ok((n, v)) = self.1.parse(s) {
                Ok((n, Either::Right(v)))
            } else {
                Err(ParseError::OrdChoiceNoMatch)
            }
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        match v {
            Either::Left(v) => {
                let n = self.0.serialize(v, data, pos)?;
                Ok(n)
            },
            Either::Right(v) => {
                let n = self.1.serialize(v, data, pos)?;
                Ok(n)
            },
        }
    }
}

/// The optional combinator that never fails.
/// If the inner combinator fails, the result is `None`.
///
/// ## Note
///
/// One might think that the `Opt<T>` combinator can be encoded as `OrdChoice<T, Success>`.
/// However, this is not the case because one cannot prove that `Success` is disjoint from `T`.
/// In fact, there is a fundamental difference between `Opt<T>` and `OrdChoice<Fst, Snd>`:
/// the `Disjoint` conditions can be aggregated for `OrdChoice`, making it "nestable", while
/// the "productivity" condition cannot be aggregated for `Opt` (i.e., `Opt<Opt<T>>` can never be
/// constructed).
pub struct Opt<T>(pub T);

impl<T: View> View for Opt<T> where  {
    type V = Opt<T::V>;

    open spec fn view(&self) -> Self::V {
        Opt(self.0@)
    }
}

impl<C: View> Opt<C> where C::V: SecureSpecCombinator {
    /// Constructs a new `Opt` combinator, only if the inner combinator is productive.
    pub fn new(c: C) -> (o: Self)
        requires
            c@.is_productive(),
        ensures
            o == Opt(c),
    {
        Opt(c)
    }
}

/// Wrapper for the `core::option::Option` type.
/// Needed because currently Verus does not implement the `View` trait for `Option`.
#[derive(Debug, PartialEq, Eq)]
pub struct Optional<T>(pub Option<T>);

impl<T: Clone> Clone for Optional<T> {
    fn clone(&self) -> Self {
        Optional(self.0.clone())
    }
}

impl<T: View> View for Optional<T> where  {
    type V = Option<T::V>;

    open spec fn view(&self) -> Self::V {
        match &self.0 {
            Some(v) => Some(v@),
            None => None,
        }
    }
}

impl<T: SecureSpecCombinator> SpecCombinator for Opt<T> where  {
    type Type = Option<T::Type>;

    open spec fn requires(&self) -> bool {
        self.0.requires() && self.0.is_productive()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            Some(vv) => self.0.wf(vv),
            None => true,
        }
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if let Some((n, v)) = self.0.spec_parse(s) {
            Some((n, Some(v)))
        } else {
            Some((0, None))
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        match v {
            Some(v) => self.0.spec_serialize(v),
            None => Seq::empty(),
        }
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for Opt<T> where  {
    open spec fn is_prefix_secure() -> bool {
        false
    }

    open spec fn is_productive(&self) -> bool {
        false
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if self.wf(v) {
            match v {
                Some(vv) => {
                    assert(self.0.wf(vv));
                    self.0.lemma_serialize_productive(vv);
                    self.0.theorem_serialize_parse_roundtrip(vv);
                },
                None => {
                    // the following two lines establish a contradiction (n > 0 and n <= 0)
                    self.0.lemma_parse_productive(Seq::empty());
                    self.0.lemma_parse_length(Seq::empty());
                },
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((n, v)) = self.0.spec_parse(buf) {
            self.0.lemma_parse_productive(buf);
            if n != 0 {
                self.0.theorem_parse_serialize_roundtrip(buf);
            }
        } else {
            assert(Seq::<u8>::empty() == buf.take(0));
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Some((n, v)) = self.0.spec_parse(s) {
            self.0.lemma_parse_length(s);
        }
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<'x, I, O, T> Combinator<'x, I, O> for Opt<T> where
    I: VestInput,
    O: VestOutput<I>,
    T: Combinator<'x, I, O, SType = &'x <T as Combinator<'x, I, O>>::Type>,
    T::V: SecureSpecCombinator<Type = <T::Type as View>::V>,
    T::Type: 'x,
 {
    type Type = Optional<T::Type>;

    type SType = &'x Self::Type;

    fn length(&self, v: Self::SType) -> usize {
        assert(self@.wf(v@)); // TODO: why is this needed?
        match &v.0 {
            Some(v) => self.0.length(v),
            None => 0,
        }
    }

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        if let Ok((n, v)) = self.0.parse(s) {
            Ok((n, Optional(Some(v))))
        } else {
            Ok((0, Optional(None)))
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        match &v.0 {
            Some(v) => self.0.serialize(v, data, pos),
            None => {
                if pos <= data.len() {
                    assert(seq_splice(old(data)@, pos, Seq::<u8>::empty()) == data@);
                    Ok(0)
                } else {
                    Err(SerializeError::InsufficientBuffer)
                }
            },
        }
    }
}

pub struct OptThen<Fst, Snd>(pub (Opt<Fst>, Snd));

impl<Fst: View, Snd: View> View for OptThen<Fst, Snd> {
    type V = OptThen<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        OptThen((self.0.0@, self.0.1@))
    }
}

impl<Fst, Snd> OptThen<Fst, Snd> where
 {
    pub open spec fn spec_new(fst: Fst, snd: Snd) -> Self {
        OptThen((Opt(fst), snd))
    }

    pub fn new(fst: Fst, snd: Snd) -> (o: Self)
        ensures
            o == OptThen((Opt(fst), snd)),
    {
        OptThen((Opt(fst), snd))
    }
}

impl<C, Fst, Snd> DisjointFrom<C> for OptThen<Fst, Snd> where
    C: SpecCombinator,
    Fst: SecureSpecCombinator + DisjointFrom<C>,
    Snd: SpecCombinator + DisjointFrom<Fst> + DisjointFrom<C>,
 {
    open spec fn disjoint_from(&self, other: &C) -> bool {
        &&& self.0.0.0.disjoint_from(other) 
        &&& self.0.1.disjoint_from(other)
    }

    proof fn parse_disjoint_on(&self, other: &C, buf: Seq<u8>) {
        match self.spec_parse(buf) {
            Some((_, (Some(_), _))) => {
                self.0.0.0.parse_disjoint_on(other, buf);
                self.0.1.parse_disjoint_on(other, buf);
            },
            Some((_, (None, _))) => {
                assert(buf.skip(0) == buf);
                self.0.1.parse_disjoint_on(other, buf);
            },
            _ => {}
        }
    }
}


impl<Fst, Snd> SpecCombinator for OptThen<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SpecCombinator + DisjointFrom<Fst>,
 {
    type Type = (<Opt<Fst> as SpecCombinator>::Type, Snd::Type);

    open spec fn requires(&self) -> bool {
        // instead of just requiring `Fst` to be
        // prefix-secure, we require `Snd`
        // to be disjoint from `Fst`
        // Note that `Opt<T>` is always not prefix-secure
        Fst::is_prefix_secure()
        && self.0.0.requires() && self.0.1.requires() 
        && self.0.1.disjoint_from(&self.0.0.0)
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.0.spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.0.spec_serialize(v)
    }
}

impl<Fst, Snd> SecureSpecCombinator for OptThen<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator + DisjointFrom<Fst>,
 {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        let buf = self.spec_serialize(v);
        let buf0 = self.0.0.spec_serialize(v.0);
        let buf1 = self.0.1.spec_serialize(v.1);
        self.0.0.theorem_serialize_parse_roundtrip(v.0);
        self.0.1.theorem_serialize_parse_roundtrip(v.1);
        assert((buf0 + buf1).skip(buf0.len() as int) == buf1);
        self.0.0.0.lemma_prefix_secure(buf0, buf1);
        self.0.1.parse_disjoint_on(&self.0.0.0, buf1); // <-- this is the key
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((nm, (v0, v1))) = self.spec_parse(buf) {
            let (n, v0_) = self.0.0.spec_parse(buf).unwrap();
            self.0.0.lemma_parse_length(buf);
            let buf0 = buf.take(n);
            let buf1 = buf.skip(n);
            assert(buf == buf0 + buf1);
            self.0.0.theorem_parse_serialize_roundtrip(buf);
            let (m, v1_) = self.0.1.spec_parse(buf1).unwrap();
            self.0.1.theorem_parse_serialize_roundtrip(buf1);
            self.0.1.lemma_parse_length(buf1);
            let buf2 = self.spec_serialize((v0, v1));
            assert(buf2 == buf.take(nm));
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if Fst::is_prefix_secure() && Snd::is_prefix_secure() {
            self.0.0.0.lemma_prefix_secure(s1, s2);
            self.0.0.lemma_parse_length(s1);
            if let Some((n1, v1)) = self.0.0.spec_parse(s1) {
                match v1 {
                    Some(v1) => {
                        assert(s1.skip(n1) + s2 == (s1 + s2).skip(n1));
                        self.0.1.lemma_prefix_secure(s1.skip(n1), s2);
                    },
                    None => {
                        assert(s1.skip(n1) == s1);
                        assert(self.0.0.0.spec_parse(s1) is None);
                        self.0.1.lemma_prefix_secure(s1, s2);
                        if let Some((n2, v2)) = self.0.1.spec_parse(s1) {
                            self.0.1.parse_disjoint_on(&self.0.0.0, s1 + s2);
                            assert(self.0.0.0.spec_parse(s1 + s2) is None);
                        }
                    },
                }
            }
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Some((n, _)) = self.0.0.spec_parse(s) {
            if let Some(_) = self.0.1.spec_parse(s.skip(n)) {
                self.0.0.lemma_parse_length(s);
                self.0.1.lemma_parse_length(s.skip(n));
            }
        }
    }

    open spec fn is_productive(&self) -> bool {
        self.0.1.is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        if let Some((n, _)) = self.0.0.spec_parse(s) {
            if let Some(_) = self.0.1.spec_parse(s.skip(n)) {
                self.0.0.0.lemma_parse_length(s);
                self.0.1.lemma_parse_productive(s.skip(n));
                self.0.1.lemma_parse_length(s.skip(n));
            }
        }
    }
}

impl<'x, I, O, Fst, Snd> Combinator<'x, I, O> for OptThen<Fst, Snd> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<'x, I, O, SType = &'x <Fst as Combinator<'x, I, O>>::Type>,
    Snd: Combinator<'x, I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
    Snd::V: DisjointFrom<Fst::V>,
    Fst::Type: 'x,
 {
    type Type = (<Opt<Fst> as Combinator<'x, I, O>>::Type, Snd::Type);

    type SType = (<Opt<Fst> as Combinator<'x, I, O>>::SType, Snd::SType);

    fn length(&self, v: Self::SType) -> usize {
        self.0.0.length(&v.0) + self.0.1.length(v.1)
    }

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (n, v1) = self.0.0.parse(s.clone())?;
        proof {
            self@.0.0.lemma_parse_length(s@);
        }
        let s_ = s.subrange(n, s.len());
        let (m, v2) = self.0.1.parse(s_)?;
        proof {
            self.0.1@.lemma_parse_length(s@.skip(n as int));
        }
        Ok((n + m, (v1, v2)))
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let n = self.0.0.serialize(&v.0, data, pos)?;
        let m = self.0.1.serialize(v.1, data, pos + n)?;
        Ok(n + m)
    }
}

/// This macro constructs a nested OrdChoice combinator
/// in the form of OrdChoice(..., OrdChoice(..., OrdChoice(..., ...)))
#[allow(unused_macros)]
#[macro_export]
macro_rules! ord_choice {
    ($c:expr $(,)?) => {
        $c
    };

    ($c:expr, $($rest:expr),* $(,)?) => {
        Choice($c, ord_choice!($($rest),*))
    };
}

pub use ord_choice;

/// Build a type for the `ord_choice!` macro
#[allow(unused_macros)]
#[macro_export]
macro_rules! ord_choice_type {
    ($c:ty $(,)?) => {
        $c
    };

    ($c:ty, $($rest:ty),* $(,)?) => {
        OrdChoice<$c, ord_choice_type!($($rest),*)>
    };
}

pub use ord_choice_type;

/// Build a type for the result of `ord_choice!`
#[allow(unused_macros)]
#[macro_export]
macro_rules! ord_choice_result {
    ($c:ty $(,)?) => {
        $c
    };

    ($c:ty, $($rest:ty),* $(,)?) => {
        Either<$c, ord_choice_result!($($rest),*)>
    };
}

pub use ord_choice_result;

/// Maps x:Ti to ord_choice_result!(T1, ..., Tn)
#[allow(unused_macros)]
#[macro_export]
macro_rules! inj_ord_choice_result {
    (*, $($rest:tt),* $(,)?) => {
        Either::Right(inj_ord_choice_result!($($rest),*))
    };

    ($x:expr $(,)?) => {
        $x
    };

    ($x:expr, $(*),* $(,)?) => {
        Either::Left($x)
    };
}

pub use inj_ord_choice_result;

/// Same as above but for patterns
#[allow(unused_macros)]
#[macro_export]
macro_rules! inj_ord_choice_pat {
    (*, $($rest:tt),* $(,)?) => {
        Either::Right(inj_ord_choice_pat!($($rest),*))
    };

    ($x:pat $(,)?) => {
        $x
    };

    ($x:pat, $(*),* $(,)?) => {
        Either::Left($x)
    };
}

pub use inj_ord_choice_pat;

// what would it look like if we manually implemented the match combinator?
//
// use super::uints::*;
// use super::tail::*;
//
// pub struct MatchU8With123 {
//     pub val: u8,
//     pub arm1: U8,
//     pub arm2: U16,
//     pub arm3: U32,
//     pub default: Tail,
// }
//
// impl View for MatchU8With123 {
//     type V = Self;
//
//     open spec fn view(&self) -> Self::V {
//         MatchU8With123 {
//             val: self.val,
//             arm1: self.arm1@,
//             arm2: self.arm2@,
//             arm3: self.arm3@,
//             default: self.default@,
//         }
//     }
// }
//
// pub enum SpecMsgMatchU8With123 {
//     Arm1(u8),
//     Arm2(u16),
//     Arm3(u32),
//     Default(Seq<u8>),
// }
//
// pub enum MsgMatchU8With123<'a> {
//     Arm1(u8),
//     Arm2(u16),
//     Arm3(u32),
//     Default(&'a [u8]),
// }
//
// pub enum MsgMatchU8With123 {
//     Arm1(u8),
//     Arm2(u16),
//     Arm3(u32),
//     Default(Vec<u8>),
// }
//
// impl View for MsgMatchU8With123<'_> {
//     type V = SpecMsgMatchU8With123;
//
//     open spec fn view(&self) -> Self::V {
//         match self {
//             MsgMatchU8With123::Arm1(v) => SpecMsgMatchU8With123::Arm1(v@),
//             MsgMatchU8With123::Arm2(v) => SpecMsgMatchU8With123::Arm2(v@),
//             MsgMatchU8With123::Arm3(v) => SpecMsgMatchU8With123::Arm3(v@),
//             MsgMatchU8With123::Default(v) => SpecMsgMatchU8With123::Default(v@),
//         }
//     }
// }
//
// impl View for MsgMatchU8With123 {
//     type V = SpecMsgMatchU8With123;
//
//     open spec fn view(&self) -> Self::V {
//         match self {
//             MsgMatchU8With123::Arm1(v) => SpecMsgMatchU8With123::Arm1(v@),
//             MsgMatchU8With123::Arm2(v) => SpecMsgMatchU8With123::Arm2(v@),
//             MsgMatchU8With123::Arm3(v) => SpecMsgMatchU8With123::Arm3(v@),
//             MsgMatchU8With123::Default(v) => SpecMsgMatchU8With123::Default(v@),
//         }
//     }
// }
//
// impl SpecCombinator for MatchU8With123 {
//     type SpecResult = SpecMsgMatchU8With123;
//
//     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
//         match self.val {
//             1u8 => {
//                 if let Ok((n, v)) = self.arm1.spec_parse(s) {
//                     Ok((n, SpecMsgMatchU8With123::Arm1(v)))
//                 } else {
//                     Err(())
//                 }
//             },
//             2u8 => {
//                 if let Ok((n, v)) = self.arm2.spec_parse(s) {
//                     Ok((n, SpecMsgMatchU8With123::Arm2(v)))
//                 } else {
//                     Err(())
//                 }
//             },
//             3u8 => {
//                 if let Ok((n, v)) = self.arm3.spec_parse(s) {
//                     Ok((n, SpecMsgMatchU8With123::Arm3(v)))
//                 } else {
//                     Err(())
//                 }
//             },
//             _ => {
//                 if let Ok((n, v)) = self.default.spec_parse(s) {
//                     Ok((n, SpecMsgMatchU8With123::Default(v)))
//                 } else {
//                     Err(())
//                 }
//             },
//         }
//     }
//
//     proof fn spec_parse_wf(&self, s: Seq<u8>) {
//         match self.val {
//             1u8 => {
//                 if let Ok((n, v)) = self.arm1.spec_parse(s) {
//                     self.arm1.spec_parse_wf(s);
//                 }
//             },
//             2u8 => {
//                 if let Ok((n, v)) = self.arm2.spec_parse(s) {
//                     self.arm2.spec_parse_wf(s);
//                 }
//             },
//             3u8 => {
//                 if let Ok((n, v)) = self.arm3.spec_parse(s) {
//                     self.arm3.spec_parse_wf(s);
//                 }
//             },
//             _ => {
//                 if let Ok((n, v)) = self.default.spec_parse(s) {
//                     self.default.spec_parse_wf(s);
//                 }
//             },
//         }
//     }
//
//     open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
//         match self.val {
//             1u8 => {
//                 if let SpecMsgMatchU8With123::Arm1(v) = v {
//                     self.arm1.spec_serialize(v)
//                 } else {
//                     Err(())
//                 }
//             },
//             2u8 => {
//                 if let SpecMsgMatchU8With123::Arm2(v) = v {
//                     self.arm2.spec_serialize(v)
//                 } else {
//                     Err(())
//                 }
//             },
//             3u8 => {
//                 if let SpecMsgMatchU8With123::Arm3(v) = v {
//                     self.arm3.spec_serialize(v)
//                 } else {
//                     Err(())
//                 }
//             },
//             _ => {
//                 if let SpecMsgMatchU8With123::Default(v) = v {
//                     self.default.spec_serialize(v)
//                 } else {
//                     Err(())
//                 }
//             },
//         }
//     }
// }
//
// impl SecureSpecCombinator for MatchU8With123 {
//     open spec fn spec_is_prefix_secure() -> bool {
//         U8::spec_is_prefix_secure() && U16::spec_is_prefix_secure() && U32::spec_is_prefix_secure()
//             && Tail::spec_is_prefix_secure()
//     }
//
//     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
//         match self.val {
//             1u8 => {
//                 self.arm1.lemma_prefix_secure(s1, s2);
//             },
//             2u8 => {
//                 self.arm2.lemma_prefix_secure(s1, s2);
//             },
//             3u8 => {
//                 self.arm3.lemma_prefix_secure(s1, s2);
//             },
//             _ => {
//                 self.default.lemma_prefix_secure(s1, s2);
//             },
//         }
//     }
//
//     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
//         match self.val {
//             1u8 => {
//                 if let SpecMsgMatchU8With123::Arm1(v) = v {
//                     self.arm1.theorem_serialize_parse_roundtrip(v);
//                 }
//             },
//             2u8 => {
//                 if let SpecMsgMatchU8With123::Arm2(v) = v {
//                     self.arm2.theorem_serialize_parse_roundtrip(v);
//                 }
//             },
//             3u8 => {
//                 if let SpecMsgMatchU8With123::Arm3(v) = v {
//                     self.arm3.theorem_serialize_parse_roundtrip(v);
//                 }
//             },
//             _ => {
//                 if let SpecMsgMatchU8With123::Default(v) = v {
//                     self.default.theorem_serialize_parse_roundtrip(v);
//                 }
//             },
//         }
//     }
//
//     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
//         match self.val {
//             1u8 => {
//                 self.arm1.theorem_parse_serialize_roundtrip(buf);
//             },
//             2u8 => {
//                 self.arm2.theorem_parse_serialize_roundtrip(buf);
//             },
//             3u8 => {
//                 self.arm3.theorem_parse_serialize_roundtrip(buf);
//             },
//             _ => {
//                 self.default.theorem_parse_serialize_roundtrip(buf);
//             },
//         }
//     }
// }
//
// impl Combinator for MatchU8With123 {
//     type Result<'a> = MsgMatchU8With123<'a>;
//
//     type  = MsgMatchU8With123;
//
//     open spec fn spec_length(&self) -> Option<usize> {
//         None
//     }
//
//     fn length(&self) -> Option<usize> {
//         None
//     }
//
//     fn exec_is_prefix_secure() -> bool {
//         U8::exec_is_prefix_secure() && U16::exec_is_prefix_secure() && U32::exec_is_prefix_secure()
//             && Tail::exec_is_prefix_secure()
//     }
//
//     open spec fn parse_requires(&self) -> bool {
//         self.arm1.parse_requires() && self.arm2.parse_requires() && self.arm3.parse_requires()
//             && self.default.parse_requires()
//     }
//
//     fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
//         match self.val {
//             1u8 => {
//                 if let Ok((n, v)) = self.arm1.parse(s) {
//                     Ok((n, MsgMatchU8With123::Arm1(v)))
//                 } else {
//                     Err(())
//                 }
//             },
//             2u8 => {
//                 if let Ok((n, v)) = self.arm2.parse(s) {
//                     Ok((n, MsgMatchU8With123::Arm2(v)))
//                 } else {
//                     Err(())
//                 }
//             },
//             3u8 => {
//                 if let Ok((n, v)) = self.arm3.parse(s) {
//                     Ok((n, MsgMatchU8With123::Arm3(v)))
//                 } else {
//                     Err(())
//                 }
//             },
//             _ => {
//                 if let Ok((n, v)) = self.default.parse(s) {
//                     Ok((n, MsgMatchU8With123::Default(v)))
//                 } else {
//                     Err(())
//                 }
//             },
//         }
//     }
//
//     open spec fn serialize_requires(&self) -> bool {
//         self.arm1.serialize_requires() && self.arm2.serialize_requires()
//             && self.arm3.serialize_requires() && self.default.serialize_requires()
//     }
//
//     fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
//         usize,
//         (),
//     >) {
//         match self.val {
//             1u8 => {
//                 if let MsgMatchU8With123::Arm1(v) = v {
//                     self.arm1.serialize(v, data, pos)
//                 } else {
//                     Err(())
//                 }
//             },
//             2u8 => {
//                 if let MsgMatchU8With123::Arm2(v) = v {
//                     self.arm2.serialize(v, data, pos)
//                 } else {
//                     Err(())
//                 }
//             },
//             3u8 => {
//                 if let MsgMatchU8With123::Arm3(v) = v {
//                     self.arm3.serialize(v, data, pos)
//                 } else {
//                     Err(())
//                 }
//             },
//             _ => {
//                 if let MsgMatchU8With123::Default(v) = v {
//                     self.default.serialize(v, data, pos)
//                 } else {
//                     Err(())
//                 }
//             },
//         }
//     }
// }
} // verus!
