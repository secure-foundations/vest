use super::{disjoint::DisjointFrom, success::Success};
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
pub struct OrdChoice<Fst, Snd>(pub Fst, pub Snd);

impl<Fst, Snd> OrdChoice<Fst, Snd> where
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
            o == OrdChoice(fst, snd),
    {
        OrdChoice(fst, snd)
    }
}

impl<Fst: View, Snd: View> View for OrdChoice<Fst, Snd> where  {
    type V = OrdChoice<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        OrdChoice(self.0@, self.1@)
    }
}

impl<Fst, Snd> SpecCombinator for OrdChoice<Fst, Snd> where
    Fst: SpecCombinator,
    Snd: SpecCombinator + DisjointFrom<Fst>,
 {
    type Type = Either<Fst::Type, Snd::Type>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if self.1.disjoint_from(&self.0) {
            if let Ok((n, v)) = self.0.spec_parse(s) {
                Ok((n, Either::Left(v)))
            } else {
                if let Ok((n, v)) = self.1.spec_parse(s) {
                    Ok((n, Either::Right(v)))
                } else {
                    Err(())
                }
            }
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if self.1.disjoint_from(&self.0) {
            match v {
                Either::Left(v) => self.0.spec_serialize(v),
                Either::Right(v) => self.1.spec_serialize(v),
            }
        } else {
            Err(())
        }
    }
}

impl<Fst, Snd> SecureSpecCombinator for OrdChoice<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator + DisjointFrom<Fst>,
 {
    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    open spec fn parse_productive() -> bool {
        Fst::parse_productive() && Snd::parse_productive()
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
                let buf = self.1.spec_serialize(v).unwrap();
                if self.1.disjoint_from(&self.0) {
                    self.1.parse_disjoint_on(&self.0, buf);
                }
            },
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v)) = self.0.spec_parse(buf) {
            self.0.theorem_parse_serialize_roundtrip(buf);
        } else {
            if let Ok((n, v)) = self.1.spec_parse(buf) {
                self.1.theorem_parse_serialize_roundtrip(buf);
            }
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Ok((n, v)) = self.0.spec_parse(s) {
            self.0.lemma_parse_length(s);
        } else {
            if let Ok((n, v)) = self.1.spec_parse(s) {
                self.1.lemma_parse_length(s);
            }
        }
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        if let Ok((n, v)) = self.0.spec_parse(s) {
            self.0.lemma_parse_productive(s);
        } else {
            if let Ok((n, v)) = self.1.spec_parse(s) {
                self.1.lemma_parse_productive(s);
            }
        }
    }
}

impl<I, O, Fst, Snd> Combinator<I, O> for OrdChoice<Fst, Snd> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
    Snd::V: DisjointFrom<Fst::V>,
 {
    type Type = Either<Fst::Type, Snd::Type>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires() && self.1.parse_requires() && self@.1.disjoint_from(&self@.0)
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

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires() && self.1.serialize_requires() && self@.1.disjoint_from(
            &self@.0,
        )
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        match v {
            Either::Left(v) => {
                let n = self.0.serialize(v, data, pos)?;
                if n <= usize::MAX - pos && n + pos <= data.len() {
                    Ok(n)
                } else {
                    Err(SerializeError::InsufficientBuffer)
                }
            },
            Either::Right(v) => {
                let n = self.1.serialize(v, data, pos)?;
                if n <= usize::MAX - pos && n + pos <= data.len() {
                    Ok(n)
                } else {
                    Err(SerializeError::InsufficientBuffer)
                }
            },
        }
    }
}

// TODO: Add Non-emptiness proof
// pub struct Opt<T>(pub OrdChoice<T, Success>);
//
//         fn test () {
//             let _ = Opt(OrdChoice::new(super::uints::U8, Success));
//     }
/// This macro constructs a nested OrdChoice combinator
/// in the form of OrdChoice(..., OrdChoice(..., OrdChoice(..., ...)))
#[allow(unused_macros)]
#[macro_export]
macro_rules! ord_choice {
    ($c:expr $(,)?) => {
        $c
    };

    ($c:expr, $($rest:expr),* $(,)?) => {
        OrdChoice($c, ord_choice!($($rest),*))
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
