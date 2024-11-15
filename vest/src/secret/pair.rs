use super::*;
use crate::properties::*;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

pub struct SecPair<Fst, Snd>(pub Fst, pub Snd);

impl<Fst: View, Snd:View> View for SecPair<Fst, Snd> {
    type V = (Fst::V, Snd::V);

    open spec fn view(&self) -> Self::V {
        (self.0.view(), self.1.view())
    }
}

impl<Fst: SecureSpecCombinator, Snd: SpecCombinator> SpecCombinator for SecPair<Fst, Snd> {
    type SpecResult = (Fst::SpecResult, Snd::SpecResult);

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if Fst::is_prefix_secure() {
            if let Ok((n, v1)) = self.0.spec_parse(s) {
                if let Ok((m, v2)) = self.1.spec_parse(s.subrange(n as int, s.len() as int)) {
                    if n <= usize::MAX - m {
                        Ok(((n + m) as usize, (v1, v2)))
                    } else {
                        Err(())
                    }
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        if let Ok((n, v1)) = self.0.spec_parse(s) {
            if let Ok((m, v2)) = self.1.spec_parse(s.subrange(n as int, s.len() as int)) {
                self.0.spec_parse_wf(s);
                self.1.spec_parse_wf(s.subrange(n as int, s.len() as int));
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if Fst::is_prefix_secure() {
            if let Ok(buf1) = self.0.spec_serialize(v.0) {
                if let Ok(buf2) = self.1.spec_serialize(v.1) {
                    if buf1.len() + buf2.len() <= usize::MAX {
                        Ok(buf1.add(buf2))
                    } else {
                        Err(())
                    }
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }
}

impl<Fst: SecureSpecCombinator, Snd: SecureSpecCombinator> SecureSpecCombinator for SecPair<Fst, Snd> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok((buf)) = self.spec_serialize(v) {
            let buf0 = self.0.spec_serialize(v.0).unwrap();
            let buf1 = self.1.spec_serialize(v.1).unwrap();
            self.0.theorem_serialize_parse_roundtrip(v.0);
            self.0.lemma_prefix_secure(buf0, buf1);
            self.1.theorem_serialize_parse_roundtrip(v.1);
            assert(buf0.add(buf1).subrange(buf0.len() as int, buf.len() as int) == buf1);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((nm, (v0, v1))) = self.spec_parse(buf) {
            let (n, v0_) = self.0.spec_parse(buf).unwrap();
            self.0.spec_parse_wf(buf);
            let buf0 = buf.subrange(0, n as int);
            let buf1 = buf.subrange(n as int, buf.len() as int);
            assert(buf == buf0.add(buf1));
            self.0.lemma_prefix_secure(buf0, buf1);
            self.0.theorem_parse_serialize_roundtrip(buf);
            let (m, v1_) = self.1.spec_parse(buf1).unwrap();
            self.1.theorem_parse_serialize_roundtrip(buf1);
            self.1.spec_parse_wf(buf1);
            let buf2 = self.spec_serialize((v0, v1)).unwrap();
            assert(buf2 == buf.subrange(0, nm as int));
        } else {
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        if Fst::is_prefix_secure() && Snd::is_prefix_secure() {
            if let Ok((nm, (v0, v1))) = self.spec_parse(buf) {
                let (n, _) = self.0.spec_parse(buf).unwrap();
                self.0.spec_parse_wf(buf);
                let buf0 = buf.subrange(0, n as int);
                let buf1 = buf.subrange(n as int, buf.len() as int);
                self.0.lemma_prefix_secure(buf0, buf1);
                self.0.lemma_prefix_secure(buf0, buf1.add(s2));
                self.0.lemma_prefix_secure(buf, s2);
                let (m, v1_) = self.1.spec_parse(buf1).unwrap();
                assert(buf.add(s2).subrange(0, n as int) == buf0);
                assert(buf.add(s2).subrange(n as int, buf.add(s2).len() as int) == buf1.add(s2));
                self.1.lemma_prefix_secure(buf1, s2);
            } else {
            }
        } else {
        }
    }
}

impl<Fst, Snd> SecCombinator for SecPair<Fst, Snd> where
    Fst: SecCombinator,
    Snd: SecCombinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as DeepView>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as DeepView>::V>,
    {
    type Result<'a> = (Fst::Result<'a>, Snd::Result<'a>);

    type Owned = (Fst::Owned, Snd::Owned);

    open spec fn spec_length(&self) -> Option<usize> {
        if let Some(n) = self.0.spec_length() {
            if let Some(m) = self.1.spec_length() {
                if n <= usize::MAX - m {
                    Some((n + m) as usize)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    fn length(&self) -> Option<usize> {
        if let Some(n) = self.0.length() {
            if let Some(m) = self.1.length() {
                if n <= usize::MAX - m {
                    Some(n + m)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires() && self.1.parse_requires() && Fst::V::is_prefix_secure()
    }

    fn parse<'a>(&self, s: &'a [SecByte]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (n, v1) = self.0.parse(s)?;
        let s_ = slice_subrange(s, n, s.len());
        assert(s_.deep_view() == s.deep_view().subrange(n as int, s.len() as int));
        let (m, v2) = self.1.parse(s_)?;
        if n <= usize::MAX - m {
            Ok(((n + m), (v1, v2)))
        } else {
            Err(ParseError::SizeOverflow)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires() && self.1.serialize_requires() && Fst::V::is_prefix_secure()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<SecByte>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let n = self.0.serialize(v.0, data, pos)?;
        if n <= usize::MAX - pos && n + pos <= data.len() {
            let m = self.1.serialize(v.1, data, pos + n)?;
            if m <= usize::MAX - n {
                assert(data.deep_view().subrange(pos as int, pos + n + m as int) == self@.spec_serialize(
                    v.deep_view(),
                ).unwrap());
                assert(data.deep_view() == seq_splice(old(data).deep_view(), pos, self@.spec_serialize(v.deep_view()).unwrap()));
                Ok(n + m)
            } else {
                Err(SerializeError::SizeOverflow)
            }
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!



// verus! {

// pub exec fn sec_parse_pair<P1, P2, R1, R2>(
//     exec_parser1: P1,
//     exec_parser2: P2,
//     Ghost(spec_parser1): Ghost<spec_fn(SpecStream) -> SpecParseResult<R1::V>>,
//     Ghost(spec_parser2): Ghost<spec_fn(SpecStream) -> SpecParseResult<R2::V>>,
//     s: SecStream,
// ) -> (res: SecParseResult<(R1, R2)>) where
//     R1: DView,
//     R2: DView,
//     P1: FnOnce(SecStream) -> SecParseResult<R1>,
//     P2: FnOnce(SecStream) -> SecParseResult<R2>,

//     requires
//         prop_sec_parse_exec_spec_equiv(exec_parser1, spec_parser1),
//         prop_sec_parse_exec_spec_equiv(exec_parser2, spec_parser2),
//     ensures
//         prop_sec_parse_exec_spec_equiv_on(
//             s,
//             res,
//             spec_parse_pair(spec_parser1, spec_parser2),
//         ),
// // prop_parse_exec_spec_equiv(parse_pair(exec_parser1, exec_parser2, spec_parser1, spec_parser2), spec_parse_pair(spec_parser1, spec_parser2))

// {
//     proof {
//         reveal(prop_sec_parse_exec_spec_equiv);
//     }
//     let res1 = exec_parser1(s);
//     proof {
//         lemma_sec_parse_exec_spec_equiv_on(exec_parser1, spec_parser1, s, res1);
//     }
//     match res1 {
//         Ok((s1, n1, r1)) => {
//             let res2 = exec_parser2(s1);
//             proof {
//                 lemma_sec_parse_exec_spec_equiv_on(exec_parser2, spec_parser2, s1, res2);
//             }
//             match res2 {
//                 Ok((s2, n2, r2)) => {
//                     if n1 > usize::MAX - n2 {
//                         Err(ParseError::IntegerOverflow)
//                     } else {
//                         Ok((s2, n1 + n2, (r1, r2)))
//                     }
//                 },
//                 Err(e) => Err(e),
//             }
//         },
//         Err(e) => Err(e),
//     }
// }

// pub exec fn sec_serialize_pair<S1, S2, T1, T2>(
//     exec_serializer1: S1,
//     exec_serializer2: S2,
//     Ghost(spec_serializer1): Ghost<spec_fn(SpecStream, T1::V) -> SpecSerializeResult>,
//     Ghost(spec_serializer2): Ghost<spec_fn(SpecStream, T2::V) -> SpecSerializeResult>,
//     s: SecStream,
//     v: (T1, T2),
// ) -> (res: SecSerializeResult) where
//     S1: FnOnce(SecStream, T1) -> SecSerializeResult,
//     S2: FnOnce(SecStream, T2) -> SecSerializeResult,
//     T1: std::fmt::Debug + DView,
//     T2: std::fmt::Debug + DView,

//     requires
//         prop_sec_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
//         prop_sec_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
//     ensures
//         prop_sec_serialize_exec_spec_equiv_on(
//             s,
//             v,
//             res,
//             spec_serialize_pair(spec_serializer1, spec_serializer2),
//         ),
// {
//     proof {
//         reveal(prop_sec_serialize_exec_spec_equiv);
//     }
//     let res1 = exec_serializer1(s, v.0);
//     proof {
//         lemma_sec_serialize_exec_spec_equiv_on(exec_serializer1, spec_serializer1, s, v.0, res1);
//     }
//     match res1 {
//         Ok((s, n)) => {
//             let res2 = exec_serializer2(s, v.1);
//             proof {
//                 lemma_sec_serialize_exec_spec_equiv_on(
//                     exec_serializer2,
//                     spec_serializer2,
//                     s,
//                     v.1,
//                     res2,
//                 );
//             }
//             match res2 {
//                 Ok((s, m)) => {
//                     if n > usize::MAX - m {
//                         Err(SerializeError::IntegerOverflow)
//                     } else {
//                         Ok((s, n + m))
//                     }
//                 },
//                 Err(e) => Err(e),
//             }
//         },
//         Err(e) => Err(e),
//     }
// }

// pub exec fn sec_parse_quadruple<P1, P2, P3, P4, R1, R2, R3, R4>(
//     exec_parser1: P1,
//     exec_parser2: P2,
//     exec_parser3: P3,
//     exec_parser4: P4,
//     Ghost(spec_parser1): Ghost<spec_fn(SpecStream) -> SpecParseResult<R1::V>>,
//     Ghost(spec_parser2): Ghost<spec_fn(SpecStream) -> SpecParseResult<R2::V>>,
//     Ghost(spec_parser3): Ghost<spec_fn(SpecStream) -> SpecParseResult<R3::V>>,
//     Ghost(spec_parser4): Ghost<spec_fn(SpecStream) -> SpecParseResult<R4::V>>,
//     s: SecStream,
// ) -> (res: SecParseResult<(((R1, R2), R3), R4)>) where
//     R1: DView,
//     R2: DView,
//     R3: DView,
//     R4: DView,
//     P1: FnOnce(SecStream) -> SecParseResult<R1>,
//     P2: FnOnce(SecStream) -> SecParseResult<R2>,
//     P3: FnOnce(SecStream) -> SecParseResult<R3>,
//     P4: FnOnce(SecStream) -> SecParseResult<R4>,

//     requires
//         prop_sec_parse_exec_spec_equiv(exec_parser1, spec_parser1),
//         prop_sec_parse_exec_spec_equiv(exec_parser2, spec_parser2),
//         prop_sec_parse_exec_spec_equiv(exec_parser3, spec_parser3),
//         prop_sec_parse_exec_spec_equiv(exec_parser4, spec_parser4),
//     ensures
//         prop_sec_parse_exec_spec_equiv_on(
//             s,
//             res,
//             spec_parse_quadruple(spec_parser1, spec_parser2, spec_parser3, spec_parser4),
//         ),
// {
//     proof {
//         reveal(prop_sec_parse_exec_spec_equiv);
//     }
//     let pair = |s| -> (res: SecParseResult<(R1, R2)>)
//         ensures
//             prop_sec_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2)),
//         { sec_parse_pair(exec_parser1, exec_parser2, Ghost(spec_parser1), Ghost(spec_parser2), s) };
//     let triple = |s| -> (res: SecParseResult<((R1, R2), R3)>)
//         ensures
//             prop_sec_parse_exec_spec_equiv_on(
//                 s,
//                 res,
//                 spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3),
//             ),
//         {
//             sec_parse_pair(
//                 pair,
//                 exec_parser3,
//                 Ghost(spec_parse_pair(spec_parser1, spec_parser2)),
//                 Ghost(spec_parser3),
//                 s,
//             )
//         };
//     sec_parse_pair(
//         triple,
//         exec_parser4,
//         Ghost(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)),
//         Ghost(spec_parser4),
//         s,
//     )
// }

// pub exec fn sec_serialize_quadruple<S1, S2, S3, S4, T1, T2, T3, T4>(
//     exec_serializer1: S1,
//     exec_serializer2: S2,
//     exec_serializer3: S3,
//     exec_serializer4: S4,
//     Ghost(spec_serializer1): Ghost<spec_fn(SpecStream, T1::V) -> SpecSerializeResult>,
//     Ghost(spec_serializer2): Ghost<spec_fn(SpecStream, T2::V) -> SpecSerializeResult>,
//     Ghost(spec_serializer3): Ghost<spec_fn(SpecStream, T3::V) -> SpecSerializeResult>,
//     Ghost(spec_serializer4): Ghost<spec_fn(SpecStream, T4::V) -> SpecSerializeResult>,
//     s: SecStream,
//     v: (((T1, T2), T3), T4),
// ) -> (res: SecSerializeResult) where
//     T1: std::fmt::Debug + DView,
//     T2: std::fmt::Debug + DView,
//     T3: std::fmt::Debug + DView,
//     T4: std::fmt::Debug + DView,
//     S1: FnOnce(SecStream, T1) -> SecSerializeResult,
//     S2: FnOnce(SecStream, T2) -> SecSerializeResult,
//     S3: FnOnce(SecStream, T3) -> SecSerializeResult,
//     S4: FnOnce(SecStream, T4) -> SecSerializeResult,

//     requires
//         prop_sec_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
//         prop_sec_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
//         prop_sec_serialize_exec_spec_equiv(exec_serializer3, spec_serializer3),
//         prop_sec_serialize_exec_spec_equiv(exec_serializer4, spec_serializer4),
//     ensures
//         prop_sec_serialize_exec_spec_equiv_on(
//             s,
//             v,
//             res,
//             spec_serialize_quadruple(
//                 spec_serializer1,
//                 spec_serializer2,
//                 spec_serializer3,
//                 spec_serializer4,
//             ),
//         ),
// {
//     proof {
//         reveal(prop_sec_serialize_exec_spec_equiv);
//     }
//     let pair = |s, v| -> (res: SecSerializeResult)
//         ensures
//             prop_sec_serialize_exec_spec_equiv_on(
//                 s,
//                 v,
//                 res,
//                 spec_serialize_pair(spec_serializer1, spec_serializer2),
//             ),
//         {
//             sec_serialize_pair(
//                 exec_serializer1,
//                 exec_serializer2,
//                 Ghost(spec_serializer1),
//                 Ghost(spec_serializer2),
//                 s,
//                 v,
//             )
//         };
//     let triple = |s, v| -> (res: SecSerializeResult)
//         ensures
//             prop_sec_serialize_exec_spec_equiv_on(
//                 s,
//                 v,
//                 res,
//                 spec_serialize_pair(
//                     spec_serialize_pair(spec_serializer1, spec_serializer2),
//                     spec_serializer3,
//                 ),
//             ),
//         {
//             sec_serialize_pair(
//                 pair,
//                 exec_serializer3,
//                 Ghost(spec_serialize_pair(spec_serializer1, spec_serializer2)),
//                 Ghost(spec_serializer3),
//                 s,
//                 v,
//             )
//         };
//     sec_serialize_pair(
//         triple,
//         exec_serializer4,
//         Ghost(
//             spec_serialize_pair(
//                 spec_serialize_pair(spec_serializer1, spec_serializer2),
//                 spec_serializer3,
//             ),
//         ),
//         Ghost(spec_serializer4),
//         s,
//         v,
//     )
// }

// } // verus!
