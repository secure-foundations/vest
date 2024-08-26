use super::*;
use crate::properties::*;
use crate::regular::pair::{spec_parse_pair, spec_serialize_pair};
use crate::regular::quadruple::{spec_parse_quadruple, spec_serialize_quadruple};
use vstd::prelude::*;

verus! {

pub exec fn sec_parse_pair<P1, P2, R1, R2>(
    exec_parser1: P1,
    exec_parser2: P2,
    Ghost(spec_parser1): Ghost<spec_fn(SpecStream) -> SpecParseResult<R1::V>>,
    Ghost(spec_parser2): Ghost<spec_fn(SpecStream) -> SpecParseResult<R2::V>>,
    s: SecStream,
) -> (res: SecParseResult<(R1, R2)>) where
    R1: DView,
    R2: DView,
    P1: FnOnce(SecStream) -> SecParseResult<R1>,
    P2: FnOnce(SecStream) -> SecParseResult<R2>,

    requires
        prop_sec_parse_exec_spec_equiv(exec_parser1, spec_parser1),
        prop_sec_parse_exec_spec_equiv(exec_parser2, spec_parser2),
    ensures
        prop_sec_parse_exec_spec_equiv_on(
            s,
            res,
            spec_parse_pair(spec_parser1, spec_parser2),
        ),
// prop_parse_exec_spec_equiv(parse_pair(exec_parser1, exec_parser2, spec_parser1, spec_parser2), spec_parse_pair(spec_parser1, spec_parser2))

{
    proof {
        reveal(prop_sec_parse_exec_spec_equiv);
    }
    let res1 = exec_parser1(s);
    proof {
        lemma_sec_parse_exec_spec_equiv_on(exec_parser1, spec_parser1, s, res1);
    }
    match res1 {
        Ok((s1, n1, r1)) => {
            let res2 = exec_parser2(s1);
            proof {
                lemma_sec_parse_exec_spec_equiv_on(exec_parser2, spec_parser2, s1, res2);
            }
            match res2 {
                Ok((s2, n2, r2)) => {
                    if n1 > usize::MAX - n2 {
                        Err(ParseError::IntegerOverflow)
                    } else {
                        Ok((s2, n1 + n2, (r1, r2)))
                    }
                },
                Err(e) => Err(e),
            }
        },
        Err(e) => Err(e),
    }
}

pub exec fn sec_serialize_pair<S1, S2, T1, T2>(
    exec_serializer1: S1,
    exec_serializer2: S2,
    Ghost(spec_serializer1): Ghost<spec_fn(SpecStream, T1::V) -> SpecSerializeResult>,
    Ghost(spec_serializer2): Ghost<spec_fn(SpecStream, T2::V) -> SpecSerializeResult>,
    s: SecStream,
    v: (T1, T2),
) -> (res: SecSerializeResult) where
    S1: FnOnce(SecStream, T1) -> SecSerializeResult,
    S2: FnOnce(SecStream, T2) -> SecSerializeResult,
    T1: std::fmt::Debug + DView,
    T2: std::fmt::Debug + DView,

    requires
        prop_sec_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
        prop_sec_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
    ensures
        prop_sec_serialize_exec_spec_equiv_on(
            s,
            v,
            res,
            spec_serialize_pair(spec_serializer1, spec_serializer2),
        ),
{
    proof {
        reveal(prop_sec_serialize_exec_spec_equiv);
    }
    let res1 = exec_serializer1(s, v.0);
    proof {
        lemma_sec_serialize_exec_spec_equiv_on(exec_serializer1, spec_serializer1, s, v.0, res1);
    }
    match res1 {
        Ok((s, n)) => {
            let res2 = exec_serializer2(s, v.1);
            proof {
                lemma_sec_serialize_exec_spec_equiv_on(
                    exec_serializer2,
                    spec_serializer2,
                    s,
                    v.1,
                    res2,
                );
            }
            match res2 {
                Ok((s, m)) => {
                    if n > usize::MAX - m {
                        Err(SerializeError::IntegerOverflow)
                    } else {
                        Ok((s, n + m))
                    }
                },
                Err(e) => Err(e),
            }
        },
        Err(e) => Err(e),
    }
}

pub exec fn sec_parse_quadruple<P1, P2, P3, P4, R1, R2, R3, R4>(
    exec_parser1: P1,
    exec_parser2: P2,
    exec_parser3: P3,
    exec_parser4: P4,
    Ghost(spec_parser1): Ghost<spec_fn(SpecStream) -> SpecParseResult<R1::V>>,
    Ghost(spec_parser2): Ghost<spec_fn(SpecStream) -> SpecParseResult<R2::V>>,
    Ghost(spec_parser3): Ghost<spec_fn(SpecStream) -> SpecParseResult<R3::V>>,
    Ghost(spec_parser4): Ghost<spec_fn(SpecStream) -> SpecParseResult<R4::V>>,
    s: SecStream,
) -> (res: SecParseResult<(((R1, R2), R3), R4)>) where
    R1: DView,
    R2: DView,
    R3: DView,
    R4: DView,
    P1: FnOnce(SecStream) -> SecParseResult<R1>,
    P2: FnOnce(SecStream) -> SecParseResult<R2>,
    P3: FnOnce(SecStream) -> SecParseResult<R3>,
    P4: FnOnce(SecStream) -> SecParseResult<R4>,

    requires
        prop_sec_parse_exec_spec_equiv(exec_parser1, spec_parser1),
        prop_sec_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        prop_sec_parse_exec_spec_equiv(exec_parser3, spec_parser3),
        prop_sec_parse_exec_spec_equiv(exec_parser4, spec_parser4),
    ensures
        prop_sec_parse_exec_spec_equiv_on(
            s,
            res,
            spec_parse_quadruple(spec_parser1, spec_parser2, spec_parser3, spec_parser4),
        ),
{
    proof {
        reveal(prop_sec_parse_exec_spec_equiv);
    }
    let pair = |s| -> (res: SecParseResult<(R1, R2)>)
        ensures
            prop_sec_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2)),
        { sec_parse_pair(exec_parser1, exec_parser2, Ghost(spec_parser1), Ghost(spec_parser2), s) };
    let triple = |s| -> (res: SecParseResult<((R1, R2), R3)>)
        ensures
            prop_sec_parse_exec_spec_equiv_on(
                s,
                res,
                spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3),
            ),
        {
            sec_parse_pair(
                pair,
                exec_parser3,
                Ghost(spec_parse_pair(spec_parser1, spec_parser2)),
                Ghost(spec_parser3),
                s,
            )
        };
    sec_parse_pair(
        triple,
        exec_parser4,
        Ghost(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)),
        Ghost(spec_parser4),
        s,
    )
}

pub exec fn sec_serialize_quadruple<S1, S2, S3, S4, T1, T2, T3, T4>(
    exec_serializer1: S1,
    exec_serializer2: S2,
    exec_serializer3: S3,
    exec_serializer4: S4,
    Ghost(spec_serializer1): Ghost<spec_fn(SpecStream, T1::V) -> SpecSerializeResult>,
    Ghost(spec_serializer2): Ghost<spec_fn(SpecStream, T2::V) -> SpecSerializeResult>,
    Ghost(spec_serializer3): Ghost<spec_fn(SpecStream, T3::V) -> SpecSerializeResult>,
    Ghost(spec_serializer4): Ghost<spec_fn(SpecStream, T4::V) -> SpecSerializeResult>,
    s: SecStream,
    v: (((T1, T2), T3), T4),
) -> (res: SecSerializeResult) where
    T1: std::fmt::Debug + DView,
    T2: std::fmt::Debug + DView,
    T3: std::fmt::Debug + DView,
    T4: std::fmt::Debug + DView,
    S1: FnOnce(SecStream, T1) -> SecSerializeResult,
    S2: FnOnce(SecStream, T2) -> SecSerializeResult,
    S3: FnOnce(SecStream, T3) -> SecSerializeResult,
    S4: FnOnce(SecStream, T4) -> SecSerializeResult,

    requires
        prop_sec_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
        prop_sec_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
        prop_sec_serialize_exec_spec_equiv(exec_serializer3, spec_serializer3),
        prop_sec_serialize_exec_spec_equiv(exec_serializer4, spec_serializer4),
    ensures
        prop_sec_serialize_exec_spec_equiv_on(
            s,
            v,
            res,
            spec_serialize_quadruple(
                spec_serializer1,
                spec_serializer2,
                spec_serializer3,
                spec_serializer4,
            ),
        ),
{
    proof {
        reveal(prop_sec_serialize_exec_spec_equiv);
    }
    let pair = |s, v| -> (res: SecSerializeResult)
        ensures
            prop_sec_serialize_exec_spec_equiv_on(
                s,
                v,
                res,
                spec_serialize_pair(spec_serializer1, spec_serializer2),
            ),
        {
            sec_serialize_pair(
                exec_serializer1,
                exec_serializer2,
                Ghost(spec_serializer1),
                Ghost(spec_serializer2),
                s,
                v,
            )
        };
    let triple = |s, v| -> (res: SecSerializeResult)
        ensures
            prop_sec_serialize_exec_spec_equiv_on(
                s,
                v,
                res,
                spec_serialize_pair(
                    spec_serialize_pair(spec_serializer1, spec_serializer2),
                    spec_serializer3,
                ),
            ),
        {
            sec_serialize_pair(
                pair,
                exec_serializer3,
                Ghost(spec_serialize_pair(spec_serializer1, spec_serializer2)),
                Ghost(spec_serializer3),
                s,
                v,
            )
        };
    sec_serialize_pair(
        triple,
        exec_serializer4,
        Ghost(
            spec_serialize_pair(
                spec_serialize_pair(spec_serializer1, spec_serializer2),
                spec_serializer3,
            ),
        ),
        Ghost(spec_serializer4),
        s,
        v,
    )
}

} // verus!
