use crate::combinators::{Fixed, Refined, Star};
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{SpecCombinator, SpecParser, SpecSerializer, SpecType},
};
use vstd::prelude::*;

verus! {

proof fn test_star_1() {
    let c = Star { inner: Fixed::<2> };
    let obuf = Seq::empty();
    let v = seq![seq![1u8, 2u8], seq![3u8, 4u8], seq![5u8, 6u8]];
    
    assert(c.wf(v));
    assert(c.serializable(v, obuf));
    let ibuf = c.spec_serialize_dps(v, obuf);
    let len = ibuf.len() - obuf.len();
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) matches Some((n, parsed_v)) ==> n == len && parsed_v == v);
}

proof fn test_star_2() {
    let star_then_bad = (Star { inner: Fixed::<1> }, Fixed::<1>);
    let obuf = Seq::empty();
    let v = (seq![seq![1u8], seq![2u8], seq![3u8]], seq![4u8]);
    
    assert(star_then_bad.wf(v));
    assert(!star_then_bad.serializable(v, obuf));

    let star_empty_bad = Star { inner: Fixed::<0> };
    assert(star_empty_bad.wf(Seq::empty()));
    assert(forall|s, buf| !star_empty_bad.serializable(s, buf));
}

proof fn test_star_3() {
    let c = (Star { inner: Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] < 10u8 } }, Fixed::<1>);
    let obuf = Seq::empty();
    let v = (seq![seq![1u8], seq![2u8], seq![3u8]], seq![10u8]);
    let v_bad = (seq![seq![1u8], seq![2u8], seq![3u8]], seq![9u8]);
    
    assert(c.wf(v));
    assert(c.wf(v_bad));
    assert(c.serializable(v, obuf)); // serializable because 10 >= 10
    assert(!c.serializable(v_bad, obuf)); // serializable because 9 < 10
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) matches Some((n, parsed_v)) ==> parsed_v == v);
}

proof fn test_star_4() {
    // this works because Star serializes first
    let c = (Fixed::<1>, Star { inner: Fixed::<1> });
    let obuf = Seq::empty();
    let v = (seq![1u8], seq![seq![2u8], seq![3u8]]);
    
    assert(c.wf(v));
    assert(c.serializable(v, obuf));
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) matches Some((n, parsed_v)) ==> parsed_v == v);
}

proof fn test_star_5() {
    let nested_bad = Star { inner: Star { inner: Fixed::<1> } };
    // [[1], [2]]
    let v = seq![seq![seq![1u8], seq![2u8]]];
    
    assert(nested_bad.wf(v));
    
    // for serializability, we need inner.spec_parse(obuf) is None, which is
    // never the case for `Star`
    assert(!nested_bad.serializable(v, Seq::empty()));

    let nested_good = Star {
        inner: Refined {
            inner: Star { inner: Fixed::<1> },
            pred: |x: Seq<Seq<u8>>| x.len() > 0,
        },
    };

    assert(nested_good.wf(v));
    assert(nested_good.serializable(v, Seq::empty()));
}

proof fn test_star_6() {
    let c = Star { inner: Refined { inner: Fixed::<2>, pred: |x: Seq<u8>| x[0] == x[1] } };
    let obuf = Seq::empty();
    let v_good = seq![seq![1u8, 1u8], seq![2u8, 2u8]];
    let v_bad = seq![seq![1u8, 2u8], seq![3u8, 4u8]];  // elements don't satisfy pred
    
    // Verify wf for good values
    assert(c.inner.wf(v_good[0]));
    assert(c.inner.wf(v_good[1]));
    assert(c.wf(v_good));
    
    // Verify wf violation for bad values
    assert(!c.inner.wf(v_bad[0]));  // pred fails: 1 != 2
    assert(!c.inner.wf(v_bad[1]));  // pred fails: 3 != 4
    
    assert(c.serializable(v_good, obuf));
}

proof fn test_star_varying_lengths() {
    // Test Star with variable-length elements using Refined to control parsing
    let c = Star {
        inner: Refined {
            inner: (Fixed::<1>, Fixed::<2>),
            pred: |x: (Seq<u8>, Seq<u8>)| x.0[0] < 100u8
        }
    };
    let obuf = seq![255u8];  // obuf[0] = 255 >= 100, so inner won't parse it
    let v = seq![
        (seq![1u8], seq![2u8, 3u8]),
        (seq![4u8], seq![5u8, 6u8])
    ];
    
    assert(c.wf(v));
    assert(c.serializable(v, obuf));
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) matches Some((n, parsed_v)) ==> parsed_v == v);
}

}
