#![allow(unused_imports)]
use super::my_vec;
use vest::properties::*;
use vest::regular::bytes;
use vest::regular::modifier::*;
use vest::regular::repetition::*;
use vest::regular::sequence::*;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;

verus! {

struct SpecNominal {
    x: u24,
    y: Seq<u8>,
}

type SpecStructural = (u24, Seq<u8>);

struct Nominal<'a> {
    x: u24,
    y: &'a [u8],
}

impl View for Nominal<'_> {
    type V = SpecNominal;

    closed spec fn view(&self) -> SpecNominal {
        SpecNominal { x: self.x, y: self.y@ }
    }
}

type Structural<'a> = (u24, &'a [u8]);

type StructuralRef<'a> = (&'a u24, &'a &'a [u8]);

impl<'a> From<Structural<'a>> for Nominal<'a> {
    fn ex_from(s: Structural<'a>) -> Self {
        let (x, y) = s;
        Nominal { x, y }
    }
}

impl<'a> From<&'a Nominal<'a>> for StructuralRef<'a> {
    fn ex_from(n: &'a Nominal<'a>) -> Self {
        (&n.x, &n.y)
    }
}

impl SpecFrom<SpecStructural> for SpecNominal {
    closed spec fn spec_from(s: SpecStructural) -> Self {
        let (x, y) = s;
        SpecNominal { x, y }
    }
}

impl SpecFrom<SpecNominal> for SpecStructural {
    closed spec fn spec_from(n: SpecNominal) -> Self {
        (n.x, n.y)
    }
}

struct AIso;

impl View for AIso {
    type V = Self;

    closed spec fn view(&self) -> Self {
        *self
    }
}

impl SpecIso for AIso {
    type Src = SpecStructural;

    type Dst = SpecNominal;
}

impl SpecIsoProof for AIso {
    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso<'a> for AIso {
    type Src = Structural<'a>;

    type Dst = Nominal<'a>;

    type RefSrc = StructuralRef<'a>;
}

pub open spec fn spec_a_cont(deps: u24) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

struct ACont;

impl View for ACont {
    type V = spec_fn(u24) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u24| spec_a_cont(deps)
    }
}

impl Continuation<&u24> for ACont {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: &u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: &u24, o: Self::Output) -> bool {
        o@ == spec_a_cont(deps@)
    }

    fn apply(&self, deps: &u24) -> Self::Output {
        let l = *deps;
        bytes::Variable(l.ex_into())
    }
}

spec fn spec_a() -> Mapped<SpecPair<U24Le, bytes::Variable>, AIso> {
    Mapped { inner: Pair::spec_new(U24Le, |deps| spec_a_cont(deps)), mapper: AIso }
}

fn a() -> (o: Mapped<Pair<U24Le, bytes::Variable, ACont>, AIso>)
    ensures
        o@ == spec_a(),
{
    Mapped { inner: Pair::new(U24Le, ACont), mapper: AIso }
}

fn test_parse_serialize(buf: &[u8])
    requires
        buf@.len() <= usize::MAX,
{
    if let Ok((consumed, val)) = a().parse(buf) {
        let mut outbuf = my_vec![0, 0, 0, 0, 0, 0, 0, 0];
        if let Ok(len) = a().serialize(&val, &mut outbuf, 0) {
            proof {
                spec_a().theorem_parse_serialize_roundtrip(buf@);
            }
            assert(len == consumed);
            assert(buf@.take(len as int) == outbuf@.take(len as int));
        }
    }
    // let (consumed, val) = a().parse(buf).unwrap();
    // let mut outbuf = my_vec![0, 0, 0, 0, 0, 0, 0, 0];
    // let len = a().serialize(&val, &mut outbuf, 0).unwrap();

}

} // verus!
