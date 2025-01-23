#![allow(unused_imports)]
#![allow(warnings)]
mod choice;
mod depend;
mod enums;
mod map;
mod pair;
mod opt;
mod refserializer;
pub mod repeat;
// mod tlv;
mod wireguard;
use vest::properties::*;
use vest::regular::bytes::*;
use vest::regular::depend::*;
use vest::regular::map::*;
use vest::regular::repeat_n::RepeatN;
use vest::regular::repeat::RepeatResult;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;

verus! {


struct SpecNominal {
    x: u24,
    y: Seq<u8>,
}

type SpecStructural = (u24, Seq<u8>);

struct Nominal {
    x: u24,
    y: RepeatResult<u8>,
}

impl View for Nominal {
    type V = SpecNominal;

    closed spec fn view(&self) -> SpecNominal {
        SpecNominal { x: self.x, y: self.y@ }
    }
}

type Structural = (u24, RepeatResult<u8>);

type StructuralRef<'a> = (u24, &'a RepeatResult<u8>);

impl From<Structural> for Nominal {
    fn ex_from(s: Structural) -> Self {
        let (x, y) = s;
        Nominal { x, y }
    }
}

impl<'a> From<&'a Nominal> for StructuralRef<'a> {
    fn ex_from(n: &'a Nominal) -> Self {
        (n.x, &n.y)
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

struct AIso<'a>(std::marker::PhantomData<&'a ()>);
impl AIso<'_> {
    closed spec fn spec_new() -> Self {
        AIso(std::marker::PhantomData)
    }
    fn new() -> Self {
        AIso(std::marker::PhantomData)
    }
}

impl View for AIso<'_> {
    type V = Self;

    closed spec fn view(&self) -> Self {
        *self
    }
}

impl SpecIso for AIso<'_> {
    type Src = SpecStructural;

    type Dst = SpecNominal;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for AIso<'a> {
    type Src = Structural;

    type Dst = Nominal;

    type RefSrc = StructuralRef<'a>;

    type RefDst = &'a Nominal;
}

pub open spec fn spec_a_cont(deps: u24) -> RepeatN<U8, 'static> {
    let l = deps;
    // RepeatN::spec_new(U8, l.spec_into())
    RepeatN(U8, l.spec_into(), &())
}

struct APCont<'a>(std::marker::PhantomData<&'a ()>);
struct ASCont<'a>(std::marker::PhantomData<&'a ()>);


impl<'a> APCont<'a> {
    pub fn new() -> Self {
        APCont(std::marker::PhantomData)
    }
}

impl<'a> ASCont<'a> {
    pub fn new() -> Self {
        ASCont(std::marker::PhantomData)
    }
}

impl<'a> Continuation<&u24> for APCont<'a> {
    type Output = RepeatN<U8, 'a>;

    open spec fn requires(&self, deps: &u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: &u24, o: Self::Output) -> bool {
        o@ == spec_a_cont(deps@)
    }

    fn apply(&self, deps: &u24) -> Self::Output {
        let l = *deps;
        RepeatN(U8, l.ex_into(), &())
    }
}

impl<'a> Continuation<u24> for ASCont<'a> {
    type Output = RepeatN<U8, 'a>;

    open spec fn requires(&self, deps: u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u24, o: Self::Output) -> bool {
        o@ == spec_a_cont(deps@)
    }

    fn apply(&self, deps: u24) -> Self::Output {
        let l = deps;
        RepeatN(U8, l.ex_into(), &())
    }
}

spec fn spec_a() -> Mapped<SpecDepend<U24Le, RepeatN<U8, 'static>>, AIso<'static>> {
    Mapped {
        inner:
        SpecDepend { fst: U24Le, snd: |deps| spec_a_cont(deps) },
        mapper: AIso::spec_new(),
    }
}

fn a<'a>() -> (o: Mapped<Depend<&'a [u8], Vec<u8>, U24Le, RepeatN<U8, 'a>, APCont<'a>, ASCont<'a>>, AIso<'a>>  )
    ensures
        o@ == spec_a(),
{
    Mapped {
        inner:
        Depend {
            fst: U24Le,
            p_snd: APCont::new(),
            s_snd: ASCont::new(),
            spec_snd: Ghost(|deps| spec_a_cont(deps)),
        },
        mapper: AIso::new(),
    }
}

fn test_parse_serialize(buf: &[u8])
    requires buf@.len() <= usize::MAX,
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

}

macro_rules! my_vec {
    // Match against any number of comma-separated expressions.
    ($($x:expr),* $(,)?) => {
        {
            let mut temp_vec = Vec::new();
            // $(temp_vec.push($x);)*
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}
pub(crate) use my_vec;
