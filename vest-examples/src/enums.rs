use vest::properties::*;
use vest::regular::bytes::Bytes;
use vest::regular::choice::Either;
use vest::regular::choice::*;
use vest::regular::tag::*;
use vest::regular::tail::Tail;
use vest::regular::uints::*;
use vstd::prelude::*;

verus! {

broadcast use vest::regular::uints::size_of_facts;

pub enum MyEnum {
    A(Seq<u8>),
    B(Seq<u8>),
    C(),
}

pub enum MyEnumExec<'a> {
    A(&'a [u8]),
    B(&'a [u8]),
    C(),
}

impl View for MyEnumExec<'_> {
    type V = MyEnum;

    open spec fn view(&self) -> MyEnum {
        match self {
            MyEnumExec::A(x) => MyEnum::A(x.view()),
            MyEnumExec::B(x) => MyEnum::B(x.view()),
            MyEnumExec::C() => MyEnum::C(),
        }
    }
}

spec fn spec_parse(x: Seq<u8>) -> Option<MyEnum> {
    let tag1 = Tag::spec_new(U8, 1);
    let payload1 = Tail;
    let tag2 = Tag::spec_new(U8, 2);
    let payload2 = Bytes(8);
    let tag3 = Tag::spec_new(U8, 3);
    let payload3 = Bytes(0);
    let case1 = (tag1, payload1);
    let case2 = (tag2, payload2);
    let case3 = (tag3, payload3);
    let comb = OrdChoice(OrdChoice(case1, case2), case3);
    if let Ok((_, eithers)) = comb.spec_parse(x) {
        match eithers {
            Either::Left(Either::Left((_, x))) => Some(MyEnum::A(x)),
            Either::Left(Either::Right((_, x))) => Some(MyEnum::B(x)),
            Either::Right(_) => Some(MyEnum::C()),
        }
    } else {
        None
    }
}

fn exec_parse<'a>(x: &'a [u8]) -> (res: Option<MyEnumExec<'a>>)
    ensures
        res is Some ==> spec_parse(x.view()) is Some,
        res matches Some(r) ==> r.view() == spec_parse(x.view())->Some_0,
{
    let tag1 = Tag::new(U8, 1);
    let payload1 = Tail;
    let tag2 = Tag::new(U8, 2);
    let payload2 = Bytes(8);
    let tag3 = Tag::new(U8, 3);
    let payload3 = Bytes(0);
    let case1 = (tag1, payload1);
    let case2 = (tag2, payload2);
    let case3 = (tag3, payload3);
    let comb = OrdChoice(OrdChoice(case1, case2), case3);
    if let Ok((_, eithers)) = comb.parse(x) {
        match eithers {
            Either::Left(Either::Left((_, x))) => Some(MyEnumExec::A(x)),
            Either::Left(Either::Right((_, x))) => Some(MyEnumExec::B(x)),
            Either::Right(_) => Some(MyEnumExec::C()),
        }
    } else {
        None
    }
}

} // verus!
