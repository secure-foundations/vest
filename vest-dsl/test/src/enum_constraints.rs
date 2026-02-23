
#![allow(warnings)]
#![allow(unused)]
use vstd::prelude::*;
use vest_lib::regular::modifier::*;
use vest_lib::regular::bytes;
use vest_lib::regular::variant::*;
use vest_lib::regular::sequence::*;
use vest_lib::regular::repetition::*;
use vest_lib::regular::disjoint::DisjointFrom;
use vest_lib::regular::tag::*;
use vest_lib::regular::uints::*;
use vest_lib::utils::*;
use vest_lib::properties::*;
use vest_lib::bitcoin::varint::{BtcVarint, VarInt};
use vest_lib::regular::leb128::*;

macro_rules! impl_wrapper_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::vstd::prelude::verus! {
            impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for $combinator {
                type Type = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
                type SType = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
                fn length(&self, v: Self::SType) -> usize
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
                open spec fn ex_requires(&self) -> bool
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
                fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
                fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
            }
        } // verus!
    };
}
verus!{

pub spec const SPEC_MyTypedEnum_X: u16 = 1;
pub spec const SPEC_MyTypedEnum_Y: u16 = 2;
pub spec const SPEC_MyTypedEnum_Z: u16 = 3;
pub exec static EXEC_MyTypedEnum_X: u16 ensures EXEC_MyTypedEnum_X == SPEC_MyTypedEnum_X { 1 }
pub exec static EXEC_MyTypedEnum_Y: u16 ensures EXEC_MyTypedEnum_Y == SPEC_MyTypedEnum_Y { 2 }
pub exec static EXEC_MyTypedEnum_Z: u16 ensures EXEC_MyTypedEnum_Z == SPEC_MyTypedEnum_Z { 3 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum MyTypedEnum {
    X = 1,
Y = 2,
Z = 3
}
pub type SpecMyTypedEnum = MyTypedEnum;

pub type MyTypedEnumInner = u16;

pub type MyTypedEnumInnerRef<'a> = &'a u16;

impl View for MyTypedEnum {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<MyTypedEnumInner> for MyTypedEnum {
    type Error = ();

    open spec fn spec_try_from(v: MyTypedEnumInner) -> Result<MyTypedEnum, ()> {
        match v {
            1u16 => Ok(MyTypedEnum::X),
            2u16 => Ok(MyTypedEnum::Y),
            3u16 => Ok(MyTypedEnum::Z),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<MyTypedEnum> for MyTypedEnumInner {
    type Error = ();

    open spec fn spec_try_from(v: MyTypedEnum) -> Result<MyTypedEnumInner, ()> {
        match v {
            MyTypedEnum::X => Ok(SPEC_MyTypedEnum_X),
            MyTypedEnum::Y => Ok(SPEC_MyTypedEnum_Y),
            MyTypedEnum::Z => Ok(SPEC_MyTypedEnum_Z),
        }
    }
}

impl TryFrom<MyTypedEnumInner> for MyTypedEnum {
    type Error = ();

    fn ex_try_from(v: MyTypedEnumInner) -> Result<MyTypedEnum, ()> {
        match v {
            1u16 => Ok(MyTypedEnum::X),
            2u16 => Ok(MyTypedEnum::Y),
            3u16 => Ok(MyTypedEnum::Z),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a MyTypedEnum> for MyTypedEnumInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a MyTypedEnum) -> Result<MyTypedEnumInnerRef<'a>, ()> {
        match v {
            MyTypedEnum::X => Ok(&EXEC_MyTypedEnum_X),
            MyTypedEnum::Y => Ok(&EXEC_MyTypedEnum_Y),
            MyTypedEnum::Z => Ok(&EXEC_MyTypedEnum_Z),
        }
    }
}

pub struct MyTypedEnumMapper;

impl View for MyTypedEnumMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for MyTypedEnumMapper {
    type Src = MyTypedEnumInner;
    type Dst = MyTypedEnum;
}

impl SpecPartialIsoProof for MyTypedEnumMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl<'a> PartialIso<'a> for MyTypedEnumMapper {
    type Src = MyTypedEnumInner;
    type Dst = MyTypedEnum;
    type RefSrc = MyTypedEnumInnerRef<'a>;
}


pub struct SpecMyTypedEnumCombinator(pub SpecMyTypedEnumCombinatorAlias);

impl SpecCombinator for SpecMyTypedEnumCombinator {
    type Type = SpecMyTypedEnum;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMyTypedEnumCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMyTypedEnumCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMyTypedEnumCombinatorAlias = TryMap<U16Le, MyTypedEnumMapper>;

pub struct MyTypedEnumCombinator(pub MyTypedEnumCombinatorAlias);

impl View for MyTypedEnumCombinator {
    type V = SpecMyTypedEnumCombinator;
    open spec fn view(&self) -> Self::V { SpecMyTypedEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MyTypedEnumCombinator {
    type Type = MyTypedEnum;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type MyTypedEnumCombinatorAlias = TryMap<U16Le, MyTypedEnumMapper>;


pub open spec fn spec_my_typed_enum() -> SpecMyTypedEnumCombinator {
    SpecMyTypedEnumCombinator(TryMap { inner: U16Le, mapper: MyTypedEnumMapper })
}

                
pub fn my_typed_enum<'a>() -> (o: MyTypedEnumCombinator)
    ensures o@ == spec_my_typed_enum(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MyTypedEnumCombinator(TryMap { inner: U16Le, mapper: MyTypedEnumMapper });
    // assert({
    //     &&& combinator@ == spec_my_typed_enum()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_my_typed_enum<'a>(input: &'a [u8]) -> (res: PResult<<MyTypedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_my_typed_enum().spec_parse(input@) == Some((n as int, v@)),
        spec_my_typed_enum().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_my_typed_enum().spec_parse(input@) is None,
        spec_my_typed_enum().spec_parse(input@) is None ==> res is Err,
{
    let combinator = my_typed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_my_typed_enum<'a>(v: <MyTypedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_my_typed_enum().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_my_typed_enum().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_my_typed_enum().spec_serialize(v@))
        },
{
    let combinator = my_typed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn my_typed_enum_len<'a>(v: <MyTypedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_my_typed_enum().wf(v@),
        spec_my_typed_enum().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_my_typed_enum().spec_serialize(v@).len(),
{
    let combinator = my_typed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub spec const SPEC_MyEnum_A: u8 = 1;
pub spec const SPEC_MyEnum_B: u8 = 2;
pub spec const SPEC_MyEnum_C: u8 = 3;
pub exec static EXEC_MyEnum_A: u8 ensures EXEC_MyEnum_A == SPEC_MyEnum_A { 1 }
pub exec static EXEC_MyEnum_B: u8 ensures EXEC_MyEnum_B == SPEC_MyEnum_B { 2 }
pub exec static EXEC_MyEnum_C: u8 ensures EXEC_MyEnum_C == SPEC_MyEnum_C { 3 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum MyEnum {
    A = 1,
B = 2,
C = 3
}
pub type SpecMyEnum = MyEnum;

pub type MyEnumInner = u8;

pub type MyEnumInnerRef<'a> = &'a u8;

impl View for MyEnum {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<MyEnumInner> for MyEnum {
    type Error = ();

    open spec fn spec_try_from(v: MyEnumInner) -> Result<MyEnum, ()> {
        match v {
            1u8 => Ok(MyEnum::A),
            2u8 => Ok(MyEnum::B),
            3u8 => Ok(MyEnum::C),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<MyEnum> for MyEnumInner {
    type Error = ();

    open spec fn spec_try_from(v: MyEnum) -> Result<MyEnumInner, ()> {
        match v {
            MyEnum::A => Ok(SPEC_MyEnum_A),
            MyEnum::B => Ok(SPEC_MyEnum_B),
            MyEnum::C => Ok(SPEC_MyEnum_C),
        }
    }
}

impl TryFrom<MyEnumInner> for MyEnum {
    type Error = ();

    fn ex_try_from(v: MyEnumInner) -> Result<MyEnum, ()> {
        match v {
            1u8 => Ok(MyEnum::A),
            2u8 => Ok(MyEnum::B),
            3u8 => Ok(MyEnum::C),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a MyEnum> for MyEnumInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a MyEnum) -> Result<MyEnumInnerRef<'a>, ()> {
        match v {
            MyEnum::A => Ok(&EXEC_MyEnum_A),
            MyEnum::B => Ok(&EXEC_MyEnum_B),
            MyEnum::C => Ok(&EXEC_MyEnum_C),
        }
    }
}

pub struct MyEnumMapper;

impl View for MyEnumMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for MyEnumMapper {
    type Src = MyEnumInner;
    type Dst = MyEnum;
}

impl SpecPartialIsoProof for MyEnumMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl<'a> PartialIso<'a> for MyEnumMapper {
    type Src = MyEnumInner;
    type Dst = MyEnum;
    type RefSrc = MyEnumInnerRef<'a>;
}


pub struct SpecMyEnumCombinator(pub SpecMyEnumCombinatorAlias);

impl SpecCombinator for SpecMyEnumCombinator {
    type Type = SpecMyEnum;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMyEnumCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMyEnumCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMyEnumCombinatorAlias = TryMap<U8, MyEnumMapper>;

pub struct MyEnumCombinator(pub MyEnumCombinatorAlias);

impl View for MyEnumCombinator {
    type V = SpecMyEnumCombinator;
    open spec fn view(&self) -> Self::V { SpecMyEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MyEnumCombinator {
    type Type = MyEnum;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type MyEnumCombinatorAlias = TryMap<U8, MyEnumMapper>;


pub open spec fn spec_my_enum() -> SpecMyEnumCombinator {
    SpecMyEnumCombinator(TryMap { inner: U8, mapper: MyEnumMapper })
}

                
pub fn my_enum<'a>() -> (o: MyEnumCombinator)
    ensures o@ == spec_my_enum(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MyEnumCombinator(TryMap { inner: U8, mapper: MyEnumMapper });
    // assert({
    //     &&& combinator@ == spec_my_enum()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_my_enum<'a>(input: &'a [u8]) -> (res: PResult<<MyEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_my_enum().spec_parse(input@) == Some((n as int, v@)),
        spec_my_enum().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_my_enum().spec_parse(input@) is None,
        spec_my_enum().spec_parse(input@) is None ==> res is Err,
{
    let combinator = my_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_my_enum<'a>(v: <MyEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_my_enum().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_my_enum().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_my_enum().spec_serialize(v@))
        },
{
    let combinator = my_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn my_enum_len<'a>(v: <MyEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_my_enum().wf(v@),
        spec_my_enum().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_my_enum().spec_serialize(v@).len(),
{
    let combinator = my_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecTypedEnumConstraints {
    pub foo: SpecMyTypedEnum,
    pub bar: SpecMyTypedEnum,
    pub baz: SpecMyTypedEnum,
    pub tag: MyTypedEnum,
}

pub type SpecTypedEnumConstraintsInner = (SpecMyTypedEnum, (SpecMyTypedEnum, (SpecMyTypedEnum, MyTypedEnum)));


impl SpecFrom<SpecTypedEnumConstraints> for SpecTypedEnumConstraintsInner {
    open spec fn spec_from(m: SpecTypedEnumConstraints) -> SpecTypedEnumConstraintsInner {
        (m.foo, (m.bar, (m.baz, m.tag)))
    }
}

impl SpecFrom<SpecTypedEnumConstraintsInner> for SpecTypedEnumConstraints {
    open spec fn spec_from(m: SpecTypedEnumConstraintsInner) -> SpecTypedEnumConstraints {
        let (foo, (bar, (baz, tag))) = m;
        SpecTypedEnumConstraints { foo, bar, baz, tag }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TypedEnumConstraints {
    pub foo: MyTypedEnum,
    pub bar: MyTypedEnum,
    pub baz: MyTypedEnum,
    pub tag: MyTypedEnum,
}

impl View for TypedEnumConstraints {
    type V = SpecTypedEnumConstraints;

    open spec fn view(&self) -> Self::V {
        SpecTypedEnumConstraints {
            foo: self.foo@,
            bar: self.bar@,
            baz: self.baz@,
            tag: self.tag@,
        }
    }
}
pub type TypedEnumConstraintsInner = (MyTypedEnum, (MyTypedEnum, (MyTypedEnum, MyTypedEnum)));

pub type TypedEnumConstraintsInnerRef<'a> = (&'a MyTypedEnum, (&'a MyTypedEnum, (&'a MyTypedEnum, &'a MyTypedEnum)));
impl<'a> From<&'a TypedEnumConstraints> for TypedEnumConstraintsInnerRef<'a> {
    fn ex_from(m: &'a TypedEnumConstraints) -> TypedEnumConstraintsInnerRef<'a> {
        (&m.foo, (&m.bar, (&m.baz, &m.tag)))
    }
}

impl From<TypedEnumConstraintsInner> for TypedEnumConstraints {
    fn ex_from(m: TypedEnumConstraintsInner) -> TypedEnumConstraints {
        let (foo, (bar, (baz, tag))) = m;
        TypedEnumConstraints { foo, bar, baz, tag }
    }
}

pub struct TypedEnumConstraintsMapper;
impl View for TypedEnumConstraintsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TypedEnumConstraintsMapper {
    type Src = SpecTypedEnumConstraintsInner;
    type Dst = SpecTypedEnumConstraints;
}
impl SpecIsoProof for TypedEnumConstraintsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TypedEnumConstraintsMapper {
    type Src = TypedEnumConstraintsInner;
    type Dst = TypedEnumConstraints;
    type RefSrc = TypedEnumConstraintsInnerRef<'a>;
}
pub const TYPEDENUMCONSTRAINTSTAG_CONST: u16 = 1;
type SpecTypedEnumConstraintsCombinatorAlias1 = (Refined<SpecMyTypedEnumCombinator, Predicate13159921752950921642>, TryMap<Refined<U16Le, TagPred<u16>>, MyTypedEnumMapper>);
type SpecTypedEnumConstraintsCombinatorAlias2 = (Refined<SpecMyTypedEnumCombinator, Predicate945793182160552516>, SpecTypedEnumConstraintsCombinatorAlias1);
type SpecTypedEnumConstraintsCombinatorAlias3 = (Refined<SpecMyTypedEnumCombinator, Predicate17940557908687846566>, SpecTypedEnumConstraintsCombinatorAlias2);
pub struct SpecTypedEnumConstraintsCombinator(pub SpecTypedEnumConstraintsCombinatorAlias);

impl SpecCombinator for SpecTypedEnumConstraintsCombinator {
    type Type = SpecTypedEnumConstraints;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypedEnumConstraintsCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTypedEnumConstraintsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTypedEnumConstraintsCombinatorAlias = Mapped<SpecTypedEnumConstraintsCombinatorAlias3, TypedEnumConstraintsMapper>;
pub struct Predicate17940557908687846566;
impl View for Predicate17940557908687846566 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<MyTypedEnum> for Predicate17940557908687846566 {
    fn apply(&self, e: &MyTypedEnum) -> bool {
        matches!(e, MyTypedEnum::X)
    }
}
impl SpecPred<MyTypedEnum> for Predicate17940557908687846566 {
    open spec fn spec_apply(&self, e: &MyTypedEnum) -> bool {
        matches!(e, MyTypedEnum::X)
    }
}
pub struct Predicate945793182160552516;
impl View for Predicate945793182160552516 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<MyTypedEnum> for Predicate945793182160552516 {
    fn apply(&self, e: &MyTypedEnum) -> bool {
        !(matches!(e, MyTypedEnum::Y))
    }
}
impl SpecPred<MyTypedEnum> for Predicate945793182160552516 {
    open spec fn spec_apply(&self, e: &MyTypedEnum) -> bool {
        !(matches!(e, MyTypedEnum::Y))
    }
}
pub struct Predicate13159921752950921642;
impl View for Predicate13159921752950921642 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<MyTypedEnum> for Predicate13159921752950921642 {
    fn apply(&self, e: &MyTypedEnum) -> bool {
        matches!(e, MyTypedEnum::X | MyTypedEnum::Z)
    }
}
impl SpecPred<MyTypedEnum> for Predicate13159921752950921642 {
    open spec fn spec_apply(&self, e: &MyTypedEnum) -> bool {
        matches!(e, MyTypedEnum::X | MyTypedEnum::Z)
    }
}
type TypedEnumConstraintsCombinatorAlias1 = (Refined<MyTypedEnumCombinator, Predicate13159921752950921642>, TryMap<Refined<U16Le, TagPred<u16>>, MyTypedEnumMapper>);
type TypedEnumConstraintsCombinatorAlias2 = (Refined<MyTypedEnumCombinator, Predicate945793182160552516>, TypedEnumConstraintsCombinator1);
type TypedEnumConstraintsCombinatorAlias3 = (Refined<MyTypedEnumCombinator, Predicate17940557908687846566>, TypedEnumConstraintsCombinator2);
pub struct TypedEnumConstraintsCombinator1(pub TypedEnumConstraintsCombinatorAlias1);
impl View for TypedEnumConstraintsCombinator1 {
    type V = SpecTypedEnumConstraintsCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TypedEnumConstraintsCombinator1, TypedEnumConstraintsCombinatorAlias1);

pub struct TypedEnumConstraintsCombinator2(pub TypedEnumConstraintsCombinatorAlias2);
impl View for TypedEnumConstraintsCombinator2 {
    type V = SpecTypedEnumConstraintsCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TypedEnumConstraintsCombinator2, TypedEnumConstraintsCombinatorAlias2);

pub struct TypedEnumConstraintsCombinator3(pub TypedEnumConstraintsCombinatorAlias3);
impl View for TypedEnumConstraintsCombinator3 {
    type V = SpecTypedEnumConstraintsCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TypedEnumConstraintsCombinator3, TypedEnumConstraintsCombinatorAlias3);

pub struct TypedEnumConstraintsCombinator(pub TypedEnumConstraintsCombinatorAlias);

impl View for TypedEnumConstraintsCombinator {
    type V = SpecTypedEnumConstraintsCombinator;
    open spec fn view(&self) -> Self::V { SpecTypedEnumConstraintsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TypedEnumConstraintsCombinator {
    type Type = TypedEnumConstraints;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type TypedEnumConstraintsCombinatorAlias = Mapped<TypedEnumConstraintsCombinator3, TypedEnumConstraintsMapper>;


pub open spec fn spec_typed_enum_constraints() -> SpecTypedEnumConstraintsCombinator {
    SpecTypedEnumConstraintsCombinator(
    Mapped {
        inner: (Refined { inner: spec_my_typed_enum(), predicate: Predicate17940557908687846566 }, (Refined { inner: spec_my_typed_enum(), predicate: Predicate945793182160552516 }, (Refined { inner: spec_my_typed_enum(), predicate: Predicate13159921752950921642 }, TryMap { inner: Refined { inner: U16Le, predicate: TagPred(TYPEDENUMCONSTRAINTSTAG_CONST) }, mapper: MyTypedEnumMapper }))),
        mapper: TypedEnumConstraintsMapper,
    })
}

                
pub fn typed_enum_constraints<'a>() -> (o: TypedEnumConstraintsCombinator)
    ensures o@ == spec_typed_enum_constraints(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TypedEnumConstraintsCombinator(
    Mapped {
        inner: TypedEnumConstraintsCombinator3((Refined { inner: my_typed_enum(), predicate: Predicate17940557908687846566 }, TypedEnumConstraintsCombinator2((Refined { inner: my_typed_enum(), predicate: Predicate945793182160552516 }, TypedEnumConstraintsCombinator1((Refined { inner: my_typed_enum(), predicate: Predicate13159921752950921642 }, TryMap { inner: Refined { inner: U16Le, predicate: TagPred(TYPEDENUMCONSTRAINTSTAG_CONST) }, mapper: MyTypedEnumMapper })))))),
        mapper: TypedEnumConstraintsMapper,
    });
    // assert({
    //     &&& combinator@ == spec_typed_enum_constraints()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_typed_enum_constraints<'a>(input: &'a [u8]) -> (res: PResult<<TypedEnumConstraintsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_typed_enum_constraints().spec_parse(input@) == Some((n as int, v@)),
        spec_typed_enum_constraints().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_typed_enum_constraints().spec_parse(input@) is None,
        spec_typed_enum_constraints().spec_parse(input@) is None ==> res is Err,
{
    let combinator = typed_enum_constraints();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_typed_enum_constraints<'a>(v: <TypedEnumConstraintsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_typed_enum_constraints().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_typed_enum_constraints().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_typed_enum_constraints().spec_serialize(v@))
        },
{
    let combinator = typed_enum_constraints();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn typed_enum_constraints_len<'a>(v: <TypedEnumConstraintsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_typed_enum_constraints().wf(v@),
        spec_typed_enum_constraints().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_typed_enum_constraints().spec_serialize(v@).len(),
{
    let combinator = typed_enum_constraints();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecEnumConstraints {
    pub foo: SpecMyEnum,
    pub bar: SpecMyEnum,
    pub baz: SpecMyEnum,
    pub tag: MyEnum,
}

pub type SpecEnumConstraintsInner = (SpecMyEnum, (SpecMyEnum, (SpecMyEnum, MyEnum)));


impl SpecFrom<SpecEnumConstraints> for SpecEnumConstraintsInner {
    open spec fn spec_from(m: SpecEnumConstraints) -> SpecEnumConstraintsInner {
        (m.foo, (m.bar, (m.baz, m.tag)))
    }
}

impl SpecFrom<SpecEnumConstraintsInner> for SpecEnumConstraints {
    open spec fn spec_from(m: SpecEnumConstraintsInner) -> SpecEnumConstraints {
        let (foo, (bar, (baz, tag))) = m;
        SpecEnumConstraints { foo, bar, baz, tag }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EnumConstraints {
    pub foo: MyEnum,
    pub bar: MyEnum,
    pub baz: MyEnum,
    pub tag: MyEnum,
}

impl View for EnumConstraints {
    type V = SpecEnumConstraints;

    open spec fn view(&self) -> Self::V {
        SpecEnumConstraints {
            foo: self.foo@,
            bar: self.bar@,
            baz: self.baz@,
            tag: self.tag@,
        }
    }
}
pub type EnumConstraintsInner = (MyEnum, (MyEnum, (MyEnum, MyEnum)));

pub type EnumConstraintsInnerRef<'a> = (&'a MyEnum, (&'a MyEnum, (&'a MyEnum, &'a MyEnum)));
impl<'a> From<&'a EnumConstraints> for EnumConstraintsInnerRef<'a> {
    fn ex_from(m: &'a EnumConstraints) -> EnumConstraintsInnerRef<'a> {
        (&m.foo, (&m.bar, (&m.baz, &m.tag)))
    }
}

impl From<EnumConstraintsInner> for EnumConstraints {
    fn ex_from(m: EnumConstraintsInner) -> EnumConstraints {
        let (foo, (bar, (baz, tag))) = m;
        EnumConstraints { foo, bar, baz, tag }
    }
}

pub struct EnumConstraintsMapper;
impl View for EnumConstraintsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EnumConstraintsMapper {
    type Src = SpecEnumConstraintsInner;
    type Dst = SpecEnumConstraints;
}
impl SpecIsoProof for EnumConstraintsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EnumConstraintsMapper {
    type Src = EnumConstraintsInner;
    type Dst = EnumConstraints;
    type RefSrc = EnumConstraintsInnerRef<'a>;
}
pub const ENUMCONSTRAINTSTAG_CONST: u8 = 1;
type SpecEnumConstraintsCombinatorAlias1 = (Refined<SpecMyEnumCombinator, Predicate18102098100666777803>, TryMap<Refined<U8, TagPred<u8>>, MyEnumMapper>);
type SpecEnumConstraintsCombinatorAlias2 = (Refined<SpecMyEnumCombinator, Predicate747078089795820719>, SpecEnumConstraintsCombinatorAlias1);
type SpecEnumConstraintsCombinatorAlias3 = (Refined<SpecMyEnumCombinator, Predicate1673031309162834621>, SpecEnumConstraintsCombinatorAlias2);
pub struct SpecEnumConstraintsCombinator(pub SpecEnumConstraintsCombinatorAlias);

impl SpecCombinator for SpecEnumConstraintsCombinator {
    type Type = SpecEnumConstraints;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEnumConstraintsCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEnumConstraintsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecEnumConstraintsCombinatorAlias = Mapped<SpecEnumConstraintsCombinatorAlias3, EnumConstraintsMapper>;
pub struct Predicate1673031309162834621;
impl View for Predicate1673031309162834621 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<MyEnum> for Predicate1673031309162834621 {
    fn apply(&self, e: &MyEnum) -> bool {
        matches!(e, MyEnum::A)
    }
}
impl SpecPred<MyEnum> for Predicate1673031309162834621 {
    open spec fn spec_apply(&self, e: &MyEnum) -> bool {
        matches!(e, MyEnum::A)
    }
}
pub struct Predicate747078089795820719;
impl View for Predicate747078089795820719 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<MyEnum> for Predicate747078089795820719 {
    fn apply(&self, e: &MyEnum) -> bool {
        !(matches!(e, MyEnum::B))
    }
}
impl SpecPred<MyEnum> for Predicate747078089795820719 {
    open spec fn spec_apply(&self, e: &MyEnum) -> bool {
        !(matches!(e, MyEnum::B))
    }
}
pub struct Predicate18102098100666777803;
impl View for Predicate18102098100666777803 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<MyEnum> for Predicate18102098100666777803 {
    fn apply(&self, e: &MyEnum) -> bool {
        matches!(e, MyEnum::A | MyEnum::C)
    }
}
impl SpecPred<MyEnum> for Predicate18102098100666777803 {
    open spec fn spec_apply(&self, e: &MyEnum) -> bool {
        matches!(e, MyEnum::A | MyEnum::C)
    }
}
type EnumConstraintsCombinatorAlias1 = (Refined<MyEnumCombinator, Predicate18102098100666777803>, TryMap<Refined<U8, TagPred<u8>>, MyEnumMapper>);
type EnumConstraintsCombinatorAlias2 = (Refined<MyEnumCombinator, Predicate747078089795820719>, EnumConstraintsCombinator1);
type EnumConstraintsCombinatorAlias3 = (Refined<MyEnumCombinator, Predicate1673031309162834621>, EnumConstraintsCombinator2);
pub struct EnumConstraintsCombinator1(pub EnumConstraintsCombinatorAlias1);
impl View for EnumConstraintsCombinator1 {
    type V = SpecEnumConstraintsCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EnumConstraintsCombinator1, EnumConstraintsCombinatorAlias1);

pub struct EnumConstraintsCombinator2(pub EnumConstraintsCombinatorAlias2);
impl View for EnumConstraintsCombinator2 {
    type V = SpecEnumConstraintsCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EnumConstraintsCombinator2, EnumConstraintsCombinatorAlias2);

pub struct EnumConstraintsCombinator3(pub EnumConstraintsCombinatorAlias3);
impl View for EnumConstraintsCombinator3 {
    type V = SpecEnumConstraintsCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EnumConstraintsCombinator3, EnumConstraintsCombinatorAlias3);

pub struct EnumConstraintsCombinator(pub EnumConstraintsCombinatorAlias);

impl View for EnumConstraintsCombinator {
    type V = SpecEnumConstraintsCombinator;
    open spec fn view(&self) -> Self::V { SpecEnumConstraintsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EnumConstraintsCombinator {
    type Type = EnumConstraints;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type EnumConstraintsCombinatorAlias = Mapped<EnumConstraintsCombinator3, EnumConstraintsMapper>;


pub open spec fn spec_enum_constraints() -> SpecEnumConstraintsCombinator {
    SpecEnumConstraintsCombinator(
    Mapped {
        inner: (Refined { inner: spec_my_enum(), predicate: Predicate1673031309162834621 }, (Refined { inner: spec_my_enum(), predicate: Predicate747078089795820719 }, (Refined { inner: spec_my_enum(), predicate: Predicate18102098100666777803 }, TryMap { inner: Refined { inner: U8, predicate: TagPred(ENUMCONSTRAINTSTAG_CONST) }, mapper: MyEnumMapper }))),
        mapper: EnumConstraintsMapper,
    })
}

                
pub fn enum_constraints<'a>() -> (o: EnumConstraintsCombinator)
    ensures o@ == spec_enum_constraints(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EnumConstraintsCombinator(
    Mapped {
        inner: EnumConstraintsCombinator3((Refined { inner: my_enum(), predicate: Predicate1673031309162834621 }, EnumConstraintsCombinator2((Refined { inner: my_enum(), predicate: Predicate747078089795820719 }, EnumConstraintsCombinator1((Refined { inner: my_enum(), predicate: Predicate18102098100666777803 }, TryMap { inner: Refined { inner: U8, predicate: TagPred(ENUMCONSTRAINTSTAG_CONST) }, mapper: MyEnumMapper })))))),
        mapper: EnumConstraintsMapper,
    });
    // assert({
    //     &&& combinator@ == spec_enum_constraints()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_enum_constraints<'a>(input: &'a [u8]) -> (res: PResult<<EnumConstraintsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_enum_constraints().spec_parse(input@) == Some((n as int, v@)),
        spec_enum_constraints().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_enum_constraints().spec_parse(input@) is None,
        spec_enum_constraints().spec_parse(input@) is None ==> res is Err,
{
    let combinator = enum_constraints();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_enum_constraints<'a>(v: <EnumConstraintsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_enum_constraints().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_enum_constraints().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_enum_constraints().spec_serialize(v@))
        },
{
    let combinator = enum_constraints();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn enum_constraints_len<'a>(v: <EnumConstraintsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_enum_constraints().wf(v@),
        spec_enum_constraints().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_enum_constraints().spec_serialize(v@).len(),
{
    let combinator = enum_constraints();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
