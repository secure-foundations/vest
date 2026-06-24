use crate::combinators::mapped::spec::*;
use crate::combinators::recursive::exec::*;
use crate::combinators::recursive::*;
use crate::combinators::*;
use crate::core::exec::input::InputBuf;
use crate::core::exec::parser::*;
use crate::core::exec::serializer::*;
use crate::core::exec::ParseError;
use crate::core::proof::*;
use crate::core::spec::*;
use vstd::assert_seqs_equal;
use vstd::prelude::*;

verus! {

/*
 * ```vest
 * expr_kind = enum {
 *   Num   = 0x10,
 *   Group = 0x11,
 * }
 *
 * list_kind = enum {
 *   Nil  = 0x20,
 *   Cons = 0x21,
 * }
 *
 * expr = {
 *   @t: expr_kind,
 *   v: choose(@t) {
 *     Num => u8,
 *     Group => list,
 *   },
 * }
 *
 * list = {
 *   @t: list_kind,
 *   v: choose(@t) {
 *     Nil => [u8; 0],
 *     Cons => {
 *        head: expr,
 *        tail: list,
 *     },
 * }
 */
// ============================================================
// Data Types
// ============================================================
#[derive(Debug, PartialEq, Eq)]
#[verifier::ext_equal]
pub enum Expr {
    Num(u8),
    Group(Box<List>),
}

#[derive(Debug, PartialEq, Eq)]
#[verifier::ext_equal]
pub enum List {
    Nil,
    Cons(Box<Expr>, Box<List>),
}

pub type ExprSpec = Expr;

pub type ListSpec = List;

impl DeepView for Expr {
    type V = ExprSpec;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepView for List {
    type V = ListSpec;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

/*
 *  Helpers for mutual recursion
 */

#[derive(Debug, PartialEq, Eq)]
pub enum Value {
    Expr { expr: Expr },
    List { list: List },
}

#[derive(Debug, PartialEq, Eq)]
#[verifier::ext_equal]
pub enum ByteList {
    Nil,
    Cons(u8, Box<ByteList>),
}

pub type ByteListSpec = ByteList;

impl DeepView for ByteList {
    type V = ByteListSpec;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ByteListValue {
    ByteList { list: ByteList },
}

// ============================================================
// Chain Mutually Recursive Data Types
// ============================================================
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum WhichChain {
    A,
    B,
}

impl DeepView for WhichChain {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub struct ChainParam {
    pub which: WhichChain,
    pub tag: u8,
}

impl DeepView for ChainParam {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ChainA<'i> {
    End(u8),
    Step(u8, &'i [u8], u8, Box<ChainB<'i>>),
}

#[verifier::ext_equal]
pub enum ChainASpec {
    End(u8),
    Step(u8, Seq<u8>, u8, Box<ChainBSpec>),
}

pub open spec fn chain_a_view(a: &ChainA) -> ChainASpec
    decreases a,
{
    match a {
        ChainA::End(val) => ChainASpec::End(*val),
        ChainA::Step(len, payload, next_tag, tail) => ChainASpec::Step(
            *len,
            payload.deep_view(),
            *next_tag,
            Box::new(chain_b_view(tail)),
        ),
    }
}

impl<'i> DeepView for ChainA<'i> {
    type V = ChainASpec;

    open spec fn deep_view(&self) -> Self::V {
        chain_a_view(self)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ChainB<'i> {
    End(u16),
    Step(u32, u8, Box<ChainA<'i>>),
}

#[verifier::ext_equal]
pub enum ChainBSpec {
    End(u16),
    Step(u32, u8, Box<ChainASpec>),
}

pub open spec fn chain_b_view(b: &ChainB) -> ChainBSpec
    decreases b,
{
    match b {
        ChainB::End(val) => ChainBSpec::End(*val),
        ChainB::Step(payload, next_tag, tail) => ChainBSpec::Step(
            *payload,
            *next_tag,
            Box::new(chain_a_view(tail)),
        ),
    }
}

impl<'i> DeepView for ChainB<'i> {
    type V = ChainBSpec;

    open spec fn deep_view(&self) -> Self::V {
        chain_b_view(self)
    }
}

#[verifier::ext_equal]
pub enum ChainValueSpec {
    A { a: ChainASpec },
    B { b: ChainBSpec },
}

// ============================================================
// Format Specifications
// ============================================================
#[derive(Clone, Copy)]
pub struct ExprFmt<const LIMIT: usize>;

pub type ExprFmtSpec<const LIMIT: usize> = ExprProj<FixWith<LIMIT, ExprListRecBody, WhichFmt>>;

impl<const LIMIT: usize> ExprFmt<LIMIT> {
    pub open spec fn spec_inner() -> ExprFmtSpec<LIMIT> {
        expr_proj(FixWith::<LIMIT, _, _>(ExprListRecBody, WhichFmt::EXPR))
    }
}

#[derive(Clone, Copy)]
pub struct ListFmt<const LIMIT: usize>;

pub type ListFmtSpec<const LIMIT: usize> = ListProj<FixWith<LIMIT, ExprListRecBody, WhichFmt>>;

impl<const LIMIT: usize> ListFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListFmtSpec<LIMIT> {
        list_proj(FixWith::<LIMIT, _, _>(ExprListRecBody, WhichFmt::LIST))
    }
}

/*
 *  Helpers for mutual recursion
 */

pub type ExprProj<Rec> = Mapped<Refined<Rec, PredFnSpec<Value>>, FnSpecMapper<Value, ExprSpec>>;

pub type ListProj<Rec> = Mapped<Refined<Rec, PredFnSpec<Value>>, FnSpecMapper<Value, ListSpec>>;

pub open spec fn expr_proj<Rec>(rec: Rec) -> ExprProj<Rec> where Rec: SpecCombinator<T = Value> {
    Mapped {
        inner: Refined(rec, |v: Value| v is Expr),
        mapper: (
            |v: Value| -> ExprSpec { v->expr },
            |expr: ExprSpec| -> Value { Value::Expr { expr } },
        ),
    }
}

pub open spec fn list_proj<Rec>(rec: Rec) -> ListProj<Rec> where Rec: SpecCombinator<T = Value> {
    Mapped {
        inner: Refined(rec, |v: Value| v is List),
        mapper: (
            |v: Value| -> ListSpec { v->list },
            |list: ListSpec| -> Value { Value::List { list } },
        ),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum WhichFmt {
    EXPR,
    LIST,
}

impl DeepView for WhichFmt {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

pub type ExprBodyFmt<Rec> = Mapped<
    Choice<PrefixTagged<U8, U8>, PrefixTagged<U8, ListProj<Rec>>>,
    ExprMapper,
>;

pub type ListBodyFmt<Rec> = Mapped<
    Choice<PrefixTagged<U8, Empty>, PrefixTagged<U8, Pair<ExprProj<Rec>, ListProj<Rec>>>>,
    ListMapper,
>;

pub type ExprListBodyFmt<Rec> = Alt<Cond<ExprBodyFmt<Rec>>, Cond<ListBodyFmt<Rec>>>;

pub struct ExprListRecBody;

pub struct ExprRecBody;

pub struct ListRecBody;

impl SpecRecBody for ExprListRecBody {
    type Param = WhichFmt;

    type T = Value;

    type Body = ExprListBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        which: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Alt(
            Cond(which == WhichFmt::EXPR, ExprRecBody.spec_body(WhichFmt::EXPR, rec)),
            Cond(which == WhichFmt::LIST, ListRecBody.spec_body(WhichFmt::LIST, rec)),
        )
    }
}

impl SpecRecBody for ExprRecBody {
    type Param = WhichFmt;

    type T = Value;

    type Body = ExprBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        _which: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Choice(
                PrefixTagged(U8, 0x10u8, U8),
                PrefixTagged(U8, 0x11u8, list_proj(rec(WhichFmt::LIST))),
            ),
            mapper: ExprMapper,
        }
    }
}

impl SpecRecBody for ListRecBody {
    type Param = WhichFmt;

    type T = Value;

    type Body = ListBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        _which: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Choice(
                PrefixTagged(U8, 0x20u8, Empty),
                PrefixTagged(
                    U8,
                    0x21u8,
                    Pair(expr_proj(rec(WhichFmt::EXPR)), list_proj(rec(WhichFmt::LIST))),
                ),
            ),
            mapper: ListMapper,
        }
    }
}

pub struct ExprMapper;

impl SpecMapper for ExprMapper {
    type In = Sum<u8, ListSpec>;

    type Out = Value;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(n) => Value::Expr { expr: ExprSpec::Num(n) },
            Sum::Inr(list) => Value::Expr { expr: ExprSpec::Group(Box::new(list)) },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is Expr
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            Value::Expr { expr: ExprSpec::Num(n) } => Sum::Inl(n),
            Value::Expr { expr: ExprSpec::Group(list) } => Sum::Inr(*list),
            _ => arbitrary(),
        }
    }
}

pub struct ListMapper;

impl SpecMapper for ListMapper {
    type In = Sum<(), (ExprSpec, ListSpec)>;

    type Out = Value;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(_) => Value::List { list: ListSpec::Nil },
            Sum::Inr((head, tail)) => Value::List {
                list: ListSpec::Cons(Box::new(head), Box::new(tail)),
            },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is List
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            Value::List { list: ListSpec::Nil } => Sum::Inl(()),
            Value::List { list: ListSpec::Cons(head, tail) } => Sum::Inr((*head, *tail)),
            _ => arbitrary(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum WhichFmt2 {
    BYTELIST,
}

impl DeepView for WhichFmt2 {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

#[derive(Clone, Copy)]
pub struct ByteListFmt<const LIMIT: usize>;

pub type ByteListFmtSpec<const LIMIT: usize> = ByteListProj<
    FixWith<LIMIT, ByteListRecBody, WhichFmt2>,
>;

impl<const LIMIT: usize> ByteListFmt<LIMIT> {
    pub open spec fn spec_inner() -> ByteListFmtSpec<LIMIT> {
        byte_list_proj(FixWith::<LIMIT, _, _>(ByteListRecBody, WhichFmt2::BYTELIST))
    }
}

pub type ByteListProj<Rec> = Mapped<
    Refined<Rec, PredFnSpec<ByteListValue>>,
    FnSpecMapper<ByteListValue, ByteListSpec>,
>;

pub open spec fn byte_list_proj<Rec>(rec: Rec) -> ByteListProj<Rec> where
    Rec: SpecCombinator<T = ByteListValue>,
 {
    Mapped {
        inner: Refined(rec, |v: ByteListValue| v is ByteList),
        mapper: (
            |v: ByteListValue| -> ByteListSpec { v->list },
            |list: ByteListSpec| -> ByteListValue { ByteListValue::ByteList { list } },
        ),
    }
}

pub type ByteListBodyFmt<Rec> = Mapped<
    Choice<PrefixTagged<U8, Empty>, PrefixTagged<U8, Pair<U8, ByteListProj<Rec>>>>,
    ByteListMapper,
>;

pub struct ByteListRecBody;

impl SpecRecBody for ByteListRecBody {
    type Param = WhichFmt2;

    type T = ByteListValue;

    type Body = ByteListBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        _param: WhichFmt2,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Choice(
                PrefixTagged(U8, 0x20u8, Empty),
                PrefixTagged(U8, 0x21u8, Pair(U8, byte_list_proj(rec(WhichFmt2::BYTELIST)))),
            ),
            mapper: ByteListMapper,
        }
    }
}

pub struct ByteListMapper;

impl SpecMapper for ByteListMapper {
    type In = Sum<(), (u8, ByteListSpec)>;

    type Out = ByteListValue;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(_) => ByteListValue::ByteList { list: ByteListSpec::Nil },
            Sum::Inr((head, tail)) => ByteListValue::ByteList {
                list: ByteListSpec::Cons(head, Box::new(tail)),
            },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ByteList
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            ByteListValue::ByteList { list: ByteListSpec::Nil } => Sum::Inl(()),
            ByteListValue::ByteList { list: ByteListSpec::Cons(head, tail) } => Sum::Inr(
                (head, *tail),
            ),
        }
    }
}

// ============================================================
// Chain Mutually Recursive Format Specifications
// ============================================================
#[derive(Clone, Copy)]
pub struct ChainAFmt<const LIMIT: usize> {
    pub tag: u8,
}

pub type ChainAFmtSpec<const LIMIT: usize> = ChainAProj<FixWith<LIMIT, ChainRecBody, ChainParam>>;

impl<const LIMIT: usize> ChainAFmt<LIMIT> {
    pub open spec fn spec_inner(&self) -> ChainAFmtSpec<LIMIT> {
        chain_a_proj(
            FixWith::<LIMIT, _, _>(
                ChainRecBody,
                ChainParam { which: WhichChain::A, tag: self.tag },
            ),
        )
    }
}

#[derive(Clone, Copy)]
pub struct ChainBFmt<const LIMIT: usize> {
    pub tag: u8,
}

pub type ChainBFmtSpec<const LIMIT: usize> = ChainBProj<FixWith<LIMIT, ChainRecBody, ChainParam>>;

impl<const LIMIT: usize> ChainBFmt<LIMIT> {
    pub open spec fn spec_inner(&self) -> ChainBFmtSpec<LIMIT> {
        chain_b_proj(
            FixWith::<LIMIT, _, _>(
                ChainRecBody,
                ChainParam { which: WhichChain::B, tag: self.tag },
            ),
        )
    }
}

pub type ChainAProj<Rec> = Mapped<
    Refined<Rec, PredFnSpec<ChainValueSpec>>,
    FnSpecMapper<ChainValueSpec, ChainASpec>,
>;

pub type ChainBProj<Rec> = Mapped<
    Refined<Rec, PredFnSpec<ChainValueSpec>>,
    FnSpecMapper<ChainValueSpec, ChainBSpec>,
>;

pub open spec fn chain_a_proj<Rec>(rec: Rec) -> ChainAProj<Rec> where
    Rec: SpecCombinator<T = ChainValueSpec>,
 {
    Mapped {
        inner: Refined(rec, |v: ChainValueSpec| v is A),
        mapper: (
            |v: ChainValueSpec| -> ChainASpec { v->a },
            |a: ChainASpec| -> ChainValueSpec { ChainValueSpec::A { a } },
        ),
    }
}

pub open spec fn chain_b_proj<Rec>(rec: Rec) -> ChainBProj<Rec> where
    Rec: SpecCombinator<T = ChainValueSpec>,
 {
    Mapped {
        inner: Refined(rec, |v: ChainValueSpec| v is B),
        mapper: (
            |v: ChainValueSpec| -> ChainBSpec { v->b },
            |b: ChainBSpec| -> ChainValueSpec { ChainValueSpec::B { b } },
        ),
    }
}

pub type ChainABodyFmt<Rec> = Mapped<
    Sum<
        Refined<U8, PredFnSpec<u8>>,
        Bind<U8, spec_fn(u8) -> Pair<Varied<u8>, Bind<U8, spec_fn(u8) -> ChainBProj<Rec>>>>,
    >,
    ChainAMapper,
>;

pub type ChainBBodyFmt<Rec> = Mapped<
    Sum<Refined<U16Le, PredFnSpec<u16>>, Pair<U32Le, Bind<U8, spec_fn(u8) -> ChainAProj<Rec>>>>,
    ChainBMapper,
>;

pub type ChainBodyFmt<Rec> = Alt<Cond<ChainABodyFmt<Rec>>, Cond<ChainBBodyFmt<Rec>>>;

pub struct ChainRecBody;

impl SpecRecBody for ChainRecBody {
    type Param = ChainParam;

    type T = ChainValueSpec;

    type Body = ChainBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Alt(
            Cond(param.which == WhichChain::A, ChainABodyRec.spec_body(param, rec)),
            Cond(param.which == WhichChain::B, ChainBBodyRec.spec_body(param, rec)),
        )
    }
}

pub struct ChainABodyRec;

impl SpecRecBody for ChainABodyRec {
    type Param = ChainParam;

    type T = ChainValueSpec;

    type Body = ChainABodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.tag {
                0u8 => Sum::Inl(Refined(U8, |val: u8| val >= 1 && val <= 10)),
                _ => Sum::Inr(
                    Bind(
                        U8,
                        |len: u8|
                            {
                                Pair(
                                    Varied::<u8>(len),
                                    Bind(
                                        U8,
                                        |next_tag: u8|
                                            chain_b_proj(
                                                rec(
                                                    ChainParam {
                                                        which: WhichChain::B,
                                                        tag: next_tag,
                                                    },
                                                ),
                                            ),
                                    ),
                                )
                            },
                    ),
                ),
            },
            mapper: ChainAMapper,
        }
    }
}

pub struct ChainBBodyRec;

impl SpecRecBody for ChainBBodyRec {
    type Param = ChainParam;

    type T = ChainValueSpec;

    type Body = ChainBBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.tag {
                0u8 => Sum::Inl(Refined(U16Le, |val: u16| val >= 256)),
                _ => Sum::Inr(
                    Pair(
                        U32Le,
                        Bind(
                            U8,
                            |next_tag: u8|
                                chain_a_proj(
                                    rec(ChainParam { which: WhichChain::A, tag: next_tag }),
                                ),
                        ),
                    ),
                ),
            },
            mapper: ChainBMapper,
        }
    }
}

pub struct ChainAMapper;

impl SpecMapper for ChainAMapper {
    type In = Sum<u8, (u8, (Seq<u8>, (u8, ChainBSpec)))>;

    type Out = ChainValueSpec;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(val) => ChainValueSpec::A { a: ChainASpec::End(val) },
            Sum::Inr((len, (payload, (next_tag, tail)))) => ChainValueSpec::A {
                a: ChainASpec::Step(len, payload, next_tag, Box::new(tail)),
            },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is A
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            ChainValueSpec::A { a: ChainASpec::End(val) } => Sum::Inl(val),
            ChainValueSpec::A { a: ChainASpec::Step(len, payload, next_tag, tail) } => {
                Sum::Inr((len, (payload, (next_tag, *tail))))
            },
            _ => arbitrary(),
        }
    }
}

pub struct ChainBMapper;

impl SpecMapper for ChainBMapper {
    type In = Sum<u16, (u32, (u8, ChainASpec))>;

    type Out = ChainValueSpec;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(val) => ChainValueSpec::B { b: ChainBSpec::End(val) },
            Sum::Inr((payload, (next_tag, tail))) => ChainValueSpec::B {
                b: ChainBSpec::Step(payload, next_tag, Box::new(tail)),
            },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is B
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            ChainValueSpec::B { b: ChainBSpec::End(val) } => Sum::Inl(val),
            ChainValueSpec::B { b: ChainBSpec::Step(payload, next_tag, tail) } => {
                Sum::Inr((payload, (next_tag, *tail)))
            },
            _ => arbitrary(),
        }
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_spec_proof {
    use super::*;

    impl<const LIMIT: usize> SpecParser for ExprFmt<LIMIT> {
        type PVal = ExprSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ExprFmt<LIMIT> {
        type Val = ExprSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ExprFmt<LIMIT> {
        type T = ExprSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ExprFmt<LIMIT> {
        type SValue = ExprSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ExprFmt<LIMIT> {
        type SVal = ExprSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ListFmt<LIMIT> {
        type PVal = ListSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ListFmt<LIMIT> {
        type Val = ListSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ListFmt<LIMIT> {
        type T = ListSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ListFmt<LIMIT> {
        type SValue = ListSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ListFmt<LIMIT> {
        type SVal = ListSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    // ============================================================
    // Proven Format Properties
    // ============================================================
    impl<const LIMIT: usize> SafeParser for ExprFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ExprFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ExprFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ExprFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ExprFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ExprFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ExprFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ExprFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for ListFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ListFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ListFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ListFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ListFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ListFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ListFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ListFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    /*
 *  Helpers for mutual recursion
 */

    impl LossyMapper for ExprMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ExprMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl LossyMapper for ListMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ListMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl StrictRecBody for ExprRecBody {
        proof fn lemma_body_all_inv_preservation(
            &self,
            param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use crate::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListRecBody {
        proof fn lemma_body_all_inv_preservation(
            &self,
            param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use crate::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ExprListRecBody {
        proof fn lemma_body_all_inv_preservation(
            &self,
            param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            hide(<ExprRecBody as SpecRecBody>::spec_body);
            hide(<ListRecBody as SpecRecBody>::spec_body);
            broadcast use crate::combinators::disjoint::disjointness_lemmas;

            ExprRecBody.lemma_body_all_inv_preservation(WhichFmt::EXPR, rec);
            ListRecBody.lemma_body_all_inv_preservation(WhichFmt::LIST, rec);
        }
    }

    impl<const LIMIT: usize> SpecParser for ByteListFmt<LIMIT> {
        type PVal = ByteListSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ByteListFmt<LIMIT> {
        type Val = ByteListSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ByteListFmt<LIMIT> {
        type T = ByteListSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ByteListFmt<LIMIT> {
        type SValue = ByteListSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ByteListFmt<LIMIT> {
        type SVal = ByteListSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SafeParser for ByteListFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ByteListFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ByteListFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ByteListFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ByteListFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ByteListFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ByteListFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ByteListFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl LossyMapper for ByteListMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ByteListMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl StrictRecBody for ByteListRecBody {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use crate::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl<const LIMIT: usize> SpecParser for ChainAFmt<LIMIT> {
        type PVal = ChainASpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ChainAFmt<LIMIT> {
        type Val = ChainASpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self).consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ChainAFmt<LIMIT> {
        type T = ChainASpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self).byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ChainAFmt<LIMIT> {
        type SValue = ChainASpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self).spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ChainAFmt<LIMIT> {
        type SVal = ChainASpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self).spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ChainBFmt<LIMIT> {
        type PVal = ChainBSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ChainBFmt<LIMIT> {
        type Val = ChainBSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self).consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ChainBFmt<LIMIT> {
        type T = ChainBSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self).byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ChainBFmt<LIMIT> {
        type SValue = ChainBSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self).spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ChainBFmt<LIMIT> {
        type SVal = ChainBSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self).spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SafeParser for ChainAFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner(self).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ChainAFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ChainAFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ChainAFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self);
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ChainAFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ChainAFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ChainAFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ChainAFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self);
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for ChainBFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner(self).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ChainBFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ChainBFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ChainBFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self);
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ChainBFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ChainBFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ChainBFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self);
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ChainBFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self);
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl LossyMapper for ChainAMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ChainAMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl LossyMapper for ChainBMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ChainBMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl StrictRecBody for ChainABodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use crate::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ChainBBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use crate::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ChainRecBody {
        proof fn lemma_body_all_inv_preservation(
            &self,
            param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            hide(<ChainABodyRec as SpecRecBody>::spec_body);
            hide(<ChainBBodyRec as SpecRecBody>::spec_body);
            broadcast use crate::combinators::disjoint::disjointness_lemmas;

            ChainABodyRec.lemma_body_all_inv_preservation(param, rec);
            ChainBBodyRec.lemma_body_all_inv_preservation(param, rec);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
impl<const LIMIT: usize> ExprFmt<LIMIT> {
    fn parse_gas(&self, gas: usize, ibuf: &&[u8]) -> (r: PResult<Expr>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, WhichFmt>(ExprListRecBody, WhichFmt::EXPR).spec_parse_gas(
                    gas as nat,
                    WhichFmt::EXPR,
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->expr)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        let (n1, tag) = U8.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        match tag {
            0x10u8 => {
                let (n2, n) = U8.parse(&rest)?;
                Ok((n1 + n2, Expr::Num(n)))
            },
            0x11u8 => {
                if gas > 0 {
                    let (n2, list) = ListFmt::<LIMIT>.parse_gas(gas - 1, &rest)?;

                    Ok((n1 + n2, Expr::Group(Box::new(list))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
            _ => { Err(ParseError::invalid_tag()) },
        }
    }

    fn serialize_gas(&self, gas: usize, v: &Expr, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ExprListRecBody, WhichFmt>(ExprListRecBody, WhichFmt::EXPR).consistent_gas(
                gas as nat,
                WhichFmt::EXPR,
                Value::Expr { expr: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                WhichFmt,
            >(ExprListRecBody, WhichFmt::EXPR).spec_serialize_gas(gas as nat, WhichFmt::EXPR, Value::Expr { expr: v.deep_view() }),
        decreases gas,
    {
        match v {
            Expr::Num(n) => {
                U8.serialize(&0x10u8, obuf);
                U8.serialize(n, obuf);
            },
            Expr::Group(list) => {
                U8.serialize(&0x11u8, obuf);
                ListFmt::<LIMIT>.serialize_gas(gas - 1, list, obuf);
            },
        }
    }

    fn prepare_gas(&self, gas: usize, v: &Expr) -> (checked: Result<usize, PreSerializeError>)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, WhichFmt>(ExprListRecBody, WhichFmt::EXPR).consistent_gas(
                    gas as nat,
                    WhichFmt::EXPR,
                    Value::Expr { expr: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, WhichFmt>(ExprListRecBody, WhichFmt::EXPR).byte_len_gas(
                    gas as nat,
                    WhichFmt::EXPR,
                    Value::Expr { expr: v.deep_view() },
                )
            },
        decreases gas,
    {
        match v {
            Expr::Num(n) => {
                let l1 = U8.prepare(&0x10u8)?;
                let l2 = U8.prepare(n)?;
                let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                Ok(total)
            },
            Expr::Group(list) => {
                let l1 = U8.prepare(&0x11u8)?;
                if gas == 0 {
                    return Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    );
                }
                let l2 = ListFmt::<LIMIT>.prepare_gas(gas - 1, list)?;
                let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                Ok(total)
            },
        }
    }
}

impl<const LIMIT: usize> ListFmt<LIMIT> {
    fn parse_gas(&self, gas: usize, ibuf: &&[u8]) -> (r: PResult<List>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, WhichFmt>(ExprListRecBody, WhichFmt::LIST).spec_parse_gas(
                    gas as nat,
                    WhichFmt::LIST,
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->list)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        let (n1, tag) = U8.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        match tag {
            0x20u8 => { Ok((n1, List::Nil)) },
            0x21u8 => {
                if gas > 0 {
                    let (n2, head) = ExprFmt::<LIMIT>.parse_gas(gas - 1, &rest)?;
                    let rest = rest.skip(n2);
                    let (n3, tail) = self.parse_gas(gas - 1, &rest)?;
                    Ok((n1 + n2 + n3, List::Cons(Box::new(head), Box::new(tail))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
            _ => { Err(ParseError::invalid_tag()) },
        }
    }

    fn serialize_gas(&self, gas: usize, v: &List, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ExprListRecBody, WhichFmt>(ExprListRecBody, WhichFmt::LIST).consistent_gas(
                gas as nat,
                WhichFmt::LIST,
                Value::List { list: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                WhichFmt,
            >(ExprListRecBody, WhichFmt::LIST).spec_serialize_gas(gas as nat, WhichFmt::LIST, Value::List { list: v.deep_view() }),
        decreases gas,
    {
        match v {
            List::Nil => {
                U8.serialize(&0x20u8, obuf);
            },
            List::Cons(head, tail) => {
                U8.serialize(&0x21u8, obuf);
                ExprFmt::<LIMIT>.serialize_gas(gas - 1, head, obuf);
                self.serialize_gas(gas - 1, tail, obuf);
            },
        }
    }

    fn prepare_gas(&self, gas: usize, v: &List) -> (checked: Result<usize, PreSerializeError>)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, WhichFmt>(ExprListRecBody, WhichFmt::LIST).consistent_gas(
                    gas as nat,
                    WhichFmt::LIST,
                    Value::List { list: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, WhichFmt>(ExprListRecBody, WhichFmt::LIST).byte_len_gas(
                    gas as nat,
                    WhichFmt::LIST,
                    Value::List { list: v.deep_view() },
                )
            },
        decreases gas,
    {
        match v {
            List::Nil => {
                let total = U8.prepare(&0x20u8)?;
                Ok(total)
            },
            List::Cons(head, tail) => {
                let l1 = U8.prepare(&0x21u8)?;
                if gas == 0 {
                    return Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    );
                }
                let l2 = ExprFmt::<LIMIT>.prepare_gas(gas - 1, head)?;
                let l3 = self.prepare_gas(gas - 1, tail)?;
                let total = l1.checked_add(l2).ok_or(
                    PreSerializeError::length_too_large(),
                )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
                Ok(total)
            },
        }
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ExprFmt<LIMIT> {
    type PT = Expr;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<const LIMIT: usize> Serializer<Expr> for ExprFmt<LIMIT> {
    fn serialize(&self, v: &Expr, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<const LIMIT: usize> Prepare<Expr> for ExprFmt<LIMIT> {
    fn prepare(&self, v: &Expr) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ListFmt<LIMIT> {
    type PT = List;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<const LIMIT: usize> Serializer<List> for ListFmt<LIMIT> {
    fn serialize(&self, v: &List, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<const LIMIT: usize> Prepare<List> for ListFmt<LIMIT> {
    fn prepare(&self, v: &List) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<const LIMIT: usize> ByteListFmt<LIMIT> {
    fn parse_gas(&self, gas: usize, ibuf: &&[u8]) -> (r: PResult<ByteList>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ByteListRecBody, WhichFmt2>(ByteListRecBody, WhichFmt2::BYTELIST).spec_parse_gas(
                    gas as nat,
                    WhichFmt2::BYTELIST,
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->list)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        let (n1, tag) = U8.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        match tag {
            0x20u8 => { Ok((n1, ByteList::Nil)) },
            0x21u8 => {
                if gas > 0 {
                    let (n2, head) = U8.parse(&rest)?;
                    let rest2 = rest.skip(n2);
                    let (n3, tail) = self.parse_gas(gas - 1, &rest2)?;
                    Ok((n1 + n2 + n3, ByteList::Cons(head, Box::new(tail))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
            _ => { Err(ParseError::invalid_tag()) },
        }
    }

    fn serialize_gas(&self, gas: usize, v: &ByteList, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ByteListRecBody, WhichFmt2>(ByteListRecBody, WhichFmt2::BYTELIST).consistent_gas(
                gas as nat,
                WhichFmt2::BYTELIST,
                ByteListValue::ByteList { list: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ByteListRecBody,
                WhichFmt2,
            >(ByteListRecBody, WhichFmt2::BYTELIST).spec_serialize_gas(
                gas as nat,
                WhichFmt2::BYTELIST,
                ByteListValue::ByteList { list: v.deep_view() },
            ),
        decreases gas,
    {
        match v {
            ByteList::Nil => {
                U8.serialize(&0x20u8, obuf);
            },
            ByteList::Cons(head, tail) => {
                U8.serialize(&0x21u8, obuf);
                U8.serialize(head, obuf);
                self.serialize_gas(gas - 1, tail, obuf);
            },
        }
    }

    fn prepare_gas(&self, gas: usize, v: &ByteList) -> (checked: Result<usize, PreSerializeError>)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ByteListRecBody, WhichFmt2>(ByteListRecBody, WhichFmt2::BYTELIST).consistent_gas(
                    gas as nat,
                    WhichFmt2::BYTELIST,
                    ByteListValue::ByteList { list: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ByteListRecBody, WhichFmt2>(ByteListRecBody, WhichFmt2::BYTELIST).byte_len_gas(
                    gas as nat,
                    WhichFmt2::BYTELIST,
                    ByteListValue::ByteList { list: v.deep_view() },
                )
            },
        decreases gas,
    {
        match v {
            ByteList::Nil => {
                let total = U8.prepare(&0x20u8)?;
                Ok(total)
            },
            ByteList::Cons(head, tail) => {
                let l1 = U8.prepare(&0x21u8)?;
                let l2 = U8.prepare(head)?;
                if gas == 0 {
                    return Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    );
                }
                let l3 = self.prepare_gas(gas - 1, tail)?;
                let sum1 = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                let total = sum1.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
                Ok(total)
            },
        }
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ByteListFmt<LIMIT> {
    type PT = ByteList;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<const LIMIT: usize> Serializer<ByteList> for ByteListFmt<LIMIT> {
    fn serialize(&self, v: &ByteList, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<const LIMIT: usize> Prepare<ByteList> for ByteListFmt<LIMIT> {
    fn prepare(&self, v: &ByteList) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<const LIMIT: usize> ChainAFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ChainA<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ChainRecBody, ChainParam>(ChainRecBody, ChainParam { which: WhichChain::A, tag: self.tag }).spec_parse_gas(
                    gas as nat,
                    ChainParam { which: WhichChain::A, tag: self.tag },
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->a)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        match self.tag {
            0u8 => {
                let (n1, val) = U8.parse(ibuf)?;
                if val >= 1 && val <= 10 {
                    Ok((n1, ChainA::End(val)))
                } else {
                    Err(ParseError::cond_rejected())
                }
            },
            _ => {
                let (n1, len) = U8.parse(ibuf)?;
                let rest = ibuf.skip(n1);
                let (n2, payload) = Varied(len).parse(&rest)?;
                let rest2 = rest.skip(n2);
                let (n3, next_tag) = U8.parse(&rest2)?;
                let rest3 = rest2.skip(n3);
                if gas > 0 {
                    let (n4, tail) = ChainBFmt::<LIMIT> { tag: next_tag }.parse_gas(
                        gas - 1,
                        &rest3,
                    )?;
                    Ok((n1 + n2 + n3 + n4, ChainA::Step(len, payload, next_tag, Box::new(tail))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
        }
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &ChainA<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ChainRecBody, ChainParam>(ChainRecBody, ChainParam { which: WhichChain::A, tag: self.tag }).consistent_gas(
                gas as nat,
                ChainParam { which: WhichChain::A, tag: self.tag },
                ChainValueSpec::A { a: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ChainRecBody,
                ChainParam,
            >(ChainRecBody, ChainParam { which: WhichChain::A, tag: self.tag }).spec_serialize_gas(
                gas as nat,
                ChainParam { which: WhichChain::A, tag: self.tag },
                ChainValueSpec::A { a: v.deep_view() },
            ),
        decreases gas,
    {
        match v {
            ChainA::End(val) => {
                U8.serialize(val, obuf);
            },
            ChainA::Step(len, payload, next_tag, tail) => {
                U8.serialize(len, obuf);
                Varied(*len).serialize(payload, obuf);
                U8.serialize(next_tag, obuf);
                ChainBFmt::<LIMIT> { tag: *next_tag }.serialize_gas(gas - 1, tail, obuf);
            },
        }
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &ChainA<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ChainRecBody, ChainParam>(ChainRecBody, ChainParam { which: WhichChain::A, tag: self.tag }).consistent_gas(
                    gas as nat,
                    ChainParam { which: WhichChain::A, tag: self.tag },
                    ChainValueSpec::A { a: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ChainRecBody, ChainParam>(ChainRecBody, ChainParam { which: WhichChain::A, tag: self.tag }).byte_len_gas(
                    gas as nat,
                    ChainParam { which: WhichChain::A, tag: self.tag },
                    ChainValueSpec::A { a: v.deep_view() },
                )
            },
        decreases gas,
    {
        match v {
            ChainA::End(val) => {
                if self.tag == 0u8 && *val >= 1 && *val <= 10 {
                    U8.prepare(val)
                } else {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::CondRejected))
                }
            },
            ChainA::Step(len, payload, next_tag, tail) => {
                if self.tag == 0u8 {
                    return Err(PreSerializeError::not_compliant(ComplianceErrorKind::CondRejected));
                }
                let l1 = U8.prepare(len)?;
                let l2 = Varied(*len).prepare(payload)?;
                let l3 = U8.prepare(next_tag)?;
                if gas == 0 {
                    return Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    );
                }
                let l4 = ChainBFmt::<LIMIT> { tag: *next_tag }.prepare_gas(gas - 1, tail)?;
                let sum1 = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                let sum2 = sum1.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
                let total = sum2.checked_add(l4).ok_or(PreSerializeError::length_too_large())?;
                Ok(total)
            },
        }
    }
}

impl<const LIMIT: usize> ChainBFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ChainB<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ChainRecBody, ChainParam>(ChainRecBody, ChainParam { which: WhichChain::B, tag: self.tag }).spec_parse_gas(
                    gas as nat,
                    ChainParam { which: WhichChain::B, tag: self.tag },
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->b)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        match self.tag {
            0u8 => {
                let (n1, val) = U16Le.parse(ibuf)?;
                if val >= 256 {
                    Ok((n1, ChainB::End(val)))
                } else {
                    Err(ParseError::cond_rejected())
                }
            },
            _ => {
                let (n1, payload) = U32Le.parse(ibuf)?;
                let rest = ibuf.skip(n1);
                let (n2, next_tag) = U8.parse(&rest)?;
                let rest2 = rest.skip(n2);
                if gas > 0 {
                    let (n3, tail) = ChainAFmt::<LIMIT> { tag: next_tag }.parse_gas(
                        gas - 1,
                        &rest2,
                    )?;
                    Ok((n1 + n2 + n3, ChainB::Step(payload, next_tag, Box::new(tail))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
        }
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &ChainB<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ChainRecBody, ChainParam>(ChainRecBody, ChainParam { which: WhichChain::B, tag: self.tag }).consistent_gas(
                gas as nat,
                ChainParam { which: WhichChain::B, tag: self.tag },
                ChainValueSpec::B { b: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ChainRecBody,
                ChainParam,
            >(ChainRecBody, ChainParam { which: WhichChain::B, tag: self.tag }).spec_serialize_gas(
                gas as nat,
                ChainParam { which: WhichChain::B, tag: self.tag },
                ChainValueSpec::B { b: v.deep_view() },
            ),
        decreases gas,
    {
        match v {
            ChainB::End(val) => {
                U16Le.serialize(val, obuf);
            },
            ChainB::Step(payload, next_tag, tail) => {
                U32Le.serialize(payload, obuf);
                U8.serialize(next_tag, obuf);
                ChainAFmt::<LIMIT> { tag: *next_tag }.serialize_gas(gas - 1, tail, obuf);
            },
        }
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &ChainB<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ChainRecBody, ChainParam>(ChainRecBody, ChainParam { which: WhichChain::B, tag: self.tag }).consistent_gas(
                    gas as nat,
                    ChainParam { which: WhichChain::B, tag: self.tag },
                    ChainValueSpec::B { b: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ChainRecBody, ChainParam>(ChainRecBody, ChainParam { which: WhichChain::B, tag: self.tag }).byte_len_gas(
                    gas as nat,
                    ChainParam { which: WhichChain::B, tag: self.tag },
                    ChainValueSpec::B { b: v.deep_view() },
                )
            },
        decreases gas,
    {
        match v {
            ChainB::End(val) => {
                if self.tag == 0u8 && *val >= 256 {
                    U16Le.prepare(val)
                } else {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::CondRejected))
                }
            },
            ChainB::Step(payload, next_tag, tail) => {
                if self.tag == 0u8 {
                    return Err(PreSerializeError::not_compliant(ComplianceErrorKind::CondRejected));
                }
                let l1 = U32Le.prepare(payload)?;
                let l2 = U8.prepare(next_tag)?;
                if gas == 0 {
                    return Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    );
                }
                let l3 = ChainAFmt::<LIMIT> { tag: *next_tag }.prepare_gas(gas - 1, tail)?;
                let sum1 = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                let total = sum1.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
                Ok(total)
            },
        }
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ChainAFmt<LIMIT> {
    type PT = ChainA<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<'i, const LIMIT: usize> Serializer<ChainA<'i>> for ChainAFmt<LIMIT> {
    fn serialize(&self, v: &ChainA<'i>, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<'i, const LIMIT: usize> Prepare<ChainA<'i>> for ChainAFmt<LIMIT> {
    fn prepare(&self, v: &ChainA<'i>) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ChainBFmt<LIMIT> {
    type PT = ChainB<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<'i, const LIMIT: usize> Serializer<ChainB<'i>> for ChainBFmt<LIMIT> {
    fn serialize(&self, v: &ChainB<'i>, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<'i, const LIMIT: usize> Prepare<ChainB<'i>> for ChainBFmt<LIMIT> {
    fn prepare(&self, v: &ChainB<'i>) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chain_mutual_exec_roundtrip() {
        let payload: &[u8] = &[10, 20, 30];
        let chain = ChainA::Step(
            3,
            payload,
            1,
            Box::new(ChainB::Step(0x12345678, 0, Box::new(ChainA::End(5)))),
        );

        let fmt = ChainAFmt::<10> { tag: 1 };
        let mut obuf = Vec::new();
        fmt.serialize(&chain, &mut obuf);
        assert_eq!(obuf, vec![3, 10, 20, 30, 1, 0x78, 0x56, 0x34, 0x12, 0, 5]);

        let mut ibuf = obuf.as_slice();
        let (n, parsed) = fmt.parse(&&mut ibuf).unwrap();
        assert_eq!(n, 11);
        assert_eq!(parsed, chain);
    }
}
