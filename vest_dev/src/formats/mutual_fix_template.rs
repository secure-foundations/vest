use crate::combinators::mapped::spec::*;
use crate::combinators::recursive::exec::*;
use crate::combinators::recursive::*;
use crate::combinators::*;
use crate::core::exec::input::InputBuf;
use crate::core::exec::parser::*;
use crate::core::exec::serializer::*;
use crate::core::exec::DeepEq;
use crate::core::exec::ParseError;
use crate::core::exec::SelfView;
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
# [doc = "data type for `expr_kind`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum ExprKind {
    Num = 16,
    Group = 17,
}

pub type ExprKindSpec = ExprKind;

pub type ExprKindInner = u8;

impl DeepView for ExprKind {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepEq for ExprKind {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for ExprKind {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `list_kind`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum ListKind {
    Nil = 32,
    Cons = 33,
}

pub type ListKindSpec = ListKind;

pub type ListKindInner = u8;

impl DeepView for ListKind {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepEq for ListKind {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for ListKind {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `expr`."]
# [derive (Debug, PartialEq, Eq)]
pub struct Expr<'i> {
    pub t: ExprKind,
    pub v: Box<ExprV<'i>>,
}

# [verifier::ext_equal]
pub struct ExprSpec {
    pub t: ExprKindSpec,
    pub v: Box<ExprVSpec>,
}

pub type ExprInner = (ExprKindSpec, Box<ExprVSpec>);

pub open spec fn expr_view(x: &Expr) -> ExprSpec
    decreases *x,
{
    ExprSpec { t: x.t.deep_view(), v: Box::new(expr_v_view(&*x.v)) }
}

impl<'i> DeepView for Expr<'i> {
    type V = ExprSpec;

    open spec fn deep_view(&self) -> Self::V {
        expr_view(self)
    }
}

# [doc = "data type for `list`."]
# [derive (Debug, PartialEq, Eq)]
pub struct List<'i> {
    pub t: ListKind,
    pub v: Box<ListV<'i>>,
}

# [verifier::ext_equal]
pub struct ListSpec {
    pub t: ListKindSpec,
    pub v: Box<ListVSpec>,
}

pub type ListInner = (ListKindSpec, Box<ListVSpec>);

pub open spec fn list_view(x: &List) -> ListSpec
    decreases *x,
{
    ListSpec { t: x.t.deep_view(), v: Box::new(list_v_view(&*x.v)) }
}

impl<'i> DeepView for List<'i> {
    type V = ListSpec;

    open spec fn deep_view(&self) -> Self::V {
        list_view(self)
    }
}

# [doc = "data type for `expr_v`."]
# [derive (Debug, PartialEq, Eq)]
pub enum ExprV<'i> {
    Num(u8),
    Group(Box<List<'i>>),
}

# [verifier::ext_equal]
pub enum ExprVSpec {
    Num(u8),
    Group(Box<ListSpec>),
}

pub type ExprVInner = Sum<u8, Box<ListSpec>>;

pub open spec fn expr_v_view(x: &ExprV) -> ExprVSpec
    decreases *x,
{
    match x {
        ExprV::Num(v) => ExprVSpec::Num(v.deep_view()),
        ExprV::Group(v) => ExprVSpec::Group(Box::new(list_view(&**v))),
    }
}

impl<'i> DeepView for ExprV<'i> {
    type V = ExprVSpec;

    open spec fn deep_view(&self) -> Self::V {
        expr_v_view(self)
    }
}

# [doc = "data type for `list_v_cons`."]
# [derive (Debug, PartialEq, Eq)]
pub struct ListVCons<'i> {
    pub head: Box<Expr<'i>>,
    pub tail: Box<List<'i>>,
}

# [verifier::ext_equal]
pub struct ListVConsSpec {
    pub head: Box<ExprSpec>,
    pub tail: Box<ListSpec>,
}

pub type ListVConsInner = (Box<ExprSpec>, Box<ListSpec>);

pub open spec fn list_v_cons_view(x: &ListVCons) -> ListVConsSpec
    decreases *x,
{
    ListVConsSpec { head: Box::new(expr_view(&*x.head)), tail: Box::new(list_view(&*x.tail)) }
}

impl<'i> DeepView for ListVCons<'i> {
    type V = ListVConsSpec;

    open spec fn deep_view(&self) -> Self::V {
        list_v_cons_view(self)
    }
}

# [doc = "data type for `list_v`."]
# [derive (Debug, PartialEq, Eq)]
pub enum ListV<'i> {
    Nil(&'i [u8]),
    Cons(Box<ListVCons<'i>>),
}

# [verifier::ext_equal]
pub enum ListVSpec {
    Nil(Seq<u8>),
    Cons(Box<ListVConsSpec>),
}

pub type ListVInner = Sum<Seq<u8>, Box<ListVConsSpec>>;

pub open spec fn list_v_view(x: &ListV) -> ListVSpec
    decreases *x,
{
    match x {
        ListV::Nil(v) => ListVSpec::Nil(v.deep_view()),
        ListV::Cons(v) => ListVSpec::Cons(Box::new(list_v_cons_view(&**v))),
    }
}

impl<'i> DeepView for ListV<'i> {
    type V = ListVSpec;

    open spec fn deep_view(&self) -> Self::V {
        list_v_view(self)
    }
}

# [verifier::ext_equal]
pub enum SCC1 {
    Expr { expr: ExprSpec },
    List { list: ListSpec },
    ExprV { expr_v: ExprVSpec },
    ListVCons { list_v_cons: ListVConsSpec },
    ListV { list_v: ListVSpec },
}

# [derive (Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum WhichSCC1 {
    EXPR,
    LIST,
    EXPRV,
    LISTVCONS,
    LISTV,
}

impl DeepView for WhichSCC1 {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [derive (Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub struct ExprListParam {
    pub which: WhichSCC1,
    pub expr_kind: ExprKind,
    pub list_kind: ListKind,
}

impl DeepView for ExprListParam {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
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
# [doc = "named format combinator for `expr_kind`."]
# [derive (Clone, Copy)]
pub struct ExprKindFmt;

pub type ExprKindFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<ExprKindInner, ExprKindSpec>>,
>;

impl ExprKindFmt {
    # [doc = "specification constructor for `expr_kind`."]
    pub open spec fn spec_inner() -> ExprKindFmtSpec {
        Named(
            "expr_kind",
            Mapped {
                inner: Refined(U8, |x: u8| (x == 16) || (x == 17)),
                mapper: (
                    |parsed: ExprKindInner| -> ExprKindSpec
                        {
                            match parsed {
                                16 => ExprKindSpec::Num,
                                17 => ExprKindSpec::Group,
                                _ => arbitrary(),
                            }
                        },
                    |value: ExprKindSpec| -> ExprKindInner
                        {
                            match value {
                                ExprKindSpec::Num => 16,
                                ExprKindSpec::Group => 17,
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `list_kind`."]
# [derive (Clone, Copy)]
pub struct ListKindFmt;

pub type ListKindFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<ListKindInner, ListKindSpec>>,
>;

impl ListKindFmt {
    # [doc = "specification constructor for `list_kind`."]
    pub open spec fn spec_inner() -> ListKindFmtSpec {
        Named(
            "list_kind",
            Mapped {
                inner: Refined(U8, |x: u8| (x == 32) || (x == 33)),
                mapper: (
                    |parsed: ListKindInner| -> ListKindSpec
                        {
                            match parsed {
                                32 => ListKindSpec::Nil,
                                33 => ListKindSpec::Cons,
                                _ => arbitrary(),
                            }
                        },
                    |value: ListKindSpec| -> ListKindInner
                        {
                            match value {
                                ListKindSpec::Nil => 32,
                                ListKindSpec::Cons => 33,
                            }
                        },
                ),
            },
        )
    }
}

pub type ExprProj<Rec> = Mapped<Refined<Rec, PredFnSpec<SCC1>>, FnSpecMapper<SCC1, ExprSpec>>;

pub open spec fn expr_proj<Rec>(rec: Rec) -> ExprProj<Rec> where Rec: SpecCombinator<T = SCC1> {
    Mapped {
        inner: Refined(rec, |v: SCC1| v is Expr),
        mapper: (
            |v: SCC1| -> ExprSpec { v->expr },
            |expr: ExprSpec| -> SCC1 { SCC1::Expr { expr } },
        ),
    }
}

pub type ListProj<Rec> = Mapped<Refined<Rec, PredFnSpec<SCC1>>, FnSpecMapper<SCC1, ListSpec>>;

pub open spec fn list_proj<Rec>(rec: Rec) -> ListProj<Rec> where Rec: SpecCombinator<T = SCC1> {
    Mapped {
        inner: Refined(rec, |v: SCC1| v is List),
        mapper: (
            |v: SCC1| -> ListSpec { v->list },
            |list: ListSpec| -> SCC1 { SCC1::List { list } },
        ),
    }
}

pub type ExprVProj<Rec> = Mapped<Refined<Rec, PredFnSpec<SCC1>>, FnSpecMapper<SCC1, ExprVSpec>>;

pub open spec fn expr_v_proj<Rec>(rec: Rec) -> ExprVProj<Rec> where Rec: SpecCombinator<T = SCC1> {
    Mapped {
        inner: Refined(rec, |v: SCC1| v is ExprV),
        mapper: (
            |v: SCC1| -> ExprVSpec { v->expr_v },
            |expr_v: ExprVSpec| -> SCC1 { SCC1::ExprV { expr_v } },
        ),
    }
}

pub type ListVConsProj<Rec> = Mapped<
    Refined<Rec, PredFnSpec<SCC1>>,
    FnSpecMapper<SCC1, ListVConsSpec>,
>;

pub open spec fn list_v_cons_proj<Rec>(rec: Rec) -> ListVConsProj<Rec> where
    Rec: SpecCombinator<T = SCC1>,
 {
    Mapped {
        inner: Refined(rec, |v: SCC1| v is ListVCons),
        mapper: (
            |v: SCC1| -> ListVConsSpec { v->list_v_cons },
            |list_v_cons: ListVConsSpec| -> SCC1 { SCC1::ListVCons { list_v_cons } },
        ),
    }
}

pub type ListVProj<Rec> = Mapped<Refined<Rec, PredFnSpec<SCC1>>, FnSpecMapper<SCC1, ListVSpec>>;

pub open spec fn list_v_proj<Rec>(rec: Rec) -> ListVProj<Rec> where Rec: SpecCombinator<T = SCC1> {
    Mapped {
        inner: Refined(rec, |v: SCC1| v is ListV),
        mapper: (
            |v: SCC1| -> ListVSpec { v->list_v },
            |list_v: ListVSpec| -> SCC1 { SCC1::ListV { list_v } },
        ),
    }
}

pub type ExprFmtSpec<const LIMIT: usize> = ExprProj<FixWith<LIMIT, ExprListRecBody, ExprListParam>>;

# [derive (Clone, Copy)]
pub struct ExprFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ExprFmt<LIMIT> {
    pub open spec fn spec_inner() -> ExprProj<FixWith<LIMIT, ExprListRecBody, ExprListParam>> {
        expr_proj(
            FixWith::<LIMIT, _, _>(
                ExprListRecBody,
                ExprListParam {
                    which: WhichSCC1::EXPR,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
            ),
        )
    }
}

pub type ListFmtSpec<const LIMIT: usize> = ListProj<FixWith<LIMIT, ExprListRecBody, ExprListParam>>;

# [derive (Clone, Copy)]
pub struct ListFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ListFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListProj<FixWith<LIMIT, ExprListRecBody, ExprListParam>> {
        list_proj(
            FixWith::<LIMIT, _, _>(
                ExprListRecBody,
                ExprListParam {
                    which: WhichSCC1::LIST,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
            ),
        )
    }
}

pub type ExprVFmtSpec<const LIMIT: usize> = ExprVProj<
    FixWith<LIMIT, ExprListRecBody, ExprListParam>,
>;

# [derive (Clone, Copy)]
pub struct ExprVFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ExprVFmt<LIMIT> {
    pub open spec fn spec_inner() -> ExprVFmtSpec<LIMIT> {
        expr_v_proj(
            FixWith::<LIMIT, _, _>(
                ExprListRecBody,
                ExprListParam {
                    which: WhichSCC1::EXPRV,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
            ),
        )
    }
}

pub type ListVConsFmtSpec<const LIMIT: usize> = ListVConsProj<
    FixWith<LIMIT, ExprListRecBody, ExprListParam>,
>;

# [derive (Clone, Copy)]
pub struct ListVConsFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ListVConsFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListVConsFmtSpec<LIMIT> {
        list_v_cons_proj(
            FixWith::<LIMIT, _, _>(
                ExprListRecBody,
                ExprListParam {
                    which: WhichSCC1::LISTVCONS,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
            ),
        )
    }
}

pub type ListVFmtSpec<const LIMIT: usize> = ListVProj<
    FixWith<LIMIT, ExprListRecBody, ExprListParam>,
>;

# [derive (Clone, Copy)]
pub struct ListVFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ListVFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListVFmtSpec<LIMIT> {
        list_v_proj(
            FixWith::<LIMIT, _, _>(
                ExprListRecBody,
                ExprListParam {
                    which: WhichSCC1::LISTV,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
            ),
        )
    }
}

pub struct ExprMapper;

impl SpecMapper for ExprMapper {
    type In = (ExprKindSpec, ExprVSpec);

    type Out = SCC1;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (t, v) = i;
        SCC1::Expr { expr: ExprSpec { t, v: Box::new(v) } }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is Expr
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::Expr { expr: ExprSpec { t, v } } => (t, *v),
            _ => arbitrary(),
        }
    }
}

pub struct ListMapper;

impl SpecMapper for ListMapper {
    type In = (ListKindSpec, ListVSpec);

    type Out = SCC1;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (t, v) = i;
        SCC1::List { list: ListSpec { t, v: Box::new(v) } }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is List
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::List { list: ListSpec { t, v } } => (t, *v),
            _ => arbitrary(),
        }
    }
}

pub struct ExprVMapper;

impl SpecMapper for ExprVMapper {
    type In = Sum<u8, ListSpec>;

    type Out = SCC1;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(v) => SCC1::ExprV { expr_v: ExprVSpec::Num(v) },
            Sum::Inr(v) => SCC1::ExprV { expr_v: ExprVSpec::Group(Box::new(v)) },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ExprV
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::ExprV { expr_v: ExprVSpec::Num(v) } => Sum::Inl(v),
            SCC1::ExprV { expr_v: ExprVSpec::Group(v) } => Sum::Inr(*v),
            _ => arbitrary(),
        }
    }
}

pub struct ListVConsMapper;

impl SpecMapper for ListVConsMapper {
    type In = (ExprSpec, ListSpec);

    type Out = SCC1;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (head, tail) = i;
        SCC1::ListVCons {
            list_v_cons: ListVConsSpec { head: Box::new(head), tail: Box::new(tail) },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ListVCons
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::ListVCons { list_v_cons: ListVConsSpec { head, tail } } => (*head, *tail),
            _ => arbitrary(),
        }
    }
}

pub struct ListVMapper;

impl SpecMapper for ListVMapper {
    type In = Sum<Seq<u8>, ListVConsSpec>;

    type Out = SCC1;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(v) => SCC1::ListV { list_v: ListVSpec::Nil(v) },
            Sum::Inr(v) => SCC1::ListV { list_v: ListVSpec::Cons(Box::new(v)) },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ListV
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::ListV { list_v: ListVSpec::Nil(v) } => Sum::Inl(v),
            SCC1::ListV { list_v: ListVSpec::Cons(v) } => Sum::Inr(*v),
            _ => arbitrary(),
        }
    }
}

pub type ExprBodyFmt = Mapped<
    Bind<ExprKindFmt, spec_fn(ExprKindSpec) -> ExprVProj<BundledSpecs<SCC1>>>,
    ExprMapper,
>;

pub struct ExprBodyRec;

impl SpecRecBody for ExprBodyRec {
    type Param = ExprListParam;

    type T = SCC1;

    type Body = ExprBodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Bind(
                ExprKindFmt,
                |t: ExprKindSpec|
                    expr_v_proj(
                        rec(
                            ExprListParam {
                                which: WhichSCC1::EXPRV,
                                expr_kind: t,
                                list_kind: ListKind::Nil,
                            },
                        ),
                    ),
            ),
            mapper: ExprMapper,
        }
    }
}

pub type ListBodyFmt = Mapped<
    Bind<ListKindFmt, spec_fn(ListKindSpec) -> ListVProj<BundledSpecs<SCC1>>>,
    ListMapper,
>;

pub struct ListBodyRec;

impl SpecRecBody for ListBodyRec {
    type Param = ExprListParam;

    type T = SCC1;

    type Body = ListBodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Bind(
                ListKindFmt,
                |t: ListKindSpec|
                    list_v_proj(
                        rec(
                            ExprListParam {
                                which: WhichSCC1::LISTV,
                                expr_kind: ExprKind::Num,
                                list_kind: t,
                            },
                        ),
                    ),
            ),
            mapper: ListMapper,
        }
    }
}

pub type ExprVBodyFmt = Mapped<Sum<U8, ListProj<BundledSpecs<SCC1>>>, ExprVMapper>;

pub struct ExprVBodyRec;

impl SpecRecBody for ExprVBodyRec {
    type Param = ExprListParam;

    type T = SCC1;

    type Body = ExprVBodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.expr_kind {
                ExprKind::Num => Sum::Inl(U8),
                ExprKind::Group => Sum::Inr(
                    list_proj(
                        rec(
                            ExprListParam {
                                which: WhichSCC1::LIST,
                                expr_kind: ExprKind::Num,
                                list_kind: ListKind::Nil,
                            },
                        ),
                    ),
                ),
            },
            mapper: ExprVMapper,
        }
    }
}

pub type ListVConsBodyFmt = Mapped<
    Pair<ExprProj<BundledSpecs<SCC1>>, ListProj<BundledSpecs<SCC1>>>,
    ListVConsMapper,
>;

pub struct ListVConsBodyRec;

impl SpecRecBody for ListVConsBodyRec {
    type Param = ExprListParam;

    type T = SCC1;

    type Body = ListVConsBodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Pair(
                expr_proj(
                    rec(
                        ExprListParam {
                            which: WhichSCC1::EXPR,
                            expr_kind: ExprKind::Num,
                            list_kind: ListKind::Nil,
                        },
                    ),
                ),
                list_proj(
                    rec(
                        ExprListParam {
                            which: WhichSCC1::LIST,
                            expr_kind: ExprKind::Num,
                            list_kind: ListKind::Nil,
                        },
                    ),
                ),
            ),
            mapper: ListVConsMapper,
        }
    }
}

pub type ListVBodyFmt = Mapped<Sum<Fixed<0>, ListVConsProj<BundledSpecs<SCC1>>>, ListVMapper>;

pub struct ListVBodyRec;

impl SpecRecBody for ListVBodyRec {
    type Param = ExprListParam;

    type T = SCC1;

    type Body = ListVBodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.list_kind {
                ListKind::Nil => Sum::Inl(Fixed::<0>),
                ListKind::Cons => Sum::Inr(
                    list_v_cons_proj(
                        rec(
                            ExprListParam {
                                which: WhichSCC1::LISTVCONS,
                                expr_kind: ExprKind::Num,
                                list_kind: ListKind::Nil,
                            },
                        ),
                    ),
                ),
            },
            mapper: ListVMapper,
        }
    }
}

pub struct ExprListRecBody;

impl SpecRecBody for ExprListRecBody {
    type Param = ExprListParam;

    type T = SCC1;

    type Body = Alt<
        Cond<ExprBodyFmt>,
        Alt<
            Cond<ListBodyFmt>,
            Alt<Cond<ExprVBodyFmt>, Alt<Cond<ListVConsBodyFmt>, Cond<ListVBodyFmt>>>,
        >,
    >;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Alt(
            Cond(param.which == WhichSCC1::EXPR, ExprBodyRec.spec_body(param, rec)),
            Alt(
                Cond(param.which == WhichSCC1::LIST, ListBodyRec.spec_body(param, rec)),
                Alt(
                    Cond(param.which == WhichSCC1::EXPRV, ExprVBodyRec.spec_body(param, rec)),
                    Alt(
                        Cond(
                            param.which == WhichSCC1::LISTVCONS,
                            ListVConsBodyRec.spec_body(param, rec),
                        ),
                        Cond(param.which == WhichSCC1::LISTV, ListVBodyRec.spec_body(param, rec)),
                    ),
                ),
            ),
        )
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

    impl SpecParser for ExprKindFmt {
        type PVal = ExprKindSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ExprKindFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ExprKindFmt {
        type Val = ExprKindSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ExprKindFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ExprKindFmt {
        type SValue = ExprKindSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ExprKindFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ExprKindFmt {
        type SVal = ExprKindSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ExprKindFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ExprKindFmt {
        type T = ExprKindSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ExprKindFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ListKindFmt {
        type PVal = ListKindSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ListKindFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ListKindFmt {
        type Val = ListKindSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ListKindFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ListKindFmt {
        type SValue = ListKindSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ListKindFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ListKindFmt {
        type SVal = ListKindSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ListKindFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ListKindFmt {
        type T = ListKindSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ListKindFmt::spec_inner().byte_len(v)
        }
    }

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

    impl<const LIMIT: usize> SpecParser for ExprVFmt<LIMIT> {
        type PVal = ExprVSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ExprVFmt<LIMIT> {
        type Val = ExprVSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ExprVFmt<LIMIT> {
        type T = ExprVSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ExprVFmt<LIMIT> {
        type SValue = ExprVSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ExprVFmt<LIMIT> {
        type SVal = ExprVSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ListVConsFmt<LIMIT> {
        type PVal = ListVConsSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ListVConsFmt<LIMIT> {
        type Val = ListVConsSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ListVConsFmt<LIMIT> {
        type T = ListVConsSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ListVConsFmt<LIMIT> {
        type SValue = ListVConsSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ListVConsFmt<LIMIT> {
        type SVal = ListVConsSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ListVFmt<LIMIT> {
        type PVal = ListVSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ListVFmt<LIMIT> {
        type Val = ListVSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ListVFmt<LIMIT> {
        type T = ListVSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ListVFmt<LIMIT> {
        type SValue = ListVSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ListVFmt<LIMIT> {
        type SVal = ListVSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    // ============================================================
    // Proven Format Properties
    // ============================================================
    impl SafeParser for ExprKindFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            ExprKindFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ExprKindFmt {
        open spec fn productive_inv(&self) -> bool {
            ExprKindFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ExprKindFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            reveal(<ExprKindFmt as Consistency>::consistent);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ExprKindFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ExprKindFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ExprKindFmt as SpecSerializer>::spec_serialize);
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ExprKindFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ExprKindFmt as Consistency>::consistent);
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ExprKindFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ExprKindFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ExprKindFmt as SpecSerializer>::spec_serialize);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ExprKindFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ExprKindFmt as SpecSerializer>::spec_serialize);
            let fmt = ExprKindFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ListKindFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            ListKindFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ListKindFmt {
        open spec fn productive_inv(&self) -> bool {
            ListKindFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ListKindFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            reveal(<ListKindFmt as Consistency>::consistent);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ListKindFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ListKindFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ListKindFmt as SpecSerializer>::spec_serialize);
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ListKindFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ListKindFmt as Consistency>::consistent);
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ListKindFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ListKindFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ListKindFmt as SpecSerializer>::spec_serialize);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ListKindFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ListKindFmt as SpecSerializer>::spec_serialize);
            let fmt = ListKindFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl NoLookAhead for ExprKindFmt {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            let fmt = ExprKindFmt::spec_inner();
            fmt.lemma_no_lookahead(i1, i2);
        }
    }

    impl NoLookAhead for ListKindFmt {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            let fmt = ListKindFmt::spec_inner();
            fmt.lemma_no_lookahead(i1, i2);
        }
    }

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

    impl<const LIMIT: usize> SafeParser for ExprVFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ExprVFmt<LIMIT> {
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

    impl<const LIMIT: usize> NonTailFmt for ExprVFmt<LIMIT> {
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

    impl<const LIMIT: usize> GoodSerializer for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ExprVFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ExprVFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for ListVConsFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ListVConsFmt<LIMIT> {
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

    impl<const LIMIT: usize> NonTailFmt for ListVConsFmt<LIMIT> {
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

    impl<const LIMIT: usize> GoodSerializer for ListVConsFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ListVConsFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ListVConsFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ListVConsFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ListVConsFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for ListVFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ListVFmt<LIMIT> {
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

    impl<const LIMIT: usize> NonTailFmt for ListVFmt<LIMIT> {
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

    impl<const LIMIT: usize> GoodSerializer for ListVFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ListVFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ListVFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ListVFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ListVFmt<LIMIT> {
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
            assert(self.spec_map_rev(self.spec_map(i)) == i);
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

    impl LossyMapper for ExprVMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ExprVMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl LossyMapper for ListVConsMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ListVConsMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl LossyMapper for ListVMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ListVMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl StrictRecBody for ExprBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ExprVBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListVBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListVConsBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ExprListRecBody {
        proof fn lemma_body_all_inv_preservation(
            &self,
            param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            hide(<ExprBodyRec as SpecRecBody>::spec_body);
            hide(<ListBodyRec as SpecRecBody>::spec_body);
            hide(<ExprVBodyRec as SpecRecBody>::spec_body);
            hide(<ListVBodyRec as SpecRecBody>::spec_body);
            hide(<ListVConsBodyRec as SpecRecBody>::spec_body);
            broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

            ExprBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListBodyRec.lemma_body_all_inv_preservation(param, rec);
            ExprVBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListVBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListVConsBodyRec.lemma_body_all_inv_preservation(param, rec);
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
impl<'i> Parser<&'i [u8]> for ExprKindFmt {
    type PT = ExprKind;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        reveal(<ExprKindFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = U8.parse(&rest)?;
        let enum_val = match v {
            16 => ExprKind::Num,
            17 => ExprKind::Group,
            _ => return Err(ParseError::invalid_tag()),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        Ok((n, enum_val))
    }
}

impl Serializer<ExprKind> for ExprKindFmt {
    fn serialize(&self, v: &ExprKind, obuf: &mut Vec<u8>) {
        reveal(<ExprKindFmt as SpecSerializer>::spec_serialize);
        let ghost old_obuf = obuf@;

        let tag = match *v {
            ExprKind::Num => 16,
            ExprKind::Group => 17,
        };
        U8.serialize(&tag, obuf);

        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl Prepare<ExprKind> for ExprKindFmt {
    fn prepare(&self, v: &ExprKind) -> Result<usize, PreSerializeError> {
        reveal(<ExprKindFmt as SpecByteLen>::byte_len);
        let tag = match *v {
            ExprKind::Num => 16,
            ExprKind::Group => 17,
        };
        U8.prepare(&tag)
    }
}

impl<'i> Parser<&'i [u8]> for ListKindFmt {
    type PT = ListKind;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        reveal(<ListKindFmt as SpecParser>::spec_parse);
        let _ = ibuf.len();
        let rest = *ibuf;

        let (n, v) = U8.parse(&rest)?;
        let enum_val = match v {
            32 => ListKind::Nil,
            33 => ListKind::Cons,
            _ => return Err(ParseError::invalid_tag()),
        };
        assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        Ok((n, enum_val))
    }
}

impl Serializer<ListKind> for ListKindFmt {
    fn serialize(&self, v: &ListKind, obuf: &mut Vec<u8>) {
        reveal(<ListKindFmt as SpecSerializer>::spec_serialize);
        let ghost old_obuf = obuf@;

        let tag = match *v {
            ListKind::Nil => 32,
            ListKind::Cons => 33,
        };
        U8.serialize(&tag, obuf);

        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl Prepare<ListKind> for ListKindFmt {
    fn prepare(&self, v: &ListKind) -> Result<usize, PreSerializeError> {
        reveal(<ListKindFmt as SpecByteLen>::byte_len);
        let tag = match *v {
            ListKind::Nil => 32,
            ListKind::Cons => 33,
        };
        U8.prepare(&tag)
    }
}

impl<const LIMIT: usize> ExprFmt<LIMIT> {
    fn parse_expr_gas<'i>(&self, gas: usize, param: ExprListParam, ibuf: &&'i [u8]) -> (r: PResult<
        Expr<'i>,
    >)
        requires
            param.which == WhichSCC1::EXPR,
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    ibuf@,
                ) {
                    Some((n, SCC1::Expr { expr })) => Some((n, expr)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas, 1nat,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        let (n1, tag) = ExprKindFmt.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        let param_v = ExprListParam {
            which: WhichSCC1::EXPRV,
            expr_kind: tag,
            list_kind: ListKind::Nil,
        };
        if gas > 0 {
            let (n2, v) = self.parse_expr_v_gas(gas - 1, param_v, &rest)?;
            Ok((n1 + n2, Expr { t: tag, v: Box::new(v) }))
        } else {
            Err(ParseError::recursion_limit_exceeded())
        }
    }

    fn parse_expr_v_gas<'i>(&self, gas: usize, param: ExprListParam, ibuf: &&'i [u8]) -> (r:
        PResult<ExprV<'i>>)
        requires
            param.which == WhichSCC1::EXPRV,
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    ibuf@,
                ) {
                    Some((n, SCC1::ExprV { expr_v })) => Some((n, expr_v)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas, 0nat,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        match param.expr_kind {
            ExprKind::Num => {
                let (n, val) = U8.parse(ibuf)?;
                Ok((n, ExprV::Num(val)))
            },
            ExprKind::Group => {
                if gas > 0 {
                    let param_list = ExprListParam {
                        which: WhichSCC1::LIST,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    };
                    let (n, list) = self.parse_list_gas(gas - 1, param_list, ibuf)?;
                    Ok((n, ExprV::Group(Box::new(list))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
        }
    }

    fn parse_list_gas<'i>(&self, gas: usize, param: ExprListParam, ibuf: &&'i [u8]) -> (r: PResult<
        List<'i>,
    >)
        requires
            param.which == WhichSCC1::LIST,
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    ibuf@,
                ) {
                    Some((n, SCC1::List { list })) => Some((n, list)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas, 4nat,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        let (n1, tag) = ListKindFmt.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        let param_v = ExprListParam {
            which: WhichSCC1::LISTV,
            expr_kind: ExprKind::Num,
            list_kind: tag,
        };
        if gas > 0 {
            let (n2, v) = self.parse_list_v_gas(gas - 1, param_v, &rest)?;
            Ok((n1 + n2, List { t: tag, v: Box::new(v) }))
        } else {
            Err(ParseError::recursion_limit_exceeded())
        }
    }

    fn parse_list_v_gas<'i>(&self, gas: usize, param: ExprListParam, ibuf: &&'i [u8]) -> (r:
        PResult<ListV<'i>>)
        requires
            param.which == WhichSCC1::LISTV,
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    ibuf@,
                ) {
                    Some((n, SCC1::ListV { list_v })) => Some((n, list_v)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas, 3nat,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        match param.list_kind {
            ListKind::Nil => {
                let (n, val) = Fixed::<0>.parse(ibuf)?;
                Ok((n, ListV::Nil(val)))
            },
            ListKind::Cons => {
                if gas > 0 {
                    let param_cons = ExprListParam {
                        which: WhichSCC1::LISTVCONS,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    };
                    let (n, cons) = self.parse_list_v_cons_gas(gas - 1, param_cons, ibuf)?;
                    Ok((n, ListV::Cons(Box::new(cons))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
        }
    }

    fn parse_list_v_cons_gas<'i>(&self, gas: usize, param: ExprListParam, ibuf: &&'i [u8]) -> (r:
        PResult<ListVCons<'i>>)
        requires
            param.which == WhichSCC1::LISTVCONS,
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    ibuf@,
                ) {
                    Some((n, SCC1::ListVCons { list_v_cons })) => Some((n, list_v_cons)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas, 2nat,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        if gas > 0 {
            let param_head = ExprListParam {
                which: WhichSCC1::EXPR,
                expr_kind: ExprKind::Num,
                list_kind: ListKind::Nil,
            };
            let (n1, head) = self.parse_expr_gas(gas - 1, param_head, ibuf)?;
            let rest = ibuf.skip(n1);
            let param_tail = ExprListParam {
                which: WhichSCC1::LIST,
                expr_kind: ExprKind::Num,
                list_kind: ListKind::Nil,
            };
            let (n2, tail) = self.parse_list_gas(gas - 1, param_tail, &rest)?;
            Ok((n1 + n2, ListVCons { head: Box::new(head), tail: Box::new(tail) }))
        } else {
            Err(ParseError::recursion_limit_exceeded())
        }
    }

    fn serialize_expr_gas<'i>(
        &self,
        gas: usize,
        param: ExprListParam,
        v: &Expr<'i>,
        obuf: &mut Vec<u8>,
    )
        requires
            param.which == WhichSCC1::EXPR,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::Expr { expr: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::Expr { expr: v.deep_view() },
            ),
        decreases gas, 1nat,
    {
        ExprKindFmt.serialize(&v.t, obuf);
        let param_v = ExprListParam {
            which: WhichSCC1::EXPRV,
            expr_kind: v.t,
            list_kind: ListKind::Nil,
        };
        assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
            &ExprListRecBody,
            gas as nat,
            param,
            SCC1::Expr { expr: v.deep_view() },
        ));
        assert(ExprListRecBody.spec_body(
            param,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                &ExprListRecBody,
                gas as nat,
            ),
        ).consistent(SCC1::Expr { expr: v.deep_view() }));
        assert(ExprBodyRec.spec_body(
            param,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                &ExprListRecBody,
                gas as nat,
            ),
        ).consistent(SCC1::Expr { expr: v.deep_view() }));
        assert(Bind(
            ExprKindFmt,
            |t: ExprKindSpec|
                expr_v_proj(
                    FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                        &ExprListRecBody,
                        gas as nat,
                    )(
                        ExprListParam {
                            which: WhichSCC1::EXPRV,
                            expr_kind: t,
                            list_kind: ListKind::Nil,
                        },
                    ),
                ),
        ).consistent((v.t.deep_view(), v.v.deep_view())));
        assert(expr_v_proj(
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                &ExprListRecBody,
                gas as nat,
            )(param_v),
        ).consistent(v.v.deep_view()));
        assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
            &ExprListRecBody,
            (gas - 1) as nat,
            param_v,
            SCC1::ExprV { expr_v: v.v.deep_view() },
        ));
        if gas > 0 {
            self.serialize_expr_v_gas(gas - 1, param_v, &*v.v, obuf);
        }
    }

    fn serialize_expr_v_gas<'i>(
        &self,
        gas: usize,
        param: ExprListParam,
        v: &ExprV<'i>,
        obuf: &mut Vec<u8>,
    )
        requires
            param.which == WhichSCC1::EXPRV,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::ExprV { expr_v: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::ExprV { expr_v: v.deep_view() },
            ),
        decreases gas, 0nat,
    {
        match v {
            ExprV::Num(num_val) => {
                U8.serialize(num_val, obuf);
            },
            ExprV::Group(list_val) => {
                if gas > 0 {
                    let param_list = ExprListParam {
                        which: WhichSCC1::LIST,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    };
                    assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                        &ExprListRecBody,
                        gas as nat,
                        param,
                        SCC1::ExprV { expr_v: v.deep_view() },
                    ));
                    assert(ExprListRecBody.spec_body(
                        param,
                        FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                            &ExprListRecBody,
                            gas as nat,
                        ),
                    ).consistent(SCC1::ExprV { expr_v: v.deep_view() }));
                    assert(ExprVBodyRec.spec_body(
                        param,
                        FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                            &ExprListRecBody,
                            gas as nat,
                        ),
                    ).consistent(SCC1::ExprV { expr_v: v.deep_view() }));
                    assert(Sum::<U8, ListProj<BundledSpecs<SCC1>>>::Inr(
                        list_proj(
                            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                &ExprListRecBody,
                                gas as nat,
                            )(param_list),
                        ),
                    ).consistent(ExprVMapper.spec_map_rev(SCC1::ExprV { expr_v: v.deep_view() })));
                    assert(list_proj(
                        FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                            &ExprListRecBody,
                            gas as nat,
                        )(param_list),
                    ).consistent(list_val.deep_view()));
                    assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                        &ExprListRecBody,
                        (gas - 1) as nat,
                        param_list,
                        SCC1::List { list: list_val.deep_view() },
                    ));
                    self.serialize_list_gas(gas - 1, param_list, list_val, obuf);
                }
            },
        }
    }

    fn serialize_list_gas<'i>(
        &self,
        gas: usize,
        param: ExprListParam,
        v: &List<'i>,
        obuf: &mut Vec<u8>,
    )
        requires
            param.which == WhichSCC1::LIST,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::List { list: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::List { list: v.deep_view() },
            ),
        decreases gas, 4nat,
    {
        ListKindFmt.serialize(&v.t, obuf);
        let param_v = ExprListParam {
            which: WhichSCC1::LISTV,
            expr_kind: ExprKind::Num,
            list_kind: v.t,
        };
        assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
            &ExprListRecBody,
            gas as nat,
            param,
            SCC1::List { list: v.deep_view() },
        ));
        assert(ExprListRecBody.spec_body(
            param,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                &ExprListRecBody,
                gas as nat,
            ),
        ).consistent(SCC1::List { list: v.deep_view() }));
        assert(ListBodyRec.spec_body(
            param,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                &ExprListRecBody,
                gas as nat,
            ),
        ).consistent(SCC1::List { list: v.deep_view() }));
        assert(Bind(
            ListKindFmt,
            |t: ListKindSpec|
                list_v_proj(
                    FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                        &ExprListRecBody,
                        gas as nat,
                    )(
                        ExprListParam {
                            which: WhichSCC1::LISTV,
                            expr_kind: ExprKind::Num,
                            list_kind: t,
                        },
                    ),
                ),
        ).consistent((v.t.deep_view(), v.v.deep_view())));
        assert(list_v_proj(
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                &ExprListRecBody,
                gas as nat,
            )(param_v),
        ).consistent(v.v.deep_view()));
        assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
            &ExprListRecBody,
            (gas - 1) as nat,
            param_v,
            SCC1::ListV { list_v: v.v.deep_view() },
        ));
        if gas > 0 {
            self.serialize_list_v_gas(gas - 1, param_v, &*v.v, obuf);
        }
    }

    fn serialize_list_v_gas<'i>(
        &self,
        gas: usize,
        param: ExprListParam,
        v: &ListV<'i>,
        obuf: &mut Vec<u8>,
    )
        requires
            param.which == WhichSCC1::LISTV,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::ListV { list_v: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::ListV { list_v: v.deep_view() },
            ),
        decreases gas, 3nat,
    {
        match v {
            ListV::Nil(bytes_val) => {
                Fixed::<0>.serialize(bytes_val, obuf);
            },
            ListV::Cons(cons_val) => {
                if gas > 0 {
                    let param_cons = ExprListParam {
                        which: WhichSCC1::LISTVCONS,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    };
                    assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                        &ExprListRecBody,
                        gas as nat,
                        param,
                        SCC1::ListV { list_v: v.deep_view() },
                    ));
                    assert(ExprListRecBody.spec_body(
                        param,
                        FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                            &ExprListRecBody,
                            gas as nat,
                        ),
                    ).consistent(SCC1::ListV { list_v: v.deep_view() }));
                    assert(ListVBodyRec.spec_body(
                        param,
                        FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                            &ExprListRecBody,
                            gas as nat,
                        ),
                    ).consistent(SCC1::ListV { list_v: v.deep_view() }));
                    assert(Sum::<Fixed<0>, ListVConsProj<BundledSpecs<SCC1>>>::Inr(
                        list_v_cons_proj(
                            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                &ExprListRecBody,
                                gas as nat,
                            )(param_cons),
                        ),
                    ).consistent(ListVMapper.spec_map_rev(SCC1::ListV { list_v: v.deep_view() })));
                    assert(list_v_cons_proj(
                        FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                            &ExprListRecBody,
                            gas as nat,
                        )(param_cons),
                    ).consistent(cons_val.deep_view()));
                    assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                        &ExprListRecBody,
                        (gas - 1) as nat,
                        param_cons,
                        SCC1::ListVCons { list_v_cons: cons_val.deep_view() },
                    ));
                    self.serialize_list_v_cons_gas(gas - 1, param_cons, cons_val, obuf);
                }
            },
        }
    }

    fn serialize_list_v_cons_gas<'i>(
        &self,
        gas: usize,
        param: ExprListParam,
        v: &ListVCons<'i>,
        obuf: &mut Vec<u8>,
    )
        requires
            param.which == WhichSCC1::LISTVCONS,
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::ListVCons { list_v_cons: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::ListVCons { list_v_cons: v.deep_view() },
            ),
        decreases gas, 2nat,
    {
        if gas > 0 {
            let param_head = ExprListParam {
                which: WhichSCC1::EXPR,
                expr_kind: ExprKind::Num,
                list_kind: ListKind::Nil,
            };
            let param_tail = ExprListParam {
                which: WhichSCC1::LIST,
                expr_kind: ExprKind::Num,
                list_kind: ListKind::Nil,
            };
            assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::ListVCons { list_v_cons: v.deep_view() },
            ));
            assert(ExprListRecBody.spec_body(
                param,
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                ),
            ).consistent(SCC1::ListVCons { list_v_cons: v.deep_view() }));
            assert(ListVConsBodyRec.spec_body(
                param,
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                ),
            ).consistent(SCC1::ListVCons { list_v_cons: v.deep_view() }));
            assert(Pair(
                expr_proj(
                    FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                        &ExprListRecBody,
                        gas as nat,
                    )(param_head),
                ),
                list_proj(
                    FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                        &ExprListRecBody,
                        gas as nat,
                    )(param_tail),
                ),
            ).consistent(
                ListVConsMapper.spec_map_rev(SCC1::ListVCons { list_v_cons: v.deep_view() }),
            ));
            assert(expr_proj(
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                )(param_head),
            ).consistent(v.head.deep_view()));
            assert(list_proj(
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                )(param_tail),
            ).consistent(v.tail.deep_view()));
            assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                (gas - 1) as nat,
                param_head,
                SCC1::Expr { expr: v.head.deep_view() },
            ));
            assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                (gas - 1) as nat,
                param_tail,
                SCC1::List { list: v.tail.deep_view() },
            ));
            self.serialize_expr_gas(gas - 1, param_head, &v.head, obuf);
            self.serialize_list_gas(gas - 1, param_tail, &v.tail, obuf);
        }
    }

    fn prepare_expr_gas<'i>(&self, gas: usize, param: ExprListParam, v: &Expr<'i>) -> (checked:
        Result<usize, PreSerializeError>)
        requires
            param.which == WhichSCC1::EXPR,
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::Expr { expr: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::Expr { expr: v.deep_view() },
                )
            },
        decreases gas, 1nat,
    {
        let l1 = ExprKindFmt.prepare(&v.t)?;
        let param_v = ExprListParam {
            which: WhichSCC1::EXPRV,
            expr_kind: v.t,
            list_kind: ListKind::Nil,
        };
        if gas > 0 {
            let l2 = self.prepare_expr_v_gas(gas - 1, param_v, &*v.v)?;
            proof {
                assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    (gas - 1) as nat,
                    param_v,
                    SCC1::ExprV { expr_v: v.v.deep_view() },
                ));
                let rec = FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                );
                assert(rec(param_v).0(SCC1::ExprV { expr_v: v.v.deep_view() }) == FixWith::<
                    LIMIT,
                    ExprListRecBody,
                    ExprListParam,
                >::consistent_gas(
                    &ExprListRecBody,
                    (gas - 1) as nat,
                    param_v,
                    SCC1::ExprV { expr_v: v.v.deep_view() },
                ));
                assert(rec(param_v).1(SCC1::ExprV { expr_v: v.v.deep_view() }) == FixWith::<
                    LIMIT,
                    ExprListRecBody,
                    ExprListParam,
                >::byte_len_gas(
                    &ExprListRecBody,
                    (gas - 1) as nat,
                    param_v,
                    SCC1::ExprV { expr_v: v.v.deep_view() },
                ));

                assert(expr_v_proj(rec(param_v)).consistent(v.v.deep_view()));
                assert(Bind(
                    ExprKindFmt,
                    |t: ExprKindSpec|
                        expr_v_proj(
                            rec(
                                ExprListParam {
                                    which: WhichSCC1::EXPRV,
                                    expr_kind: t,
                                    list_kind: ListKind::Nil,
                                },
                            ),
                        ),
                ).consistent((v.t.deep_view(), v.v.deep_view())));
                assert(ExprBodyRec.spec_body(param, rec).consistent(
                    SCC1::Expr { expr: v.deep_view() },
                ));
                assert(ExprListRecBody.spec_body(param, rec).consistent(
                    SCC1::Expr { expr: v.deep_view() },
                ));

                assert(l2 == expr_v_proj(rec(param_v)).byte_len(v.v.deep_view()));
                assert(Bind(
                    ExprKindFmt,
                    |t: ExprKindSpec|
                        expr_v_proj(
                            rec(
                                ExprListParam {
                                    which: WhichSCC1::EXPRV,
                                    expr_kind: t,
                                    list_kind: ListKind::Nil,
                                },
                            ),
                        ),
                ).byte_len((v.t.deep_view(), v.v.deep_view())) == l1 + l2);
                assert(ExprBodyRec.spec_body(param, rec).byte_len(
                    SCC1::Expr { expr: v.deep_view() },
                ) == l1 + l2);
                assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::Expr { expr: v.deep_view() },
                ) == l1 + l2);
            }
            Ok(l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded))
        }
    }

    fn prepare_expr_v_gas<'i>(&self, gas: usize, param: ExprListParam, v: &ExprV<'i>) -> (checked:
        Result<usize, PreSerializeError>)
        requires
            param.which == WhichSCC1::EXPRV,
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::ExprV { expr_v: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::ExprV { expr_v: v.deep_view() },
                )
            },
        decreases gas, 0nat,
    {
        match v {
            ExprV::Num(num_val) => {
                if param.expr_kind == ExprKind::Num {
                    let len = U8.prepare(num_val)?;
                    assert(ExprListRecBody.spec_body(
                        param,
                        FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                            &ExprListRecBody,
                            gas as nat,
                        ),
                    ).consistent(SCC1::ExprV { expr_v: v.deep_view() }));
                    assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                        &ExprListRecBody,
                        gas as nat,
                        param,
                        SCC1::ExprV { expr_v: v.deep_view() },
                    ));
                    assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                        &ExprListRecBody,
                        gas as nat,
                        param,
                        SCC1::ExprV { expr_v: v.deep_view() },
                    ) == len);
                    Ok(len)
                } else {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidChoice))
                }
            },
            ExprV::Group(list_val) => {
                if param.expr_kind == ExprKind::Group {
                    if gas > 0 {
                        let param_list = ExprListParam {
                            which: WhichSCC1::LIST,
                            expr_kind: ExprKind::Num,
                            list_kind: ListKind::Nil,
                        };
                        let len = self.prepare_list_gas(gas - 1, param_list, list_val)?;
                        assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                            &ExprListRecBody,
                            (gas - 1) as nat,
                            param_list,
                            SCC1::List { list: list_val.deep_view() },
                        ));
                        assert(list_proj(
                            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                &ExprListRecBody,
                                gas as nat,
                            )(param_list),
                        ).consistent(list_val.deep_view()));
                        assert(Sum::<U8, ListProj<BundledSpecs<SCC1>>>::Inr(
                            list_proj(
                                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                    &ExprListRecBody,
                                    gas as nat,
                                )(param_list),
                            ),
                        ).consistent(
                            ExprVMapper.spec_map_rev(SCC1::ExprV { expr_v: v.deep_view() }),
                        ));
                        assert(ExprVBodyRec.spec_body(
                            param,
                            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                &ExprListRecBody,
                                gas as nat,
                            ),
                        ).consistent(SCC1::ExprV { expr_v: v.deep_view() }));
                        assert(ExprListRecBody.spec_body(
                            param,
                            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                &ExprListRecBody,
                                gas as nat,
                            ),
                        ).consistent(SCC1::ExprV { expr_v: v.deep_view() }));

                        assert(len == list_proj(
                            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                &ExprListRecBody,
                                gas as nat,
                            )(param_list),
                        ).byte_len(list_val.deep_view()));
                        assert(Sum::<U8, ListProj<BundledSpecs<SCC1>>>::Inr(
                            list_proj(
                                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                    &ExprListRecBody,
                                    gas as nat,
                                )(param_list),
                            ),
                        ).byte_len(ExprVMapper.spec_map_rev(SCC1::ExprV { expr_v: v.deep_view() }))
                            == len);
                        assert(ExprVBodyRec.spec_body(
                            param,
                            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                &ExprListRecBody,
                                gas as nat,
                            ),
                        ).byte_len(SCC1::ExprV { expr_v: v.deep_view() }) == len);
                        assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                            &ExprListRecBody,
                            gas as nat,
                            param,
                            SCC1::ExprV { expr_v: v.deep_view() },
                        ) == len);
                        Ok(len)
                    } else {
                        Err(
                            PreSerializeError::not_compliant(
                                ComplianceErrorKind::RecursionLimitExceeded,
                            ),
                        )
                    }
                } else {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidChoice))
                }
            },
        }
    }

    fn prepare_list_gas<'i>(&self, gas: usize, param: ExprListParam, v: &List<'i>) -> (checked:
        Result<usize, PreSerializeError>)
        requires
            param.which == WhichSCC1::LIST,
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::List { list: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::List { list: v.deep_view() },
                )
            },
        decreases gas, 4nat,
    {
        let l1 = ListKindFmt.prepare(&v.t)?;
        let param_v = ExprListParam {
            which: WhichSCC1::LISTV,
            expr_kind: ExprKind::Num,
            list_kind: v.t,
        };
        if gas > 0 {
            let l2 = self.prepare_list_v_gas(gas - 1, param_v, &*v.v)?;
            proof {
                assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    (gas - 1) as nat,
                    param_v,
                    SCC1::ListV { list_v: v.v.deep_view() },
                ));
                let rec = FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                );
                assert(rec(param_v).0(SCC1::ListV { list_v: v.v.deep_view() }) == FixWith::<
                    LIMIT,
                    ExprListRecBody,
                    ExprListParam,
                >::consistent_gas(
                    &ExprListRecBody,
                    (gas - 1) as nat,
                    param_v,
                    SCC1::ListV { list_v: v.v.deep_view() },
                ));
                assert(rec(param_v).1(SCC1::ListV { list_v: v.v.deep_view() }) == FixWith::<
                    LIMIT,
                    ExprListRecBody,
                    ExprListParam,
                >::byte_len_gas(
                    &ExprListRecBody,
                    (gas - 1) as nat,
                    param_v,
                    SCC1::ListV { list_v: v.v.deep_view() },
                ));

                assert(list_v_proj(rec(param_v)).consistent(v.v.deep_view()));
                assert(Bind(
                    ListKindFmt,
                    |t: ListKindSpec|
                        list_v_proj(
                            rec(
                                ExprListParam {
                                    which: WhichSCC1::LISTV,
                                    expr_kind: ExprKind::Num,
                                    list_kind: t,
                                },
                            ),
                        ),
                ).consistent((v.t.deep_view(), v.v.deep_view())));
                assert(ListBodyRec.spec_body(param, rec).consistent(
                    SCC1::List { list: v.deep_view() },
                ));
                assert(ExprListRecBody.spec_body(param, rec).consistent(
                    SCC1::List { list: v.deep_view() },
                ));

                assert(l2 == list_v_proj(rec(param_v)).byte_len(v.v.deep_view()));
                assert(Bind(
                    ListKindFmt,
                    |t: ListKindSpec|
                        list_v_proj(
                            rec(
                                ExprListParam {
                                    which: WhichSCC1::LISTV,
                                    expr_kind: ExprKind::Num,
                                    list_kind: t,
                                },
                            ),
                        ),
                ).byte_len((v.t.deep_view(), v.v.deep_view())) == l1 + l2);
                assert(ListBodyRec.spec_body(param, rec).byte_len(
                    SCC1::List { list: v.deep_view() },
                ) == l1 + l2);
                assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::List { list: v.deep_view() },
                ) == l1 + l2);
            }
            Ok(l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded))
        }
    }

    fn prepare_list_v_gas<'i>(&self, gas: usize, param: ExprListParam, v: &ListV<'i>) -> (checked:
        Result<usize, PreSerializeError>)
        requires
            param.which == WhichSCC1::LISTV,
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::ListV { list_v: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::ListV { list_v: v.deep_view() },
                )
            },
        decreases gas, 3nat,
    {
        match v {
            ListV::Nil(bytes_val) => {
                if param.list_kind == ListKind::Nil {
                    let len = Fixed::<0>.prepare(bytes_val)?;
                    proof {
                        assert(ExprListRecBody.spec_body(
                            param,
                            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                                &ExprListRecBody,
                                gas as nat,
                            ),
                        ).consistent(SCC1::ListV { list_v: v.deep_view() }));
                        assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                            &ExprListRecBody,
                            gas as nat,
                            param,
                            SCC1::ListV { list_v: v.deep_view() },
                        ));
                        assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                            &ExprListRecBody,
                            gas as nat,
                            param,
                            SCC1::ListV { list_v: v.deep_view() },
                        ) == len);
                    }
                    Ok(len)
                } else {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidChoice))
                }
            },
            ListV::Cons(cons_val) => {
                if param.list_kind == ListKind::Cons {
                    if gas > 0 {
                        let param_cons = ExprListParam {
                            which: WhichSCC1::LISTVCONS,
                            expr_kind: ExprKind::Num,
                            list_kind: ListKind::Nil,
                        };
                        let len = self.prepare_list_v_cons_gas(gas - 1, param_cons, cons_val)?;
                        proof {
                            assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                                &ExprListRecBody,
                                (gas - 1) as nat,
                                param_cons,
                                SCC1::ListVCons { list_v_cons: cons_val.deep_view() },
                            ));
                            let rec = FixWith::<
                                LIMIT,
                                ExprListRecBody,
                                ExprListParam,
                            >::specs_callback(&ExprListRecBody, gas as nat);
                            assert(rec(param_cons).0(
                                SCC1::ListVCons { list_v_cons: cons_val.deep_view() },
                            ) == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                                &ExprListRecBody,
                                (gas - 1) as nat,
                                param_cons,
                                SCC1::ListVCons { list_v_cons: cons_val.deep_view() },
                            ));
                            assert(rec(param_cons).1(
                                SCC1::ListVCons { list_v_cons: cons_val.deep_view() },
                            ) == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                                &ExprListRecBody,
                                (gas - 1) as nat,
                                param_cons,
                                SCC1::ListVCons { list_v_cons: cons_val.deep_view() },
                            ));

                            assert(list_v_cons_proj(rec(param_cons)).consistent(
                                cons_val.deep_view(),
                            ));
                            assert(Sum::<Fixed<0>, ListVConsProj<BundledSpecs<SCC1>>>::Inr(
                                list_v_cons_proj(rec(param_cons)),
                            ).consistent(
                                ListVMapper.spec_map_rev(SCC1::ListV { list_v: v.deep_view() }),
                            ));
                            assert(ListVBodyRec.spec_body(param, rec).consistent(
                                SCC1::ListV { list_v: v.deep_view() },
                            ));
                            assert(ExprListRecBody.spec_body(param, rec).consistent(
                                SCC1::ListV { list_v: v.deep_view() },
                            ));

                            assert(len == list_v_cons_proj(rec(param_cons)).byte_len(
                                cons_val.deep_view(),
                            ));
                            assert(Sum::<Fixed<0>, ListVConsProj<BundledSpecs<SCC1>>>::Inr(
                                list_v_cons_proj(rec(param_cons)),
                            ).byte_len(
                                ListVMapper.spec_map_rev(SCC1::ListV { list_v: v.deep_view() }),
                            ) == len);
                            assert(ListVBodyRec.spec_body(param, rec).byte_len(
                                SCC1::ListV { list_v: v.deep_view() },
                            ) == len);
                            assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                                &ExprListRecBody,
                                gas as nat,
                                param,
                                SCC1::ListV { list_v: v.deep_view() },
                            ) == len);
                        }
                        Ok(len)
                    } else {
                        Err(
                            PreSerializeError::not_compliant(
                                ComplianceErrorKind::RecursionLimitExceeded,
                            ),
                        )
                    }
                } else {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidChoice))
                }
            },
        }
    }

    fn prepare_list_v_cons_gas<'i>(
        &self,
        gas: usize,
        param: ExprListParam,
        v: &ListVCons<'i>,
    ) -> (checked: Result<usize, PreSerializeError>)
        requires
            param.which == WhichSCC1::LISTVCONS,
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::ListVCons { list_v_cons: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    param,
                    SCC1::ListVCons { list_v_cons: v.deep_view() },
                )
            },
        decreases gas, 2nat,
    {
        if gas > 0 {
            let param_head = ExprListParam {
                which: WhichSCC1::EXPR,
                expr_kind: ExprKind::Num,
                list_kind: ListKind::Nil,
            };
            let l1 = self.prepare_expr_gas(gas - 1, param_head, &v.head)?;
            let param_tail = ExprListParam {
                which: WhichSCC1::LIST,
                expr_kind: ExprKind::Num,
                list_kind: ListKind::Nil,
            };
            let l2 = self.prepare_list_gas(gas - 1, param_tail, &v.tail)?;
            assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                (gas - 1) as nat,
                param_head,
                SCC1::Expr { expr: v.head.deep_view() },
            ));
            assert(expr_proj(
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                )(param_head),
            ).consistent(v.head.deep_view()));
            assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                (gas - 1) as nat,
                param_tail,
                SCC1::List { list: v.tail.deep_view() },
            ));
            assert(list_proj(
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                )(param_tail),
            ).consistent(v.tail.deep_view()));
            assert(Pair(
                expr_proj(
                    FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                        &ExprListRecBody,
                        gas as nat,
                    )(param_head),
                ),
                list_proj(
                    FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                        &ExprListRecBody,
                        gas as nat,
                    )(param_tail),
                ),
            ).consistent(
                ListVConsMapper.spec_map_rev(SCC1::ListVCons { list_v_cons: v.deep_view() }),
            ));
            assert(ListVConsBodyRec.spec_body(
                param,
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                ),
            ).consistent(SCC1::ListVCons { list_v_cons: v.deep_view() }));
            assert(ExprListRecBody.spec_body(
                param,
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                ),
            ).consistent(SCC1::ListVCons { list_v_cons: v.deep_view() }));

            assert(l1 == expr_proj(
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                )(param_head),
            ).byte_len(v.head.deep_view()));
            assert(l2 == list_proj(
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                )(param_tail),
            ).byte_len(v.tail.deep_view()));
            assert(Pair(
                expr_proj(
                    FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                        &ExprListRecBody,
                        gas as nat,
                    )(param_head),
                ),
                list_proj(
                    FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                        &ExprListRecBody,
                        gas as nat,
                    )(param_tail),
                ),
            ).byte_len(ListVConsMapper.spec_map_rev(SCC1::ListVCons { list_v_cons: v.deep_view() }))
                == l1 + l2);
            assert(ListVConsBodyRec.spec_body(
                param,
                FixWith::<LIMIT, ExprListRecBody, ExprListParam>::specs_callback(
                    &ExprListRecBody,
                    gas as nat,
                ),
            ).byte_len(SCC1::ListVCons { list_v_cons: v.deep_view() }) == l1 + l2);
            assert(FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                &ExprListRecBody,
                gas as nat,
                param,
                SCC1::ListVCons { list_v_cons: v.deep_view() },
            ) == l1 + l2);
            Ok(l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded))
        }
    }

    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<Expr<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::EXPR,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    ibuf@,
                ) {
                    Some((n, SCC1::Expr { expr })) => Some((n, expr)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
    {
        let param = ExprListParam {
            which: WhichSCC1::EXPR,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        self.parse_expr_gas(gas, param, ibuf)
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &Expr<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::EXPR,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::Expr { expr: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::EXPR,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::Expr { expr: v.deep_view() },
            ),
    {
        let param = ExprListParam {
            which: WhichSCC1::EXPR,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        self.serialize_expr_gas(gas, param, v, obuf);
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &Expr<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::EXPR,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::Expr { expr: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::EXPR,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::Expr { expr: v.deep_view() },
                )
            },
    {
        let param = ExprListParam {
            which: WhichSCC1::EXPR,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        self.prepare_expr_gas(gas, param, v)
    }
}

impl<const LIMIT: usize> ListFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<List<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LIST,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    ibuf@,
                ) {
                    Some((n, SCC1::List { list })) => Some((n, list)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
    {
        let param = ExprListParam {
            which: WhichSCC1::LIST,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.parse_list_gas(gas, param, ibuf)
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &List<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::LIST,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::List { list: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::LIST,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::List { list: v.deep_view() },
            ),
    {
        let param = ExprListParam {
            which: WhichSCC1::LIST,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.serialize_list_gas(gas, param, v, obuf);
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &List<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LIST,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::List { list: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LIST,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::List { list: v.deep_view() },
                )
            },
    {
        let param = ExprListParam {
            which: WhichSCC1::LIST,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.prepare_list_gas(gas, param, v)
    }
}

impl<const LIMIT: usize> ExprVFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ExprV<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::EXPRV,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    ibuf@,
                ) {
                    Some((n, SCC1::ExprV { expr_v })) => Some((n, expr_v)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
    {
        let param = ExprListParam {
            which: WhichSCC1::EXPRV,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.parse_expr_v_gas(gas, param, ibuf)
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &ExprV<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::EXPRV,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::ExprV { expr_v: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::EXPRV,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::ExprV { expr_v: v.deep_view() },
            ),
    {
        let param = ExprListParam {
            which: WhichSCC1::EXPRV,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.serialize_expr_v_gas(gas, param, v, obuf);
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &ExprV<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::EXPRV,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::ExprV { expr_v: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::EXPRV,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::ExprV { expr_v: v.deep_view() },
                )
            },
    {
        let param = ExprListParam {
            which: WhichSCC1::EXPRV,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.prepare_expr_v_gas(gas, param, v)
    }
}

impl<const LIMIT: usize> ListVConsFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ListVCons<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LISTVCONS,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    ibuf@,
                ) {
                    Some((n, SCC1::ListVCons { list_v_cons })) => Some((n, list_v_cons)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
    {
        let param = ExprListParam {
            which: WhichSCC1::LISTVCONS,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.parse_list_v_cons_gas(gas, param, ibuf)
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &ListVCons<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::LISTVCONS,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::ListVCons { list_v_cons: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::LISTVCONS,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::ListVCons { list_v_cons: v.deep_view() },
            ),
    {
        let param = ExprListParam {
            which: WhichSCC1::LISTVCONS,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.serialize_list_v_cons_gas(gas, param, v, obuf);
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &ListVCons<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LISTVCONS,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::ListVCons { list_v_cons: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LISTVCONS,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::ListVCons { list_v_cons: v.deep_view() },
                )
            },
    {
        let param = ExprListParam {
            which: WhichSCC1::LISTVCONS,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.prepare_list_v_cons_gas(gas, param, v)
    }
}

impl<const LIMIT: usize> ListVFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ListV<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, ExprListParam>::spec_parse_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LISTV,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    ibuf@,
                ) {
                    Some((n, SCC1::ListV { list_v })) => Some((n, list_v)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
    {
        let param = ExprListParam {
            which: WhichSCC1::LISTV,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.parse_list_v_gas(gas, param, ibuf)
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &ListV<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::LISTV,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::ListV { list_v: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                ExprListParam,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                ExprListParam {
                    which: WhichSCC1::LISTV,
                    expr_kind: ExprKind::Num,
                    list_kind: ListKind::Nil,
                },
                SCC1::ListV { list_v: v.deep_view() },
            ),
    {
        let param = ExprListParam {
            which: WhichSCC1::LISTV,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.serialize_list_v_gas(gas, param, v, obuf);
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &ListV<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, ExprListRecBody, ExprListParam>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LISTV,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::ListV { list_v: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, ExprListParam>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    ExprListParam {
                        which: WhichSCC1::LISTV,
                        expr_kind: ExprKind::Num,
                        list_kind: ListKind::Nil,
                    },
                    SCC1::ListV { list_v: v.deep_view() },
                )
            },
    {
        let param = ExprListParam {
            which: WhichSCC1::LISTV,
            expr_kind: ExprKind::Num,
            list_kind: ListKind::Nil,
        };
        ExprFmt::<LIMIT>.prepare_list_v_gas(gas, param, v)
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ExprFmt<LIMIT> {
    type PT = Expr<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<'i, const LIMIT: usize> Serializer<Expr<'i>> for ExprFmt<LIMIT> {
    fn serialize(&self, v: &Expr<'i>, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<'i, const LIMIT: usize> Prepare<Expr<'i>> for ExprFmt<LIMIT> {
    fn prepare(&self, v: &Expr<'i>) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ListFmt<LIMIT> {
    type PT = List<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<'i, const LIMIT: usize> Serializer<List<'i>> for ListFmt<LIMIT> {
    fn serialize(&self, v: &List<'i>, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<'i, const LIMIT: usize> Prepare<List<'i>> for ListFmt<LIMIT> {
    fn prepare(&self, v: &List<'i>) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ExprVFmt<LIMIT> {
    type PT = ExprV<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<'i, const LIMIT: usize> Serializer<ExprV<'i>> for ExprVFmt<LIMIT> {
    fn serialize(&self, v: &ExprV<'i>, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<'i, const LIMIT: usize> Prepare<ExprV<'i>> for ExprVFmt<LIMIT> {
    fn prepare(&self, v: &ExprV<'i>) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ListVConsFmt<LIMIT> {
    type PT = ListVCons<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<'i, const LIMIT: usize> Serializer<ListVCons<'i>> for ListVConsFmt<LIMIT> {
    fn serialize(&self, v: &ListVCons<'i>, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<'i, const LIMIT: usize> Prepare<ListVCons<'i>> for ListVConsFmt<LIMIT> {
    fn prepare(&self, v: &ListVCons<'i>) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ListVFmt<LIMIT> {
    type PT = ListV<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        self.parse_gas(LIMIT, ibuf)
    }
}

impl<'i, const LIMIT: usize> Serializer<ListV<'i>> for ListVFmt<LIMIT> {
    fn serialize(&self, v: &ListV<'i>, obuf: &mut Vec<u8>) {
        self.serialize_gas(LIMIT, v, obuf);
    }
}

impl<'i, const LIMIT: usize> Prepare<ListV<'i>> for ListVFmt<LIMIT> {
    fn prepare(&self, v: &ListV<'i>) -> Result<usize, PreSerializeError> {
        self.prepare_gas(LIMIT, v)
    }
}

impl<const LIMIT: usize> ByteListFmt<LIMIT> {
    fn parse_gas(&self, gas: usize, ibuf: &&[u8]) -> (r: PResult<ByteList>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ByteListRecBody, WhichFmt2>::spec_parse_gas(
                    &ByteListRecBody,
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
            FixWith::<LIMIT, ByteListRecBody, WhichFmt2>::consistent_gas(
                &ByteListRecBody,
                gas as nat,
                WhichFmt2::BYTELIST,
                ByteListValue::ByteList { list: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ByteListRecBody,
                WhichFmt2,
            >::spec_serialize_gas(
                &ByteListRecBody,
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
                &&& FixWith::<LIMIT, ByteListRecBody, WhichFmt2>::consistent_gas(
                    &ByteListRecBody,
                    gas as nat,
                    WhichFmt2::BYTELIST,
                    ByteListValue::ByteList { list: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ByteListRecBody, WhichFmt2>::byte_len_gas(
                    &ByteListRecBody,
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
                match FixWith::<LIMIT, ChainRecBody, ChainParam>::spec_parse_gas(
                    &ChainRecBody,
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
            FixWith::<LIMIT, ChainRecBody, ChainParam>::consistent_gas(
                &ChainRecBody,
                gas as nat,
                ChainParam { which: WhichChain::A, tag: self.tag },
                ChainValueSpec::A { a: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ChainRecBody,
                ChainParam,
            >::spec_serialize_gas(
                &ChainRecBody,
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
                &&& FixWith::<LIMIT, ChainRecBody, ChainParam>::consistent_gas(
                    &ChainRecBody,
                    gas as nat,
                    ChainParam { which: WhichChain::A, tag: self.tag },
                    ChainValueSpec::A { a: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ChainRecBody, ChainParam>::byte_len_gas(
                    &ChainRecBody,
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
                match FixWith::<LIMIT, ChainRecBody, ChainParam>::spec_parse_gas(
                    &ChainRecBody,
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
            FixWith::<LIMIT, ChainRecBody, ChainParam>::consistent_gas(
                &ChainRecBody,
                gas as nat,
                ChainParam { which: WhichChain::B, tag: self.tag },
                ChainValueSpec::B { b: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ChainRecBody,
                ChainParam,
            >::spec_serialize_gas(
                &ChainRecBody,
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
                &&& FixWith::<LIMIT, ChainRecBody, ChainParam>::consistent_gas(
                    &ChainRecBody,
                    gas as nat,
                    ChainParam { which: WhichChain::B, tag: self.tag },
                    ChainValueSpec::B { b: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ChainRecBody, ChainParam>::byte_len_gas(
                    &ChainRecBody,
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
