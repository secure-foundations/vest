use crate::combinators::mapped::spec::*;
use crate::combinators::recursive::exec::*;
use crate::combinators::recursive::*;
use crate::combinators::*;
use crate::core::exec::fns::{FnParser, FnSerializer};
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
 *   Num    = 0x10,
 *   Group  = 0x11,
 *   Forest = 0x12,
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
 *     Forest => forest,
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
 *   }
 * }
 *
 * forest = {
 *   len: u8,
 *   items: [expr; @len],
 * }
 *
 * outer = forest
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
    Forest = 18,
}

pub type ExprKindSpec = ExprKind;

pub type ExprKindInner = u8;

impl DeepView for ExprKind {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
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

    open spec fn deep_view(&self) -> Self::V
        decreases *self,
    {
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

    open spec fn deep_view(&self) -> Self::V
        decreases *self,
    {
        list_view(self)
    }
}

# [doc = "data type for `expr_v`."]
# [derive (Debug, PartialEq, Eq)]
pub enum ExprV<'i> {
    Num(u8),
    Group(Box<List<'i>>),
    Forest(Box<Forest<'i>>),
}

# [verifier::ext_equal]
pub enum ExprVSpec {
    Num(u8),
    Group(Box<ListSpec>),
    Forest(Box<ForestSpec>),
}

pub type ExprVInner = Sum<u8, Sum<Box<ListSpec>, Box<ForestSpec>>>;

pub open spec fn expr_v_view(x: &ExprV) -> ExprVSpec
    decreases *x,
{
    match x {
        ExprV::Num(v) => ExprVSpec::Num(v.deep_view()),
        ExprV::Group(v) => ExprVSpec::Group(Box::new(list_view(&**v))),
        ExprV::Forest(v) => ExprVSpec::Forest(Box::new(forest_view(&**v))),
    }
}

impl<'i> DeepView for ExprV<'i> {
    type V = ExprVSpec;

    open spec fn deep_view(&self) -> Self::V
        decreases *self,
    {
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

    open spec fn deep_view(&self) -> Self::V
        decreases *self,
    {
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

    open spec fn deep_view(&self) -> Self::V
        decreases *self,
    {
        list_v_view(self)
    }
}

#[doc = "data type for `forest`."]
#[derive(Debug, PartialEq, Eq)]
pub struct Forest<'i> {
    pub len: u8,
    pub items: Vec<Expr<'i>>,
}

#[verifier::ext_equal]
pub struct ForestSpec {
    pub len: u8,
    pub items: Seq<ExprSpec>,
}

pub type ForestInner = (u8, Seq<ExprSpec>);

pub open spec fn forest_view(x: &Forest) -> ForestSpec
    decreases *x,
{
    ForestSpec {
        len: x.len.deep_view(),
        items: Seq::new(x.items@.len(), |i: int| {
            if 0 <= i < x.items@.len() {
                proof {
                    assert(decreases_to!(*x => x.items));
                };
                expr_view(&x.items@[i])
            } else {
                arbitrary()
            }
        }),
    }
}

impl<'i> DeepView for Forest<'i> {
    type V = ForestSpec;

    open spec fn deep_view(&self) -> Self::V
        decreases *self,
    {
        forest_view(self)
    }
}

# [verifier::ext_equal]
pub enum SCC1 {
    Expr { expr: ExprSpec },
    List { list: ListSpec },
    ExprV { expr_v: ExprVSpec },
    Forest { forest: ForestSpec },
    ListVCons { list_v_cons: ListVConsSpec },
    ListV { list_v: ListVSpec },
}

# [derive (Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum SCC1Which {
    EXPR,
    LIST,
    EXPRV,
    FOREST,
    LISTVCONS,
    LISTV,
}

impl DeepView for SCC1Which {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [derive (Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub struct SCC1Param {
    pub which: SCC1Which,
    pub expr_kind: ExprKind,
    pub list_kind: ListKind,
}

impl DeepView for SCC1Param {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
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
                inner: Refined(U8, |x: u8| (x == 16) || (x == 17) || (x == 18)),
                mapper: (
                    |parsed: ExprKindInner| -> ExprKindSpec
                        {
                            match parsed {
                                16 => ExprKindSpec::Num,
                                17 => ExprKindSpec::Group,
                                18 => ExprKindSpec::Forest,
                                _ => arbitrary(),
                            }
                        },
                    |value: ExprKindSpec| -> ExprKindInner
                        {
                            match value {
                                ExprKindSpec::Num => 16,
                                ExprKindSpec::Group => 17,
                                ExprKindSpec::Forest => 18,
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

pub type ForestProj<Rec> = Mapped<Refined<Rec, PredFnSpec<SCC1>>, FnSpecMapper<SCC1, ForestSpec>>;

pub open spec fn forest_proj<Rec>(rec: Rec) -> ForestProj<Rec> where
    Rec: SpecCombinator<T = SCC1>,
{
    Mapped {
        inner: Refined(rec, |v: SCC1| v is Forest),
        mapper: (
            |v: SCC1| -> ForestSpec { v->forest },
            |forest: ForestSpec| -> SCC1 { SCC1::Forest { forest } },
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

pub type ExprFmtSpec<const LIMIT: usize> = ExprProj<FixWith<LIMIT, SCC1RecBody, SCC1Param>>;

# [derive (Clone, Copy)]
pub struct ExprFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ExprFmt<LIMIT> {
    pub open spec fn spec_inner() -> ExprFmtSpec<LIMIT> {
        expr_proj(
            FixWith::<LIMIT, _, _>(
                SCC1RecBody,
                SCC1Param {
                    which: SCC1Which::EXPR,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
            ),
        )
    }
}

pub type ListFmtSpec<const LIMIT: usize> = ListProj<FixWith<LIMIT, SCC1RecBody, SCC1Param>>;

# [derive (Clone, Copy)]
pub struct ListFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ListFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListFmtSpec<LIMIT> {
        list_proj(
            FixWith::<LIMIT, _, _>(
                SCC1RecBody,
                SCC1Param {
                    which: SCC1Which::LIST,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
            ),
        )
    }
}

pub type ExprVFmtSpec<const LIMIT: usize> = ExprVProj<FixWith<LIMIT, SCC1RecBody, SCC1Param>>;

# [derive (Clone, Copy)]
pub struct ExprVFmt<const LIMIT: usize> {
    pub expr_kind: ExprKind,
}

impl<const LIMIT: usize> ExprVFmt<LIMIT> {
    pub open spec fn spec_inner(expr_kind: ExprKind) -> ExprVFmtSpec<LIMIT> {
        expr_v_proj(
            FixWith::<LIMIT, _, _>(
                SCC1RecBody,
                SCC1Param { which: SCC1Which::EXPRV, expr_kind, list_kind: arbitrary() },
            ),
        )
    }
}

pub type ForestFmtSpec<const LIMIT: usize> = ForestProj<FixWith<LIMIT, SCC1RecBody, SCC1Param>>;

#[derive(Clone, Copy)]
pub struct ForestFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ForestFmt<LIMIT> {
    pub open spec fn spec_inner() -> ForestFmtSpec<LIMIT> {
        forest_proj(
            FixWith::<LIMIT, _, _>(
                SCC1RecBody,
                SCC1Param {
                    which: SCC1Which::FOREST,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
            ),
        )
    }
}

pub type ListVConsFmtSpec<const LIMIT: usize> = ListVConsProj<
    FixWith<LIMIT, SCC1RecBody, SCC1Param>,
>;

# [derive (Clone, Copy)]
pub struct ListVConsFmt<const LIMIT: usize>;

impl<const LIMIT: usize> ListVConsFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListVConsFmtSpec<LIMIT> {
        list_v_cons_proj(
            FixWith::<LIMIT, _, _>(
                SCC1RecBody,
                SCC1Param {
                    which: SCC1Which::LISTVCONS,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
            ),
        )
    }
}

pub type ListVFmtSpec<const LIMIT: usize> = ListVProj<FixWith<LIMIT, SCC1RecBody, SCC1Param>>;

# [derive (Clone, Copy)]
pub struct ListVFmt<const LIMIT: usize> {
    pub list_kind: ListKind,
}

impl<const LIMIT: usize> ListVFmt<LIMIT> {
    pub open spec fn spec_inner(list_kind: ListKind) -> ListVFmtSpec<LIMIT> {
        list_v_proj(
            FixWith::<LIMIT, _, _>(
                SCC1RecBody,
                SCC1Param { which: SCC1Which::LISTV, expr_kind: arbitrary(), list_kind },
            ),
        )
    }
}

pub struct ForestMapper;

impl SpecMapper for ForestMapper {
    type In = ForestInner;

    type Out = SCC1;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        let (len, items) = i;
        items.len() == len as int
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (len, items) = i;
        SCC1::Forest { forest: ForestSpec { len, items } }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        &&& o is Forest
        &&& o->forest.items.len() == o->forest.len as int
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::Forest { forest: ForestSpec { len, items } } => (len, items),
            _ => arbitrary(),
        }
    }
}

#[doc = "named format combinator for `outer`."]
#[derive(Clone, Copy)]
pub struct OuterFmt<const LIMIT: usize>;

pub type OuterFmtSpec<const LIMIT: usize> = Named<ForestFmt<LIMIT>>;

impl<const LIMIT: usize> OuterFmt<LIMIT> {
    pub open spec fn spec_inner() -> OuterFmtSpec<LIMIT> {
        Named("outer", ForestFmt::<LIMIT>)
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
    type In = Sum<u8, Sum<ListSpec, ForestSpec>>;

    type Out = SCC1;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(v) => SCC1::ExprV { expr_v: ExprVSpec::Num(v) },
            Sum::Inr(Sum::Inl(v)) => SCC1::ExprV { expr_v: ExprVSpec::Group(Box::new(v)) },
            Sum::Inr(Sum::Inr(v)) => SCC1::ExprV { expr_v: ExprVSpec::Forest(Box::new(v)) },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ExprV
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::ExprV { expr_v: ExprVSpec::Num(v) } => Sum::Inl(v),
            SCC1::ExprV { expr_v: ExprVSpec::Group(v) } => Sum::Inr(Sum::Inl(*v)),
            SCC1::ExprV { expr_v: ExprVSpec::Forest(v) } => Sum::Inr(Sum::Inr(*v)),
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

pub type ExprBodyFmt<Rec> = Mapped<
    Bind<ExprKindFmt, spec_fn(ExprKindSpec) -> ExprVProj<Rec>>,
    ExprMapper,
>;

pub struct ExprBodyRec;

impl SpecRecBody for ExprBodyRec {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = ExprBodyFmt<BundledSpecs<Self::T>>;

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
                            SCC1Param {
                                which: SCC1Which::EXPRV,
                                expr_kind: t,
                                list_kind: arbitrary(),
                            },
                        ),
                    ),
            ),
            mapper: ExprMapper,
        }
    }
}

pub type ListBodyFmt<Rec> = Mapped<
    Bind<ListKindFmt, spec_fn(ListKindSpec) -> ListVProj<Rec>>,
    ListMapper,
>;

pub struct ListBodyRec;

impl SpecRecBody for ListBodyRec {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = ListBodyFmt<BundledSpecs<Self::T>>;

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
                            SCC1Param {
                                which: SCC1Which::LISTV,
                                expr_kind: arbitrary(),
                                list_kind: t,
                            },
                        ),
                    ),
            ),
            mapper: ListMapper,
        }
    }
}

pub type ExprVBodyFmt<Rec> = Mapped<Sum<U8, Sum<ListProj<Rec>, ForestProj<Rec>>>, ExprVMapper>;

pub struct ExprVBodyRec;

impl SpecRecBody for ExprVBodyRec {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = ExprVBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.expr_kind {
                ExprKind::Num => Sum::Inl(U8),
                ExprKind::Group => Sum::Inr(Sum::Inl(
                    list_proj(
                        rec(
                            SCC1Param {
                                which: SCC1Which::LIST,
                                expr_kind: arbitrary(),
                                list_kind: arbitrary(),
                            },
                        ),
                    ),
                )),
                ExprKind::Forest => Sum::Inr(Sum::Inr(
                    forest_proj(
                        rec(
                            SCC1Param {
                                which: SCC1Which::FOREST,
                                expr_kind: arbitrary(),
                                list_kind: arbitrary(),
                            },
                        ),
                    ),
                )),
            },
            mapper: ExprVMapper,
        }
    }
}

pub type ForestBodyFmt<Rec> = Mapped<Bind<U8, spec_fn(u8) -> RepeatN<ExprProj<Rec>, u8>>, ForestMapper>;

pub struct ForestBodyRec;

impl SpecRecBody for ForestBodyRec {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = ForestBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        _param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Bind(
                U8,
                |len: u8|
                    RepeatN(
                        len,
                        expr_proj(
                            rec(
                                SCC1Param {
                                    which: SCC1Which::EXPR,
                                    expr_kind: arbitrary(),
                                    list_kind: arbitrary(),
                                },
                            ),
                        ),
                    ),
            ),
            mapper: ForestMapper,
        }
    }
}

pub type ListVConsBodyFmt<Rec> = Mapped<Pair<ExprProj<Rec>, ListProj<Rec>>, ListVConsMapper>;

pub struct ListVConsBodyRec;

impl SpecRecBody for ListVConsBodyRec {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = ListVConsBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Pair(
                expr_proj(
                    rec(
                        SCC1Param {
                            which: SCC1Which::EXPR,
                            expr_kind: arbitrary(),
                            list_kind: arbitrary(),
                        },
                    ),
                ),
                list_proj(
                    rec(
                        SCC1Param {
                            which: SCC1Which::LIST,
                            expr_kind: arbitrary(),
                            list_kind: arbitrary(),
                        },
                    ),
                ),
            ),
            mapper: ListVConsMapper,
        }
    }
}

pub type ListVBodyFmt<Rec> = Mapped<Sum<Fixed<0>, ListVConsProj<Rec>>, ListVMapper>;

pub struct ListVBodyRec;

impl SpecRecBody for ListVBodyRec {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = ListVBodyFmt<BundledSpecs<Self::T>>;

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
                            SCC1Param {
                                which: SCC1Which::LISTVCONS,
                                expr_kind: arbitrary(),
                                list_kind: arbitrary(),
                            },
                        ),
                    ),
                ),
            },
            mapper: ListVMapper,
        }
    }
}

pub struct SCC1RecBody;

impl SpecRecBody for SCC1RecBody {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = Alt<
        Cond<ExprBodyFmt<BundledSpecs<SCC1>>>,
        Alt<
            Cond<ListBodyFmt<BundledSpecs<SCC1>>>,
            Alt<
                Cond<ExprVBodyFmt<BundledSpecs<SCC1>>>,
                Alt<
                    Cond<ForestBodyFmt<BundledSpecs<SCC1>>>,
                    Alt<
                        Cond<ListVConsBodyFmt<BundledSpecs<SCC1>>>,
                        Cond<ListVBodyFmt<BundledSpecs<SCC1>>>,
                    >,
                >,
            >,
        >,
    >;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Alt(
            Cond(param.which == SCC1Which::EXPR, ExprBodyRec.spec_body(param, rec)),
            Alt(
                Cond(param.which == SCC1Which::LIST, ListBodyRec.spec_body(param, rec)),
                Alt(
                    Cond(param.which == SCC1Which::EXPRV, ExprVBodyRec.spec_body(param, rec)),
                    Alt(
                        Cond(param.which == SCC1Which::FOREST, ForestBodyRec.spec_body(param, rec)),
                        Alt(
                            Cond(
                                param.which == SCC1Which::LISTVCONS,
                                ListVConsBodyRec.spec_body(param, rec),
                            ),
                            Cond(param.which == SCC1Which::LISTV, ListVBodyRec.spec_body(param, rec)),
                        ),
                    ),
                ),
            ),
        )
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
            Self::spec_inner(self.expr_kind.deep_view()).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ExprVFmt<LIMIT> {
        type Val = ExprVSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.expr_kind.deep_view()).consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ExprVFmt<LIMIT> {
        type T = ExprVSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.expr_kind.deep_view()).byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ExprVFmt<LIMIT> {
        type SValue = ExprVSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.expr_kind.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ExprVFmt<LIMIT> {
        type SVal = ExprVSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.expr_kind.deep_view()).spec_serialize(v)
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
            Self::spec_inner(self.list_kind.deep_view()).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ListVFmt<LIMIT> {
        type Val = ListVSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.list_kind.deep_view()).consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ListVFmt<LIMIT> {
        type T = ListVSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.list_kind.deep_view()).byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ListVFmt<LIMIT> {
        type SValue = ListVSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.list_kind.deep_view()).spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ListVFmt<LIMIT> {
        type SVal = ListVSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.list_kind.deep_view()).spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ForestFmt<LIMIT> {
        type PVal = ForestSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ForestFmt<LIMIT> {
        type Val = ForestSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ForestFmt<LIMIT> {
        type T = ForestSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ForestFmt<LIMIT> {
        type SValue = ForestSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ForestFmt<LIMIT> {
        type SVal = ForestSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for OuterFmt<LIMIT> {
        type PVal = ForestSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for OuterFmt<LIMIT> {
        type Val = ForestSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for OuterFmt<LIMIT> {
        type T = ForestSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for OuterFmt<LIMIT> {
        type SValue = ForestSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for OuterFmt<LIMIT> {
        type SVal = ForestSpec;

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
            Self::spec_inner(self.expr_kind.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ExprVFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ExprVFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ExprVFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.expr_kind.deep_view());
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
            Self::spec_inner(self.list_kind.deep_view()).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ListVFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ListVFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ListVFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ListVFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ListVFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ListVFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ListVFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.list_kind.deep_view());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for ForestFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ForestFmt<LIMIT> {
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

    impl<const LIMIT: usize> NonTailFmt for ForestFmt<LIMIT> {
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

    impl<const LIMIT: usize> GoodSerializer for ForestFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ForestFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ForestFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ForestFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ForestFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for OuterFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for OuterFmt<LIMIT> {
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

    impl<const LIMIT: usize> NonTailFmt for OuterFmt<LIMIT> {
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

    impl<const LIMIT: usize> GoodSerializer for OuterFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for OuterFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for OuterFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for OuterFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for OuterFmt<LIMIT> {
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

    impl LossyMapper for ForestMapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
            assert(self.spec_map(self.spec_map_rev(o)) == o);
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
            assert(self.wf_in(self.spec_map_rev(o)));
        }
    }

    impl LosslessMapper for ForestMapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
            assert(self.wf_out(self.spec_map(i)));
        }
    }

    impl StrictRecBody for ExprBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ExprVBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ForestBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListVBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListVConsBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vest_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for SCC1RecBody {
        proof fn lemma_body_all_inv_preservation(
            &self,
            param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            hide(<ExprBodyRec as SpecRecBody>::spec_body);
            hide(<ListBodyRec as SpecRecBody>::spec_body);
            hide(<ExprVBodyRec as SpecRecBody>::spec_body);
            hide(<ForestBodyRec as SpecRecBody>::spec_body);
            hide(<ListVBodyRec as SpecRecBody>::spec_body);
            hide(<ListVConsBodyRec as SpecRecBody>::spec_body);
            broadcast use vest_lib::combinators::disjoint::disjointness_lemmas;

            ExprBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListBodyRec.lemma_body_all_inv_preservation(param, rec);
            ExprVBodyRec.lemma_body_all_inv_preservation(param, rec);
            ForestBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListVBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListVConsBodyRec.lemma_body_all_inv_preservation(param, rec);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
mod derived_execs {
    use super::*;

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
                18 => ExprKind::Forest,
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
                ExprKind::Forest => 18,
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
                ExprKind::Forest => 18,
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

    impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ForestFmt<LIMIT> {
        type PT = Forest<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            self.parse_gas(LIMIT, ibuf)
        }
    }

    impl<'i, const LIMIT: usize> Serializer<Forest<'i>> for ForestFmt<LIMIT> {
        fn serialize(&self, v: &Forest<'i>, obuf: &mut Vec<u8>) {
            self.serialize_gas(LIMIT, v, obuf);
        }
    }

    impl<'i, const LIMIT: usize> Prepare<Forest<'i>> for ForestFmt<LIMIT> {
        fn prepare(&self, v: &Forest<'i>) -> Result<usize, PreSerializeError> {
            self.prepare_gas(LIMIT, v)
        }
    }

    impl<'i, const LIMIT: usize> Parser<&'i [u8]> for OuterFmt<LIMIT> {
        type PT = Forest<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            Named("outer", ForestFmt::<LIMIT>).parse(ibuf)
        }
    }

    impl<'i, const LIMIT: usize> Serializer<Forest<'i>> for OuterFmt<LIMIT> {
        fn serialize(&self, v: &Forest<'i>, obuf: &mut Vec<u8>) {
            Named("outer", ForestFmt::<LIMIT>).serialize(v, obuf);
        }
    }

    impl<'i, const LIMIT: usize> Prepare<Forest<'i>> for OuterFmt<LIMIT> {
        fn prepare(&self, v: &Forest<'i>) -> Result<usize, PreSerializeError> {
            Named("outer", ForestFmt::<LIMIT>).prepare(v)
        }
    }

}

impl<const LIMIT: usize> ExprFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<Expr<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::EXPR,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
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
        let (n1, expr_kind) = ExprKindFmt.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        if gas > 0 {
            let (n2, v) = ExprVFmt::<LIMIT> { expr_kind }.parse_gas(gas - 1, &rest)?;
            Ok((n1 + n2, Expr { t: expr_kind, v: Box::new(v) }))
        } else {
            Err(ParseError::recursion_limit_exceeded())
        }
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &Expr<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::EXPR,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
                SCC1::Expr { expr: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                SCC1RecBody,
                SCC1Param,
            >::spec_serialize_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::EXPR,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
                SCC1::Expr { expr: v.deep_view() },
            ),
        decreases gas,
    {
        ExprKindFmt.serialize(&v.t, obuf);
        ExprVFmt::<LIMIT> { expr_kind: v.t }.serialize_gas(gas - 1, &v.v, obuf);
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &Expr<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::EXPR,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    SCC1::Expr { expr: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::EXPR,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    SCC1::Expr { expr: v.deep_view() },
                )
            },
        decreases gas,
    {
        let l1 = ExprKindFmt.prepare(&v.t)?;
        if gas == 0 {
            return Err(
                PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
            );
        }
        let l2 = ExprVFmt::<LIMIT> { expr_kind: v.t }.prepare_gas(gas - 1, &v.v)?;
        let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
        Ok(total)
    }
}

impl<const LIMIT: usize> ListFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<List<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LIST,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
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
        let (n1, list_kind) = ListKindFmt.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        if gas > 0 {
            let (n2, v) = ListVFmt::<LIMIT> { list_kind }.parse_gas(gas - 1, &rest)?;
            Ok((n1 + n2, List { t: list_kind, v: Box::new(v) }))
        } else {
            Err(ParseError::recursion_limit_exceeded())
        }
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &List<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::LIST,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
                SCC1::List { list: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                SCC1RecBody,
                SCC1Param,
            >::spec_serialize_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::LIST,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
                SCC1::List { list: v.deep_view() },
            ),
        decreases gas,
    {
        ListKindFmt.serialize(&v.t, obuf);
        ListVFmt::<LIMIT> { list_kind: v.t }.serialize_gas(gas - 1, &v.v, obuf);
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &List<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LIST,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    SCC1::List { list: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LIST,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    SCC1::List { list: v.deep_view() },
                )
            },
        decreases gas,
    {
        let l1 = ListKindFmt.prepare(&v.t)?;
        if gas == 0 {
            return Err(
                PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
            );
        }
        let l2 = ListVFmt::<LIMIT> { list_kind: v.t }.prepare_gas(gas - 1, &v.v)?;
        let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
        Ok(total)
    }
}

impl<const LIMIT: usize> ExprVFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ExprV<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::EXPRV,
                        expr_kind: self.expr_kind.deep_view(),
                        list_kind: arbitrary(),
                    },
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->expr_v)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        match self.expr_kind {
            ExprKind::Num => {
                let (n1, v) = U8.parse(ibuf)?;
                Ok((n1, ExprV::Num(v)))
            },
            ExprKind::Group => {
                if gas > 0 {
                    let (n1, v) = ListFmt::<LIMIT>.parse_gas(gas - 1, ibuf)?;
                    Ok((n1, ExprV::Group(Box::new(v))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
            ExprKind::Forest => {
                if gas > 0 {
                    let (n1, v) = ForestFmt::<LIMIT>.parse_gas(gas - 1, ibuf)?;
                    Ok((n1, ExprV::Forest(Box::new(v))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
        }
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &ExprV<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::EXPRV,
                    expr_kind: self.expr_kind.deep_view(),
                    list_kind: arbitrary(),
                },
                SCC1::ExprV { expr_v: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                SCC1RecBody,
                SCC1Param,
            >::spec_serialize_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::EXPRV,
                    expr_kind: self.expr_kind,
                    list_kind: arbitrary(),
                },
                SCC1::ExprV { expr_v: v.deep_view() },
            ),
        decreases gas,
    {
        match v {
            ExprV::Num(n) => {
                U8.serialize(n, obuf);
            },
            ExprV::Group(list) => {
                ListFmt::<LIMIT>.serialize_gas(gas - 1, list, obuf);
            },
            ExprV::Forest(forest) => {
                ForestFmt::<LIMIT>.serialize_gas(gas - 1, forest, obuf);
            },
        }
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &ExprV<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::EXPRV,
                        expr_kind: self.expr_kind.deep_view(),
                        list_kind: arbitrary(),
                    },
                    SCC1::ExprV { expr_v: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::EXPRV,
                        expr_kind: self.expr_kind.deep_view(),
                        list_kind: arbitrary(),
                    },
                    SCC1::ExprV { expr_v: v.deep_view() },
                )
            },
        decreases gas,
    {
        match (self.expr_kind, v) {
            (ExprKind::Num, ExprV::Num(n)) => { U8.prepare(n) },
            (ExprKind::Group, ExprV::Group(list)) => {
                if gas == 0 {
                    return Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    );
                }
                ListFmt::<LIMIT>.prepare_gas(gas - 1, list)
            },
            (ExprKind::Forest, ExprV::Forest(forest)) => {
                if gas == 0 {
                    return Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    );
                }
                ForestFmt::<LIMIT>.prepare_gas(gas - 1, forest)
            },
            _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::CondRejected)),
        }
    }
}

impl<const LIMIT: usize> ForestFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<Forest<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::FOREST,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->forest)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        hide(<ExprBodyRec as SpecRecBody>::spec_body);
        hide(<ListBodyRec as SpecRecBody>::spec_body);
        hide(<ExprVBodyRec as SpecRecBody>::spec_body);
        hide(<ListVBodyRec as SpecRecBody>::spec_body);
        hide(<ListVConsBodyRec as SpecRecBody>::spec_body);
        hide(<SCC1RecBody as SpecRecBody>::spec_body);

        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let ghost forest_param = SCC1Param {
            which: SCC1Which::FOREST,
            expr_kind: arbitrary(),
            list_kind: arbitrary(),
        };
        let ghost expr_param = SCC1Param {
            which: SCC1Which::EXPR,
            expr_kind: arbitrary(),
            list_kind: arbitrary(),
        };
        let ghost callback = FixWith::<LIMIT, SCC1RecBody, SCC1Param>::specs_callback(
            &SCC1RecBody,
            gas as nat,
        );
        let ghost expr_spec = expr_proj(callback(expr_param));
        let ghost parse_spec =
            match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
                &SCC1RecBody,
                gas as nat,
                forest_param,
                ibuf@,
            ) {
                Some((n, v)) => Some((n, v->forest)),
                _ => None,
            };
        let _ = ibuf.len();
        let (n1, len) = U8.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        if gas == 0 {
            Err(ParseError::recursion_limit_exceeded())
        } else {
            let expr_exec = |buf: &&'i [u8]| -> (rr: PResult<Expr<'i>>)
                ensures
                    parse_matches_spec(rr, expr_spec.spec_parse(buf@)),
            {
                proof {
                    let pg = FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
                        &SCC1RecBody,
                        (gas - 1) as nat,
                        expr_param,
                        buf@,
                    );
                    if let Some((n, v)) = pg {
                        FixWith::<LIMIT, SCC1RecBody, SCC1Param>(
                            SCC1RecBody,
                            expr_param,
                        ).sound_parser_by_induction((gas - 1) as nat, expr_param, buf@, n, v);
                        reveal(<SCC1RecBody as SpecRecBody>::spec_body);
                        reveal(<ExprBodyRec as SpecRecBody>::spec_body);
                        assert(FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                            &SCC1RecBody,
                            (gas - 1) as nat,
                            expr_param,
                            v,
                        ));
                        assert(v is Expr);
                    }
                }
                ExprFmt::<LIMIT>.parse_gas(gas - 1, buf)
            };
            proof {
                let fix = FixWith::<LIMIT, SCC1RecBody, SCC1Param>(SCC1RecBody, forest_param);
                fix.lemma_specs_callback_safe_inv(gas as nat, expr_param);
                fix.lemma_specs_callback_productive_inv(gas as nat, expr_param);
                assert(expr_spec.safe_inv());
                assert(expr_spec.productive_inv());
            }
            let expr_parser: FnParser<&'i [u8], Expr<'i>, _, _> = FnParser::new(
                expr_exec,
                Ghost(expr_spec),
            );
            let repeat_expr = RepeatN(len, expr_parser);
            assume(repeat_expr.exec_inv());
            assume(repeat_expr.safe_inv());
            proof {
                repeat_expr.lemma_parse_safe(rest@);
            }
            let (n2, items) = repeat_expr.parse(&rest)?;
            let v = Forest { len, items };
            Ok((n1 + n2, v))
        }
    }

    #[verifier::external_body]
    fn serialize_gas<'i>(&self, gas: usize, v: &Forest<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::FOREST,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
                SCC1::Forest { forest: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                SCC1RecBody,
                SCC1Param,
            >::spec_serialize_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::FOREST,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
                SCC1::Forest { forest: v.deep_view() },
            ),
        decreases gas,
    {
        let ghost old_obuf = obuf@;
        U8.serialize(&v.len, obuf);
        if v.len != 0 {
            let ghost expr_param = SCC1Param {
                which: SCC1Which::EXPR,
                expr_kind: arbitrary(),
                list_kind: arbitrary(),
            };
            let ghost expr_spec = expr_proj(
                FixWith::<LIMIT, SCC1RecBody, SCC1Param>::specs_callback(
                    &SCC1RecBody,
                    gas as nat,
                )(expr_param),
            );
            let expr_serializer =
                |expr: &Expr<'i>, obuf: &mut Vec<u8>| -> ()
                    requires
                        expr_spec.consistent(expr.deep_view()),
                    ensures
                        final(obuf)@ == old(obuf)@ + expr_spec.spec_serialize(expr.deep_view()),
                {
                    proof {
                        assert(gas > 0) by {
                            if gas == 0 {
                                assert(!expr_spec.consistent(expr.deep_view()));
                            }
                        }
                        assert(
                            expr_spec.consistent(expr.deep_view())
                                == FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                                    &SCC1RecBody,
                                    (gas - 1) as nat,
                                    expr_param,
                                    SCC1::Expr { expr: expr.deep_view() },
                                )
                        );
                    }
                    ExprFmt::<LIMIT>.serialize_gas(gas - 1, expr, obuf);
                    proof {
                        assert(
                            expr_spec.spec_serialize(expr.deep_view())
                                == FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_serialize_gas(
                                    &SCC1RecBody,
                                    (gas - 1) as nat,
                                    expr_param,
                                    SCC1::Expr { expr: expr.deep_view() },
                                )
                        );
                    }
                };
            let expr_serializer: FnSerializer<Expr<'i>, _, _> = FnSerializer::new(
                expr_serializer,
                Ghost(expr_spec),
            );
            proof {
                assert(expr_serializer.exec_inv());
            }
            let expr_repeat = RepeatN(v.len, expr_serializer);
            proof {
                assert(expr_repeat.1.exec_inv());
                assert(expr_repeat.consistent(v.items.deep_view()));
            }
            expr_repeat.serialize(&v.items, obuf);
        }
        assert(obuf@ == old_obuf + FixWith::<
            LIMIT,
            SCC1RecBody,
            SCC1Param,
        >::spec_serialize_gas(
            &SCC1RecBody,
            gas as nat,
            SCC1Param {
                which: SCC1Which::FOREST,
                expr_kind: arbitrary(),
                list_kind: arbitrary(),
            },
            SCC1::Forest { forest: v.deep_view() },
        ));
    }

    #[verifier::external_body]
    fn prepare_gas<'i>(&self, gas: usize, v: &Forest<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::FOREST,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    SCC1::Forest { forest: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::FOREST,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    SCC1::Forest { forest: v.deep_view() },
                )
            },
        decreases gas,
    {
        if v.items.len() != v.len as usize {
            return Err(PreSerializeError::not_compliant(ComplianceErrorKind::CondRejected));
        }
        let l1 = U8.prepare(&v.len)?;
        if v.len == 0 {
            return Ok(l1);
        }
        if gas == 0 {
            return Err(
                PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
            );
        }
        let next_gas = gas - 1;
        let mut total = l1;
        for item in v.items.iter()
            invariant
                total >= l1,
        {
            let li = ExprFmt::<LIMIT>.prepare_gas(next_gas, item)?;
            total = total.checked_add(li).ok_or(PreSerializeError::length_too_large())?;
        }
        Ok(total)
    }
}

impl<const LIMIT: usize> ListVConsFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ListVCons<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LISTVCONS,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->list_v_cons)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        if gas > 0 {
            let (n1, head) = ExprFmt::<LIMIT>.parse_gas(gas - 1, ibuf)?;
            let rest = ibuf.skip(n1);
            let (n2, tail) = ListFmt::<LIMIT>.parse_gas(gas - 1, &rest)?;
            Ok((n1 + n2, ListVCons { head: Box::new(head), tail: Box::new(tail) }))
        } else {
            Err(ParseError::recursion_limit_exceeded())
        }
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &ListVCons<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::LISTVCONS,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
                SCC1::ListVCons { list_v_cons: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                SCC1RecBody,
                SCC1Param,
            >::spec_serialize_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::LISTVCONS,
                    expr_kind: arbitrary(),
                    list_kind: arbitrary(),
                },
                SCC1::ListVCons { list_v_cons: v.deep_view() },
            ),
        decreases gas,
    {
        ExprFmt::<LIMIT>.serialize_gas(gas - 1, &v.head, obuf);
        ListFmt::<LIMIT>.serialize_gas(gas - 1, &v.tail, obuf);
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &ListVCons<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LISTVCONS,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    SCC1::ListVCons { list_v_cons: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LISTVCONS,
                        expr_kind: arbitrary(),
                        list_kind: arbitrary(),
                    },
                    SCC1::ListVCons { list_v_cons: v.deep_view() },
                )
            },
        decreases gas,
    {
        if gas == 0 {
            return Err(
                PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
            );
        }
        let l1 = ExprFmt::<LIMIT>.prepare_gas(gas - 1, &v.head)?;
        let l2 = ListFmt::<LIMIT>.prepare_gas(gas - 1, &v.tail)?;
        let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
        Ok(total)
    }
}

impl<const LIMIT: usize> ListVFmt<LIMIT> {
    fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ListV<'i>>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LISTV,
                        expr_kind: arbitrary(),
                        list_kind: self.list_kind.deep_view(),
                    },
                    ibuf@,
                ) {
                    Some((n, v)) => Some((n, v->list_v)),
                    _ => None,
                },
            ),
            r matches Ok((n, _)) ==> n <= ibuf@.len(),
        decreases gas,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        match self.list_kind {
            ListKind::Nil => {
                let (n1, v) = Fixed::<0>.parse(ibuf)?;
                Ok((n1, ListV::Nil(v)))
            },
            ListKind::Cons => {
                if gas > 0 {
                    let (n1, v) = ListVConsFmt::<LIMIT>.parse_gas(gas - 1, ibuf)?;
                    Ok((n1, ListV::Cons(Box::new(v))))
                } else {
                    Err(ParseError::recursion_limit_exceeded())
                }
            },
        }
    }

    fn serialize_gas<'i>(&self, gas: usize, v: &ListV<'i>, obuf: &mut Vec<u8>)
        requires
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::LISTV,
                    expr_kind: arbitrary(),
                    list_kind: self.list_kind.deep_view(),
                },
                SCC1::ListV { list_v: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                SCC1RecBody,
                SCC1Param,
            >::spec_serialize_gas(
                &SCC1RecBody,
                gas as nat,
                SCC1Param {
                    which: SCC1Which::LISTV,
                    expr_kind: arbitrary(),
                    list_kind: self.list_kind.deep_view(),
                },
                SCC1::ListV { list_v: v.deep_view() },
            ),
        decreases gas,
    {
        match v {
            ListV::Nil(bytes) => {
                Fixed::<0>.serialize(bytes, obuf);
            },
            ListV::Cons(cons) => {
                ListVConsFmt::<LIMIT>.serialize_gas(gas - 1, cons, obuf);
            },
        }
    }

    fn prepare_gas<'i>(&self, gas: usize, v: &ListV<'i>) -> (checked: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            checked matches Ok(len) ==> {
                &&& FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LISTV,
                        expr_kind: arbitrary(),
                        list_kind: self.list_kind.deep_view(),
                    },
                    SCC1::ListV { list_v: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
                    &SCC1RecBody,
                    gas as nat,
                    SCC1Param {
                        which: SCC1Which::LISTV,
                        expr_kind: arbitrary(),
                        list_kind: self.list_kind.deep_view(),
                    },
                    SCC1::ListV { list_v: v.deep_view() },
                )
            },
        decreases gas,
    {
        match (self.list_kind, v) {
            (ListKind::Nil, ListV::Nil(bytes)) => { Fixed::<0>.prepare(bytes) },
            (ListKind::Cons, ListV::Cons(cons)) => {
                if gas == 0 {
                    return Err(
                        PreSerializeError::not_compliant(
                            ComplianceErrorKind::RecursionLimitExceeded,
                        ),
                    );
                }
                ListVConsFmt::<LIMIT>.prepare_gas(gas - 1, cons)
            },
            _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::CondRejected)),
        }
    }
}

} // verus!
