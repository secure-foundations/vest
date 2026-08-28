#![allow(warnings)]
use vps_lib::combinators::mapped::spec::*;
use vps_lib::combinators::recursive::*;
use vps_lib::combinators::*;
use vps_lib::core::exec::bytes_eq;
use vps_lib::core::exec::input::{InputBuf, InputSlice};
use vps_lib::core::exec::output::OutputBuf;
use vps_lib::core::exec::parser::*;
use vps_lib::core::exec::serializer::*;
use vps_lib::core::exec::ParseError;
use vps_lib::core::{proof::*, spec::*};
use vps_lib::primitives::btcvarint::VarInt;
use vps_lib::primitives::leb128::ULeb128;
use vps_lib::Never;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `expr_kind`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum ExprKind {
    Num = 16,
    Group = 17,
}

pub type ExprKindSpec = ExprKind;

pub type ExprKindInner = u8;

impl DeepView for ExprKind {
    type V = Self;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl ExprKind {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<ExprKind as DeepView>::deep_view);
    }

    pub open spec fn structural_valid(input: ExprKindInner) -> bool {
        {
            let x = input;
            x == 16 || x == 17
        }
    }

    # [verifier::opaque]
    pub open spec fn from_structural(input: ExprKindInner) -> Self {
        match input {
            16 => Self::Num,
            17 => Self::Group,
            _ => arbitrary(),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> ExprKindInner {
        match self {
            Self::Num => 16,
            Self::Group => 17,
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ExprKind::from_structural);
        reveal(ExprKind::into_structural);
        match self {
            Self::Num => {},
            Self::Group => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: ExprKindInner)
        requires
            Self::structural_valid(input),
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ExprKind::from_structural);
        reveal(ExprKind::into_structural);
        match input {
            16 => {},
            17 => {},
            _ => {
                assert(false);
            },
        }
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ExprKindForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ExprKindReverse;

impl SpecMap for ExprKindForward {
    type Input = ExprKindInner;

    type Output = ExprKindSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ExprKind::from_structural(input)
    }
}

impl SpecMap for ExprKindReverse {
    type Input = ExprKindSpec;

    type Output = ExprKindInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for ExprKind {

}

# [doc = "data type for `list_kind`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum ListKind {
    Nil = 32,
    Cons = 33,
}

pub type ListKindSpec = ListKind;

pub type ListKindInner = u8;

impl DeepView for ListKind {
    type V = Self;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl ListKind {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<ListKind as DeepView>::deep_view);
    }

    pub open spec fn structural_valid(input: ListKindInner) -> bool {
        {
            let x = input;
            x == 32 || x == 33
        }
    }

    # [verifier::opaque]
    pub open spec fn from_structural(input: ListKindInner) -> Self {
        match input {
            32 => Self::Nil,
            33 => Self::Cons,
            _ => arbitrary(),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> ListKindInner {
        match self {
            Self::Nil => 32,
            Self::Cons => 33,
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ListKind::from_structural);
        reveal(ListKind::into_structural);
        match self {
            Self::Nil => {},
            Self::Cons => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: ListKindInner)
        requires
            Self::structural_valid(input),
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ListKind::from_structural);
        reveal(ListKind::into_structural);
        match input {
            32 => {},
            33 => {},
            _ => {
                assert(false);
            },
        }
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ListKindForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ListKindReverse;

impl SpecMap for ListKindForward {
    type Input = ListKindInner;

    type Output = ListKindSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ListKind::from_structural(input)
    }
}

impl SpecMap for ListKindReverse {
    type Input = ListKindSpec;

    type Output = ListKindInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for ListKind {

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
pub enum SCC1Which {
    EXPR,
    LIST,
    EXPRV,
    LISTVCONS,
    LISTV,
}

impl DeepView for SCC1Which {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [verifier::ext_equal]
pub struct SCC1Param {
    pub which: SCC1Which,
    pub expr_kind: ExprKindSpec,
    pub list_kind: ListKindSpec,
}

impl DeepView for SCC1Param {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        SCC1Param {
            which: self.which.deep_view(),
            expr_kind: self.expr_kind.deep_view(),
            list_kind: self.list_kind.deep_view(),
        }
    }
}

# [doc = "data type for `chain_a`."]
# [derive (Debug, PartialEq, Eq)]
pub enum ChainA<'i> {
    Variant1(u8),
    Default(Box<ChainAChoice1<'i>>),
}

# [verifier::ext_equal]
pub enum ChainASpec {
    Variant1(u8),
    Default(Box<ChainAChoice1Spec>),
}

pub type ChainAInner = Sum<u8, Box<ChainAChoice1Spec>>;

pub open spec fn chain_a_view(x: &ChainA) -> ChainASpec
    decreases *x,
{
    match x {
        ChainA::Variant1(v) => ChainASpec::Variant1(v.deep_view()),
        ChainA::Default(v) => ChainASpec::Default(Box::new(chain_a_choice1_view(&**v))),
    }
}

impl<'i> DeepView for ChainA<'i> {
    type V = ChainASpec;

    open spec fn deep_view(&self) -> Self::V {
        chain_a_view(self)
    }
}

# [doc = "data type for `chain_b`."]
# [derive (Debug, PartialEq, Eq)]
pub enum ChainB<'i> {
    Variant1(u16),
    Default(Box<ChainBChoice1<'i>>),
}

# [verifier::ext_equal]
pub enum ChainBSpec {
    Variant1(u16),
    Default(Box<ChainBChoice1Spec>),
}

pub type ChainBInner = Sum<u16, Box<ChainBChoice1Spec>>;

pub open spec fn chain_b_view(x: &ChainB) -> ChainBSpec
    decreases *x,
{
    match x {
        ChainB::Variant1(v) => ChainBSpec::Variant1(v.deep_view()),
        ChainB::Default(v) => ChainBSpec::Default(Box::new(chain_b_choice1_view(&**v))),
    }
}

impl<'i> DeepView for ChainB<'i> {
    type V = ChainBSpec;

    open spec fn deep_view(&self) -> Self::V {
        chain_b_view(self)
    }
}

# [doc = "data type for `chain_a_choice1`."]
# [derive (Debug, PartialEq, Eq)]
pub struct ChainAChoice1<'i> {
    pub len: u8,
    pub payload: &'i [u8],
    pub next_tag: u8,
    pub tail: Box<ChainB<'i>>,
}

# [verifier::ext_equal]
pub struct ChainAChoice1Spec {
    pub len: u8,
    pub payload: Seq<u8>,
    pub next_tag: u8,
    pub tail: Box<ChainBSpec>,
}

pub type ChainAChoice1Inner = (u8, (Seq<u8>, (u8, Box<ChainBSpec>)));

pub open spec fn chain_a_choice1_view(x: &ChainAChoice1) -> ChainAChoice1Spec
    decreases *x,
{
    ChainAChoice1Spec {
        len: x.len.deep_view(),
        payload: x.payload.deep_view(),
        next_tag: x.next_tag.deep_view(),
        tail: Box::new(chain_b_view(&*x.tail)),
    }
}

impl<'i> DeepView for ChainAChoice1<'i> {
    type V = ChainAChoice1Spec;

    open spec fn deep_view(&self) -> Self::V {
        chain_a_choice1_view(self)
    }
}

# [doc = "data type for `chain_b_choice1`."]
# [derive (Debug, PartialEq, Eq)]
pub struct ChainBChoice1<'i> {
    pub payload: u32,
    pub next_tag: u8,
    pub tail: Box<ChainA<'i>>,
}

# [verifier::ext_equal]
pub struct ChainBChoice1Spec {
    pub payload: u32,
    pub next_tag: u8,
    pub tail: Box<ChainASpec>,
}

pub type ChainBChoice1Inner = (u32, (u8, Box<ChainASpec>));

pub open spec fn chain_b_choice1_view(x: &ChainBChoice1) -> ChainBChoice1Spec
    decreases *x,
{
    ChainBChoice1Spec {
        payload: x.payload.deep_view(),
        next_tag: x.next_tag.deep_view(),
        tail: Box::new(chain_a_view(&*x.tail)),
    }
}

impl<'i> DeepView for ChainBChoice1<'i> {
    type V = ChainBChoice1Spec;

    open spec fn deep_view(&self) -> Self::V {
        chain_b_choice1_view(self)
    }
}

# [verifier::ext_equal]
pub enum SCC2 {
    ChainA { chain_a: ChainASpec },
    ChainB { chain_b: ChainBSpec },
    ChainAChoice1 { chain_a_choice1: ChainAChoice1Spec },
    ChainBChoice1 { chain_b_choice1: ChainBChoice1Spec },
}

# [derive (Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum SCC2Which {
    CHAINA,
    CHAINB,
    CHAINACHOICE1,
    CHAINBCHOICE1,
}

impl DeepView for SCC2Which {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [verifier::ext_equal]
pub struct SCC2Param {
    pub which: SCC2Which,
    pub tag: u8,
}

impl DeepView for SCC2Param {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        SCC2Param { which: self.which.deep_view(), tag: self.tag.deep_view() }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `expr_kind`."]
# [derive (Clone, Copy)]
pub struct ExprKindFmt;

pub type ExprKindFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, BiMap<ExprKindForward, ExprKindReverse>>,
>;

impl ExprKindFmt {
    # [doc = "specification constructor for `expr_kind`."]
    pub open spec fn spec_inner() -> ExprKindFmtSpec {
        Named(
            "expr_kind",
            Mapped {
                inner: Refined(U8, |x: u8| (x == 16) || (x == 17)),
                mapper: BiMap(ExprKindForward, ExprKindReverse),
            },
        )
    }
}

# [doc = "named format combinator for `list_kind`."]
# [derive (Clone, Copy)]
pub struct ListKindFmt;

pub type ListKindFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, BiMap<ListKindForward, ListKindReverse>>,
>;

impl ListKindFmt {
    # [doc = "specification constructor for `list_kind`."]
    pub open spec fn spec_inner() -> ListKindFmtSpec {
        Named(
            "list_kind",
            Mapped {
                inner: Refined(U8, |x: u8| (x == 32) || (x == 33)),
                mapper: BiMap(ListKindForward, ListKindReverse),
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

pub type ExprFmtSpec<const LIMIT: usize> = ExprProj<FixWith<LIMIT, SCC1RecBody, SCC1Param>>;

# [derive (Clone, Copy)]
pub struct ExprFmt<const LIMIT: usize> {}

impl<const LIMIT: usize> ExprFmt<LIMIT> {
    pub open spec fn spec_inner() -> ExprFmtSpec<LIMIT> {
        expr_proj(
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>(
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
pub struct ListFmt<const LIMIT: usize> {}

impl<const LIMIT: usize> ListFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListFmtSpec<LIMIT> {
        list_proj(
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>(
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
    pub closed spec fn expr_kind_spec(&self) -> ExprKindSpec {
        self.expr_kind.deep_view()
    }

    pub open spec fn spec_inner(expr_kind: ExprKindSpec) -> ExprVFmtSpec<LIMIT> {
        expr_v_proj(
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>(
                SCC1RecBody,
                SCC1Param { which: SCC1Which::EXPRV, expr_kind, list_kind: arbitrary() },
            ),
        )
    }
}

pub type ListVConsFmtSpec<const LIMIT: usize> = ListVConsProj<
    FixWith<LIMIT, SCC1RecBody, SCC1Param>,
>;

# [derive (Clone, Copy)]
pub struct ListVConsFmt<const LIMIT: usize> {}

impl<const LIMIT: usize> ListVConsFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListVConsFmtSpec<LIMIT> {
        list_v_cons_proj(
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>(
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
    pub closed spec fn list_kind_spec(&self) -> ListKindSpec {
        self.list_kind.deep_view()
    }

    pub open spec fn spec_inner(list_kind: ListKindSpec) -> ListVFmtSpec<LIMIT> {
        list_v_proj(
            FixWith::<LIMIT, SCC1RecBody, SCC1Param>(
                SCC1RecBody,
                SCC1Param { which: SCC1Which::LISTV, expr_kind: arbitrary(), list_kind },
            ),
        )
    }
}

pub open spec fn expr_param() -> SCC1Param {
    SCC1Param { which: SCC1Which::EXPR, expr_kind: arbitrary(), list_kind: arbitrary() }
}

pub open spec fn expr_into_scc(v: ExprSpec) -> SCC1 {
    SCC1::Expr { expr: v }
}

pub open spec fn expr_parse_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    ibuf: Seq<u8>,
) -> Option<(int, ExprSpec)> {
    match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(body, gas, expr_param(), ibuf) {
        Some((n, SCC1::Expr { expr })) => Some((n, expr)),
        _ => None,
    }
}

pub open spec fn expr_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ExprSpec,
) -> bool {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
        body,
        gas,
        expr_param(),
        expr_into_scc(v),
    )
}

pub open spec fn expr_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ExprSpec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_serialize_gas(
        body,
        gas,
        expr_param(),
        expr_into_scc(v),
    )
}

pub open spec fn expr_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ExprSpec,
) -> nat {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
        body,
        gas,
        expr_param(),
        expr_into_scc(v),
    )
}

pub open spec fn list_param() -> SCC1Param {
    SCC1Param { which: SCC1Which::LIST, expr_kind: arbitrary(), list_kind: arbitrary() }
}

pub open spec fn list_into_scc(v: ListSpec) -> SCC1 {
    SCC1::List { list: v }
}

pub open spec fn list_parse_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    ibuf: Seq<u8>,
) -> Option<(int, ListSpec)> {
    match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(body, gas, list_param(), ibuf) {
        Some((n, SCC1::List { list })) => Some((n, list)),
        _ => None,
    }
}

pub open spec fn list_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ListSpec,
) -> bool {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
        body,
        gas,
        list_param(),
        list_into_scc(v),
    )
}

pub open spec fn list_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ListSpec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_serialize_gas(
        body,
        gas,
        list_param(),
        list_into_scc(v),
    )
}

pub open spec fn list_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ListSpec,
) -> nat {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
        body,
        gas,
        list_param(),
        list_into_scc(v),
    )
}

pub open spec fn expr_v_param(expr_kind: ExprKindSpec) -> SCC1Param {
    SCC1Param { which: SCC1Which::EXPRV, expr_kind, list_kind: arbitrary() }
}

pub open spec fn expr_v_into_scc(v: ExprVSpec) -> SCC1 {
    SCC1::ExprV { expr_v: v }
}

pub open spec fn expr_v_parse_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    expr_kind: ExprKindSpec,
    ibuf: Seq<u8>,
) -> Option<(int, ExprVSpec)> {
    match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
        body,
        gas,
        expr_v_param(expr_kind),
        ibuf,
    ) {
        Some((n, SCC1::ExprV { expr_v })) => Some((n, expr_v)),
        _ => None,
    }
}

pub open spec fn expr_v_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    expr_kind: ExprKindSpec,
    v: ExprVSpec,
) -> bool {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
        body,
        gas,
        expr_v_param(expr_kind),
        expr_v_into_scc(v),
    )
}

pub open spec fn expr_v_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    expr_kind: ExprKindSpec,
    v: ExprVSpec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_serialize_gas(
        body,
        gas,
        expr_v_param(expr_kind),
        expr_v_into_scc(v),
    )
}

pub open spec fn expr_v_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    expr_kind: ExprKindSpec,
    v: ExprVSpec,
) -> nat {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
        body,
        gas,
        expr_v_param(expr_kind),
        expr_v_into_scc(v),
    )
}

pub open spec fn list_v_cons_param() -> SCC1Param {
    SCC1Param { which: SCC1Which::LISTVCONS, expr_kind: arbitrary(), list_kind: arbitrary() }
}

pub open spec fn list_v_cons_into_scc(v: ListVConsSpec) -> SCC1 {
    SCC1::ListVCons { list_v_cons: v }
}

pub open spec fn list_v_cons_parse_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    ibuf: Seq<u8>,
) -> Option<(int, ListVConsSpec)> {
    match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
        body,
        gas,
        list_v_cons_param(),
        ibuf,
    ) {
        Some((n, SCC1::ListVCons { list_v_cons })) => Some((n, list_v_cons)),
        _ => None,
    }
}

pub open spec fn list_v_cons_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ListVConsSpec,
) -> bool {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
        body,
        gas,
        list_v_cons_param(),
        list_v_cons_into_scc(v),
    )
}

pub open spec fn list_v_cons_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ListVConsSpec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_serialize_gas(
        body,
        gas,
        list_v_cons_param(),
        list_v_cons_into_scc(v),
    )
}

pub open spec fn list_v_cons_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    v: ListVConsSpec,
) -> nat {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
        body,
        gas,
        list_v_cons_param(),
        list_v_cons_into_scc(v),
    )
}

pub open spec fn list_v_param(list_kind: ListKindSpec) -> SCC1Param {
    SCC1Param { which: SCC1Which::LISTV, expr_kind: arbitrary(), list_kind }
}

pub open spec fn list_v_into_scc(v: ListVSpec) -> SCC1 {
    SCC1::ListV { list_v: v }
}

pub open spec fn list_v_parse_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    list_kind: ListKindSpec,
    ibuf: Seq<u8>,
) -> Option<(int, ListVSpec)> {
    match FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_parse_gas(
        body,
        gas,
        list_v_param(list_kind),
        ibuf,
    ) {
        Some((n, SCC1::ListV { list_v })) => Some((n, list_v)),
        _ => None,
    }
}

pub open spec fn list_v_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    list_kind: ListKindSpec,
    v: ListVSpec,
) -> bool {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::consistent_gas(
        body,
        gas,
        list_v_param(list_kind),
        list_v_into_scc(v),
    )
}

pub open spec fn list_v_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    list_kind: ListKindSpec,
    v: ListVSpec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::spec_serialize_gas(
        body,
        gas,
        list_v_param(list_kind),
        list_v_into_scc(v),
    )
}

pub open spec fn list_v_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC1RecBody,
    gas: nat,
    list_kind: ListKindSpec,
    v: ListVSpec,
) -> nat {
    FixWith::<LIMIT, SCC1RecBody, SCC1Param>::byte_len_gas(
        body,
        gas,
        list_v_param(list_kind),
        list_v_into_scc(v),
    )
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
            L(v) => SCC1::ExprV { expr_v: ExprVSpec::Num(v) },
            R(v) => SCC1::ExprV { expr_v: ExprVSpec::Group(Box::new(v)) },
            _ => arbitrary(),
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ExprV
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::ExprV { expr_v: ExprVSpec::Num(v) } => L(v),
            SCC1::ExprV { expr_v: ExprVSpec::Group(v) } => R(*v),
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
            L(v) => SCC1::ListV { list_v: ListVSpec::Nil(v) },
            R(v) => SCC1::ListV { list_v: ListVSpec::Cons(Box::new(v)) },
            _ => arbitrary(),
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ListV
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC1::ListV { list_v: ListVSpec::Nil(v) } => L(v),
            SCC1::ListV { list_v: ListVSpec::Cons(v) } => R(*v),
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
    type Param = SCC1Param;

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

pub type ListBodyFmt = Mapped<
    Bind<ListKindFmt, spec_fn(ListKindSpec) -> ListVProj<BundledSpecs<SCC1>>>,
    ListMapper,
>;

pub struct ListBodyRec;

impl SpecRecBody for ListBodyRec {
    type Param = SCC1Param;

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

pub type ExprVBodyFmt = Mapped<Sum<U8, ListProj<BundledSpecs<SCC1>>>, ExprVMapper>;

pub struct ExprVBodyRec;

impl SpecRecBody for ExprVBodyRec {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = ExprVBodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.expr_kind {
                ExprKindSpec::Num => L(U8),
                ExprKindSpec::Group => R(
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
    type Param = SCC1Param;

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

pub type ListVBodyFmt = Mapped<Sum<Fixed<0>, ListVConsProj<BundledSpecs<SCC1>>>, ListVMapper>;

pub struct ListVBodyRec;

impl SpecRecBody for ListVBodyRec {
    type Param = SCC1Param;

    type T = SCC1;

    type Body = ListVBodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.list_kind {
                ListKindSpec::Nil => L(Fixed::<0>),
                ListKindSpec::Cons => R(
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
            Cond(param.which == SCC1Which::EXPR, ExprBodyRec.spec_body(param, rec)),
            Alt(
                Cond(param.which == SCC1Which::LIST, ListBodyRec.spec_body(param, rec)),
                Alt(
                    Cond(param.which == SCC1Which::EXPRV, ExprVBodyRec.spec_body(param, rec)),
                    Alt(
                        Cond(
                            param.which == SCC1Which::LISTVCONS,
                            ListVConsBodyRec.spec_body(param, rec),
                        ),
                        Cond(param.which == SCC1Which::LISTV, ListVBodyRec.spec_body(param, rec)),
                    ),
                ),
            ),
        )
    }
}

pub type ChainAProj<Rec> = Mapped<Refined<Rec, PredFnSpec<SCC2>>, FnSpecMapper<SCC2, ChainASpec>>;

pub open spec fn chain_a_proj<Rec>(rec: Rec) -> ChainAProj<Rec> where
    Rec: SpecCombinator<T = SCC2>,
 {
    Mapped {
        inner: Refined(rec, |v: SCC2| v is ChainA),
        mapper: (
            |v: SCC2| -> ChainASpec { v->chain_a },
            |chain_a: ChainASpec| -> SCC2 { SCC2::ChainA { chain_a } },
        ),
    }
}

pub type ChainBProj<Rec> = Mapped<Refined<Rec, PredFnSpec<SCC2>>, FnSpecMapper<SCC2, ChainBSpec>>;

pub open spec fn chain_b_proj<Rec>(rec: Rec) -> ChainBProj<Rec> where
    Rec: SpecCombinator<T = SCC2>,
 {
    Mapped {
        inner: Refined(rec, |v: SCC2| v is ChainB),
        mapper: (
            |v: SCC2| -> ChainBSpec { v->chain_b },
            |chain_b: ChainBSpec| -> SCC2 { SCC2::ChainB { chain_b } },
        ),
    }
}

pub type ChainAChoice1Proj<Rec> = Mapped<
    Refined<Rec, PredFnSpec<SCC2>>,
    FnSpecMapper<SCC2, ChainAChoice1Spec>,
>;

pub open spec fn chain_a_choice1_proj<Rec>(rec: Rec) -> ChainAChoice1Proj<Rec> where
    Rec: SpecCombinator<T = SCC2>,
 {
    Mapped {
        inner: Refined(rec, |v: SCC2| v is ChainAChoice1),
        mapper: (
            |v: SCC2| -> ChainAChoice1Spec { v->chain_a_choice1 },
            |chain_a_choice1: ChainAChoice1Spec| -> SCC2
                { SCC2::ChainAChoice1 { chain_a_choice1 } },
        ),
    }
}

pub type ChainBChoice1Proj<Rec> = Mapped<
    Refined<Rec, PredFnSpec<SCC2>>,
    FnSpecMapper<SCC2, ChainBChoice1Spec>,
>;

pub open spec fn chain_b_choice1_proj<Rec>(rec: Rec) -> ChainBChoice1Proj<Rec> where
    Rec: SpecCombinator<T = SCC2>,
 {
    Mapped {
        inner: Refined(rec, |v: SCC2| v is ChainBChoice1),
        mapper: (
            |v: SCC2| -> ChainBChoice1Spec { v->chain_b_choice1 },
            |chain_b_choice1: ChainBChoice1Spec| -> SCC2
                { SCC2::ChainBChoice1 { chain_b_choice1 } },
        ),
    }
}

pub type ChainAFmtSpec<const LIMIT: usize> = ChainAProj<FixWith<LIMIT, SCC2RecBody, SCC2Param>>;

# [derive (Clone, Copy)]
pub struct ChainAFmt<const LIMIT: usize> {
    pub tag: u8,
}

impl<const LIMIT: usize> ChainAFmt<LIMIT> {
    pub closed spec fn tag_spec(&self) -> u8 {
        self.tag.deep_view()
    }

    pub open spec fn spec_inner(tag: u8) -> ChainAFmtSpec<LIMIT> {
        chain_a_proj(
            FixWith::<LIMIT, SCC2RecBody, SCC2Param>(
                SCC2RecBody,
                SCC2Param { which: SCC2Which::CHAINA, tag },
            ),
        )
    }
}

pub type ChainBFmtSpec<const LIMIT: usize> = ChainBProj<FixWith<LIMIT, SCC2RecBody, SCC2Param>>;

# [derive (Clone, Copy)]
pub struct ChainBFmt<const LIMIT: usize> {
    pub tag: u8,
}

impl<const LIMIT: usize> ChainBFmt<LIMIT> {
    pub closed spec fn tag_spec(&self) -> u8 {
        self.tag.deep_view()
    }

    pub open spec fn spec_inner(tag: u8) -> ChainBFmtSpec<LIMIT> {
        chain_b_proj(
            FixWith::<LIMIT, SCC2RecBody, SCC2Param>(
                SCC2RecBody,
                SCC2Param { which: SCC2Which::CHAINB, tag },
            ),
        )
    }
}

pub type ChainAChoice1FmtSpec<const LIMIT: usize> = ChainAChoice1Proj<
    FixWith<LIMIT, SCC2RecBody, SCC2Param>,
>;

# [derive (Clone, Copy)]
pub struct ChainAChoice1Fmt<const LIMIT: usize> {}

impl<const LIMIT: usize> ChainAChoice1Fmt<LIMIT> {
    pub open spec fn spec_inner() -> ChainAChoice1FmtSpec<LIMIT> {
        chain_a_choice1_proj(
            FixWith::<LIMIT, SCC2RecBody, SCC2Param>(
                SCC2RecBody,
                SCC2Param { which: SCC2Which::CHAINACHOICE1, tag: arbitrary() },
            ),
        )
    }
}

pub type ChainBChoice1FmtSpec<const LIMIT: usize> = ChainBChoice1Proj<
    FixWith<LIMIT, SCC2RecBody, SCC2Param>,
>;

# [derive (Clone, Copy)]
pub struct ChainBChoice1Fmt<const LIMIT: usize> {}

impl<const LIMIT: usize> ChainBChoice1Fmt<LIMIT> {
    pub open spec fn spec_inner() -> ChainBChoice1FmtSpec<LIMIT> {
        chain_b_choice1_proj(
            FixWith::<LIMIT, SCC2RecBody, SCC2Param>(
                SCC2RecBody,
                SCC2Param { which: SCC2Which::CHAINBCHOICE1, tag: arbitrary() },
            ),
        )
    }
}

pub open spec fn chain_a_param(tag: u8) -> SCC2Param {
    SCC2Param { which: SCC2Which::CHAINA, tag }
}

pub open spec fn chain_a_into_scc(v: ChainASpec) -> SCC2 {
    SCC2::ChainA { chain_a: v }
}

pub open spec fn chain_a_parse_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    tag: u8,
    ibuf: Seq<u8>,
) -> Option<(int, ChainASpec)> {
    match FixWith::<LIMIT, SCC2RecBody, SCC2Param>::spec_parse_gas(
        body,
        gas,
        chain_a_param(tag),
        ibuf,
    ) {
        Some((n, SCC2::ChainA { chain_a })) => Some((n, chain_a)),
        _ => None,
    }
}

pub open spec fn chain_a_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    tag: u8,
    v: ChainASpec,
) -> bool {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::consistent_gas(
        body,
        gas,
        chain_a_param(tag),
        chain_a_into_scc(v),
    )
}

pub open spec fn chain_a_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    tag: u8,
    v: ChainASpec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::spec_serialize_gas(
        body,
        gas,
        chain_a_param(tag),
        chain_a_into_scc(v),
    )
}

pub open spec fn chain_a_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    tag: u8,
    v: ChainASpec,
) -> nat {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::byte_len_gas(
        body,
        gas,
        chain_a_param(tag),
        chain_a_into_scc(v),
    )
}

pub open spec fn chain_b_param(tag: u8) -> SCC2Param {
    SCC2Param { which: SCC2Which::CHAINB, tag }
}

pub open spec fn chain_b_into_scc(v: ChainBSpec) -> SCC2 {
    SCC2::ChainB { chain_b: v }
}

pub open spec fn chain_b_parse_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    tag: u8,
    ibuf: Seq<u8>,
) -> Option<(int, ChainBSpec)> {
    match FixWith::<LIMIT, SCC2RecBody, SCC2Param>::spec_parse_gas(
        body,
        gas,
        chain_b_param(tag),
        ibuf,
    ) {
        Some((n, SCC2::ChainB { chain_b })) => Some((n, chain_b)),
        _ => None,
    }
}

pub open spec fn chain_b_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    tag: u8,
    v: ChainBSpec,
) -> bool {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::consistent_gas(
        body,
        gas,
        chain_b_param(tag),
        chain_b_into_scc(v),
    )
}

pub open spec fn chain_b_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    tag: u8,
    v: ChainBSpec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::spec_serialize_gas(
        body,
        gas,
        chain_b_param(tag),
        chain_b_into_scc(v),
    )
}

pub open spec fn chain_b_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    tag: u8,
    v: ChainBSpec,
) -> nat {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::byte_len_gas(
        body,
        gas,
        chain_b_param(tag),
        chain_b_into_scc(v),
    )
}

pub open spec fn chain_a_choice1_param() -> SCC2Param {
    SCC2Param { which: SCC2Which::CHAINACHOICE1, tag: arbitrary() }
}

pub open spec fn chain_a_choice1_into_scc(v: ChainAChoice1Spec) -> SCC2 {
    SCC2::ChainAChoice1 { chain_a_choice1: v }
}

pub open spec fn chain_a_choice1_parse_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    ibuf: Seq<u8>,
) -> Option<(int, ChainAChoice1Spec)> {
    match FixWith::<LIMIT, SCC2RecBody, SCC2Param>::spec_parse_gas(
        body,
        gas,
        chain_a_choice1_param(),
        ibuf,
    ) {
        Some((n, SCC2::ChainAChoice1 { chain_a_choice1 })) => Some((n, chain_a_choice1)),
        _ => None,
    }
}

pub open spec fn chain_a_choice1_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    v: ChainAChoice1Spec,
) -> bool {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::consistent_gas(
        body,
        gas,
        chain_a_choice1_param(),
        chain_a_choice1_into_scc(v),
    )
}

pub open spec fn chain_a_choice1_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    v: ChainAChoice1Spec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::spec_serialize_gas(
        body,
        gas,
        chain_a_choice1_param(),
        chain_a_choice1_into_scc(v),
    )
}

pub open spec fn chain_a_choice1_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    v: ChainAChoice1Spec,
) -> nat {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::byte_len_gas(
        body,
        gas,
        chain_a_choice1_param(),
        chain_a_choice1_into_scc(v),
    )
}

pub open spec fn chain_b_choice1_param() -> SCC2Param {
    SCC2Param { which: SCC2Which::CHAINBCHOICE1, tag: arbitrary() }
}

pub open spec fn chain_b_choice1_into_scc(v: ChainBChoice1Spec) -> SCC2 {
    SCC2::ChainBChoice1 { chain_b_choice1: v }
}

pub open spec fn chain_b_choice1_parse_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    ibuf: Seq<u8>,
) -> Option<(int, ChainBChoice1Spec)> {
    match FixWith::<LIMIT, SCC2RecBody, SCC2Param>::spec_parse_gas(
        body,
        gas,
        chain_b_choice1_param(),
        ibuf,
    ) {
        Some((n, SCC2::ChainBChoice1 { chain_b_choice1 })) => Some((n, chain_b_choice1)),
        _ => None,
    }
}

pub open spec fn chain_b_choice1_consistent_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    v: ChainBChoice1Spec,
) -> bool {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::consistent_gas(
        body,
        gas,
        chain_b_choice1_param(),
        chain_b_choice1_into_scc(v),
    )
}

pub open spec fn chain_b_choice1_serialize_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    v: ChainBChoice1Spec,
) -> Seq<u8> {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::spec_serialize_gas(
        body,
        gas,
        chain_b_choice1_param(),
        chain_b_choice1_into_scc(v),
    )
}

pub open spec fn chain_b_choice1_byte_len_spec_gas<const LIMIT: usize>(
    body: &SCC2RecBody,
    gas: nat,
    v: ChainBChoice1Spec,
) -> nat {
    FixWith::<LIMIT, SCC2RecBody, SCC2Param>::byte_len_gas(
        body,
        gas,
        chain_b_choice1_param(),
        chain_b_choice1_into_scc(v),
    )
}

pub struct ChainAMapper;

impl SpecMapper for ChainAMapper {
    type In = Sum<u8, ChainAChoice1Spec>;

    type Out = SCC2;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            L(v) => SCC2::ChainA { chain_a: ChainASpec::Variant1(v) },
            R(v) => SCC2::ChainA { chain_a: ChainASpec::Default(Box::new(v)) },
            _ => arbitrary(),
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ChainA
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC2::ChainA { chain_a: ChainASpec::Variant1(v) } => L(v),
            SCC2::ChainA { chain_a: ChainASpec::Default(v) } => R(*v),
            _ => arbitrary(),
        }
    }
}

pub struct ChainBMapper;

impl SpecMapper for ChainBMapper {
    type In = Sum<u16, ChainBChoice1Spec>;

    type Out = SCC2;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            L(v) => SCC2::ChainB { chain_b: ChainBSpec::Variant1(v) },
            R(v) => SCC2::ChainB { chain_b: ChainBSpec::Default(Box::new(v)) },
            _ => arbitrary(),
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ChainB
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC2::ChainB { chain_b: ChainBSpec::Variant1(v) } => L(v),
            SCC2::ChainB { chain_b: ChainBSpec::Default(v) } => R(*v),
            _ => arbitrary(),
        }
    }
}

pub struct ChainAChoice1Mapper;

impl SpecMapper for ChainAChoice1Mapper {
    type In = (u8, (Seq<u8>, (u8, ChainBSpec)));

    type Out = SCC2;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (len, (payload, (next_tag, tail))) = i;
        SCC2::ChainAChoice1 {
            chain_a_choice1: ChainAChoice1Spec { len, payload, next_tag, tail: Box::new(tail) },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ChainAChoice1
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC2::ChainAChoice1 {
                chain_a_choice1: ChainAChoice1Spec { len, payload, next_tag, tail },
            } => (len, (payload, (next_tag, *tail))),
            _ => arbitrary(),
        }
    }
}

pub struct ChainBChoice1Mapper;

impl SpecMapper for ChainBChoice1Mapper {
    type In = (u32, (u8, ChainASpec));

    type Out = SCC2;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (payload, (next_tag, tail)) = i;
        SCC2::ChainBChoice1 {
            chain_b_choice1: ChainBChoice1Spec { payload, next_tag, tail: Box::new(tail) },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is ChainBChoice1
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            SCC2::ChainBChoice1 {
                chain_b_choice1: ChainBChoice1Spec { payload, next_tag, tail },
            } => (payload, (next_tag, *tail)),
            _ => arbitrary(),
        }
    }
}

pub type ChainABodyFmt = Mapped<
    Sum<Refined<U8, PredFnSpec<u8>>, ChainAChoice1Proj<BundledSpecs<SCC2>>>,
    ChainAMapper,
>;

pub struct ChainABodyRec;

impl SpecRecBody for ChainABodyRec {
    type Param = SCC2Param;

    type T = SCC2;

    type Body = ChainABodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.tag {
                0 => L(Refined(U8, |x: u8| x >= 1 && x <= 10)),
                _ => R(
                    chain_a_choice1_proj(
                        rec(SCC2Param { which: SCC2Which::CHAINACHOICE1, tag: arbitrary() }),
                    ),
                ),
            },
            mapper: ChainAMapper,
        }
    }
}

pub type ChainBBodyFmt = Mapped<
    Sum<Refined<U16Le, PredFnSpec<u16>>, ChainBChoice1Proj<BundledSpecs<SCC2>>>,
    ChainBMapper,
>;

pub struct ChainBBodyRec;

impl SpecRecBody for ChainBBodyRec {
    type Param = SCC2Param;

    type T = SCC2;

    type Body = ChainBBodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: match param.tag {
                0 => L(Refined(U16Le, |x: u16| x >= 256)),
                _ => R(
                    chain_b_choice1_proj(
                        rec(SCC2Param { which: SCC2Which::CHAINBCHOICE1, tag: arbitrary() }),
                    ),
                ),
            },
            mapper: ChainBMapper,
        }
    }
}

pub type ChainAChoice1BodyFmt = Mapped<
    Bind<
        U8,
        spec_fn(u8) -> Pair<Varied<u8>, Bind<U8, spec_fn(u8) -> ChainBProj<BundledSpecs<SCC2>>>>,
    >,
    ChainAChoice1Mapper,
>;

pub struct ChainAChoice1BodyRec;

impl SpecRecBody for ChainAChoice1BodyRec {
    type Param = SCC2Param;

    type T = SCC2;

    type Body = ChainAChoice1BodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Bind(
                U8,
                |len: u8|
                    Pair(
                        Varied(len),
                        Bind(
                            U8,
                            |next_tag: u8|
                                chain_b_proj(
                                    rec(SCC2Param { which: SCC2Which::CHAINB, tag: next_tag }),
                                ),
                        ),
                    ),
            ),
            mapper: ChainAChoice1Mapper,
        }
    }
}

pub type ChainBChoice1BodyFmt = Mapped<
    Pair<U32Le, Bind<U8, spec_fn(u8) -> ChainAProj<BundledSpecs<SCC2>>>>,
    ChainBChoice1Mapper,
>;

pub struct ChainBChoice1BodyRec;

impl SpecRecBody for ChainBChoice1BodyRec {
    type Param = SCC2Param;

    type T = SCC2;

    type Body = ChainBChoice1BodyFmt;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Pair(
                U32Le,
                Bind(
                    U8,
                    |next_tag: u8|
                        chain_a_proj(rec(SCC2Param { which: SCC2Which::CHAINA, tag: next_tag })),
                ),
            ),
            mapper: ChainBChoice1Mapper,
        }
    }
}

pub struct SCC2RecBody;

impl SpecRecBody for SCC2RecBody {
    type Param = SCC2Param;

    type T = SCC2;

    type Body = Alt<
        Cond<ChainABodyFmt>,
        Alt<Cond<ChainBBodyFmt>, Alt<Cond<ChainAChoice1BodyFmt>, Cond<ChainBChoice1BodyFmt>>>,
    >;

    open spec fn spec_body(
        &self,
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Alt(
            Cond(param.which == SCC2Which::CHAINA, ChainABodyRec.spec_body(param, rec)),
            Alt(
                Cond(param.which == SCC2Which::CHAINB, ChainBBodyRec.spec_body(param, rec)),
                Alt(
                    Cond(
                        param.which == SCC2Which::CHAINACHOICE1,
                        ChainAChoice1BodyRec.spec_body(param, rec),
                    ),
                    Cond(
                        param.which == SCC2Which::CHAINBCHOICE1,
                        ChainBChoice1BodyRec.spec_body(param, rec),
                    ),
                ),
            ),
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ExprKindFmt {
        type PVal = ExprKindSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ExprKindFmt {
        type Val = ExprKindSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ExprKindFmt {
        type SValue = ExprKindSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ExprKindFmt {
        type SVal = ExprKindSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ExprKindFmt {
        type T = ExprKindSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ListKindFmt {
        type PVal = ListKindSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ListKindFmt {
        type Val = ListKindSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ListKindFmt {
        type SValue = ListKindSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ListKindFmt {
        type SVal = ListKindSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ListKindFmt {
        type T = ListKindSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
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

    impl<const LIMIT: usize> SpecByteLen for ExprFmt<LIMIT> {
        type T = ExprSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
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

    impl<const LIMIT: usize> SpecByteLen for ListFmt<LIMIT> {
        type T = ListSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ExprVFmt<LIMIT> {
        type PVal = ExprVSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.expr_kind_spec()).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ExprVFmt<LIMIT> {
        type Val = ExprVSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.expr_kind_spec()).consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ExprVFmt<LIMIT> {
        type SValue = ExprVSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.expr_kind_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ExprVFmt<LIMIT> {
        type SVal = ExprVSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.expr_kind_spec()).spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ExprVFmt<LIMIT> {
        type T = ExprVSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.expr_kind_spec()).byte_len(v)
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

    impl<const LIMIT: usize> SpecByteLen for ListVConsFmt<LIMIT> {
        type T = ListVConsSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ListVFmt<LIMIT> {
        type PVal = ListVSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.list_kind_spec()).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ListVFmt<LIMIT> {
        type Val = ListVSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.list_kind_spec()).consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ListVFmt<LIMIT> {
        type SValue = ListVSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.list_kind_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ListVFmt<LIMIT> {
        type SVal = ListVSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.list_kind_spec()).spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ListVFmt<LIMIT> {
        type T = ListVSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.list_kind_spec()).byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ChainAFmt<LIMIT> {
        type PVal = ChainASpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ChainAFmt<LIMIT> {
        type Val = ChainASpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.tag_spec()).consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ChainAFmt<LIMIT> {
        type SValue = ChainASpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ChainAFmt<LIMIT> {
        type SVal = ChainASpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ChainAFmt<LIMIT> {
        type T = ChainASpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.tag_spec()).byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ChainBFmt<LIMIT> {
        type PVal = ChainBSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ChainBFmt<LIMIT> {
        type Val = ChainBSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.tag_spec()).consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ChainBFmt<LIMIT> {
        type SValue = ChainBSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ChainBFmt<LIMIT> {
        type SVal = ChainBSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ChainBFmt<LIMIT> {
        type T = ChainBSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.tag_spec()).byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ChainAChoice1Fmt<LIMIT> {
        type PVal = ChainAChoice1Spec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ChainAChoice1Fmt<LIMIT> {
        type Val = ChainAChoice1Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ChainAChoice1Fmt<LIMIT> {
        type SValue = ChainAChoice1Spec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ChainAChoice1Fmt<LIMIT> {
        type SVal = ChainAChoice1Spec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ChainAChoice1Fmt<LIMIT> {
        type T = ChainAChoice1Spec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<const LIMIT: usize> SpecParser for ChainBChoice1Fmt<LIMIT> {
        type PVal = ChainBChoice1Spec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for ChainBChoice1Fmt<LIMIT> {
        type Val = ChainBChoice1Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for ChainBChoice1Fmt<LIMIT> {
        type SValue = ChainBChoice1Spec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for ChainBChoice1Fmt<LIMIT> {
        type SVal = ChainBChoice1Spec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for ChainBChoice1Fmt<LIMIT> {
        type T = ChainBChoice1Spec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use {
        vps_lib::combinators::disjoint::disjointness_lemmas,
        ExprKind::lemma_from_into,
        ExprKind::lemma_into_from,
        ListKind::lemma_from_into,
        ListKind::lemma_into_from,
    };

    impl SafeParser for ExprKindFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ExprKindFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ExprKindFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: ExprKindInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(ExprKind::structural_valid(input));
                ExprKind::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            reveal(<ExprKindFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ExprKindInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(ExprKind::structural_valid(input));
                ExprKind::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ExprKindFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ExprKindFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ExprKindFmt as SpecSerializer>::spec_serialize);
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert forall|output: ExprKindSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ExprKind::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ExprKindFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: ExprKindInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(ExprKind::structural_valid(input));
                ExprKind::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ExprKindFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ExprKindFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ExprKindFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ExprKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ExprKindFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ListKindFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ListKindFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ListKindFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: ListKindInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(ListKind::structural_valid(input));
                ListKind::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            reveal(<ListKindFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ListKindInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(ListKind::structural_valid(input));
                ListKind::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ListKindFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ListKindFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ListKindFmt as SpecSerializer>::spec_serialize);
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert forall|output: ListKindSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ListKind::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ListKindFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: ListKindInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(ListKind::structural_valid(input));
                ListKind::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ListKindFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ListKindFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ListKindFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ListKindFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ListKindFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
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
            Self::spec_inner(self.expr_kind_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ExprVFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ExprVFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ExprVFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ExprVFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.expr_kind_spec());
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
            Self::spec_inner(self.list_kind_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ListVFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ListVFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ListVFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ListVFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ListVFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ListVFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ListVFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.list_kind_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

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
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ExprVBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListVConsBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ListVBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

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
            hide(<ListVConsBodyRec as SpecRecBody>::spec_body);
            hide(<ListVBodyRec as SpecRecBody>::spec_body);
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

            ExprBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListBodyRec.lemma_body_all_inv_preservation(param, rec);
            ExprVBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListVConsBodyRec.lemma_body_all_inv_preservation(param, rec);
            ListVBodyRec.lemma_body_all_inv_preservation(param, rec);
        }
    }

    impl<const LIMIT: usize> SafeParser for ChainAFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner(self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ChainAFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ChainAFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ChainAFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ChainAFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ChainAFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ChainAFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ChainAFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for ChainBFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner(self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ChainBFmt<LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for ChainBFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for ChainBFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ChainBFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ChainBFmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ChainBFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ChainBFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for ChainAChoice1Fmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ChainAChoice1Fmt<LIMIT> {
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

    impl<const LIMIT: usize> NonTailFmt for ChainAChoice1Fmt<LIMIT> {
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

    impl<const LIMIT: usize> GoodSerializer for ChainAChoice1Fmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ChainAChoice1Fmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ChainAChoice1Fmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ChainAChoice1Fmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ChainAChoice1Fmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<const LIMIT: usize> SafeParser for ChainBChoice1Fmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> SoundParser for ChainBChoice1Fmt<LIMIT> {
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

    impl<const LIMIT: usize> NonTailFmt for ChainBChoice1Fmt<LIMIT> {
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

    impl<const LIMIT: usize> GoodSerializer for ChainBChoice1Fmt<LIMIT> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for ChainBChoice1Fmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const LIMIT: usize> NonMalleable for ChainBChoice1Fmt<LIMIT> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for ChainBChoice1Fmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for ChainBChoice1Fmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner();
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

    impl LossyMapper for ChainAChoice1Mapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ChainAChoice1Mapper {
        proof fn lemma_lossless_mapper(&self, i: Self::In) {
            assert(self.spec_map_rev(self.spec_map(i)) == i);
        }

        proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        }
    }

    impl LossyMapper for ChainBChoice1Mapper {
        proof fn lemma_sound_mapper(&self, o: Self::Out) {
        }

        proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        }
    }

    impl LosslessMapper for ChainBChoice1Mapper {
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
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ChainBBodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ChainAChoice1BodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for ChainBChoice1BodyRec {
        proof fn lemma_body_all_inv_preservation(
            &self,
            _param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

        }
    }

    impl StrictRecBody for SCC2RecBody {
        proof fn lemma_body_all_inv_preservation(
            &self,
            param: Self::Param,
            rec: ParamRecSpecs<Self::Param, Self::T>,
        ) {
            hide(<ChainABodyRec as SpecRecBody>::spec_body);
            hide(<ChainBBodyRec as SpecRecBody>::spec_body);
            hide(<ChainAChoice1BodyRec as SpecRecBody>::spec_body);
            hide(<ChainBChoice1BodyRec as SpecRecBody>::spec_body);
            broadcast use vps_lib::combinators::disjoint::disjointness_lemmas;

            ChainABodyRec.lemma_body_all_inv_preservation(param, rec);
            ChainBBodyRec.lemma_body_all_inv_preservation(param, rec);
            ChainAChoice1BodyRec.lemma_body_all_inv_preservation(param, rec);
            ChainBChoice1BodyRec.lemma_body_all_inv_preservation(param, rec);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for ExprKindFmt {
        type PT = ExprKind;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ExprKindFmt as SpecParser>::spec_parse);
            reveal(<ExprKind as DeepView>::deep_view);
            reveal(ExprKind::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, ExprKind> for ExprKindFmt {
        fn serialize_into(&self, v: &ExprKind, obuf: &mut Output) {
            reveal(<ExprKindFmt as SpecSerializer>::spec_serialize);
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            reveal(<ExprKind as DeepView>::deep_view);
            reveal(ExprKind::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                ExprKind::Num => 16,
                ExprKind::Group => 17,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ExprKind> for ExprKindFmt {
        fn prepare(&self, v: &ExprKind) -> Result<usize, PreSerializeError> {
            reveal(<ExprKindFmt as SpecByteLen>::byte_len);
            reveal(<ExprKind as DeepView>::deep_view);
            reveal(ExprKind::into_structural);
            let tag = match *v {
                ExprKind::Num => 16,
                ExprKind::Group => 17,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for ListKindFmt {
        type PT = ListKind;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ListKindFmt as SpecParser>::spec_parse);
            reveal(<ListKind as DeepView>::deep_view);
            reveal(ListKind::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, ListKind> for ListKindFmt {
        fn serialize_into(&self, v: &ListKind, obuf: &mut Output) {
            reveal(<ListKindFmt as SpecSerializer>::spec_serialize);
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            reveal(<ListKind as DeepView>::deep_view);
            reveal(ListKind::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                ListKind::Nil => 32,
                ListKind::Cons => 33,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ListKind> for ListKindFmt {
        fn prepare(&self, v: &ListKind) -> Result<usize, PreSerializeError> {
            reveal(<ListKindFmt as SpecByteLen>::byte_len);
            reveal(<ListKind as DeepView>::deep_view);
            reveal(ListKind::into_structural);
            let tag = match *v {
                ListKind::Nil => 32,
                ListKind::Cons => 33,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
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

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<Output, Expr<'i>> for ExprFmt<
        LIMIT,
    > {
        fn serialize_into(&self, v: &Expr<'i>, obuf: &mut Output) {
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

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<Output, List<'i>> for ListFmt<
        LIMIT,
    > {
        fn serialize_into(&self, v: &List<'i>, obuf: &mut Output) {
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
            proof {
                self.expr_kind.lemma_deep_view();
            }
            self.parse_gas(LIMIT, ibuf)
        }
    }

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<Output, ExprV<'i>> for ExprVFmt<
        LIMIT,
    > {
        fn serialize_into(&self, v: &ExprV<'i>, obuf: &mut Output) {
            proof {
                self.expr_kind.lemma_deep_view();
            }
            self.serialize_gas(LIMIT, v, obuf);
        }
    }

    impl<'i, const LIMIT: usize> Prepare<ExprV<'i>> for ExprVFmt<LIMIT> {
        fn prepare(&self, v: &ExprV<'i>) -> Result<usize, PreSerializeError> {
            proof {
                self.expr_kind.lemma_deep_view();
            }
            self.prepare_gas(LIMIT, v)
        }
    }

    impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ListVConsFmt<LIMIT> {
        type PT = ListVCons<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            self.parse_gas(LIMIT, ibuf)
        }
    }

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<
        Output,
        ListVCons<'i>,
    > for ListVConsFmt<LIMIT> {
        fn serialize_into(&self, v: &ListVCons<'i>, obuf: &mut Output) {
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
            proof {
                self.list_kind.lemma_deep_view();
            }
            self.parse_gas(LIMIT, ibuf)
        }
    }

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<Output, ListV<'i>> for ListVFmt<
        LIMIT,
    > {
        fn serialize_into(&self, v: &ListV<'i>, obuf: &mut Output) {
            proof {
                self.list_kind.lemma_deep_view();
            }
            self.serialize_gas(LIMIT, v, obuf);
        }
    }

    impl<'i, const LIMIT: usize> Prepare<ListV<'i>> for ListVFmt<LIMIT> {
        fn prepare(&self, v: &ListV<'i>) -> Result<usize, PreSerializeError> {
            proof {
                self.list_kind.lemma_deep_view();
            }
            self.prepare_gas(LIMIT, v)
        }
    }

    impl<const LIMIT: usize> ExprFmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<Expr<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    expr_parse_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, ibuf@),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = expr_parse_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, ibuf@);
            let rest = *ibuf;

            let (n1, t) = (ExprKindFmt).parse(&rest)?;
            proof {
                t.lemma_deep_view();
            }
            let rest = rest.skip(n1);
            proof {
                t.lemma_deep_view();
            }

            if gas == 0 {
                return Err(ParseError::recursion_limit_exceeded());
            }
            let (n2, v) = (ExprVFmt::<LIMIT> { expr_kind: t }).parse_gas(gas - 1, &rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Expr { t: t, v: Box::new(v) };
            assert(parse_spec == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(&self, gas: usize, v: &Expr<'i>, obuf: &mut Output)
            requires
                expr_consistent_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view()),
                old(obuf).fits(
                    expr_byte_len_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view()),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + expr_serialize_spec_gas::<LIMIT>(
                    &SCC1RecBody,
                    gas as nat,
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        expr_byte_len_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view())
                            + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            let Expr { t, v } = v;
            proof {
                t.lemma_deep_view();
            }

            (ExprKindFmt).serialize_into(t, obuf);
            (ExprVFmt::<LIMIT> { expr_kind: *t }).serialize_gas(gas - 1, v, obuf);
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &Expr<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& expr_consistent_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view())
                    &&& len == expr_byte_len_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            let Expr { t, v } = v;
            proof {
                t.lemma_deep_view();
            }

            let l1 = (ExprKindFmt).prepare(t)?;
            if gas == 0 {
                return Err(
                    PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
                );
            }
            let l2 = (ExprVFmt::<LIMIT> { expr_kind: *t }).prepare_gas(gas - 1, v)?;
            let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total)
        }
    }

    impl<const LIMIT: usize> ListFmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<List<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    list_parse_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, ibuf@),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = list_parse_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, ibuf@);
            let rest = *ibuf;

            let (n1, t) = (ListKindFmt).parse(&rest)?;
            proof {
                t.lemma_deep_view();
            }
            let rest = rest.skip(n1);
            proof {
                t.lemma_deep_view();
            }

            if gas == 0 {
                return Err(ParseError::recursion_limit_exceeded());
            }
            let (n2, v) = (ListVFmt::<LIMIT> { list_kind: t }).parse_gas(gas - 1, &rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = List { t: t, v: Box::new(v) };
            assert(parse_spec == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(&self, gas: usize, v: &List<'i>, obuf: &mut Output)
            requires
                list_consistent_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view()),
                old(obuf).fits(
                    list_byte_len_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view()),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + list_serialize_spec_gas::<LIMIT>(
                    &SCC1RecBody,
                    gas as nat,
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        list_byte_len_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view())
                            + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            let List { t, v } = v;
            proof {
                t.lemma_deep_view();
            }

            (ListKindFmt).serialize_into(t, obuf);
            (ListVFmt::<LIMIT> { list_kind: *t }).serialize_gas(gas - 1, v, obuf);
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &List<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& list_consistent_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view())
                    &&& len == list_byte_len_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            let List { t, v } = v;
            proof {
                t.lemma_deep_view();
            }

            let l1 = (ListKindFmt).prepare(t)?;
            if gas == 0 {
                return Err(
                    PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
                );
            }
            let l2 = (ListVFmt::<LIMIT> { list_kind: *t }).prepare_gas(gas - 1, v)?;
            let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total)
        }
    }

    impl<const LIMIT: usize> ExprVFmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ExprV<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    expr_v_parse_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        self.expr_kind_spec(),
                        ibuf@,
                    ),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = expr_v_parse_spec_gas::<LIMIT>(
                &SCC1RecBody,
                gas as nat,
                self.expr_kind_spec(),
                ibuf@,
            );
            let rest = *ibuf;

            proof {
                self.expr_kind.lemma_deep_view();
            }

            let (n, v) = match self.expr_kind {
                ExprKind::Num => {
                    let (n, inner) = (U8).parse(ibuf)?;
                    (n, ExprV::Num(inner))
                },
                ExprKind::Group => {
                    if gas == 0 {
                        return Err(ParseError::recursion_limit_exceeded());
                    }
                    let (n, inner) = (ListFmt::<LIMIT> {  }).parse_gas(gas - 1, ibuf)?;
                    (n, ExprV::Group(Box::new(inner)))
                },
            };
            assert(parse_spec == Some((n as int, v.deep_view())));
            Ok((n, v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(&self, gas: usize, v: &ExprV<'i>, obuf: &mut Output)
            requires
                expr_v_consistent_spec_gas::<LIMIT>(
                    &SCC1RecBody,
                    gas as nat,
                    self.expr_kind_spec(),
                    v.deep_view(),
                ),
                old(obuf).fits(
                    expr_v_byte_len_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        self.expr_kind_spec(),
                        v.deep_view(),
                    ),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + expr_v_serialize_spec_gas::<LIMIT>(
                    &SCC1RecBody,
                    gas as nat,
                    self.expr_kind_spec(),
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        expr_v_byte_len_spec_gas::<LIMIT>(
                            &SCC1RecBody,
                            gas as nat,
                            self.expr_kind_spec(),
                            v.deep_view(),
                        ) + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            proof {
                self.expr_kind.lemma_deep_view();
            }

            match (self.expr_kind, v) {
                (ExprKind::Num, ExprV::Num(v)) => {
                    (U8).serialize_into(v, obuf);
                },
                (ExprKind::Group, ExprV::Group(v)) => {
                    (ListFmt::<LIMIT> {  }).serialize_gas(gas - 1, v, obuf);
                },
                _ => {},
            }
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &ExprV<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& expr_v_consistent_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        self.expr_kind_spec(),
                        v.deep_view(),
                    )
                    &&& len == expr_v_byte_len_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        self.expr_kind_spec(),
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            proof {
                self.expr_kind.lemma_deep_view();
            }

            match (self.expr_kind, v) {
                (ExprKind::Num, ExprV::Num(v)) => (U8).prepare(v),
                (ExprKind::Group, ExprV::Group(v)) => {
                    if gas == 0 {
                        Err(
                            PreSerializeError::not_compliant(
                                ComplianceErrorKind::RecursionLimitExceeded,
                            ),
                        )
                    } else {
                        (ListFmt::<LIMIT> {  }).prepare_gas(gas - 1, v)
                    }
                },
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<const LIMIT: usize> ListVConsFmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ListVCons<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    list_v_cons_parse_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, ibuf@),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = list_v_cons_parse_spec_gas::<LIMIT>(
                &SCC1RecBody,
                gas as nat,
                ibuf@,
            );
            let rest = *ibuf;

            if gas == 0 {
                return Err(ParseError::recursion_limit_exceeded());
            }
            let (n1, head) = (ExprFmt::<LIMIT> {  }).parse_gas(gas - 1, &rest)?;
            let rest = rest.skip(n1);
            let (n2, tail) = (ListFmt::<LIMIT> {  }).parse_gas(gas - 1, &rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = ListVCons { head: Box::new(head), tail: Box::new(tail) };
            assert(parse_spec == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(
            &self,
            gas: usize,
            v: &ListVCons<'i>,
            obuf: &mut Output,
        )
            requires
                list_v_cons_consistent_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view()),
                old(obuf).fits(
                    list_v_cons_byte_len_spec_gas::<LIMIT>(&SCC1RecBody, gas as nat, v.deep_view()),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + list_v_cons_serialize_spec_gas::<LIMIT>(
                    &SCC1RecBody,
                    gas as nat,
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        list_v_cons_byte_len_spec_gas::<LIMIT>(
                            &SCC1RecBody,
                            gas as nat,
                            v.deep_view(),
                        ) + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            let ListVCons { head, tail } = v;
            (ExprFmt::<LIMIT> {  }).serialize_gas(gas - 1, head, obuf);
            (ListFmt::<LIMIT> {  }).serialize_gas(gas - 1, tail, obuf);
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &ListVCons<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& list_v_cons_consistent_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        v.deep_view(),
                    )
                    &&& len == list_v_cons_byte_len_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            let ListVCons { head, tail } = v;
            if gas == 0 {
                return Err(
                    PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
                );
            }
            let l1 = (ExprFmt::<LIMIT> {  }).prepare_gas(gas - 1, head)?;
            let l2 = (ListFmt::<LIMIT> {  }).prepare_gas(gas - 1, tail)?;
            let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total)
        }
    }

    impl<const LIMIT: usize> ListVFmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ListV<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    list_v_parse_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        self.list_kind_spec(),
                        ibuf@,
                    ),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = list_v_parse_spec_gas::<LIMIT>(
                &SCC1RecBody,
                gas as nat,
                self.list_kind_spec(),
                ibuf@,
            );
            let rest = *ibuf;

            proof {
                self.list_kind.lemma_deep_view();
            }

            let (n, v) = match self.list_kind {
                ListKind::Nil => {
                    let (n, inner) = (Fixed::<0>).parse(ibuf)?;
                    (n, ListV::Nil(inner))
                },
                ListKind::Cons => {
                    if gas == 0 {
                        return Err(ParseError::recursion_limit_exceeded());
                    }
                    let (n, inner) = (ListVConsFmt::<LIMIT> {  }).parse_gas(gas - 1, ibuf)?;
                    (n, ListV::Cons(Box::new(inner)))
                },
            };
            assert(parse_spec == Some((n as int, v.deep_view())));
            Ok((n, v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(&self, gas: usize, v: &ListV<'i>, obuf: &mut Output)
            requires
                list_v_consistent_spec_gas::<LIMIT>(
                    &SCC1RecBody,
                    gas as nat,
                    self.list_kind_spec(),
                    v.deep_view(),
                ),
                old(obuf).fits(
                    list_v_byte_len_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        self.list_kind_spec(),
                        v.deep_view(),
                    ),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + list_v_serialize_spec_gas::<LIMIT>(
                    &SCC1RecBody,
                    gas as nat,
                    self.list_kind_spec(),
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        list_v_byte_len_spec_gas::<LIMIT>(
                            &SCC1RecBody,
                            gas as nat,
                            self.list_kind_spec(),
                            v.deep_view(),
                        ) + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            proof {
                self.list_kind.lemma_deep_view();
            }

            match (self.list_kind, v) {
                (ListKind::Nil, ListV::Nil(v)) => {
                    (Fixed::<0>).serialize_into(*v, obuf);
                },
                (ListKind::Cons, ListV::Cons(v)) => {
                    (ListVConsFmt::<LIMIT> {  }).serialize_gas(gas - 1, v, obuf);
                },
                _ => {},
            }
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &ListV<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& list_v_consistent_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        self.list_kind_spec(),
                        v.deep_view(),
                    )
                    &&& len == list_v_byte_len_spec_gas::<LIMIT>(
                        &SCC1RecBody,
                        gas as nat,
                        self.list_kind_spec(),
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            proof {
                self.list_kind.lemma_deep_view();
            }

            match (self.list_kind, v) {
                (ListKind::Nil, ListV::Nil(v)) => (Fixed::<0>).prepare(v),
                (ListKind::Cons, ListV::Cons(v)) => {
                    if gas == 0 {
                        Err(
                            PreSerializeError::not_compliant(
                                ComplianceErrorKind::RecursionLimitExceeded,
                            ),
                        )
                    } else {
                        (ListVConsFmt::<LIMIT> {  }).prepare_gas(gas - 1, v)
                    }
                },
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ChainAFmt<LIMIT> {
        type PT = ChainA<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            self.parse_gas(LIMIT, ibuf)
        }
    }

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<Output, ChainA<'i>> for ChainAFmt<
        LIMIT,
    > {
        fn serialize_into(&self, v: &ChainA<'i>, obuf: &mut Output) {
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

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<Output, ChainB<'i>> for ChainBFmt<
        LIMIT,
    > {
        fn serialize_into(&self, v: &ChainB<'i>, obuf: &mut Output) {
            self.serialize_gas(LIMIT, v, obuf);
        }
    }

    impl<'i, const LIMIT: usize> Prepare<ChainB<'i>> for ChainBFmt<LIMIT> {
        fn prepare(&self, v: &ChainB<'i>) -> Result<usize, PreSerializeError> {
            self.prepare_gas(LIMIT, v)
        }
    }

    impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ChainAChoice1Fmt<LIMIT> {
        type PT = ChainAChoice1<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            self.parse_gas(LIMIT, ibuf)
        }
    }

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<
        Output,
        ChainAChoice1<'i>,
    > for ChainAChoice1Fmt<LIMIT> {
        fn serialize_into(&self, v: &ChainAChoice1<'i>, obuf: &mut Output) {
            self.serialize_gas(LIMIT, v, obuf);
        }
    }

    impl<'i, const LIMIT: usize> Prepare<ChainAChoice1<'i>> for ChainAChoice1Fmt<LIMIT> {
        fn prepare(&self, v: &ChainAChoice1<'i>) -> Result<usize, PreSerializeError> {
            self.prepare_gas(LIMIT, v)
        }
    }

    impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ChainBChoice1Fmt<LIMIT> {
        type PT = ChainBChoice1<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            self.parse_gas(LIMIT, ibuf)
        }
    }

    impl<Output: OutputBuf, 'i, const LIMIT: usize> Serializer<
        Output,
        ChainBChoice1<'i>,
    > for ChainBChoice1Fmt<LIMIT> {
        fn serialize_into(&self, v: &ChainBChoice1<'i>, obuf: &mut Output) {
            self.serialize_gas(LIMIT, v, obuf);
        }
    }

    impl<'i, const LIMIT: usize> Prepare<ChainBChoice1<'i>> for ChainBChoice1Fmt<LIMIT> {
        fn prepare(&self, v: &ChainBChoice1<'i>) -> Result<usize, PreSerializeError> {
            self.prepare_gas(LIMIT, v)
        }
    }

    impl<const LIMIT: usize> ChainAFmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ChainA<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    chain_a_parse_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        self.tag_spec(),
                        ibuf@,
                    ),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = chain_a_parse_spec_gas::<LIMIT>(
                &SCC2RecBody,
                gas as nat,
                self.tag_spec(),
                ibuf@,
            );
            let rest = *ibuf;

            let (n, v) = match self.tag {
                0 => {
                    let (n, inner) = (U8).parse(ibuf)?;
                    if !(inner >= 1 && inner <= 10) {
                        return Err(ParseError::predicate_failed());
                    }
                    (n, ChainA::Variant1(inner))
                },
                _ => {
                    if gas == 0 {
                        return Err(ParseError::recursion_limit_exceeded());
                    }
                    let (n, inner) = (ChainAChoice1Fmt::<LIMIT> {  }).parse_gas(gas - 1, ibuf)?;
                    (n, ChainA::Default(Box::new(inner)))
                },
            };
            assert(parse_spec == Some((n as int, v.deep_view())));
            Ok((n, v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(
            &self,
            gas: usize,
            v: &ChainA<'i>,
            obuf: &mut Output,
        )
            requires
                chain_a_consistent_spec_gas::<LIMIT>(
                    &SCC2RecBody,
                    gas as nat,
                    self.tag_spec(),
                    v.deep_view(),
                ),
                old(obuf).fits(
                    chain_a_byte_len_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        self.tag_spec(),
                        v.deep_view(),
                    ),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + chain_a_serialize_spec_gas::<LIMIT>(
                    &SCC2RecBody,
                    gas as nat,
                    self.tag_spec(),
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        chain_a_byte_len_spec_gas::<LIMIT>(
                            &SCC2RecBody,
                            gas as nat,
                            self.tag_spec(),
                            v.deep_view(),
                        ) + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            match (self.tag, v) {
                (0, ChainA::Variant1(v)) => {
                    (U8).serialize_into(v, obuf);
                },
                (_, ChainA::Default(v)) => {
                    (ChainAChoice1Fmt::<LIMIT> {  }).serialize_gas(gas - 1, v, obuf);
                },
                _ => {},
            }
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &ChainA<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& chain_a_consistent_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        self.tag_spec(),
                        v.deep_view(),
                    )
                    &&& len == chain_a_byte_len_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        self.tag_spec(),
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            match (self.tag, v) {
                (0, ChainA::Variant1(v)) => {
                    if !(*v >= 1 && *v <= 10) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U8).prepare(v)
                    }
                },
                (x, ChainA::Default(v)) if !(x == 0) => {
                    if gas == 0 {
                        Err(
                            PreSerializeError::not_compliant(
                                ComplianceErrorKind::RecursionLimitExceeded,
                            ),
                        )
                    } else {
                        (ChainAChoice1Fmt::<LIMIT> {  }).prepare_gas(gas - 1, v)
                    }
                },
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<const LIMIT: usize> ChainBFmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ChainB<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    chain_b_parse_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        self.tag_spec(),
                        ibuf@,
                    ),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = chain_b_parse_spec_gas::<LIMIT>(
                &SCC2RecBody,
                gas as nat,
                self.tag_spec(),
                ibuf@,
            );
            let rest = *ibuf;

            let (n, v) = match self.tag {
                0 => {
                    let (n, inner) = (U16Le).parse(ibuf)?;
                    if !(inner >= 256) {
                        return Err(ParseError::predicate_failed());
                    }
                    (n, ChainB::Variant1(inner))
                },
                _ => {
                    if gas == 0 {
                        return Err(ParseError::recursion_limit_exceeded());
                    }
                    let (n, inner) = (ChainBChoice1Fmt::<LIMIT> {  }).parse_gas(gas - 1, ibuf)?;
                    (n, ChainB::Default(Box::new(inner)))
                },
            };
            assert(parse_spec == Some((n as int, v.deep_view())));
            Ok((n, v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(
            &self,
            gas: usize,
            v: &ChainB<'i>,
            obuf: &mut Output,
        )
            requires
                chain_b_consistent_spec_gas::<LIMIT>(
                    &SCC2RecBody,
                    gas as nat,
                    self.tag_spec(),
                    v.deep_view(),
                ),
                old(obuf).fits(
                    chain_b_byte_len_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        self.tag_spec(),
                        v.deep_view(),
                    ),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + chain_b_serialize_spec_gas::<LIMIT>(
                    &SCC2RecBody,
                    gas as nat,
                    self.tag_spec(),
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        chain_b_byte_len_spec_gas::<LIMIT>(
                            &SCC2RecBody,
                            gas as nat,
                            self.tag_spec(),
                            v.deep_view(),
                        ) + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            match (self.tag, v) {
                (0, ChainB::Variant1(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                (_, ChainB::Default(v)) => {
                    (ChainBChoice1Fmt::<LIMIT> {  }).serialize_gas(gas - 1, v, obuf);
                },
                _ => {},
            }
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &ChainB<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& chain_b_consistent_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        self.tag_spec(),
                        v.deep_view(),
                    )
                    &&& len == chain_b_byte_len_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        self.tag_spec(),
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            match (self.tag, v) {
                (0, ChainB::Variant1(v)) => {
                    if !(*v >= 256) {
                        Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                    } else {
                        (U16Le).prepare(v)
                    }
                },
                (x, ChainB::Default(v)) if !(x == 0) => {
                    if gas == 0 {
                        Err(
                            PreSerializeError::not_compliant(
                                ComplianceErrorKind::RecursionLimitExceeded,
                            ),
                        )
                    } else {
                        (ChainBChoice1Fmt::<LIMIT> {  }).prepare_gas(gas - 1, v)
                    }
                },
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<const LIMIT: usize> ChainAChoice1Fmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ChainAChoice1<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    chain_a_choice1_parse_spec_gas::<LIMIT>(&SCC2RecBody, gas as nat, ibuf@),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = chain_a_choice1_parse_spec_gas::<LIMIT>(
                &SCC2RecBody,
                gas as nat,
                ibuf@,
            );
            let rest = *ibuf;

            let (n1, len) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, payload) = (Varied(len)).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, next_tag) = (U8).parse(&rest)?;
            let rest = rest.skip(n3);
            if gas == 0 {
                return Err(ParseError::recursion_limit_exceeded());
            }
            let (n4, tail) = (ChainBFmt::<LIMIT> { tag: next_tag }).parse_gas(gas - 1, &rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = ChainAChoice1 {
                len: len,
                payload: payload,
                next_tag: next_tag,
                tail: Box::new(tail),
            };
            assert(parse_spec == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(
            &self,
            gas: usize,
            v: &ChainAChoice1<'i>,
            obuf: &mut Output,
        )
            requires
                chain_a_choice1_consistent_spec_gas::<LIMIT>(
                    &SCC2RecBody,
                    gas as nat,
                    v.deep_view(),
                ),
                old(obuf).fits(
                    chain_a_choice1_byte_len_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        v.deep_view(),
                    ),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + chain_a_choice1_serialize_spec_gas::<LIMIT>(
                    &SCC2RecBody,
                    gas as nat,
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        chain_a_choice1_byte_len_spec_gas::<LIMIT>(
                            &SCC2RecBody,
                            gas as nat,
                            v.deep_view(),
                        ) + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            let ChainAChoice1 { len, payload, next_tag, tail } = v;
            (U8).serialize_into(len, obuf);
            (Varied(*len)).serialize_into(*payload, obuf);
            (U8).serialize_into(next_tag, obuf);
            (ChainBFmt::<LIMIT> { tag: *next_tag }).serialize_gas(gas - 1, tail, obuf);
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &ChainAChoice1<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& chain_a_choice1_consistent_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        v.deep_view(),
                    )
                    &&& len == chain_a_choice1_byte_len_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            let ChainAChoice1 { len, payload, next_tag, tail } = v;
            let l1 = (U8).prepare(len)?;
            let l2 = (Varied(*len)).prepare(payload)?;
            let l3 = (U8).prepare(next_tag)?;
            if gas == 0 {
                return Err(
                    PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
                );
            }
            let l4 = (ChainBFmt::<LIMIT> { tag: *next_tag }).prepare_gas(gas - 1, tail)?;
            let total = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?.checked_add(l4).ok_or(
                PreSerializeError::length_too_large(),
            )?;
            Ok(total)
        }
    }

    impl<const LIMIT: usize> ChainBChoice1Fmt<LIMIT> {
        fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<ChainBChoice1<'i>>)
            ensures
                parse_matches_spec(
                    r,
                    chain_b_choice1_parse_spec_gas::<LIMIT>(&SCC2RecBody, gas as nat, ibuf@),
                ),
                r matches Ok((n, _)) ==> n <= ibuf@.len(),
            decreases gas,
        {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();
            let ghost parse_spec = chain_b_choice1_parse_spec_gas::<LIMIT>(
                &SCC2RecBody,
                gas as nat,
                ibuf@,
            );
            let rest = *ibuf;

            let (n1, payload) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, next_tag) = (U8).parse(&rest)?;
            let rest = rest.skip(n2);
            if gas == 0 {
                return Err(ParseError::recursion_limit_exceeded());
            }
            let (n3, tail) = (ChainAFmt::<LIMIT> { tag: next_tag }).parse_gas(gas - 1, &rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = ChainBChoice1 {
                payload: payload,
                next_tag: next_tag,
                tail: Box::new(tail),
            };
            assert(parse_spec == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }

        fn serialize_gas<Output: OutputBuf, 'i>(
            &self,
            gas: usize,
            v: &ChainBChoice1<'i>,
            obuf: &mut Output,
        )
            requires
                chain_b_choice1_consistent_spec_gas::<LIMIT>(
                    &SCC2RecBody,
                    gas as nat,
                    v.deep_view(),
                ),
                old(obuf).fits(
                    chain_b_choice1_byte_len_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        v.deep_view(),
                    ),
                ),
            ensures
                final(obuf)@ == old(obuf)@ + chain_b_choice1_serialize_spec_gas::<LIMIT>(
                    &SCC2RecBody,
                    gas as nat,
                    v.deep_view(),
                ),
                forall|n|
                    old(obuf).fits(
                        chain_b_choice1_byte_len_spec_gas::<LIMIT>(
                            &SCC2RecBody,
                            gas as nat,
                            v.deep_view(),
                        ) + n,
                    ) <==> final(obuf).fits(n),
                old(obuf).same_destination(final(obuf)),
            decreases gas,
        {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            let ChainBChoice1 { payload, next_tag, tail } = v;
            (U32Le).serialize_into(payload, obuf);
            (U8).serialize_into(next_tag, obuf);
            (ChainAFmt::<LIMIT> { tag: *next_tag }).serialize_gas(gas - 1, tail, obuf);
        }

        fn prepare_gas<'i>(&self, gas: usize, v: &ChainBChoice1<'i>) -> (checked: Result<
            usize,
            PreSerializeError,
        >)
            ensures
                checked matches Ok(len) ==> {
                    &&& chain_b_choice1_consistent_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        v.deep_view(),
                    )
                    &&& len == chain_b_choice1_byte_len_spec_gas::<LIMIT>(
                        &SCC2RecBody,
                        gas as nat,
                        v.deep_view(),
                    )
                },
            decreases gas,
        {
            let ChainBChoice1 { payload, next_tag, tail } = v;
            let l1 = (U32Le).prepare(payload)?;
            let l2 = (U8).prepare(next_tag)?;
            if gas == 0 {
                return Err(
                    PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded),
                );
            }
            let l3 = (ChainAFmt::<LIMIT> { tag: *next_tag }).prepare_gas(gas - 1, tail)?;
            let total = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total)
        }
    }

}

} // verus!
