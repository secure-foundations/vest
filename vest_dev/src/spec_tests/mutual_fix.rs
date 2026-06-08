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

impl Clone for Expr {
    fn clone(&self) -> (cloned: Self)
        ensures
            cloned.deep_view() == self.deep_view(),
        decreases self,
    {
        match self {
            Expr::Num(n) => Expr::Num(*n),
            Expr::Group(list) => Expr::Group(Box::new((**list).clone())),
        }
    }
}

impl Clone for List {
    fn clone(&self) -> (cloned: Self)
        ensures
            cloned.deep_view() == self.deep_view(),
        decreases self,
    {
        match self {
            List::Nil => List::Nil,
            List::Cons(head, tail) => List::Cons(
                Box::new((**head).clone()),
                Box::new((**tail).clone()),
            ),
        }
    }
}

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

pub type ValueSpec = Value;

impl DeepView for Value {
    type V = ValueSpec;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

// ============================================================
// Format Specifications
// ============================================================
#[derive(Clone, Copy)]
pub struct ExprFmt<const LIMIT: usize>;

pub type ExprFmtSpec<const LIMIT: usize> = ExprProj<FixWith<LIMIT, ExprListRecBody, FmtType>>;

impl<const LIMIT: usize> ExprFmt<LIMIT> {
    pub open spec fn spec_inner() -> ExprFmtSpec<LIMIT> {
        expr_proj(FixWith::<LIMIT, ExprListRecBody, FmtType>(ExprListRecBody, FmtType::EXPR))
    }
}

#[derive(Clone, Copy)]
pub struct ListFmt<const LIMIT: usize>;

pub type ListFmtSpec<const LIMIT: usize> = ListProj<FixWith<LIMIT, ExprListRecBody, FmtType>>;

impl<const LIMIT: usize> ListFmt<LIMIT> {
    pub open spec fn spec_inner() -> ListFmtSpec<LIMIT> {
        list_proj(FixWith::<LIMIT, ExprListRecBody, FmtType>(ExprListRecBody, FmtType::LIST))
    }
}

/*
 *  Helpers for mutual recursion
 */

pub type ExprProj<Rec> = Mapped<Refined<Rec, PredFnSpec<ValueSpec>>, BiMapper<ValueSpec, ExprSpec>>;

pub type ListProj<Rec> = Mapped<Refined<Rec, PredFnSpec<ValueSpec>>, BiMapper<ValueSpec, ListSpec>>;

pub open spec fn expr_proj<Rec>(rec: Rec) -> ExprProj<Rec> where
    Rec: SpecCombinator<T = ValueSpec>,
 {
    Mapped {
        inner: Refined(rec, |v: ValueSpec| v is Expr),
        mapper: BiMap(
            |v: ValueSpec| -> ExprSpec { v->expr },
            |expr: ExprSpec| -> ValueSpec { ValueSpec::Expr { expr } },
        ),
    }
}

pub open spec fn list_proj<Rec>(rec: Rec) -> ListProj<Rec> where
    Rec: SpecCombinator<T = ValueSpec>,
 {
    Mapped {
        inner: Refined(rec, |v: ValueSpec| v is List),
        mapper: BiMap(
            |v: ValueSpec| -> ListSpec { v->list },
            |list: ListSpec| -> ValueSpec { ValueSpec::List { list } },
        ),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum FmtType {
    EXPR,
    LIST,
}

impl DeepView for FmtType {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

pub type ExprListBodyFmt<Rec> = Alt<Cond<ExprBodyFmt<Rec>>, Cond<ListBodyFmt<Rec>>>;

pub struct ExprListRecBody;

impl SpecRecBody for ExprListRecBody {
    type Param = FmtType;

    type T = ValueSpec;

    type Body = ExprListBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        which: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Alt(
            Cond(which == FmtType::EXPR, expr_body(rec(FmtType::LIST))),
            Cond(which == FmtType::LIST, list_body(rec(FmtType::EXPR), rec(FmtType::LIST))),
        )
    }
}

pub type ExprBodyFmt<Rec> = Mapped<
    Choice<PrefixTagged<U8, U8>, PrefixTagged<U8, ListProj<Rec>>>,
    ExprMapper,
>;

pub open spec fn expr_body<Rec>(list_rec: Rec) -> ExprBodyFmt<Rec> where
    Rec: SpecCombinator<T = ValueSpec>,
 {
    Mapped {
        inner: Choice(PrefixTagged(U8, 0x10u8, U8), PrefixTagged(U8, 0x11u8, list_proj(list_rec))),
        mapper: ExprMapper,
    }
}

pub struct ExprMapper;

impl SpecMapper for ExprMapper {
    type In = Sum<u8, ListSpec>;

    type Out = ValueSpec;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(n) => ValueSpec::Expr { expr: ExprSpec::Num(n) },
            Sum::Inr(list) => ValueSpec::Expr { expr: ExprSpec::Group(Box::new(list)) },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is Expr
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            ValueSpec::Expr { expr: ExprSpec::Num(n) } => Sum::Inl(n),
            ValueSpec::Expr { expr: ExprSpec::Group(list) } => Sum::Inr(*list),
            _ => arbitrary(),
        }
    }
}

pub type ListBodyFmt<Rec> = Mapped<
    Choice<PrefixTagged<U8, Empty>, PrefixTagged<U8, Pair<ExprProj<Rec>, ListProj<Rec>>>>,
    ListMapper,
>;

pub open spec fn list_body<Rec>(expr_rec: Rec, list_rec: Rec) -> ListBodyFmt<Rec> where
    Rec: SpecCombinator<T = ValueSpec>,
 {
    Mapped {
        inner: Choice(
            PrefixTagged(U8, 0x20u8, Empty),
            PrefixTagged(U8, 0x21u8, Pair(expr_proj(expr_rec), list_proj(list_rec))),
        ),
        mapper: ListMapper,
    }
}

pub struct ListMapper;

impl SpecMapper for ListMapper {
    type In = Sum<(), (ExprSpec, ListSpec)>;

    type Out = ValueSpec;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(_) => ValueSpec::List { list: ListSpec::Nil },
            Sum::Inr((head, tail)) => ValueSpec::List {
                list: ListSpec::Cons(Box::new(head), Box::new(tail)),
            },
        }
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o is List
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            ValueSpec::List { list: ListSpec::Nil } => Sum::Inl(()),
            ValueSpec::List { list: ListSpec::Cons(head, tail) } => Sum::Inr((*head, *tail)),
            _ => arbitrary(),
        }
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
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

impl StrictRecBody for ExprListRecBody {
    proof fn lemma_body_all_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        broadcast use crate::combinators::disjoint::disjointness_lemmas;

    }
}

// ============================================================
// Executable Implementations
// ============================================================
impl<'i> ParserRecBody<&'i [u8]> for ExprListRecBody {
    type EP = FmtType;

    type O = Value;

    fn parse_body<Exec>(
        &self,
        which: &FmtType,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<Self::O> where Exec: Fn(&FmtType, &&'i [u8]) -> PResult<Self::O> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();

        match which {
            FmtType::EXPR => {
                let (n1, tag) = U8.parse(ibuf)?;
                let rest = ibuf.skip(n1);
                match tag {
                    0x10u8 => {
                        let (n2, n) = U8.parse(&rest)?;
                        Ok((n1 + n2, Value::Expr { expr: Expr::Num(n) }))
                    },
                    0x11u8 => {
                        let (n2, inner) = exec_rec(&FmtType::LIST, &rest)?;
                        match inner {
                            Value::List { list } => {
                                let total = n1 + n2;
                                Ok((total, Value::Expr { expr: Expr::Group(Box::new(list)) }))
                            },
                            Value::Expr { .. } => Err(ParseError::cond_rejected()),
                        }
                    },
                    _ => Err(ParseError::invalid_tag()),
                }
            },
            FmtType::LIST => {
                let (n1, tag) = U8.parse(ibuf)?;
                let rest = ibuf.skip(n1);
                match tag {
                    0x20u8 => Ok((n1, Value::List { list: List::Nil })),
                    0x21u8 => {
                        let (n2, head_val) = exec_rec(&FmtType::EXPR, &rest)?;
                        let rest2 = rest.skip(n2);
                        let (n3, tail_val) = exec_rec(&FmtType::LIST, &rest2)?;
                        match (head_val, tail_val) {
                            (Value::Expr { expr }, Value::List { list }) => {
                                let total = n1 + n2 + n3;
                                Ok(
                                    (
                                        total,
                                        Value::List {
                                            list: List::Cons(Box::new(expr), Box::new(list)),
                                        },
                                    ),
                                )
                            },
                            _ => Err(ParseError::cond_rejected()),
                        }
                    },
                    _ => Err(ParseError::invalid_tag()),
                }
            },
        }
    }
}

impl SerializerRecBody<Value> for ExprListRecBody {
    type EP = FmtType;

    fn serialize_body<Exec>(
        &self,
        which: &FmtType,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &Value,
        obuf: &mut Vec<u8>,
    ) where Exec: Fn(&FmtType, &Value, &mut Vec<u8>) {
        match (which, v) {
            (FmtType::EXPR, Value::Expr { expr: Expr::Num(n) }) => {
                U8.serialize(&0x10u8, obuf);
                U8.serialize(n, obuf);
            },
            (FmtType::EXPR, Value::Expr { expr: Expr::Group(list) }) => {
                U8.serialize(&0x11u8, obuf);
                let child = Value::List { list: (**list).clone() };
                exec_rec(&FmtType::LIST, &child, obuf);
            },
            (FmtType::LIST, Value::List { list: List::Nil }) => {
                U8.serialize(&0x20u8, obuf);
            },
            (FmtType::LIST, Value::List { list: List::Cons(head, tail) }) => {
                U8.serialize(&0x21u8, obuf);
                let head_child = Value::Expr { expr: (**head).clone() };
                let tail_child = Value::List { list: (**tail).clone() };
                exec_rec(&FmtType::EXPR, &head_child, obuf);
                exec_rec(&FmtType::LIST, &tail_child, obuf);
            },
            _ => {},
        }
    }
}

impl PrepareRecBody<Value> for ExprListRecBody {
    type EP = FmtType;

    fn prepare_body<Exec>(
        &self,
        which: &FmtType,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &Value,
    ) -> Result<usize, PreSerializeError> where
        Exec: Fn(&FmtType, &Value) -> Result<usize, PreSerializeError>,
     {
        match (which, v) {
            (FmtType::EXPR, Value::Expr { expr: Expr::Num(n) }) => {
                let l1 = U8.prepare(&0x10u8)?;
                let l2 = U8.prepare(n)?;
                let total = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?;
                Ok(total)
            },
            (FmtType::EXPR, Value::Expr { expr: Expr::Group(list) }) => {
                let l1 = U8.prepare(&0x11u8)?;
                let child = Value::List { list: (**list).clone() };
                let l2 = exec_rec(&FmtType::LIST, &child)?;
                let total = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?;
                Ok(total)
            },
            (FmtType::LIST, Value::List { list: List::Nil }) => {
                let total = U8.prepare(&0x20u8)?;
                Ok(total)
            },
            (FmtType::LIST, Value::List { list: List::Cons(head, tail) }) => {
                let l1 = U8.prepare(&0x21u8)?;
                let head_child = Value::Expr { expr: (**head).clone() };
                let tail_child = Value::List { list: (**tail).clone() };
                let l2 = exec_rec(&FmtType::EXPR, &head_child)?;
                let l3 = exec_rec(&FmtType::LIST, &tail_child)?;
                let sum1 = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?;
                let total = sum1.checked_add(l3).ok_or(PreSerializeError::LengthTooLarge)?;
                Ok(total)
            },
            _ => Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
        }
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ExprFmt<LIMIT> {
    type PT = Expr;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let family = FixWith::<LIMIT, ExprListRecBody, FmtType>(ExprListRecBody, FmtType::EXPR);
        match family.parse(ibuf) {
            Ok((n, Value::Expr { expr })) => Ok((n, expr)),
            Ok((_, Value::List { .. })) => Err(ParseError::cond_rejected()),
            Err(err) => Err(err),
        }
    }
}

impl<const LIMIT: usize> Serializer<Expr> for ExprFmt<LIMIT> {
    fn serialize(&self, v: &Expr, obuf: &mut Vec<u8>) {
        let family = FixWith::<LIMIT, ExprListRecBody, FmtType>(ExprListRecBody, FmtType::EXPR);
        let family_v = Value::Expr { expr: v.clone() };
        family.serialize(&family_v, obuf);
    }
}

impl<const LIMIT: usize> Prepare<Expr> for ExprFmt<LIMIT> {
    fn prepare(&self, v: &Expr) -> Result<usize, PreSerializeError> {
        let family = FixWith::<LIMIT, ExprListRecBody, FmtType>(ExprListRecBody, FmtType::EXPR);
        let family_v = Value::Expr { expr: v.clone() };
        let checked = family.prepare(&family_v);
        checked
    }
}

impl<'i, const LIMIT: usize> Parser<&'i [u8]> for ListFmt<LIMIT> {
    type PT = List;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let family = FixWith::<LIMIT, ExprListRecBody, FmtType>(ExprListRecBody, FmtType::LIST);
        match family.parse(ibuf) {
            Ok((n, Value::List { list })) => Ok((n, list)),
            Ok((_, Value::Expr { .. })) => Err(ParseError::invalid_tag()),
            Err(err) => Err(err),
        }
    }
}

impl<const LIMIT: usize> Serializer<List> for ListFmt<LIMIT> {
    fn serialize(&self, v: &List, obuf: &mut Vec<u8>) {
        let family = FixWith::<LIMIT, ExprListRecBody, FmtType>(ExprListRecBody, FmtType::LIST);
        let family_v = Value::List { list: v.clone() };
        family.serialize(&family_v, obuf);

    }
}

impl<const LIMIT: usize> Prepare<List> for ListFmt<LIMIT> {
    fn prepare(&self, v: &List) -> Result<usize, PreSerializeError> {
        let family = FixWith::<LIMIT, ExprListRecBody, FmtType>(ExprListRecBody, FmtType::LIST);
        let family_v = Value::List { list: v.clone() };
        let checked = family.prepare(&family_v);
        checked
    }
}

} // verus!
#[test]
fn mutual_list_exec_roundtrip() {
    let fmt = ListFmt::<16>;

    let v = List::Cons(Box::new(Expr::Num(1)), Box::new(List::Nil));
    let input: &[u8] = &[0x21, 0x10, 0x01, 0x20];

    let parsed = fmt.parse(&input);
    assert!(matches!(
        parsed,
        Ok((4, List::Cons(head, tail)))
            if *head == Expr::Num(1) && *tail == List::Nil
    ));

    let prepared = fmt.prepare(&v);
    assert!(matches!(prepared, Ok(4)));

    let mut obuf = Vec::with_capacity(prepared.unwrap());
    fmt.serialize(&v, &mut obuf);
    assert_eq!(obuf.as_slice(), input);
}

#[test]
fn mutual_group_exec_roundtrip() {
    let expr_fmt = ExprFmt::<16>;

    let list = List::Cons(Box::new(Expr::Num(1)), Box::new(List::Nil));
    let v = Expr::Group(Box::new(list));
    let input: &[u8] = &[0x11, 0x21, 0x10, 0x01, 0x20];

    let parsed = expr_fmt.parse(&input);
    assert!(matches!(
        parsed,
        Ok((5, Expr::Group(list)))
            if matches!(
                list.as_ref(),
                List::Cons(head, tail) if **head == Expr::Num(1) && **tail == List::Nil
            )
    ));

    let prepared = expr_fmt.prepare(&v);
    assert!(matches!(prepared, Ok(5)));

    let mut obuf = Vec::with_capacity(prepared.unwrap());
    expr_fmt.serialize(&v, &mut obuf);
    assert_eq!(obuf.as_slice(), input);
}

#[test]
fn mutual_recursion_limit() {
    fn deep_group(depth: usize) -> Expr {
        let mut list = List::Nil;
        for _ in 0..depth {
            list = List::Cons(Box::new(Expr::Num(1)), Box::new(list));
        }
        Expr::Group(Box::new(list))
    }

    let expr_fmt = ExprFmt::<3>;
    let too_deep = deep_group(5);
    let prepared = expr_fmt.prepare(&too_deep);
    assert!(matches!(
        prepared,
        Err(PreSerializeError::NotCompliant(
            ComplianceErrorKind::RecursionLimitExceeded
        ))
    ));
}
