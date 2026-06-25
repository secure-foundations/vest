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

pub type ValueSpec = Value;

impl DeepView for Value {
    type V = ValueSpec;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

pub enum ValueRef<'a> {
    Expr { expr: &'a Expr },
    List { list: &'a List },
}

impl DeepView for ValueRef<'_> {
    type V = ValueSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ValueRef::Expr { expr } => ValueSpec::Expr { expr: expr.deep_view() },
            ValueRef::List { list } => ValueSpec::List { list: list.deep_view() },
        }
    }
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

pub type ExprProj<Rec> = Mapped<
    Refined<Rec, PredFnSpec<ValueSpec>>,
    FnSpecMapper<ValueSpec, ExprSpec>,
>;

pub type ListProj<Rec> = Mapped<
    Refined<Rec, PredFnSpec<ValueSpec>>,
    FnSpecMapper<ValueSpec, ListSpec>,
>;

pub open spec fn expr_proj<Rec>(rec: Rec) -> ExprProj<Rec> where
    Rec: SpecCombinator<T = ValueSpec>,
 {
    Mapped {
        inner: Refined(rec, |v: ValueSpec| v is Expr),
        mapper: (
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
        mapper: (
            |v: ValueSpec| -> ListSpec { v->list },
            |list: ListSpec| -> ValueSpec { ValueSpec::List { list } },
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

    type T = ValueSpec;

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

    type T = ValueSpec;

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

    type T = ValueSpec;

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

// ============================================================
// Executable Implementations
// ============================================================
mod slow_exec_impl {
    use super::*;

    impl<'i> ParserRecBody<&'i [u8]> for ExprListRecBody {
        type EP = WhichFmt;

        type O = Value;

        fn parse_body<Exec>(
            &self,
            which: &WhichFmt,
            Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
            exec_rec: Exec,
            ibuf: &&'i [u8],
        ) -> PResult<Self::O> where Exec: Fn(&WhichFmt, &&'i [u8]) -> PResult<Self::O> {
            broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

            let _ = ibuf.len();

            match which {
                WhichFmt::EXPR => {
                    let (n1, tag) = U8.parse(ibuf)?;
                    let rest = ibuf.skip(n1);
                    match tag {
                        0x10u8 => {
                            let (n2, n) = U8.parse(&rest)?;
                            Ok((n1 + n2, Value::Expr { expr: Expr::Num(n) }))
                        },
                        0x11u8 => {
                            let (n2, inner) = exec_rec(&WhichFmt::LIST, &rest)?;
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
                WhichFmt::LIST => {
                    let (n1, tag) = U8.parse(ibuf)?;
                    let rest = ibuf.skip(n1);
                    match tag {
                        0x20u8 => Ok((n1, Value::List { list: List::Nil })),
                        0x21u8 => {
                            let (n2, head_val) = exec_rec(&WhichFmt::EXPR, &rest)?;
                            let rest2 = rest.skip(n2);
                            let (n3, tail_val) = exec_rec(&WhichFmt::LIST, &rest2)?;
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

    impl<'a> SerializerRecBody<ValueRef<'a>> for ExprListRecBody {
        type EP = WhichFmt;

        fn serialize_body<Exec>(
            &self,
            which: &WhichFmt,
            Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
            exec_rec: Exec,
            v: &ValueRef<'a>,
            obuf: &mut Vec<u8>,
        ) where Exec: Fn(&WhichFmt, &ValueRef<'a>, &mut Vec<u8>) {
            match v {
                ValueRef::Expr { expr: Expr::Num(n) } => {
                    U8.serialize(&0x10u8, obuf);
                    U8.serialize(n, obuf);
                },
                ValueRef::Expr { expr: Expr::Group(list) } => {
                    U8.serialize(&0x11u8, obuf);
                    let child = ValueRef::List { list };
                    exec_rec(&WhichFmt::LIST, &child, obuf);
                },
                ValueRef::List { list: List::Nil } => {
                    U8.serialize(&0x20u8, obuf);
                },
                ValueRef::List { list: List::Cons(head, tail) } => {
                    U8.serialize(&0x21u8, obuf);
                    let head_child = ValueRef::Expr { expr: head };
                    let tail_child = ValueRef::List { list: tail };
                    exec_rec(&WhichFmt::EXPR, &head_child, obuf);
                    exec_rec(&WhichFmt::LIST, &tail_child, obuf);
                },
            }
        }
    }

    impl<'a> PrepareRecBody<ValueRef<'a>> for ExprListRecBody {
        type EP = WhichFmt;

        fn prepare_body<Exec>(
            &self,
            which: &WhichFmt,
            Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
            exec_rec: Exec,
            v: &ValueRef<'a>,
        ) -> Result<usize, PreSerializeError> where
            Exec: Fn(&WhichFmt, &ValueRef<'a>) -> Result<usize, PreSerializeError>,
         {
            match (which, v) {
                (WhichFmt::EXPR, ValueRef::Expr { expr: Expr::Num(n) }) => {
                    let l1 = U8.prepare(&0x10u8)?;
                    let l2 = U8.prepare(n)?;
                    let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                    Ok(total)
                },
                (WhichFmt::EXPR, ValueRef::Expr { expr: Expr::Group(list) }) => {
                    let l1 = U8.prepare(&0x11u8)?;
                    let child = ValueRef::List { list };
                    let l2 = exec_rec(&WhichFmt::LIST, &child)?;
                    let total = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                    Ok(total)
                },
                (WhichFmt::LIST, ValueRef::List { list: List::Nil }) => {
                    let total = U8.prepare(&0x20u8)?;
                    Ok(total)
                },
                (WhichFmt::LIST, ValueRef::List { list: List::Cons(head, tail) }) => {
                    let l1 = U8.prepare(&0x21u8)?;
                    let head_child = ValueRef::Expr { expr: head };
                    let tail_child = ValueRef::List { list: tail };
                    let l2 = exec_rec(&WhichFmt::EXPR, &head_child)?;
                    let l3 = exec_rec(&WhichFmt::LIST, &tail_child)?;
                    let sum1 = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                    let total = sum1.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
                    Ok(total)
                },
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

impl<const LIMIT: usize> ExprFmt<LIMIT> {
    fn parse_gas(&self, gas: usize, ibuf: &&[u8]) -> (r: PResult<Expr>)
        ensures
            parse_matches_spec(
                r,
                match FixWith::<LIMIT, ExprListRecBody, WhichFmt>::spec_parse_gas(
                    &ExprListRecBody,
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
            FixWith::<LIMIT, ExprListRecBody, WhichFmt>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                WhichFmt::EXPR,
                ValueSpec::Expr { expr: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                WhichFmt,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                WhichFmt::EXPR,
                ValueSpec::Expr { expr: v.deep_view() },
            ),
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
                &&& FixWith::<LIMIT, ExprListRecBody, WhichFmt>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    WhichFmt::EXPR,
                    ValueSpec::Expr { expr: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, WhichFmt>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    WhichFmt::EXPR,
                    ValueSpec::Expr { expr: v.deep_view() },
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
                match FixWith::<LIMIT, ExprListRecBody, WhichFmt>::spec_parse_gas(
                    &ExprListRecBody,
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
            FixWith::<LIMIT, ExprListRecBody, WhichFmt>::consistent_gas(
                &ExprListRecBody,
                gas as nat,
                WhichFmt::LIST,
                ValueSpec::List { list: v.deep_view() },
            ),
        ensures
            final(obuf)@ == old(obuf)@ + FixWith::<
                LIMIT,
                ExprListRecBody,
                WhichFmt,
            >::spec_serialize_gas(
                &ExprListRecBody,
                gas as nat,
                WhichFmt::LIST,
                ValueSpec::List { list: v.deep_view() },
            ),
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
                &&& FixWith::<LIMIT, ExprListRecBody, WhichFmt>::consistent_gas(
                    &ExprListRecBody,
                    gas as nat,
                    WhichFmt::LIST,
                    ValueSpec::List { list: v.deep_view() },
                )
                &&& len == FixWith::<LIMIT, ExprListRecBody, WhichFmt>::byte_len_gas(
                    &ExprListRecBody,
                    gas as nat,
                    WhichFmt::LIST,
                    ValueSpec::List { list: v.deep_view() },
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

// ============================================================
// Self-recursive byte list
// ============================================================
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

pub type ByteListBodyFmt<Rec> = Mapped<
    Choice<PrefixTagged<U8, Empty>, PrefixTagged<U8, Pair<U8, Rec>>>,
    BiMapper<Sum<(), (u8, ByteListSpec)>, ByteListSpec>,
>;

pub struct ByteListRecBody;

impl SpecRecBody for ByteListRecBody {
    type Param = ();

    type T = ByteListSpec;

    type Body = ByteListBodyFmt<BundledSpecs<Self::T>>;

    open spec fn spec_body(
        &self,
        _param: (),
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Choice(
                PrefixTagged(U8, 0x20u8, Empty),
                PrefixTagged(U8, 0x21u8, Pair(U8, rec(()))),
            ),
            mapper: BiMap(
                |i: Sum<(), (u8, ByteListSpec)>|
                    match i {
                        Sum::Inl(_) => ByteListSpec::Nil,
                        Sum::Inr((head, tail)) => ByteListSpec::Cons(head, Box::new(tail)),
                    },
                |byte_list: ByteListSpec|
                    match byte_list {
                        ByteListSpec::Nil => Sum::Inl(()),
                        ByteListSpec::Cons(head, tail) => Sum::Inr((head, *tail)),
                    },
            ),
        }
    }
}

impl<'i> ParserRecBody<&'i [u8]> for ByteListRecBody {
    type EP = ();

    type O = ByteList;

    fn parse_body<Exec>(
        &self,
        _param: &(),
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<Self::O> where Exec: Fn(&(), &&'i [u8]) -> PResult<Self::O> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = ibuf.len();
        let (n1, tag) = U8.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        match tag {
            0x20u8 => Ok((n1, ByteList::Nil)),
            0x21u8 => {
                let (n2, head) = U8.parse(&rest)?;
                let rest2 = rest.skip(n2);
                let (n3, tail) = exec_rec(&(), &rest2)?;
                Ok((n1 + n2 + n3, ByteList::Cons(head, Box::new(tail))))
            },
            _ => Err(ParseError::invalid_tag()),
        }
    }
}

impl SerializerRecBody<ByteList> for ByteListRecBody {
    type EP = ();

    fn serialize_body<Exec>(
        &self,
        _param: &(),
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &ByteList,
        obuf: &mut Vec<u8>,
    ) where Exec: Fn(&(), &ByteList, &mut Vec<u8>) {
        match v {
            ByteList::Nil => {
                U8.serialize(&0x20u8, obuf);
            },
            ByteList::Cons(head, tail) => {
                U8.serialize(&0x21u8, obuf);
                U8.serialize(head, obuf);
                exec_rec(&(), tail, obuf);
            },
        }
    }
}

impl PrepareRecBody<ByteList> for ByteListRecBody {
    type EP = ();

    fn prepare_body<Exec>(
        &self,
        _param: &(),
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &ByteList,
    ) -> Result<usize, PreSerializeError> where
        Exec: Fn(&(), &ByteList) -> Result<usize, PreSerializeError>,
     {
        match v {
            ByteList::Nil => U8.prepare(&0x20u8),
            ByteList::Cons(head, tail) => {
                let l1 = U8.prepare(&0x21u8)?;
                let l2 = U8.prepare(head)?;
                let l3 = exec_rec(&(), tail)?;
                let sum1 = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
                let total = sum1.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
                Ok(total)
            },
        }
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
        Err(PreSerializeError {
            kind: PreSerializeErrorKind::NotCompliant(ComplianceErrorKind::RecursionLimitExceeded),
            ..
        })
    ));
}

#[cfg(feature = "std")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HandRolledError {
    UnexpectedEof,
    InvalidTag,
    RecursionLimitExceeded,
}

#[cfg(feature = "std")]
pub const BENCH_RECURSION_LIMIT: usize = 512;

#[cfg(feature = "std")]
pub fn handrolled_parse_expr_checked(input: &[u8]) -> Result<(usize, Expr), HandRolledError> {
    handrolled_parse_expr_gas(BENCH_RECURSION_LIMIT, input)
}

#[cfg(feature = "std")]
pub fn handrolled_parse_list_checked(input: &[u8]) -> Result<(usize, List), HandRolledError> {
    handrolled_parse_list_gas(BENCH_RECURSION_LIMIT, input)
}

#[cfg(feature = "std")]
pub fn handrolled_prepare_expr_checked(v: &Expr) -> Result<usize, HandRolledError> {
    handrolled_prepare_expr_gas(BENCH_RECURSION_LIMIT, v)
}

#[cfg(feature = "std")]
pub fn handrolled_prepare_list_checked(v: &List) -> Result<usize, HandRolledError> {
    handrolled_prepare_list_gas(BENCH_RECURSION_LIMIT, v)
}

#[cfg(feature = "std")]
pub fn handrolled_serialize_expr_checked(
    v: &Expr,
    obuf: &mut Vec<u8>,
) -> Result<(), HandRolledError> {
    handrolled_serialize_expr_gas(BENCH_RECURSION_LIMIT, v, obuf)
}

#[cfg(feature = "std")]
pub fn handrolled_serialize_list_checked(
    v: &List,
    obuf: &mut Vec<u8>,
) -> Result<(), HandRolledError> {
    handrolled_serialize_list_gas(BENCH_RECURSION_LIMIT, v, obuf)
}

#[cfg(feature = "std")]
fn handrolled_parse_expr_gas(gas: usize, input: &[u8]) -> Result<(usize, Expr), HandRolledError> {
    let Some((&tag, rest)) = input.split_first() else {
        return Err(HandRolledError::UnexpectedEof);
    };
    match tag {
        0x10 => {
            let Some((&n, _)) = rest.split_first() else {
                return Err(HandRolledError::UnexpectedEof);
            };
            Ok((2, Expr::Num(n)))
        }
        0x11 => {
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            let (n, list) = handrolled_parse_list_gas(gas - 1, rest)?;
            Ok((1 + n, Expr::Group(Box::new(list))))
        }
        _ => Err(HandRolledError::InvalidTag),
    }
}

#[cfg(feature = "std")]
fn handrolled_parse_list_gas(gas: usize, input: &[u8]) -> Result<(usize, List), HandRolledError> {
    let Some((&tag, rest)) = input.split_first() else {
        return Err(HandRolledError::UnexpectedEof);
    };
    match tag {
        0x20 => Ok((1, List::Nil)),
        0x21 => {
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            let (n_head, head) = handrolled_parse_expr_gas(gas - 1, rest)?;
            let (n_tail, tail) = handrolled_parse_list_gas(gas - 1, &rest[n_head..])?;
            Ok((
                1 + n_head + n_tail,
                List::Cons(Box::new(head), Box::new(tail)),
            ))
        }
        _ => Err(HandRolledError::InvalidTag),
    }
}

#[cfg(feature = "std")]
fn handrolled_prepare_expr_gas(gas: usize, v: &Expr) -> Result<usize, HandRolledError> {
    match v {
        Expr::Num(_) => Ok(2),
        Expr::Group(list) => {
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            Ok(1 + handrolled_prepare_list_gas(gas - 1, list)?)
        }
    }
}

#[cfg(feature = "std")]
fn handrolled_prepare_list_gas(gas: usize, v: &List) -> Result<usize, HandRolledError> {
    match v {
        List::Nil => Ok(1),
        List::Cons(head, tail) => {
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            let l_head = handrolled_prepare_expr_gas(gas - 1, head)?;
            let l_tail = handrolled_prepare_list_gas(gas - 1, tail)?;
            Ok(1 + l_head + l_tail)
        }
    }
}

#[cfg(feature = "std")]
fn handrolled_serialize_expr_gas(
    gas: usize,
    v: &Expr,
    obuf: &mut Vec<u8>,
) -> Result<(), HandRolledError> {
    match v {
        Expr::Num(n) => {
            obuf.push(0x10);
            obuf.push(*n);
        }
        Expr::Group(list) => {
            obuf.push(0x11);
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            handrolled_serialize_list_gas(gas - 1, list, obuf)?;
        }
    }
    Ok(())
}

#[cfg(feature = "std")]
fn handrolled_serialize_list_gas(
    gas: usize,
    v: &List,
    obuf: &mut Vec<u8>,
) -> Result<(), HandRolledError> {
    match v {
        List::Nil => {
            obuf.push(0x20);
        }
        List::Cons(head, tail) => {
            obuf.push(0x21);
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            handrolled_serialize_expr_gas(gas - 1, head, obuf)?;
            handrolled_serialize_list_gas(gas - 1, tail, obuf)?;
        }
    }
    Ok(())
}

#[cfg(feature = "std")]
fn bench_seed_byte(seed: usize) -> u8 {
    ((seed.wrapping_mul(29).wrapping_add(7)) % 251) as u8
}

#[cfg(feature = "std")]
pub fn bench_expr(seed: usize, depth: usize) -> Expr {
    if depth == 0 || seed % 3 == 0 {
        Expr::Num(bench_seed_byte(seed))
    } else {
        Expr::Group(Box::new(bench_list(seed ^ (depth * 17 + 3), depth - 1)))
    }
}

#[cfg(feature = "std")]
pub fn bench_list(seed: usize, depth: usize) -> List {
    if depth == 0 {
        return List::Nil;
    }

    let width = (seed % 4) + 1;
    let mut tail = List::Nil;
    for i in (0..width).rev() {
        let head = if (seed + i) % 2 == 0 {
            Expr::Num(bench_seed_byte(seed + i))
        } else if depth > 1 {
            Expr::Group(Box::new(bench_list(seed + i * 13 + 5, depth - 1)))
        } else {
            Expr::Num(bench_seed_byte(seed + i * 13 + 5))
        };
        tail = List::Cons(Box::new(head), Box::new(tail));
    }
    tail
}

#[cfg(feature = "std")]
pub fn benchmark_expr_values() -> Vec<Expr> {
    let mut values = Vec::new();
    for seed in 0..96usize {
        let depth = (seed % 6) + 2;
        values.push(bench_expr(seed, depth));
    }
    values
}

#[cfg(feature = "std")]
pub fn benchmark_list_values() -> Vec<List> {
    let mut values = Vec::new();
    for seed in 0..96usize {
        let depth = (seed % 6) + 2;
        values.push(bench_list(seed * 5 + 1, depth));
    }
    values
}

#[cfg(feature = "std")]
pub fn handrolled_parse_byte_list_checked(
    input: &[u8],
) -> Result<(usize, ByteList), HandRolledError> {
    handrolled_parse_byte_list_gas(BENCH_RECURSION_LIMIT, input)
}

#[cfg(feature = "std")]
pub fn handrolled_prepare_byte_list_checked(v: &ByteList) -> Result<usize, HandRolledError> {
    handrolled_prepare_byte_list_gas(BENCH_RECURSION_LIMIT, v)
}

#[cfg(feature = "std")]
pub fn handrolled_serialize_byte_list_checked(
    v: &ByteList,
    obuf: &mut Vec<u8>,
) -> Result<(), HandRolledError> {
    handrolled_serialize_byte_list_gas(BENCH_RECURSION_LIMIT, v, obuf)
}

#[cfg(feature = "std")]
fn handrolled_parse_byte_list_gas(
    gas: usize,
    input: &[u8],
) -> Result<(usize, ByteList), HandRolledError> {
    let Some((&tag, rest)) = input.split_first() else {
        return Err(HandRolledError::UnexpectedEof);
    };
    match tag {
        0x20 => Ok((1, ByteList::Nil)),
        0x21 => {
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            let Some((&head, rest2)) = rest.split_first() else {
                return Err(HandRolledError::UnexpectedEof);
            };
            let (n_tail, tail) = handrolled_parse_byte_list_gas(gas - 1, rest2)?;
            Ok((2 + n_tail, ByteList::Cons(head, Box::new(tail))))
        }
        _ => Err(HandRolledError::InvalidTag),
    }
}

#[cfg(feature = "std")]
fn handrolled_prepare_byte_list_gas(gas: usize, v: &ByteList) -> Result<usize, HandRolledError> {
    match v {
        ByteList::Nil => Ok(1),
        ByteList::Cons(_, tail) => {
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            Ok(2 + handrolled_prepare_byte_list_gas(gas - 1, tail)?)
        }
    }
}

#[cfg(feature = "std")]
fn handrolled_serialize_byte_list_gas(
    gas: usize,
    v: &ByteList,
    obuf: &mut Vec<u8>,
) -> Result<(), HandRolledError> {
    match v {
        ByteList::Nil => {
            obuf.push(0x20);
        }
        ByteList::Cons(head, tail) => {
            if gas == 0 {
                return Err(HandRolledError::RecursionLimitExceeded);
            }
            obuf.push(0x21);
            obuf.push(*head);
            handrolled_serialize_byte_list_gas(gas - 1, tail, obuf)?;
        }
    }
    Ok(())
}

#[cfg(feature = "std")]
pub fn bench_byte_list(seed: usize, depth: usize) -> ByteList {
    let mut value = ByteList::Nil;
    for i in (0..depth).rev() {
        value = ByteList::Cons(bench_seed_byte(seed + i * 11 + 3), Box::new(value));
    }
    value
}

#[cfg(feature = "std")]
pub fn benchmark_byte_list_values() -> Vec<ByteList> {
    let mut values = Vec::new();
    for seed in 0..96usize {
        let depth = (seed % 12) + 1;
        values.push(bench_byte_list(seed * 7 + 2, depth));
    }
    values
}
