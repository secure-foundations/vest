use crate::core::{proof::*, spec::*};
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

/// The sum type.
pub enum Sum<A, B> {
    /// Left injection.
    Inl(A),
    /// Right injection.
    Inr(B),
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Choice<A, B> {
    type PVal = Sum<A::PVal, B::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n, va)) => Some((n, Sum::Inl(va))),
            None => match self.1.spec_parse(ibuf) {
                Some((n, vb)) => Some((n, Sum::Inr(vb))),
                None => None,
            },
        }
    }
}

impl<A: Consistency, B: Consistency> Consistency for super::Choice<A, B> {
    type Val = Sum<A::Val, B::Val>;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        match v {
            Sum::Inl(va) => self.0.consistent(va),
            Sum::Inr(vb) => self.1.consistent(vb),
        }
    }
}

impl<A: SoundParser, B: SoundParser> SoundParser for super::Choice<A, B> {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
        self.1.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        self.1.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        self.1.lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> SpecSerializerDps for super::Choice<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type ST = Sum<A::ST, B::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            Sum::Inl(va) => self.0.spec_serialize_dps(va, obuf),
            Sum::Inr(vb) => self.1.spec_serialize_dps(vb, obuf),
        }
    }
}

impl<A, B> SpecSerializer for super::Choice<A, B> where A: SpecSerializer, B: SpecSerializer {
    type SVal = Sum<A::SVal, B::SVal>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        match v {
            Sum::Inl(va) => self.0.spec_serialize(va),
            Sum::Inr(vb) => self.1.spec_serialize(vb),
        }
    }
}

impl<A: Unambiguity, B: Unambiguity> Unambiguity for super::Choice<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }
}

impl<A, B> NonTailFmt for super::Choice<A, B> where A: NonTailFmt, B: NonTailFmt {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            Sum::Inl(va) => {
                self.0.lemma_serialize_dps_prepend(va, obuf);
            },
            Sum::Inr(vb) => {
                self.1.lemma_serialize_dps_prepend(vb, obuf);
            },
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            Sum::Inl(va) => {
                self.0.lemma_serialize_dps_len(va, obuf);
            },
            Sum::Inr(vb) => {
                self.1.lemma_serialize_dps_len(vb, obuf);
            },
        }
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Choice<A, B> {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.1.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        match v {
            Sum::Inl(va) => {
                self.0.lemma_serialize_len(va);
            },
            Sum::Inr(vb) => {
                self.1.lemma_serialize_len(vb);
            },
        }
    }
}

impl<A, B> SpecByteLen for super::Choice<A, B> where A: SpecByteLen, B: SpecByteLen {
    type T = Sum<A::T, B::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        match v {
            Sum::Inl(va) => self.0.byte_len(va),
            Sum::Inr(vb) => self.1.byte_len(vb),
        }
    }
}

impl<A: SpecParser, B: SpecParser<PVal = A::PVal>> SpecParser for super::Alt<A, B> {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if let None = self.0.spec_parse(ibuf) {
            self.1.spec_parse(ibuf)
        } else {
            self.0.spec_parse(ibuf)
        }
    }
}

impl<A: Consistency, B: Consistency<Val = A::Val>> Consistency for super::Alt<A, B> {
    type Val = A::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0.consistent(v) || self.1.consistent(v)
    }
}

impl<A: Consistency, B: Consistency<Val = A::Val>> super::Alt<A, B> {
    /// If exactly one branch accepts `v`, this returns that branch.
    /// If both accept `v`, the choice is unspecified.
    pub open spec fn choose_left(&self, v: A::Val) -> bool {
        if self.0.consistent(v) && self.1.consistent(v) {
            arbitrary()
        } else if self.0.consistent(v) {
            true
        } else {
            false
        }
    }
}

impl<A, B> SoundParser for super::Alt<A, B> where A: SoundParser, B: SoundParser<T = A::T> {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
        &&& disjoint_values(self.0, self.1)
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
        self.1.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        self.1.lemma_parse_sound_consumption(ibuf);
        self.0.lemma_parse_sound_value(ibuf);
        self.1.lemma_parse_sound_value(ibuf);
        if let Some((n, v)) = self.0.spec_parse(ibuf) {
            assert(disjoint_values(self.0, self.1));
            assert(self.choose_left(v));
            assert(n == self.byte_len(v));
        } else if let Some((n, v)) = self.1.spec_parse(ibuf) {
            assert(self.1.consistent(v));
            assert(disjoint_values(self.0, self.1));
            assert(!self.choose_left(v));
            assert(self.byte_len(v) == self.1.byte_len(v));
            assert(n == self.1.byte_len(v));
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        self.1.lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> SpecSerializerDps for super::Alt<A, B> where
    A: SpecSerializerDps + Consistency<Val = A::ST>,
    B: SpecSerializerDps<ST = A::ST> + Consistency<Val = B::ST>,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        if self.choose_left(v) {
            self.0.spec_serialize_dps(v, obuf)
        } else {
            self.1.spec_serialize_dps(v, obuf)
        }
    }
}

impl<A: Unambiguity, B: Unambiguity<PVal = A::PVal>> Unambiguity for super::Alt<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }
}

impl<A, B> NonTailFmt for super::Alt<A, B> where
    A: NonTailFmt + Consistency<Val = A::ST>,
    B: NonTailFmt<T = A::T> + Consistency<Val = B::ST>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        if self.choose_left(v) {
            self.0.lemma_serialize_dps_prepend(v, obuf)
        } else {
            self.1.lemma_serialize_dps_prepend(v, obuf)
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        if self.choose_left(v) {
            self.0.lemma_serialize_dps_len(v, obuf)
        } else {
            self.1.lemma_serialize_dps_len(v, obuf)
        }
    }
}

impl<A, B> SpecSerializer for super::Alt<A, B> where
    A: SpecSerializer + Consistency<Val = A::SVal>,
    B: SpecSerializer<SVal = A::SVal> + Consistency<Val = B::SVal>,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        if self.choose_left(v) {
            self.0.spec_serialize(v)
        } else {
            self.1.spec_serialize(v)
        }
    }
}

impl<A, B> GoodSerializer for super::Alt<A, B> where
    A: GoodSerializer + Consistency<Val = A::SVal>,
    B: GoodSerializer<T = A::T> + Consistency<Val = B::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.1.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        if self.choose_left(v) {
            self.0.lemma_serialize_len(v)
        } else {
            self.1.lemma_serialize_len(v)
        }
    }
}

impl<A, B> SpecByteLen for super::Alt<A, B> where
    A: SpecByteLen + Consistency<Val = A::T>,
    B: SpecByteLen<T = A::T> + Consistency<Val = B::T>,
 {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        if self.choose_left(v) {
            self.0.byte_len(v)
        } else {
            self.1.byte_len(v)
        }
    }
}

pub open spec fn branch_exists<T, C>(tag: T, branches: Seq<(T, C)>) -> bool {
    exists|i: nat| i < branches.len() && #[trigger] branches[i as int].0 == tag
}

pub open spec fn unique_branch_match<T, C>(tag: T, branches: Seq<(T, C)>) -> bool {
    forall|i: nat, j: nat|
        i < branches.len() && #[trigger] branches[i as int].0 == tag && j < branches.len()
            && #[trigger] branches[j as int].0 == tag ==> i == j
}

pub open spec fn tag_position<T, C>(tag: T, branches: Seq<(T, C)>) -> nat
    recommends
        branch_exists(tag, branches),
{
    choose|i: nat| i < branches.len() && #[trigger] branches[i as int].0 == tag
}

impl<T, C, const N: usize> super::Dispatch<T, C, N> {
    pub open spec fn has_active_branch(&self) -> bool {
        branch_exists(self.0, self.1@)
    }

    pub open spec fn active_branch(&self) -> C
        recommends
            self.has_active_branch(),
    {
        self.1[tag_position(self.0, self.1@) as int].1
    }

    pub proof fn lemma_active_branch_is(&self, idx: nat)
        requires
            idx < self.1@.len(),
            self.1[idx as int].0 == self.0,
            unique_branch_match(self.0, self.1@),
        ensures
            self.has_active_branch(),
            self.active_branch() == self.1[idx as int].1,
    {
    }
}

impl<T, C: SpecParser, const N: usize> SpecParser for super::Dispatch<T, C, N> {
    type PVal = C::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if self.has_active_branch() {
            self.active_branch().spec_parse(ibuf)
        } else {
            None
        }
    }
}

impl<T, C: Consistency, const N: usize> Consistency for super::Dispatch<T, C, N> {
    type Val = C::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.has_active_branch()
        &&& self.active_branch().consistent(v)
    }
}

impl<T, C: SoundParser, const N: usize> SoundParser for super::Dispatch<T, C, N> {
    open spec fn sound_inv(&self) -> bool {
        self.active_branch().sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        if self.has_active_branch() {
            self.active_branch().lemma_parse_safe(ibuf);
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        if self.has_active_branch() {
            self.active_branch().lemma_parse_sound_consumption(ibuf);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        if self.has_active_branch() {
            self.active_branch().lemma_parse_sound_value(ibuf);
        }
    }
}

impl<T, C: SpecSerializerDps, const N: usize> SpecSerializerDps for super::Dispatch<T, C, N> {
    type ST = C::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.active_branch().spec_serialize_dps(v, obuf)
    }
}

impl<T, C: SpecSerializer, const N: usize> SpecSerializer for super::Dispatch<T, C, N> {
    type SVal = C::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.active_branch().spec_serialize(v)
    }
}

impl<T, C: Unambiguity, const N: usize> Unambiguity for super::Dispatch<T, C, N> {
    open spec fn unambiguous(&self) -> bool {
        &&& unique_branch_match(self.0, self.1@)
        &&& self.active_branch().unambiguous()
    }
}

impl<T, C: NonTailFmt, const N: usize> NonTailFmt for super::Dispatch<T, C, N> {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.active_branch().serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        self.active_branch().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.active_branch().lemma_serialize_dps_len(v, obuf);
    }
}

impl<T, C: GoodSerializer, const N: usize> GoodSerializer for super::Dispatch<T, C, N> {
    open spec fn serialize_inv(&self) -> bool {
        self.active_branch().serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.active_branch().lemma_serialize_len(v);
    }
}

impl<T, C: SpecByteLen, const N: usize> SpecByteLen for super::Dispatch<T, C, N> {
    type T = C::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.active_branch().byte_len(v)
    }
}

impl<T, C: StaticByteLen, const N: usize> StaticByteLen for super::Dispatch<T, C, N> {
    open spec fn static_byte_len() -> nat {
        C::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.active_branch().lemma_static_len_matches_byte_len(v);
    }
}

impl<A: SpecParser, B: SpecParser> SpecParser for Sum<A, B> {
    type PVal = Sum<A::PVal, B::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self {
            Sum::Inl(a) => {
                match a.spec_parse(ibuf) {
                    Some((n, va)) => Some((n, Sum::Inl(va))),
                    None => None,
                }
            },
            Sum::Inr(b) => {
                match b.spec_parse(ibuf) {
                    Some((n, vb)) => Some((n, Sum::Inr(vb))),
                    None => None,
                }
            },
        }
    }
}

impl<A: Consistency, B: Consistency> Consistency for Sum<A, B> {
    type Val = Sum<A::Val, B::Val>;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.consistent(va),
            (Sum::Inr(b), Sum::Inr(vb)) => b.consistent(vb),
            _ => false,
        }
    }
}

impl<A: SoundParser, B: SoundParser> SoundParser for Sum<A, B> {
    open spec fn sound_inv(&self) -> bool {
        match self {
            Sum::Inl(a) => a.sound_inv(),
            Sum::Inr(b) => b.sound_inv(),
        }
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        match self {
            Sum::Inl(a) => a.lemma_parse_safe(ibuf),
            Sum::Inr(b) => b.lemma_parse_safe(ibuf),
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        match self {
            Sum::Inl(a) => a.lemma_parse_sound_consumption(ibuf),
            Sum::Inr(b) => b.lemma_parse_sound_consumption(ibuf),
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        match self {
            Sum::Inl(a) => a.lemma_parse_sound_value(ibuf),
            Sum::Inr(b) => b.lemma_parse_sound_value(ibuf),
        }
    }
}

impl<A, B> SpecSerializerDps for Sum<A, B> where A: SpecSerializerDps, B: SpecSerializerDps {
    type ST = Sum<A::ST, B::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.spec_serialize_dps(va, obuf),
            (Sum::Inr(b), Sum::Inr(vb)) => b.spec_serialize_dps(vb, obuf),
            _ => obuf,
        }
    }
}

impl<A, B> SpecSerializer for Sum<A, B> where A: SpecSerializer, B: SpecSerializer {
    type SVal = Sum<A::SVal, B::SVal>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.spec_serialize(va),
            (Sum::Inr(b), Sum::Inr(vb)) => b.spec_serialize(vb),
            _ => Seq::empty(),
        }
    }
}

impl<A: Unambiguity, B: Unambiguity> Unambiguity for Sum<A, B> {
    open spec fn unambiguous(&self) -> bool {
        match self {
            Sum::Inl(a) => a.unambiguous(),
            Sum::Inr(b) => b.unambiguous(),
        }
    }
}

impl<A, B> NonTailFmt for Sum<A, B> where A: NonTailFmt, B: NonTailFmt {
    open spec fn serialize_dps_inv(&self) -> bool {
        match self {
            Sum::Inl(a) => a.serialize_dps_inv(),
            Sum::Inr(b) => b.serialize_dps_inv(),
        }
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.lemma_serialize_dps_prepend(va, obuf),
            (Sum::Inr(b), Sum::Inr(vb)) => b.lemma_serialize_dps_prepend(vb, obuf),
            _ => {
                assert(self.spec_serialize_dps(v, obuf) == Seq::<u8>::empty() + obuf);
            },
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.lemma_serialize_dps_len(va, obuf),
            (Sum::Inr(b), Sum::Inr(vb)) => b.lemma_serialize_dps_len(vb, obuf),
            _ => (),
        }
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for Sum<A, B> {
    open spec fn serialize_inv(&self) -> bool {
        match self {
            Sum::Inl(a) => a.serialize_inv(),
            Sum::Inr(b) => b.serialize_inv(),
        }
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.lemma_serialize_len(va),
            (Sum::Inr(b), Sum::Inr(vb)) => b.lemma_serialize_len(vb),
            _ => (),
        }
    }
}

impl<A, B> SpecByteLen for Sum<A, B> where A: SpecByteLen, B: SpecByteLen {
    type T = Sum<A::T, B::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.byte_len(va),
            (Sum::Inr(b), Sum::Inr(vb)) => b.byte_len(vb),
            _ => 0,
        }
    }
}

} // verus!
