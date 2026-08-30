//! Adapter for serializing a value through a shared reference.
//!
//! `Ref<F>` has exactly the same specification and parsing behavior as `F`,
//! but its executable serializer, preparation, and length APIs accept `&T`
//! whenever `F` accepts `T`. This is useful for nominal-value mappers which
//! reverse-map a struct into a tuple of references to its fields.
use crate::core::exec::output::OutputBuf;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

#[derive(Copy)]
pub struct Ref<Inner>(pub Inner);

impl<Inner: Clone> Clone for Ref<Inner> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Inner::clone, (&self.0,), cloned.0),
    {
        Ref(self.0.clone())
    }
}

impl<Inner: SpecParser> SpecParser for Ref<Inner> {
    type PVal = Inner::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.0.spec_parse(ibuf)
    }
}

impl<Inner: Consistency> Consistency for Ref<Inner> {
    type Val = Inner::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0.consistent(v)
    }
}

impl<Inner: SpecSerializerDps> SpecSerializerDps for Ref<Inner> {
    type SValue = Inner::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        self.0.spec_serialize_dps(v, obuf)
    }
}

impl<Inner: SpecSerializer> SpecSerializer for Ref<Inner> {
    type SVal = Inner::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.0.spec_serialize(v)
    }
}

impl<Inner: SpecByteLen> SpecByteLen for Ref<Inner> {
    type T = Inner::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.0.byte_len(v)
    }
}

impl<Inner: SafeParser> SafeParser for Ref<Inner> {
    open spec fn safe_inv(&self) -> bool {
        self.0.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
    }
}

impl<Inner: Productive> Productive for Ref<Inner> {
    open spec fn productive_inv(&self) -> bool {
        self.0.productive_inv()
    }

    proof fn lemma_productive(&self, ibuf: Seq<u8>) {
        self.0.lemma_productive(ibuf);
    }
}

impl<Inner: SoundParser> SoundParser for Ref<Inner> {
    open spec fn sound_inv(&self) -> bool {
        self.0.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
    }
}

impl<Inner: NonTailFmt> NonTailFmt for Ref<Inner> {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.0.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.0.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.0.lemma_serialize_dps_len(v, obuf);
    }
}

impl<Inner: GoodSerializer> GoodSerializer for Ref<Inner> {
    open spec fn serialize_inv(&self) -> bool {
        self.0.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.0.lemma_serialize_len(v);
    }
}

impl<Inner: SPRoundTripDps> SPRoundTripDps for Ref<Inner> {
    open spec fn unambiguous(&self) -> bool {
        self.0.unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.0.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<Inner: NonMalleable> NonMalleable for Ref<Inner> {
    open spec fn nonmal_inv(&self) -> bool {
        self.0.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner: NoLookAhead> NoLookAhead for Ref<Inner> {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.0.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        self.0.lemma_no_lookahead(i1, i2);
    }
}

impl<Inner: EquivSerializersGeneral> EquivSerializersGeneral for Ref<Inner> {
    open spec fn equiv_general_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.0.lemma_serialize_equiv(v, obuf);
    }
}

impl<Inner: EquivSerializers> EquivSerializers for Ref<Inner> {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.0.lemma_serialize_equiv_on_empty(v);
    }
}

impl<I, Inner> Parser<I> for Ref<Inner> where I: View<V = Seq<u8>>, Inner: Parser<I> {
    type PT = Inner::PT;

    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        self.0.parse(ibuf)
    }
}

impl<Output, Inner, T> Serializer<Output, &T> for Ref<Inner> where
    Output: OutputBuf,
    T: DeepView + ?Sized,
    Inner: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &&T, obuf: &mut Output) {
        self.0.serialize_into(*v, obuf);
    }
}

impl<Inner, T> Prepare<&T> for Ref<Inner> where T: DeepView + ?Sized, Inner: Prepare<T> {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, v: &&T) -> Result<usize, PreSerializeError> {
        self.0.prepare(*v)
    }
}

impl<Inner, T> ByteLen<&T> for Ref<Inner> where T: DeepView + ?Sized, Inner: ByteLen<T> {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &&T) -> usize {
        self.0.length(*v)
    }
}

} // verus!
