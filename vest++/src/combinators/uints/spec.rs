use crate::combinators::mapped::spec::{IsoMapper, Mapper};
use crate::combinators::{Fixed, Mapped};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub struct U16LeMapper;

impl Mapper for U16LeMapper {
    type In = [u8; 2];

    type Out = u16;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        (i[0] as u16) | (i[1] as u16) << 8
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        [(o & 0xff) as u8, ((o >> 8) & 0xff) as u8]
    }
}

impl IsoMapper for U16LeMapper {
    proof fn lemma_map_wf(&self, v: Self::In) {
        if v.wf() {
            assert(self.spec_map(v).wf());
        }
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
        if v.wf() {
            assert(self.spec_map_rev(v).wf());
        }
    }

    proof fn lemma_map_iso(&self, i: Self::In) {
        let x = self.spec_map(i);
        let i0 = i[0] as u16;
        let i1 = i[1] as u16;
        assert(((x == i0 | i1 << 8) && (i0 < 256) && (i1 < 256)) ==> i0 == (x & 0xff) && i1 == ((x
            >> 8) & 0xff)) by (bit_vector);
        assert(self.spec_map_rev(self.spec_map(i)) == i);
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
        assert({
            &&& o & 0xff < 256
            &&& (o >> 8) & 0xff < 256
        }) by (bit_vector);
        assert(o == ((o & 0xff) | ((o >> 8) & 0xff) << 8)) by (bit_vector);
    }
}

pub struct U16BeMapper;

impl Mapper for U16BeMapper {
    type In = [u8; 2];

    type Out = u16;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        (i[0] as u16) << 8 | (i[1] as u16)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        [((o >> 8) & 0xff) as u8, (o & 0xff) as u8]
    }
}

impl IsoMapper for U16BeMapper {
    proof fn lemma_map_wf(&self, v: Self::In) {
        if v.wf() {
            assert(self.spec_map(v).wf());
        }
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
        if v.wf() {
            assert(self.spec_map_rev(v).wf());
        }
    }

    proof fn lemma_map_iso(&self, i: Self::In) {
        let x = self.spec_map(i);
        let i0 = i[0] as u16;
        let i1 = i[1] as u16;
        assert(((x == i0 << 8 | i1) && (i0 < 256) && (i1 < 256)) ==> i0 == ((x >> 8) & 0xff) && i1
            == (x & 0xff)) by (bit_vector);
        assert(self.spec_map_rev(self.spec_map(i)) == i);
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
        assert({
            &&& o & 0xff < 256
            &&& (o >> 8) & 0xff < 256
        }) by (bit_vector);
        assert(o == (((o >> 8) & 0xff) << 8 | (o & 0xff))) by (bit_vector);
    }
}

impl SpecParser for super::U8 {
    type PVal = u8;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u8)> {
        if ibuf.len() >= 1 {
            Some((1, ibuf[0]))
        } else {
            None
        }
    }
}

impl SpecSerializerDps for super::U8 {
    type ST = u8;

    open spec fn spec_serialize_dps(&self, v: u8, obuf: Seq<u8>) -> Seq<u8> {
        seq![v] + obuf
    }
}

impl SpecSerializer for super::U8 {
    type SVal = u8;

    open spec fn spec_serialize(&self, v: u8) -> Seq<u8> {
        seq![v]
    }
}

impl GoodParser for super::U8 {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

impl Serializability for super::U8 {
    open spec fn serializable(&self, v: u8, obuf: Seq<u8>) -> bool {
        true
    }
}

impl Unambiguity for super::U8 {
    open spec fn unambiguous(&self) -> bool {
        true
    }
}

impl GoodSerializerDps for super::U8 {
    proof fn lemma_serialize_dps_buf(&self, v: u8, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == seq![v] + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u8, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf).len() - obuf.len() == v.blen());
    }
}

impl GoodSerializer for super::U8 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        assert(self.spec_serialize(v).len() == v.blen());
    }
}

impl SpecByteLen for super::U8 {
    type T = u8;
}

impl SpecParser for super::U16Le {
    type PVal = u16;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u16)> {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.spec_parse(ibuf)
    }
}

impl SpecSerializerDps for super::U16Le {
    type ST = u16;

    open spec fn spec_serialize_dps(&self, v: u16, obuf: Seq<u8>) -> Seq<u8> {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U16Le {
    type SVal = u16;

    open spec fn spec_serialize(&self, v: u16) -> Seq<u8> {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.spec_serialize(v)
    }
}

impl GoodParser for super::U16Le {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_parse_wf(ibuf);
    }
}

impl Serializability for super::U16Le {
    open spec fn serializable(&self, v: u16, obuf: Seq<u8>) -> bool {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.serializable(v, obuf)
    }
}

impl Unambiguity for super::U16Le {
    open spec fn unambiguous(&self) -> bool {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.unambiguous()
    }
}

impl GoodSerializerDps for super::U16Le {
    proof fn lemma_serialize_dps_buf(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_dps_buf(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U16Le {
    proof fn lemma_serialize_len(&self, v: u16) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::U16Le {
    type T = u16;
}

impl SpecParser for super::U16Be {
    type PVal = u16;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, u16)> {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.spec_parse(ibuf)
    }
}

impl SpecSerializerDps for super::U16Be {
    type ST = u16;

    open spec fn spec_serialize_dps(&self, v: u16, obuf: Seq<u8>) -> Seq<u8> {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.spec_serialize_dps(v, obuf)
    }
}

impl SpecSerializer for super::U16Be {
    type SVal = u16;

    open spec fn spec_serialize(&self, v: u16) -> Seq<u8> {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.spec_serialize(v)
    }
}

impl GoodParser for super::U16Be {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_parse_wf(ibuf);
    }
}

impl Serializability for super::U16Be {
    open spec fn serializable(&self, v: u16, obuf: Seq<u8>) -> bool {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.serializable(v, obuf)
    }
}

impl Unambiguity for super::U16Be {
    open spec fn unambiguous(&self) -> bool {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.unambiguous()
    }
}

impl GoodSerializerDps for super::U16Be {
    proof fn lemma_serialize_dps_buf(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_dps_buf(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_dps_len(v, obuf);
    }
}

impl GoodSerializer for super::U16Be {
    proof fn lemma_serialize_len(&self, v: u16) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_len(v);
    }
}

impl SpecByteLen for super::U16Be {
    type T = u16;
}

} // verus!
