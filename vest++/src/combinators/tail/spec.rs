use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl SpecParser for super::Tail {
    type PVal = Seq<u8>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Some((ibuf.len() as int, ibuf))
    }
}

impl GoodParser for super::Tail {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Tail {
    type ST = Seq<u8>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        v
    }
}

impl SpecSerializer for super::Tail {
    type SVal = Seq<u8>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        v
    }
}

impl Unambiguity for super::Tail {

}

impl SpecByteLen for super::Tail {
    type T = Seq<u8>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        v.len()
    }
}

impl GoodSerializer for super::Tail {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
    }
}

impl SpecParser for super::Eof {
    type PVal = ();

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if ibuf.len() == 0 {
            Some((0, ()))
        } else {
            None
        }
    }
}

impl GoodParser for super::Eof {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Eof {
    type ST = ();

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Seq::empty()
    }
}

impl Unambiguity for super::Eof {

}

impl SpecSerializer for super::Eof {
    type SVal = ();

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Seq::empty()
    }
}

impl SpecByteLen for super::Eof {
    type T = ();

    open spec fn byte_len(&self, v: Self::T) -> nat {
        v.blen()
    }
}

impl GoodSerializer for super::Eof {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
    }
}

} // verus!
