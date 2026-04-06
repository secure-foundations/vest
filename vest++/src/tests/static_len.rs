use crate::asn1::{BerBool, DerBool};
use crate::combinators::mapped::spec::Mapper;
use crate::combinators::{
    Array, Cond, Dispatch, Empty, Eof, Mapped, Pair, Permute3, Permute4, Preceded, Refined, Tag,
    Tagged, Terminated, U16Le, U32Be, U32Le, U8,
};
use crate::core::spec::*;
use vstd::prelude::*;

verus! {

struct IdMapper<T>(core::marker::PhantomData<T>);

impl<T> Mapper for IdMapper<T> {
    type In = T;

    type Out = T;

    open spec fn spec_map(i: Self::In) -> Self::Out {
        i
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        o
    }
}

proof fn requires_static<C: StaticByteLen>(c: C) {
}

type PairFmt = Pair<U8, U16Le>;

type PrecededFmt = Preceded<U8, U16Le>;

type TerminatedFmt = Terminated<U16Le, U8>;

type TaggedFmt = Tagged<U8, U16Le>;

type DispatchFmt = Dispatch<u8, U16Le, 2>;

type ArrayFmt = Array<3, U8>;

type BoolFmt = crate::asn1::Bool<true>;

type NestedPairFmt = Mapped<Pair<Pair<U8, U16Le>, U32Be>, IdMapper<((u8, u16), u32)>>;

type TaggedDispatchFmt = Tagged<U8, Dispatch<u8, Pair<U8, U16Le>, 2>>;

type ArrayOfTaggedFmt = Array<5, Tagged<U8, U16Le>>;

type Permute3Fmt = Permute3<U8, DerBool, U32Le>;

type Permute4Fmt = Permute4<U8, U16Le, U32Be, BerBool>;

type ZeroWrappedFmt = Preceded<Empty, Terminated<U32Be, Eof>>;

proof fn test_static_byte_len_trait_surface() {
    requires_static(U8);
    requires_static(U16Le);
    requires_static(Pair(U8, U16Le));
    requires_static(Preceded(U8, U16Le));
    requires_static(Terminated(U16Le, U8));
    requires_static(Cond(true, U16Le));
    requires_static(Mapped { inner: U8, mapper: IdMapper(core::marker::PhantomData) });
    requires_static(Refined { inner: U8, pred: |b: u8| b <= 10u8 });
    requires_static(Tag { inner: U8, tag: 0x7fu8 });
    requires_static(Tagged(U8, 0xa1u8, U16Le));
    requires_static(Dispatch(0x01u8, [(0x01u8, U16Le), (0x02u8, U16Le)]));
    requires_static(Array::<3, _>(U8));
    requires_static(DerBool);
    requires_static(BerBool);
    requires_static(Pair(Pair(U8, U16Le), U32Be));
    requires_static(
        Tagged(
            U8,
            0x01u8,
            Dispatch(0x02u8, [(0x02u8, Pair(U8, U16Le)), (0x03u8, Pair(U8, U16Le))]),
        ),
    );
    requires_static(Array::<2, _>(Tagged(U8, 0xa0u8, U16Le)));
    requires_static(Permute3(U8, DerBool, U32Le));
    requires_static(Permute4(U8, U16Le, U32Be, BerBool));
    requires_static(Preceded(Empty, Terminated(U32Be, Eof)));
}

proof fn test_static_byte_len_values() {
    assert(PairFmt::static_byte_len() == 3);
    assert(PrecededFmt::static_byte_len() == 3);
    assert(TerminatedFmt::static_byte_len() == 3);
    assert(TaggedFmt::static_byte_len() == 3);
    assert(DispatchFmt::static_byte_len() == 2);
    assert(ArrayFmt::static_byte_len() == 3);
    assert(BoolFmt::static_byte_len() == 1);
    assert(NestedPairFmt::static_byte_len() == 7);
    assert(TaggedDispatchFmt::static_byte_len() == 4);
    assert(ArrayOfTaggedFmt::static_byte_len() == 15);
    assert(Permute3Fmt::static_byte_len() == 6);
    assert(Permute4Fmt::static_byte_len() == 8);
    assert(ZeroWrappedFmt::static_byte_len() == 4);
}

} // verus!
