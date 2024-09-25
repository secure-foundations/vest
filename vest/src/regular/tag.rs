use super::refined::{Pred, Refined, SpecPred};
use super::uints::FromToBytes;
use crate::properties::*;
use vstd::prelude::*;

verus! {

/// tag predicate that matches the input with a given value
pub struct TagPred<T>(pub T);

impl<T: View> View for TagPred<T> {
    type V = TagPred<T::V>;

    open spec fn view(&self) -> Self::V {
        TagPred(self.0@)
    }
}

impl<T> SpecPred for TagPred<T> {
    type Input = T;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        *i == self.0
    }
}

impl<T: FromToBytes> Pred for TagPred<T> {
    type Input<'a> = T;

    type InputOwned = T;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        self.0.eq(i)
    }
}

impl<const N: usize> Pred for TagPred<[u8; N]> {
    type Input<'b> = &'b [u8];

    type InputOwned = Vec<u8>;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        compare_slice(self.0.as_slice(), *i)
    }
}

impl<'a> Pred for TagPred<&'a [u8]> {
    type Input<'b> = &'b [u8];

    type InputOwned = Vec<u8>;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        compare_slice(self.0, *i)
    }
}

/// Generic tag combinator that matches the input with a given value and discards it
/// e.g. `Tag(Int::<u8>, 0)` matches the byte `0`; `Tag(Bytes::<3>, &[1, 2, 3])` matches the
/// bytes `[1, 2, 3]`
pub struct Tag<Inner, T>(pub Refined<Inner, TagPred<T>>);

impl<Inner, T> Tag<Inner, T> {
    /// Creates a new `Tag` combinator.
    pub fn new(inner: Inner, tag: T) -> (o: Self)
        ensures
            o == Tag(Refined { inner, predicate: TagPred(tag) }),
    {
        Tag(Refined { inner, predicate: TagPred(tag) })
    }

    /// Creates a new `Tag` combinator.
    pub open spec fn spec_new(inner: Inner, tag: T) -> Self {
        Tag(Refined { inner, predicate: TagPred(tag) })
    }
}

impl<Inner: View, T: View> View for Tag<Inner, T> {
    type V = Tag<Inner::V, T::V>;

    open spec fn view(&self) -> Self::V {
        Tag(self.0@)
    }
}

impl<Inner: SpecCombinator<SpecResult = T>, T> SpecCombinator for Tag<Inner, T> {
    type SpecResult = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if let Ok((n, _)) = self.0.spec_parse(s) {
            Ok((n, ()))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(self.0.predicate.0)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s);
    }
}

impl<Inner: SecureSpecCombinator<SpecResult = T>, T> SecureSpecCombinator for Tag<Inner, T> {
    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(self.0.predicate.0);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2);
        assert(Self::is_prefix_secure() ==> self.spec_parse(s1).is_ok() ==> self.spec_parse(
            s1.add(s2),
        ) == self.spec_parse(s1));
    }
}

impl<Inner, T> Combinator for Tag<Inner, T> where
    Inner: for <'a>Combinator<Result<'a> = T, Owned = T>,
    Inner::V: SecureSpecCombinator<SpecResult = T::V>, T: FromToBytes
 {
    type Result<'a> = ();

    type Owned = ();

    open spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> Result<(usize, Self::Result<'a>), ParseError> {
        let (n, _) = self.0.parse(s)?;
        Ok((n, ()))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> Result<
        usize,
        SerializeError,
    > {
        self.0.serialize(self.0.predicate.0, data, pos)
    }
}

impl<Inner, const N: usize> Combinator for Tag<Inner, [u8; N]> where
    Inner: for <'b>Combinator<Result<'b> = &'b [u8], Owned = Vec<u8>>,
    Inner::V: SecureSpecCombinator<SpecResult = Seq<u8>>
 {
    type Result<'b> = ();

    type Owned = ();

    open spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'b>(&self, s: &'b [u8]) -> Result<(usize, Self::Result<'b>), ParseError> {
        let (n, _) = self.0.parse(s)?;
        Ok((n, ()))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> Result<
        usize,
        SerializeError,
    > {
        self.0.serialize(self.0.predicate.0.as_slice(), data, pos)
    }
}

impl<Inner, 'a> Combinator for Tag<Inner, &'a [u8]> where
    Inner: for <'b>Combinator<Result<'b> = &'b [u8], Owned = Vec<u8>>,
    Inner::V: SecureSpecCombinator<SpecResult = Seq<u8>>
 {
    type Result<'b> = ();

    type Owned = ();

    open spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'b>(&self, s: &'b [u8]) -> Result<(usize, Self::Result<'b>), ParseError> {
        let (n, _) = self.0.parse(s)?;
        Ok((n, ()))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> Result<
        usize,
        SerializeError,
    > {
        self.0.serialize(self.0.predicate.0, data, pos)
    }
}

#[cfg(test)]
mod test {
    use crate::regular::choice::OrdChoice;
    use super::*;
    use super::super::uints::{U8};
    use super::super::bytes::Bytes;
    use super::super::bytes_n::BytesN;

    proof fn test(s: Seq<u8>)
        requires
            s.len() <= usize::MAX,
    {
        let tag = Tag::spec_new(BytesN::<3>, seq![0u8, 0, 0]);
        if let Ok((n, v)) = tag.spec_parse(s) {
            if let Ok(buf) = tag.spec_serialize(v) {
                tag.theorem_parse_serialize_roundtrip(s);
                assert(buf == s.subrange(0, n as int));
            }
        }
    }

    fn test1(s: &[u8])
        requires
            s@.len() <= usize::MAX,
    {
        let bytes = [0u8, 0, 0];
        let tag = Tag::new(BytesN::<3>, bytes.as_slice());
        proof {
            let spec_tag = Tag::spec_new(BytesN::<3>, bytes@);
            assert(tag@ == spec_tag);
        }
        if let Ok((n, v)) = tag.parse(s) {
            let mut buf = Vec::new();
            buf.push(0);
            if let Ok(m) = tag.serialize(v, &mut buf, 0) {
                proof {
                    tag@.theorem_parse_serialize_roundtrip(s@);
                }
                assert(buf@ == s@.subrange(0, n as int));
            }
        }
    }

    proof fn test3(s: Seq<u8>)
        requires
            s.len() <= usize::MAX,
    {
        let tag1 = Tag::spec_new(U8, 0x42);
        let tag2 = Tag::spec_new(U8, 0x43);
        let ord = OrdChoice(tag1, tag2);
        if let Ok((n, v)) = ord.spec_parse(s) {
            if let Ok(buf) = ord.spec_serialize(v) {
                ord.theorem_parse_serialize_roundtrip(s);
                assert(buf == s.subrange(0, n as int));
            }
        }
        let tag3 = Tag::spec_new(BytesN::<3>, seq![1u8, 0, 0]);
        let tag4 = Tag::spec_new(BytesN::<3>, seq![2u8, 0, 0]);
        let ord2 = OrdChoice(tag3, tag4);
        if let Ok((n, v)) = ord2.spec_parse(s) {
            if let Ok(buf) = ord2.spec_serialize(v) {
                ord2.theorem_parse_serialize_roundtrip(s);
                assert(buf == s.subrange(0, n as int));
            }
        }
    }

    fn test4(s: &[u8])
        requires
            s@.len() <= usize::MAX,
    {
        let tag1 = Tag::new(U8, 0x42);
        let tag2 = Tag::new(U8, 0x43);
        let ord = OrdChoice(tag1, tag2);
        if let Ok((n, v)) = ord.parse(s) {
            let mut buf = Vec::new();
            buf.push(0);
            if let Ok(m) = ord.serialize(v, &mut buf, 0) {
                proof {
                    ord@.theorem_parse_serialize_roundtrip(s@);
                }
                assert(buf@ == s@.subrange(0, n as int));
            }
        }
        let b1 = [0u8, 0, 0];
        let b2 = [1u8, 0, 0];
        let tag3 = Tag::new(Bytes(3), b1.as_slice());
        let tag4 = Tag::new(Bytes(3), b2.as_slice());
        let ord2 = OrdChoice(tag3, tag4);
        if let Ok((n, v)) = ord2.parse(s) {
            let mut buf = Vec::new();
            buf.push(0);
            buf.push(0);
            buf.push(0);
            if let Ok(m) = ord2.serialize(v, &mut buf, 0) {
                proof {
                    ord2@.theorem_parse_serialize_roundtrip(s@);
                }
                assert(buf@ == s@.subrange(0, n as int));
            }
        }
    }

}

// old code
// /// generic tag combinator that matches the input with a given value and discards it
// /// e.g. `Tag(Int::<u8>, 0)` matches the byte `0`; `Tag(Bytes::<3>, &[1, 2, 3])` matches the bytes `[1, 2, 3]`
// pub struct Tag<Inner, T>(pub Inner, pub T);
//
// impl<Inner, T> View for Tag<Inner, T> where Inner: View, T: View {
//     type V = Tag<Inner::V, T::V>;
//
//     open spec fn view(&self) -> Self::V {
//         Tag(self.0@, self.1@)
//     }
// }
//
// impl<Inner, T> SpecCombinator for Tag<Inner, T> where Inner: SpecCombinator<SpecResult = T> {
//     type SpecResult = ();
//
//     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
//         match self.0.spec_parse(s) {
//             Ok((n, v)) if v == self.1 => Ok((n, ())),
//             _ => Err(()),
//         }
//     }
//
//     open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
//         self.0.spec_serialize(self.1)
//     }
//
//     proof fn spec_parse_wf(&self, s: Seq<u8>) {
//         self.0.spec_parse_wf(s);
//     }
// }
//
// impl<Inner, T> SecureSpecCombinator for Tag<Inner, T> where
//     Inner: SecureSpecCombinator<SpecResult = T>,
//  {
//     open spec fn spec_is_prefix_secure() -> bool {
//         Inner::spec_is_prefix_secure()
//     }
//
//     proof fn theorem_serialize_parse_roundtrip(&self, v: ()) {
//         self.0.theorem_serialize_parse_roundtrip(self.1);
//     }
//
//     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
//         self.0.theorem_parse_serialize_roundtrip(buf);
//     }
//
//     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
//         self.0.lemma_prefix_secure(s1, s2);
//     }
// }
//
// // the line `for <'a, 'b>Inner::Result<'a>: Compare<Inner::Result<'b>> + From<T>`
// // says that `Inner::Result<'a>` must impl `From<T> for all lifetimes `'a`
// // at the type level, this means even a static `Inner::Result<'static>` can be converted from
// // `T`, which in turn mandates that `T: 'static` (if both `T` and `Inner::Result<'a>` are
// // types without actual lifetimes, e.g. `u8`, then it's fine)
// //
// // it would be nice if Rust supports "existential" lifetimes like:
// // `exist <'a>Inner::Result<'a>: From<T>`
// impl<Inner, T> Combinator for Tag<Inner, T> where
//     Inner: Combinator,
//     Inner::V: SecureSpecCombinator<SpecResult = T::V>,
//     T: View<V = <Inner::Owned as View>::V> + Copy,
//     for <'a, 'b>Inner::Result<'a>: Compare<Inner::Result<'b>> + From<T>,
//  {
//     type Result<'a> = ();
//
//     type Owned = ();
//
//     open spec fn spec_length(&self) -> Option<usize> {
//         self.0.spec_length()
//     }
//
//     fn length(&self) -> Option<usize> {
//         self.0.length()
//     }
//
//     fn exec_is_prefix_secure() -> bool {
//         Inner::exec_is_prefix_secure()
//     }
//
//     open spec fn parse_requires(&self) -> bool {
//         self.0.parse_requires()
//     }
//
//     fn parse(&self, s: &[u8]) -> (res: Result<(usize, ()), ()>) {
//         match self.0.parse(s) {
//             Ok((n, v)) if v.compare(&self.1.ex_into()) => Ok((n, ())),
//             _ => Err(()),
//         }
//     }
//
//     open spec fn serialize_requires(&self) -> bool {
//         self.0.serialize_requires()
//     }
//
//     fn serialize(&self, v: (), data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
//         self.0.serialize(self.1.ex_into(), data, pos)
//     }
// }
//
// pub type U8Tag = Tag<Int<u8>, u8>;
//
// pub type U16Tag = Tag<Int<u16>, u16>;
//
// pub type U32Tag = Tag<Int<u32>, u32>;
//
// pub type U64Tag = Tag<Int<u64>, u64>;
//
// pub type SpecStaticBytesTag<const N: usize> = Tag<BytesN<N>, Seq<u8>>;
//
// pub type StaticBytesTag<const N: usize> = Tag<BytesN<N>, &'static [u8; N]>;
//
// /// combinator for matching a dynamic byte slice
// ///
// /// **Note**: due to the current limitations of Rust borrow checker
// /// the generic `Tag` combinator cannot be used with dynamic byte slices (`Tag<Bytes, &'a [u8]>`)
// pub struct DynamicBytesTag<'a>(pub Bytes, pub &'a [u8]);
//
// pub struct SpecDynamicBytesTag(pub Bytes, pub Seq<u8>);
//
// impl<'a> View for DynamicBytesTag<'a> {
//     type V = SpecDynamicBytesTag;
//
//     open spec fn view(&self) -> Self::V {
//         SpecDynamicBytesTag(self.0@, self.1@)
//     }
// }
//
// impl SpecCombinator for SpecDynamicBytesTag {
//     type SpecResult = ();
//
//     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
//         match self.0.spec_parse(s) {
//             Ok((n, v)) if n == self.1.len() && v == self.1 => Ok((n, ())),
//             _ => Err(()),
//         }
//     }
//
//     open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
//         self.0.spec_serialize(self.1)
//     }
//
//     proof fn spec_parse_wf(&self, s: Seq<u8>) {
//     }
// }
//
// impl SecureSpecCombinator for SpecDynamicBytesTag {
//     open spec fn spec_is_prefix_secure() -> bool {
//         Bytes::spec_is_prefix_secure()
//     }
//
//     proof fn theorem_serialize_parse_roundtrip(&self, v: ()) {
//         self.0.theorem_serialize_parse_roundtrip(self.1);
//     }
//
//     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
//         self.0.theorem_parse_serialize_roundtrip(buf);
//     }
//
//     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
//         self.0.lemma_prefix_secure(s1, s2);
//     }
// }
//
// impl<'a> Combinator for DynamicBytesTag<'a> {
//     type Result<'b> = ();
//
//     type Owned = ();
//
//     open spec fn spec_length(&self) -> Option<usize> {
//         Some(self.0.0)
//     }
//
//     fn length(&self) -> Option<usize> {
//         Some(self.0.0)
//     }
//
//     fn exec_is_prefix_secure() -> bool {
//         Bytes::exec_is_prefix_secure()
//     }
//
//     fn parse(&self, s: &[u8]) -> (res: Result<(usize, Self::Result<'_>), ()>) {
//         match self.0.parse(s) {
//             Ok((n, v)) if compare_slice(v, self.1) => Ok((n, ())),
//             _ => Err(()),
//         }
//     }
//
//     fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
//         usize,
//         (),
//     >) {
//         self.0.serialize(self.1, data, pos)
//     }
// }
//
// #[cfg(test)]
// mod test {
//     use super::*;
//
//     const MAGIC: u8 = 0x42;
//
//     spec const SPEC_BYTES_123: Seq<u8> = seq![1, 2, 3];
//
//     exec static BYTES_123: [u8; 3]
//         ensures
//             BYTES_123@ == SPEC_BYTES_123,
//     {
//         let a: [u8; 3] = [1, 2, 3];
//         assert(a@ == SPEC_BYTES_123);
//         a
//     }
//
//     spec fn spec_tag(input: Seq<u8>) -> (U8Tag, SpecStaticBytesTag<3>) {
//         let t1: U8Tag = Tag(U8, MAGIC);
//         let t2: SpecStaticBytesTag<3> = Tag(BytesN::<3>, SPEC_BYTES_123);
//         (t1, t2)
//     }
//
//     fn tag(input: &[u8]) -> (res: (U8Tag, StaticBytesTag<3>))
//         ensures
//             res@ == spec_tag(input@),
//     {
//         let tem_magic: u8 = 0x42;
//         let t1: U8Tag = Tag(U8, tem_magic);  // ok
//         let t1: U8Tag = Tag(U8, MAGIC);  // ok
//         let t2: StaticBytesTag<3> = Tag(BytesN::<3>, &BYTES_123);
//         (t1, t2)
//     }
//
//     fn tag2<'a>(input: &'a [u8]) {
//         // let tmp_bytes_123: [u8; 3] = [1, 2, 3];
//         // let t1 = Tag(BytesN::<3>, &tmp_bytes_123); // err: TMP_BYTES_123 does not live long enough
//         // it's required that `tmp_bytes_123` is borrowed for `'static`
//         // let t1 = Tag(Bytes(3), &TMP_BYTES_123); // same err
//         let t1 = Tag(Bytes(3), &BYTES_123);  // ok
//         let _ = t1.parse(input);
//     }
//
//     fn tag3<'a, 'b>(input: &'a [u8], tmp_bytes_123: &'b [u8; 3]) where 'b: 'a {
//         // let t1 = Tag(BytesN::<3>, tmp_bytes_123); // err: TMP_BYTES_123 does not live long enough
//         // let t1 = Tag(Bytes(3), tmp_bytes_123); // same err
//         let t1 = Tag(Bytes(3), &BYTES_123);  // ok
//         let _ = t1.parse(input);
//     }
//
// }
} // verus!
