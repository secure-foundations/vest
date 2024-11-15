use crate::properties::*;
use vstd::prelude::*;

verus! {

mod Inner {
    use super::*;
    use vstd::slice::*;

    #[repr(transparent)]
    pub struct SecByte(u8);

    impl View for SecByte {
        type V = u8;

        closed spec fn view(&self) -> u8 {
            self.0
        }
    }

    impl DeepView for SecByte {
        type V = u8;

        closed spec fn deep_view(&self) -> u8 {
            self.0
        }
    }

    // impl View for &[SecByte] {
    //     type V = Seq<u8>;

    //     closed spec fn view(&self) -> Seq<u8> {
    //         Seq::new(self.len(), |i| self[i]@)
    //     }
    // }

    #[verifier(external_body)]
    pub fn mk_secbyte_slice(xs: &[u8]) -> (res: &[SecByte])
        ensures
            res.deep_view() == xs.view(),
    {
        // TODO: is this fine?
        unsafe { std::slice::from_raw_parts(xs.as_ptr() as *const SecByte, xs.len()) }
    }

    // private, so not usable outside
    fn copy_sec_byte(x: &SecByte) -> (res: SecByte)
        ensures 
            x.deep_view() == res.deep_view(),
            x.view() == res.view()
    {
        SecByte(x.0)
    }    

    /// Helper function to set a range of bytes in a vector.
    pub fn set_range_secret<'a>(data: &mut Vec<SecByte>, i: usize, input: &[SecByte])
        requires
            0 <= i + input.deep_view().len() <= old(data).deep_view().len() <= usize::MAX,
        ensures
            data.deep_view().len() == old(data).deep_view().len() && data.deep_view() == old(data).deep_view().subrange(0, i as int).add(
                input.deep_view(),
            ).add(old(data).deep_view().subrange(i + input.deep_view().len(), data.deep_view().len() as int)),
    {
        let mut j = 0;
        while j < input.len()
            invariant
                data.deep_view().len() == old(data).deep_view().len(),
                forall|k| 0 <= k < i ==> data.deep_view()[k] == old(data).deep_view()[k],
                forall|k| i + input.deep_view().len() <= k < data.deep_view().len() ==> data.deep_view()[k] == old(data).deep_view()[k],
                0 <= i <= i + j <= i + input.deep_view().len() <= data.deep_view().len() <= usize::MAX,
                forall|k| 0 <= k < j ==> data.deep_view()[i + k] == input.deep_view()[k],
        {
            data.set(i + j, copy_sec_byte(slice_index_get(input, j)));
            j = j + 1
        }
        #[verusfmt::skip]
        assert(
            data.deep_view() =~= 
                old(data).deep_view().subrange(0, i as int)
                    .add(input.deep_view())
                    .add(old(data).deep_view().subrange(i + input.deep_view().len(), data.deep_view().len() as int))
        );
    }


    /*
        #[verifier(external_body)]
        pub fn with_secbyte_slice_mut<'a, F>(xs : &'a mut [u8], k : F) -> Result<usize, ()>
            where F : Fn(&'a mut [SecByte]) -> Result<usize, ()>
        {
            unsafe {
                k(std::slice::from_raw_parts_mut(xs.as_ptr() as *mut SecByte, xs.len()))
            }
        }
        */


}

use Inner::*;

/// Implementation for secret parser and serializer combinators. A combinator's view must be a
/// [`SecureSpecCombinator`].
pub trait SecCombinator: View where
    Self::V: SecureSpecCombinator<SpecResult = <Self::Owned as DeepView>::V>,
 {
    /// The result type of parsing and the input type of serialization.
    type Result<'a>: DeepView<V = <Self::Owned as DeepView>::V>;

    /// The owned parsed type. This is currently a hack to avoid lifetime bindings in [`SpecCombinator::SpecResult`]
    /// , but it can be useful if we want to have functions that return owned values (e.g. [`Vec<T>`]).
    type Owned: DeepView;

    /// Spec version of [`Self::length`].
    spec fn spec_length(&self) -> Option<usize>;

    /// The length of the output buffer, if known.
    /// This can be used to optimize serialization by pre-allocating the buffer.
    fn length(&self) -> (res: Option<usize>)
        ensures
            res == self.spec_length(),
    ;

    /// Pre-condition for parsing.
    open spec fn parse_requires(&self) -> bool {
        true
    }

    /// The parsing function.
    fn parse<'a>(&self, s: &'a [SecByte]) -> (res: Result<(usize, Self::Result<'a>), ParseError>)
        requires
            self.parse_requires(),
        ensures
            res matches Ok((n, v)) ==> {
                &&& self@.spec_parse(s.deep_view()) is Ok
                &&& self@.spec_parse(s.deep_view()) matches Ok((m, w)) ==> n == m && v.deep_view() == w && n <= s@.len()
            },
            res is Err ==> self@.spec_parse(s.deep_view()) is Err,
            self@.spec_parse(s.deep_view()) matches Ok((m, w)) ==> {
                &&& res is Ok
                &&& res matches Ok((n, v)) ==> m == n && w == v.deep_view()
            },
            self@.spec_parse(s.deep_view()) is Err ==> res is Err,
    ;

    /// Pre-condition for serialization.
    open spec fn serialize_requires(&self) -> bool {
        true
    }

    /// The serialization function.
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<SecByte>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >)
        requires
            self.serialize_requires(),
        ensures
            data@.len() == old(data)@.len(),
            res matches Ok(n) ==> {
                &&& self@.spec_serialize(v.deep_view()) is Ok
                &&& self@.spec_serialize(v.deep_view()) matches Ok(b) ==> {
                    n == b.len() && data.deep_view() == seq_splice(old(data).deep_view(), pos, b)
                }
            },
    ;
}

pub mod bytes;
pub mod bytes_n;
pub mod pair;
pub mod tail;

} // verus!
