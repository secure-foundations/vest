use crate::properties::*;
use crate::view::*;
use vstd::prelude::*;

verus! {

mod Inner {
    use crate::view::*;

    #[repr(transparent)]
    pub struct SecByte(u8);

    impl DView for SecByte {
        type V = u8;

        closed spec fn dview(&self) -> u8 {
            self.0
        }
    }

    #[verifier(external_body)]
    pub fn mk_secbyte_slice(xs: &[u8]) -> (res: &[SecByte])
        ensures
            res.dview() == xs.dview(),
    {
        unsafe { std::slice::from_raw_parts(xs.as_ptr() as *const SecByte, xs.len()) }
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

pub trait SecCombinator<'a, T: DView> where Self: SpecCombinator<T> {
    // Only for statically known
    spec fn spec_length(&self) -> Option<usize>;

    fn length(&self) -> (res: Option<usize>)
        ensures
            res == self.spec_length(),
    ;

    fn parse(&self, s: &'a [SecByte], pos: usize) -> (res: Result<(usize, T), ()>) where T: 'a
        requires
            pos <= s.dview().len(),  /* ensures res.dview() == self.spec_parse(..) */

        ensures
            res.is_ok() ==> self.spec_wf(res.unwrap().1.dview()) && res.dview() == self.spec_parse(
                s.dview().subrange(pos as int, s.dview().len() as int),
            ),
    ;

    spec fn serialize_req(&self, v: T::V, data: Seq<u8>, pos: usize) -> bool;

    fn serialize<'b>(&self, v: T, data: &'b mut [SecByte], pos: usize) -> (res: Result<
        usize,
        (),
    >) where T: 'a
        requires
            pos <= old(data).dview().len() && self.serialize_req(v.dview(), old(data).dview(), pos),
        ensures
            data.dview().len() == old(data).dview().len(),
            res.is_ok() ==> self.spec_serialize(v.dview()).is_ok() && res.unwrap()
                == self.spec_serialize(v.dview()).unwrap().len() && pos + res.unwrap()
                <= data.dview().len() && data.dview() == seq_splice(
                old(data).dview(),
                pos,
                self.spec_serialize(v.dview()).unwrap(),
            ),
    ;
}

pub struct ToPub<S>(pub S);

impl<T: DView, C: SpecCombinator<T>> SpecCombinator<T> for ToPub<C> {
    open spec fn spec_wf(&self, v: T::V) -> bool {
        self.0.spec_wf(v)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, T::V), ()> {
        self.0.spec_parse(s)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }

    open spec fn spec_serialize(&self, v: T::V) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_serialize_wf(&self, v: T::V) {
        self.0.spec_serialize_wf(v)
    }
}

impl<T: DView, C: SecureSpecCombinator<T>> SecureSpecCombinator<T> for ToPub<C> {
    open spec fn spec_has_prefix() -> bool {
        C::spec_has_prefix()
    }

    fn has_prefix() -> bool {
        C::has_prefix()
    }

    proof fn spec_serialize_parse(&self, v: T::V) {
        self.0.spec_serialize_parse(v)
    }

    proof fn spec_parse_serialize(&self, buf: Seq<u8>) {
        self.0.spec_parse_serialize(buf)
    }

    proof fn spec_parse_prefix(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.spec_parse_prefix(s1, s2)
    }
}

impl<'a, T: DView + 'a, C: SecCombinator<'a, T>> Combinator<'a, T> for ToPub<C> {
    open spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    fn parse(&self, s: &'a [u8], pos: usize) -> Result<(usize, T), ()> {
        self.0.parse(mk_secbyte_slice(s), pos)
    }

    open spec fn serialize_req(&self, v: T::V, data: Seq<u8>, pos: usize) -> bool {
        self.0.serialize_req(v, data, pos)
    }

    fn serialize<'b>(&self, v: T, data: &'b mut [u8], pos: usize) -> Result<usize, ()> {
        Err(())
    }
}

} // verus!
