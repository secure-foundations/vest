use crate::core::exec::output::*;
use crate::core::exec::ComplianceErrorKind;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError, ParseErrorKind,
};
use crate::Never;
use vstd::prelude::*;
use OutputBuf;

verus! {

/// An uninhabited type that implements DeepView.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[verifier::external_body]
pub struct ExecNever;

impl DeepView for ExecNever {
    type V = Never;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl<I: View<V = Seq<u8>>> Parser<I> for super::Empty {
    type PT = ();

    fn parse(&self, _ibuf: &I) -> PResult<Self::PT> {
        Ok((0, ()))
    }
}

impl<Output: OutputBuf> Serializer<Output, ()> for super::Empty {
    fn serialize_into(&self, _v: &(), _obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

    }
}

impl ByteLen<()> for super::Empty {
    fn length(&self, _v: &()) -> (len: usize) {
        0
    }
}

impl Prepare<()> for super::Empty {
    fn prepare(&self, _v: &()) -> (checked: Result<usize, PreSerializeError>) {
        Ok(0)
    }
}

impl<I: View<V = Seq<u8>>> Parser<I> for super::Void {
    type PT = ExecNever;

    fn parse(&self, _ibuf: &I) -> (r: PResult<Self::PT>) {
        Err(ParseError::new(ParseErrorKind::Custom(self.0)))
    }
}

impl<Output: OutputBuf> Serializer<Output, ExecNever> for super::Void {
    fn serialize_into(&self, _v: &ExecNever, _obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

    }
}

impl ByteLen<ExecNever> for super::Void {
    fn length(&self, _v: &ExecNever) -> (len: usize) {
        0
    }
}

impl Prepare<ExecNever> for super::Void {
    fn prepare(&self, _v: &ExecNever) -> (checked: Result<usize, PreSerializeError>) {
        Err(PreSerializeError::not_compliant(ComplianceErrorKind::Custom(self.0)))
    }
}

} // verus!
