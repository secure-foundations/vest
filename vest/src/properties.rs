pub use crate::buf_traits::*;
pub use crate::errors::*;
use alloc::boxed::Box;

/// The parse result of a combinator.
pub type PResult<T, E> = Result<(usize, T), E>;

/// The serialize result of a combinator.
pub type SResult<T, E> = Result<T, E>;

/// Implementation for parser and serializer combinators. A combinator's view must be a
/// [`SecureSpecCombinator`].
pub trait Combinator<I, O>
where
    I: VestInput,
    O: VestOutput<I>,
{
    /// The result type of parsing
    type Type<'p>;

    /// The input type of serialization, often a reference to [`Self::Type`].
    /// For "structural" formats though (e.g., [`crate::regular::sequence::Pair`] and [`crate::regular::variant::Choice`]),
    /// this is the tuple/sum of the corresponding [`Combinator::SType`] types.
    type SType<'s>;

    /// The length of the output buffer.
    /// This can be used to optimize serialization by pre-allocating the buffer.
    fn length<'s>(&self, v: Self::SType<'s>) -> usize;

    /// The parsing function.
    /// To enable "zero-copy" parsing, implementations of `parse` should not
    /// consume/deepcopy the input buffer `I`, but rather return a slice of the
    /// input buffer for `Self::Type` whenever possible.
    /// See [`crate::buf_traits::VestInput`] and [`crate::buf_traits::VestPublicInput`] for
    /// more details.
    ///
    /// ## Pre-conditions
    ///
    /// - [`SpecCombinator::requires`]
    /// - [`Combinator::ex_requires`]
    ///
    /// ## Post-conditions
    /// Essentially, the implementation of `parse` is functionally correct with respect to the
    /// specification `spec_parse` on both success and failure cases.
    fn parse<'p>(&self, s: I) -> PResult<Self::Type<'p>, ParseError>;

    /// The serialization function.
    /// The intended use of `serialize` is to serialize a value `v` into the
    /// buffer `buf` at the position `pos` "in-place" (i.e., without
    /// allocating a new buffer or extending the buffer).
    ///
    /// ## Pre-conditions
    ///
    /// - [`SpecCombinator::requires`]
    /// - [`Combinator::ex_requires`]
    /// - [`SpecCombinator::wf`]
    /// - `pos` is less than or equal to the length of the buffer, whose length
    ///   is less than or equal to `usize::MAX`.
    ///
    /// ## Post-conditions
    /// `serialize` ensures that it is functionally correct with respect to the
    /// specification `spec_serialize` when it returns `Ok`. This is because
    /// `serialize` being a partial function can fail (e.g.,
    /// insufficient buffer space), while `spec_serialize` is a
    /// total function (with infinite buffer size) and will never fail.
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        buf: &mut O,
        pos: usize,
    ) -> SResult<usize, SerializeError>;
}

impl<I, O, C: Combinator<I, O>> Combinator<I, O> for &C
where
    I: VestInput,
    O: VestOutput<I>,
{
    type Type<'p> = C::Type<'p>;

    type SType<'s> = C::SType<'s>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        (*self).length(v)
    }

    fn parse<'p>(&self, s: I) -> Result<(usize, Self::Type<'p>), ParseError> {
        (*self).parse(s)
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        (*self).serialize(v, data, pos)
    }
}

impl<I, O, C: Combinator<I, O>> Combinator<I, O> for Box<C>
where
    I: VestInput,
    O: VestOutput<I>,
{
    type Type<'p> = C::Type<'p>;

    type SType<'s> = C::SType<'s>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        (**self).length(v)
    }

    fn parse<'p>(&self, s: I) -> Result<(usize, Self::Type<'p>), ParseError> {
        (**self).parse(s)
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        (**self).serialize(v, data, pos)
    }
}
