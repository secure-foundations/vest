pub use crate::buf_traits::*;
pub use crate::errors::*;
use alloc::boxed::Box;

/// The parse result of a combinator.
pub type PResult<T, E> = Result<(usize, T), E>;

/// The serialize result of a combinator.
pub type SResult<T, E> = Result<T, E>;

/// The generate result of a combinator.
pub type GResult<T, E> = Result<(usize, T), E>;

/// The state for generation-related fields
pub struct GenSt {
    /// The random number generator
    pub rng: rand::rngs::StdRng,
}

impl GenSt {
    /// Create a new generation state with the given RNG seed
    pub fn new(seed: u64) -> Self {
        Self {
            rng: rand::SeedableRng::seed_from_u64(seed),
        }
    }
}

/// Helper trait to convert from `&Type` to `SType`.
pub trait FromRef<'s, T> {
    /// Convert from a reference to the serialization type.
    fn ref_to_stype(val: &'s T) -> Self;

    /// Convert from a mutable reference of [`T`] to a mutable reference of the serialization type.
    fn mut_ref_to_mut_stype(val: &mut T) -> &mut Self;
}

/// Blanket implementation for Copy types where SType equals Type.
impl<'s, T: Copy> FromRef<'s, T> for T {
    fn ref_to_stype(val: &'s T) -> Self {
        *val
    }

    fn mut_ref_to_mut_stype(val: &mut T) -> &mut Self {
        val
    }
}

/// Implementation for parser and serializer combinators. A combinator's view must be a
/// [`SecureSpecCombinator`].
pub trait Combinator<I, O>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
{
    /// The result type of parsing.
    /// The lifetime `'p` is tied to the input buffer passed to [`Self::parse`].
    type Type<'p>
    where
        I: 'p;

    /// The input type of serialization, often a reference to [`Self::Type`].
    /// For "structural" formats though (e.g., [`crate::regular::sequence::Pair`] and [`crate::regular::variant::Choice`]),
    /// this is the tuple/sum of the corresponding [`Combinator::SType`] types.
    type SType<'s>
    where
        I: 's;

    /// The result type of generation.
    /// It is often an owned version of [`Self::Type`].
    type GType;

    /// The length of the output buffer.
    /// This can be used to optimize serialization by pre-allocating the buffer.
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's;

    /// The parsing function.
    /// To enable "zero-copy" parsing, implementations of `parse` should not
    /// consume/deepcopy the input buffer `I`, but rather return a slice of the
    /// input buffer for `Self::Type` whenever possible.
    /// See [`crate::buf_traits::VestInput`] and [`crate::buf_traits::VestPublicInput`] for
    /// more details.
    ///
    /// The lifetime `'p` ties the parsed result to the input buffer.
    ///
    /// ## Pre-conditions
    ///
    /// - [`SpecCombinator::requires`]
    /// - [`Combinator::ex_requires`]
    ///
    /// ## Post-conditions
    /// Essentially, the implementation of `parse` is functionally correct with respect to the
    /// specification `spec_parse` on both success and failure cases.
    fn parse<'p>(&self, s: &'p I) -> PResult<Self::Type<'p>, ParseError>
    where
        I: 'p;

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
    ) -> SResult<usize, SerializeError>
    where
        I: 's;

    /// The generation function.
    /// This function generates a value of type `Self::GType` along with the
    /// number of bytes that would be produced when serializing this value.
    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError>;

    /// Convert from generated type to [`Self::SType`] for serialization.
    fn ref_gtype_to_stype<'s>(v: &'s Self::GType) -> Self::SType<'s>
    where
        Self::SType<'s>: FromRef<'s, Self::GType>,
    {
        Self::SType::ref_to_stype(v)
    }
}

impl<I, O, C: Combinator<I, O>> Combinator<I, O> for &C
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
{
    type Type<'p>
        = C::Type<'p>
    where
        I: 'p;

    type SType<'s>
        = C::SType<'s>
    where
        I: 's;

    type GType = C::GType;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        (*self).length(v)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        (*self).parse(s)
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        (*self).serialize(v, data, pos)
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        (*self).generate(g)
    }
}

impl<I, O, C: Combinator<I, O>> Combinator<I, O> for Box<C>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
{
    type Type<'p>
        = C::Type<'p>
    where
        I: 'p;

    type SType<'s>
        = C::SType<'s>
    where
        I: 's;

    type GType = C::GType;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        (**self).length(v)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        (**self).parse(s)
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        (**self).serialize(v, data, pos)
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        (**self).generate(g)
    }
}
