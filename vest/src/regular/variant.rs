use rand::Rng;

use crate::{properties::*, regular::modifier::RuntimeValue};

/// Dispatch combinator that selects one of `N` branches based on a runtime value.
pub struct Dispatch<'a, T, C, const N: usize> {
    /// The tag used to select a branch.
    pub tag: RuntimeValue<'a, T>,
    /// The keyed branches to dispatch to (entirely static).
    pub branches: [(T, C); N],
}

impl<'a, T, C, const N: usize> Dispatch<'a, T, C, N> {
    /// Create a new dispatch combinator with `N` branches.
    pub fn new(tag: RuntimeValue<'a, T>, branches: [(T, C); N]) -> Self {
        Self { tag, branches }
    }

    fn branch_index(&self) -> Option<usize>
    where
        T: PartialEq,
    {
        let key = self.tag.as_ref();
        self.branches
            .iter()
            .position(|(branch_key, _)| branch_key == key)
    }
}

impl<'a, I, O, T, C, const N: usize> Combinator<I, O> for Dispatch<'a, T, C, N>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    C: Combinator<I, O>,
    T: PartialEq + Clone,
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
        let Some(idx) = self.branch_index() else {
            panic!("Dispatch has no matching branch for lhs");
        };
        self.branches[idx].1.length(v)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let Some(idx) = self.branch_index() else {
            return Err(ParseError::CondFailed);
        };
        self.branches[idx].1.parse(s)
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
        let Some(idx) = self.branch_index() else {
            return Err(SerializeError::Other("condition not satisfied".into()));
        };
        self.branches[idx].1.serialize(v, data, pos)
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        if N == 0 {
            return Err(GenerateError::Other("Dispatch has no branches".into()));
        }
        let idx = g.rng.random_range(0..N);
        let key = self.branches[idx].0.clone();
        if self.tag.as_ref() != &key {
            *self.tag.as_mut() = key;
        }
        self.branches[idx].1.generate(g)
    }
}

/// Define an enum and implement `Combinator` for it in one place.
///
/// The enum variants must wrap existing combinators, and the `Type`/`SType`/`GType` enums
/// must use the same variant names, carrying the inner combinator value types.
///
/// Example:
/// ```rust
/// pub enum MsgValue<'a> {
///     Msg1(&'a [u8]),
///     Msg2(Msg2),
///     Msg3(Msg3),
/// }
/// enum_combinator! {
///
/// enum PayloadCases {
///     Msg1(Fixed<32>),
///     Msg2(Msg2Comb),
///     Msg3(Msg3Comb),
/// }
/// impl Combinator<[u8], Vec<u8>> {
///     type Type<'p> = MsgValue<'p>;
///     type SType<'s> = &'s MsgValue<'s>;
///     type GType = MsgValueOwned;
///     type TypeEnum = MsgValue;
///     type GTypeEnum = MsgValueOwned;
/// }
///
/// }
/// ```
#[macro_export]
macro_rules! enum_combinator {
    (
        $vis:vis enum $Enum:ident {
            $(
                $Variant:ident($Inner:ty)
            ),+ $(,)?
        }
        impl Combinator<$I:ty, $O:ty> {
            type Type<$p:lifetime> = $Type:ty;
            type SType<$s:lifetime> = $SType:ty;
            type GType = $GType:ty;
            type TypeEnum = $TypeEnum:ident;
            type GTypeEnum = $GTypeEnum:ident;
        }
    ) => {
        $vis enum $Enum {
            $(
                $Variant($Inner),
            )+
        }

        impl $crate::properties::Combinator<$I, $O> for $Enum
        where
            $I: $crate::buf_traits::VestInput,
            $O: $crate::buf_traits::VestOutput<$I>,
        {
            type Type<$p> = $Type;
            type SType<$s> = $SType;
            type GType = $GType;

            fn length<$s>(&self, v: Self::SType<$s>) -> usize
            where
                $I: $s,
            {
                match (self, v) {
                    $(
                        ($Enum::$Variant(inner), $TypeEnum::$Variant(val)) => {
                            <$Inner as $crate::properties::Combinator<$I, $O>>::length(
                                inner,
                                val,
                            )
                        }
                    )+,
                    _ => panic!("enum combinator does not match value"),
                }
            }

            fn parse<$p>(
                &self,
                s: &$p $I,
            ) -> Result<(usize, Self::Type<$p>), $crate::errors::ParseError>
            where
                $I: $p,
            {
                match self {
                    $(
                        $Enum::$Variant(inner) => {
                            let (n, v) =
                                <$Inner as $crate::properties::Combinator<$I, $O>>::parse(
                                    inner, s,
                                )?;
                            Ok((n, $TypeEnum::$Variant(v)))
                        }
                    )+
                }
            }

            fn serialize<$s>(
                &self,
                v: Self::SType<$s>,
                data: &mut $O,
                pos: usize,
            ) -> Result<usize, $crate::errors::SerializeError>
            where
                $I: $s,
            {
                match (self, v) {
                    $(
                        ($Enum::$Variant(inner), $TypeEnum::$Variant(val)) => {
                            <$Inner as $crate::properties::Combinator<$I, $O>>::serialize(
                                inner,
                                val,
                                data,
                                pos,
                            )
                        }
                    )+,
                    _ => Err($crate::errors::SerializeError::Other(
                        "enum combinator does not match value".into(),
                    )),
                }
            }

            fn generate(
                &mut self,
                g: &mut $crate::properties::GenSt,
            ) -> $crate::properties::GResult<Self::GType, $crate::errors::GenerateError> {
                match self {
                    $(
                        $Enum::$Variant(inner) => {
                            let (n, v) =
                                <$Inner as $crate::properties::Combinator<$I, $O>>::generate(
                                    inner, g,
                                )?;
                            Ok((n, $GTypeEnum::$Variant(v)))
                        }
                    )+
                }
            }
        }
    };
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

/// Try the first parser, fall back to the second on error.
pub struct Choice<Fst, Snd>(pub Fst, pub Snd);

impl<Fst, Snd> Choice<Fst, Snd> {
    pub fn new(fst: Fst, snd: Snd) -> Self {
        Self(fst, snd)
    }
}

impl<I, O, Fst, Snd> Combinator<I, O> for Choice<Fst, Snd>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type<'p>
        = Either<Fst::Type<'p>, Snd::Type<'p>>
    where
        I: 'p;
    type SType<'s>
        = Either<Fst::SType<'s>, Snd::SType<'s>>
    where
        I: 's;
    type GType = Either<Fst::GType, Snd::GType>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        match v {
            Either::Left(v) => self.0.length(v),
            Either::Right(v) => self.1.length(v),
        }
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        if let Ok((n, v)) = self.0.parse(s) {
            Ok((n, Either::Left(v)))
        } else {
            let (n, v) = self.1.parse(s)?;
            Ok((n, Either::Right(v)))
        }
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
        match v {
            Either::Left(v) => self.0.serialize(v, data, pos),
            Either::Right(v) => self.1.serialize(v, data, pos),
        }
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        if g.rng.random_bool(0.5) {
            let (n, v) = self.0.generate(g)?;
            Ok((n, Either::Left(v)))
        } else {
            let (n, v) = self.1.generate(g)?;
            Ok((n, Either::Right(v)))
        }
    }
}

/// Optional combinator that never fails; consumes zero bytes on `None`.
pub struct Opt<T>(pub T);

impl<T> Opt<T> {
    pub fn new(inner: T) -> Self {
        Self(inner)
    }
}

impl<I, O, T> Combinator<I, O> for Opt<T>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    T: Combinator<I, O>,
{
    type Type<'p>
        = Option<T::Type<'p>>
    where
        I: 'p;
    type SType<'s>
        = Option<T::SType<'s>>
    where
        I: 's;
    type GType = Option<T::GType>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        match v {
            Some(v) => self.0.length(v),
            None => 0,
        }
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        if let Ok((n, v)) = self.0.parse(s) {
            Ok((n, Some(v)))
        } else {
            Ok((0, None))
        }
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
        match v {
            Some(v) => self.0.serialize(v, data, pos),
            None => {
                if pos <= data.len() {
                    Ok(0)
                } else {
                    Err(SerializeError::InsufficientBuffer)
                }
            }
        }
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        if g.rng.random_bool(0.5) {
            let (n, v) = self.0.generate(g)?;
            Ok((n, Some(v)))
        } else {
            Ok((0, None))
        }
    }
}

/// Parse an optional prefix followed by a required tail.
pub struct OptThen<Fst, Snd>(pub Opt<Fst>, pub Snd);

impl<Fst, Snd> OptThen<Fst, Snd> {
    pub fn new(fst: Fst, snd: Snd) -> Self {
        Self(Opt(fst), snd)
    }
}

impl<I, O, Fst, Snd> Combinator<I, O> for OptThen<Fst, Snd>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type<'p>
        = (Option<Fst::Type<'p>>, Snd::Type<'p>)
    where
        I: 'p;
    type SType<'s>
        = (Option<Fst::SType<'s>>, Snd::SType<'s>)
    where
        I: 's;
    type GType = (Option<Fst::GType>, Snd::GType);

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        let fst_len = v.0.map(|val| self.0 .0.length(val)).unwrap_or(0);
        fst_len + self.1.length(v.1)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        if let Ok((n0, v0)) = self.0 .0.parse(s) {
            let rest = s.skip(n0);
            let (n1, v1) = self.1.parse(&rest)?;
            Ok((n0 + n1, (Some(v0), v1)))
        } else {
            let (n1, v1) = self.1.parse(s)?;
            Ok((n1, (None, v1)))
        }
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
        let mut written = 0;
        if let Some(v0) = v.0 {
            written = self.0 .0.serialize(v0, data, pos)?;
        }
        let n1 = self.1.serialize(v.1, data, pos + written)?;
        Ok(written + n1)
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let (n1, v1) = self.1.generate(g)?;
        if g.rng.random_bool(0.5) {
            let (n0, v0) = self.0 .0.generate(g)?;
            Ok((n0 + n1, (Some(v0), v1)))
        } else {
            Ok((n1, (None, v1)))
        }
    }
}
