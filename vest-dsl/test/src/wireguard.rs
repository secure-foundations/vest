use vstd::array::*;
use vstd::calc_macro::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
extern crate alloc;
use alloc::vec::Vec;

verus! {
    /// won't work for serializers
    pub struct Stream<'a> {
        pub data: &'a [u8], // the input data
        pub start: usize, // the index, in range [0, data.len())
    }

    pub struct SerializeStream {
        pub data: Vec<u8>,
        pub start: usize,
    }

    pub struct SpecStream {
        pub data: Seq<u8>,
        pub start: int, // the index, in range [0, data.len())
    }

    impl<'a> DView for Stream<'a> {
        type V = SpecStream;
        open spec fn dview(&self) -> SpecStream {
            SpecStream {
                data: self.data.dview(),
                start: self.start as int,
            }
        }
    }

    impl DView for SerializeStream {
        type V = SpecStream;
        open spec fn dview(&self) -> SpecStream {
            SpecStream {
                data: self.data.dview(),
                start: self.start as int,
            }
        }
    }

    #[derive(PartialEq, Eq)]
    pub enum ParseError {
        Eof,
        NotEnoughData,
        NegativeIndex,
        IntegerOverflow,
        ConstMismatch,
    }

    #[derive(PartialEq, Eq)]
    pub enum SerializeError {
        NotEnoughSpace,
        NegativeIndex,
        IntegerOverflow,
        RepeatNMismatch, // for spec_serialize_repeat_n
        TailLengthMismatch, // for spec_serialize_tail
        ConstMismatch, // for const serializers
        BytesLengthMismatch, // for spec_serialize_bytes
    }

    pub type ParseResult<'a, Output> = Result<(Stream<'a>, usize, Output), ParseError>;
    pub type SpecParseResult<Output> = Result<(SpecStream, nat, Output), ParseError>;

    pub type SerializeResult = Result<(usize, usize), SerializeError>; // (new start position, number of bytes written)
    pub type SpecSerializeResult = Result<(SpecStream, nat), SerializeError>;

    /// opaque type abstraction over raw bytes
    pub struct SecBytes(Vec<u8>);

    impl DView for SecBytes {
        type V = Seq<u8>;
        closed spec fn dview(&self) -> Self::V
        {
            self.0.dview()
        }
    }

    impl SecBytes {

        pub fn length(&self) -> (res: usize)
            ensures
                res == self.dview().len()
        {
            self.0.length()
        }

        /// memcpy the secret bytes from `self.0[i..j]` to a new secret bytes
        pub fn subrange(&self, i: usize, j: usize) -> (res: Self)
            requires
                0 <= i <= j <= self.dview().len()
            ensures
                res.dview() == self.dview().subrange(i as int, j as int)
        {
            Self(slice_to_vec(slice_subrange(vec_as_slice(&self.0), i, j))) // (&self.0[i..j]).to_vec()
        }

        pub fn append(&mut self, other: &mut Self)
            ensures
                self.dview() == old(self).dview() + old(other).dview()
        {
            vec_append(&mut self.0, &mut other.0);
        }
    }

    pub struct SecStream {
        pub data : SecBytes,
        pub start : usize
    }

    impl DView for SecStream {
        type V = SpecStream;
        open spec fn dview(&self) -> SpecStream {
            SpecStream {
                data: self.data.dview(),
                start: self.start as int,
            }
        }
    }

    pub type SecParseResult<Sec> = Result<(SecStream, usize, Sec), ParseError>;
    pub type SecSerializeResult = Result<(SecStream, usize), SerializeError>;

    #[verifier(external)]
    impl<'a> std::fmt::Debug for Stream<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Stream {{ data: {:?}, start: {} }}", self.data, self.start)
        }
    }

    #[verifier(external)]
    impl std::fmt::Debug for SerializeStream {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "SerializeStream {{ data: {:?}, start: {} }}", self.data, self.start)
        }
    }

    #[verifier(external)]
    impl std::fmt::Debug for SecStream {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "SecStream {{ data: {:?}, start: {} }}", self.data, self.start)
        }
    }

    #[verifier(external)]
    impl std::fmt::Debug for SecBytes {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "SecBytes {{ {:?} }}", self.0)
        }
    }

    #[verifier(external_body)]
    impl<'a> std::clone::Clone for Stream<'a> {
        fn clone(&self) -> (res: Self)
            ensures
                self.data == res.data,
                self.start == res.start
        {
            Self {
                data: self.data.clone(),
                start: self.start,
            }
        }
    }

    impl<'a> std::clone::Clone for SerializeStream {
        #[verifier(external_body)]
        fn clone(&self) -> (res: Self)
            ensures
                self.data == res.data,
                self.start == res.start
        {
            Self {
                data: self.data.clone(),
                start: self.start,
            }
        }
    }

    #[verifier(external)]
    impl std::fmt::Debug for ParseError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Eof => write!(f, "Eof"),
                Self::NotEnoughData => write!(f, "NotEnoughData"),
                Self::NegativeIndex => write!(f, "Other"),
                Self::IntegerOverflow => write!(f, "IntegerOverflow"),
                Self::ConstMismatch => write!(f, "ConstMismatch"),
            }
        }
    }

    #[verifier(external)]
    impl std::fmt::Debug for SerializeError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::NotEnoughSpace => write!(f, "NotEnoughSpace"),
                Self::NegativeIndex => write!(f, "NegativeIndex"),
                Self::RepeatNMismatch => write!(f, "RepeatNMismatch"),
                Self::IntegerOverflow => write!(f, "IntegerOverflow"),
                Self::TailLengthMismatch => write!(f, "TailLengthMismatch"),
                Self::ConstMismatch => write!(f, "ConstMismatch"),
                Self::BytesLengthMismatch => write!(f, "BytesLengthMismatch"),
            }
        }
    }

    pub enum Either<A, B> {
        Left(A),
        Right(B),
    }

    impl<A, B> DView for Either<A, B>
        where
            A: DView,
            B: DView,
    {
        type V = Either<A::V, B::V>;
        open spec fn dview(&self) -> Either<A::V, B::V> {
            match self {
                Self::Left(a) => Either::Left(a.dview()),
                Self::Right(b) => Either::Right(b.dview()),
            }
        }
    }

    #[verifier(external)]
    impl<A,B> std::fmt::Debug for Either<A, B>
        where
            A: std::fmt::Debug,
            B: std::fmt::Debug,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Left(a) => write!(f, "Left({:?})", a),
                Self::Right(b) => write!(f, "Right({:?})", b),
            }
        }
    }

}

verus! {

    /// deep view of an exec type
    pub trait DView {
        type V;
        spec fn dview(&self) -> Self::V;
    }

    impl<A: DView> DView for &A {
        type V = A::V;
        #[verifier::inline]
        open spec fn dview(&self) -> A::V {
            (**self).dview()
        }
    }

    impl<A: DView> DView for alloc::boxed::Box<A> {
        type V = A::V;
        #[verifier::inline]
        open spec fn dview(&self) -> A::V {
            (**self).dview()
        }
    }

    impl<A: DView> DView for alloc::rc::Rc<A> {
        type V = A::V;
        #[verifier::inline]
        open spec fn dview(&self) -> A::V {
            (**self).dview()
        }
    }

    impl<A: DView> DView for alloc::sync::Arc<A> {
        type V = A::V;
        #[verifier::inline]
        open spec fn dview(&self) -> A::V {
            (**self).dview()
        }
    }

    macro_rules! declare_identity_view {
        ($t:ty) => {
            #[cfg_attr(verus_keep_ghost, verifier::verify)]
            impl DView for $t {
                type V = $t;
                #[cfg(verus_keep_ghost)]
                #[verus::internal(spec)]
                #[verus::internal(open)]
                #[verifier::inline]
                fn dview(&self) -> $t {
                    *self
                }
            }
        }
    }

    declare_identity_view!(());
    declare_identity_view!(bool);
    declare_identity_view!(u8);
    declare_identity_view!(u16);
    declare_identity_view!(u32);
    declare_identity_view!(u64);
    declare_identity_view!(u128);
    declare_identity_view!(usize);
    declare_identity_view!(i8);
    declare_identity_view!(i16);
    declare_identity_view!(i32);
    declare_identity_view!(i64);
    declare_identity_view!(i128);
    declare_identity_view!(isize);

    macro_rules! declare_tuple_view {
        ([$($n:tt)*], [$($a:ident)*]) => {
            #[cfg_attr(verus_keep_ghost, verifier::verify)]
            impl<$($a: DView, )*> DView for ($($a, )*) {
                type V = ($($a::V, )*);
                #[cfg(verus_keep_ghost)]
                #[verus::internal(spec)]
                #[verus::internal(open)]
                fn dview(&self) -> ($($a::V, )*) {
                    ($(self.$n.dview(), )*)
                }
            }
        }
    }

    declare_tuple_view!([0], [A0]);
    declare_tuple_view!([0 1], [A0 A1]);
    declare_tuple_view!([0 1 2], [A0 A1 A2]);
    declare_tuple_view!([0 1 2 3], [A0 A1 A2 A3]);

    /// deep view of a Vec
    impl<T: DView> DView for Vec<T> {
        type V = Seq<T::V>;
        open spec fn dview(&self) -> Self::V;
    }

    #[verifier::external]
    pub trait VecAdditionalExecFns<T> {
        fn set(&mut self, i: usize, value: T);
        fn set_and_swap(&mut self, i: usize, value: &mut T);
        fn length(&self) -> usize;
    }

    impl<T: DView> VecAdditionalExecFns<T> for Vec<T> {
        /// Replacement for `self[i] = value;` (which Verus does not support for technical reasons)

        #[verifier::external_body]
        fn set(&mut self, i: usize, value: T)
            requires
                i < old(self).dview().len(),
            ensures
                self.dview() == old(self).dview().update(i as int, value.dview()),
        {
            self[i] = value;
        }

        /// Replacement for `swap(&mut self[i], &mut value)` (which Verus does not support for technical reasons)

        #[verifier::external_body]
        fn set_and_swap(&mut self, i: usize, value: &mut T)
            requires
                i < old(self).dview().len(),
            ensures
                value.dview() == old(self).dview().index(i as int)
        {
            core::mem::swap(&mut self[i], value);
        }

        #[verifier::external_body]
        fn length(&self) -> (res: usize)
            ensures
                res == spec_vec_len(self)
        {
            self.len()
        }
    }

    #[verifier::external_body]
    pub fn vec_index<T: DView>(vec: &Vec<T>, i: usize) -> (element: &T)
        requires i < vec.dview().len(),
        ensures element.dview() == vec.dview().index(i as int)
    {
        &vec[i]
    }

    #[verifier::external_body]
    pub fn vec_as_slice<T: DView>(vec: &Vec<T>) -> (slice: &[T])
        ensures slice.dview() == vec.dview()
    {
        vec.as_slice()
    }

    #[verifier::external_body]
    pub fn vec_push<T: DView>(vec: &mut Vec<T>, value: T)
        ensures vec.dview() == old(vec).dview().push(value.dview())
    {
        vec.push(value);
    }

    #[verifier::external_body]
    pub fn vec_new<T: DView>() -> (v: Vec<T>)
        ensures
            v.dview() == Seq::<T::V>::empty(),
    {
        Vec::<T>::new()
    }

    #[verifier::external_body]
    pub fn vec_append<T: DView>(vec: &mut Vec<T>, other: &mut Vec<T>)
        ensures
            vec.dview() == old(vec).dview() + old(other).dview(),
    {
        vec.append(other)
    }

    pub open spec fn spec_vec_len<T: DView>(v: &Vec<T>) -> usize;

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_spec_len<T: DView>(v: &Vec<T>)
        ensures
            #[trigger] spec_vec_len(v) == v.dview().len()
    {}


    impl<T: DView> DView for [T] {
        type V = Seq<T::V>;
        open spec fn dview(&self) -> Self::V;
    }

    impl<T: DView> DView for &[T] {
        type V = Seq<T::V>;
        #[verifier::inline]
        open spec fn dview(&self) -> Self::V {
            (*self).dview()
        }
    }

    #[verifier::external]
    pub trait SliceAdditionalExecFns<T> {
        fn set(&mut self, i: usize, value: T);
        fn length(&self) -> usize;
    }

    impl<T: DView> SliceAdditionalExecFns<T> for [T] {

        /// Replacement for `self[i] = value;` (which Verus does not support for technical reasons)
        #[verifier::external_body]
        fn set(&mut self, i: usize, value: T)
            requires
                i < old(self).dview().len(),
            ensures
                self.dview() == old(self).dview().update(i as int, value.dview()),
        {
            self[i] = value;
        }

        #[verifier::external_body]
        fn length(&self) -> (length: usize)
            ensures
                length >= 0,
                length == self.dview().len()
        {
            self.len()
        }

    }


    #[verifier(external_body)]
    pub exec fn slice_index_get<T: DView>(slice: &[T], i: usize) -> (out: &T)
        requires 0 <= i < slice.dview().len(),
        ensures out.dview() == slice.dview().index(i as int),
    {
        &slice[i]
    }

    #[verifier(external_body)]
    pub exec fn slice_to_vec<T: Copy + DView>(slice: &[T]) -> (out: Vec<T>)
        ensures out.dview() == slice.dview()
    {
        slice.to_vec()
    }

    #[verifier(external_body)]
    pub exec fn slice_subrange<T: DView, 'a>(slice: &'a [T], i: usize, j: usize) -> (out: &'a [T])
        requires 0 <= i <= j <= slice.dview().len()
        ensures out.dview() == slice.dview().subrange(i as int, j as int)
    {
        &slice[i .. j]
    }

    #[verifier(external_body)]
    pub exec fn swap_with_slice<T: DView>(left: &mut [T], right: &mut [T])
        requires
            old(left).dview().len() == old(right).dview().len(),
        ensures
            left.dview() == old(right).dview(),
            right.dview() == old(left).dview(),
    {
        left.swap_with_slice(right)
    }

}

verus! {
    /// A *well-behaved parser* should
    /// 1. keep the input data unchanged
    /// 2. the new start position should be the addition of the old start position and the number of consumed bytes
    /// 3. the old and new start positions should be in range
    pub open spec fn prop_parse_well_behaved_on<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        s: SpecStream) -> bool
    {
        match parser(s) {
            Ok((sout, n, _)) => {
                &&& sout.data == s.data
                &&& s.start + n == sout.start
                &&& 0 <= s.start <= sout.start <= s.data.len()
            }
            Err(_) => true, // vacuously true
        }
    }

    /// A *well-behaved serializer* should
    /// 1. keep the length of the input data unchanged
    /// 2. keep the input data prior to the start position unchanged
    /// 3. keep the input data following serialized data unchanged
    /// 4. the new start position should be the addition of the old start position and the number of serialized bytes
    /// 5. the old and new start positions should be in range
    pub open spec fn prop_serialize_well_behaved_on<R>(
        serializer: spec_fn(SpecStream, R) -> SpecSerializeResult,
s: SpecStream, v: R) -> bool
    {
        if let Ok((sout, n)) = serializer(s, v) {
            &&& sout.data.len() == s.data.len()
            &&& sout.data.subrange(0, s.start) == s.data.subrange(0, s.start)
            &&& sout.data.subrange(s.start + n, s.data.len() as int) == s.data.subrange(s.start + n, s.data.len() as int)
            &&& s.start + n == sout.start
            &&& 0 <= s.start <= sout.start <= s.data.len()
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_serialize_deterministic_on<R>(
        serializer: spec_fn(SpecStream, R) -> SpecSerializeResult,
        s1: SpecStream, s2: SpecStream, v: R) -> bool
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (serializer(s1, v), serializer(s2, v)) {
            n1 == n2 && sout1.data.subrange(s1.start, s1.start + n1) == sout2.data.subrange(s2.start, s2.start + n2)
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_parse_strong_prefix_on<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        s1: SpecStream,
        s2: SpecStream) -> bool
    {
        if let Ok((sout1, n, x1)) = parser(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len() <= usize::MAX
            && 0 <= s2.start <= s2.start + n <= s2.data.len() <= usize::MAX
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = parser(s2) {
                    n == m && x1 == x2
                } else {
                    false
                }
            } else {
                true // vacuously true
            }
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_parse_correct_on<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        serializer: spec_fn(SpecStream, R) -> SpecSerializeResult,
        s: SpecStream, v: R) -> bool
    {
        if let Ok((sout, n)) = serializer(s, v) {
            if let Ok((_, m, res)) = parser(SpecStream {start: s.start, ..sout}) {
                n == m && v == res
            } else {
                false
            }
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_parse_serialize_inverse_on<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        serializer: spec_fn(SpecStream, R) -> SpecSerializeResult,
        s: SpecStream) -> bool
    {
        if let Ok((ss, m, res)) = parser(s) {
            if let Ok((sout, n)) = serializer(s, res) {
                m == n && sout.data == s.data
            } else {
                false
            }
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_parse_nonmalleable_on<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        s1: SpecStream,
        s2: SpecStream) -> bool
    {
        if let (Ok((sout1, n, x1)), Ok((sout2, m, x2))) = (parser(s1), parser(s2)) {
            x1 == x2 ==> n == m && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + m)
        } else {
            true // vacuously true
        }
    }

    /// An `exec` parser is equivalent to a `spec` parser if
    ///
    /// 1. on the same input stream, they both success and produce the same result,
    /// including the output stream, the number of consumed bytes and the result value
    /// 2. or they both fail and throw the same error.
    pub open spec fn prop_parse_exec_spec_equiv_on<T: DView>(
        s: Stream,
        res: ParseResult<T>,
        spec_parser: spec_fn(SpecStream) -> SpecParseResult<T::V>) -> bool
    {
        match spec_parser(s.dview()) {
            Ok((sout, sn, sx)) => {
                if let Ok((s, n, x)) = res {
                    &&& s.dview() == sout
                    &&& n == sn
                    &&& x.dview() == sx
                } else {
                    false
                }
            }
            Err(e) => {
                if let Err(e2) = res {
                    e == e2
                } else {
                    false
                }
            }
        }
    }

    /// An `exec` serializer is equivalent to a `spec` serializer if
    ///
    /// 1. on the same input stream and value, they both success and produce the same result
    /// 2. or they both fail and throw the same error.
    pub open spec fn prop_serialize_exec_spec_equiv_on<T>(
        old_data: Seq<u8>, start: usize, new_data: Seq<u8>,
        v: T,
        res: SerializeResult,
        spec_serializer: spec_fn(SpecStream, T) -> SpecSerializeResult) -> bool
    {
        match spec_serializer(SpecStream {
            data: old_data,
            start: start as int,
        }, v) {
            Ok((sout, sn)) => {
                &&& res.is_ok()
                &&& res.unwrap().1 == sn
                &&& res.unwrap().0 as int == sout.start
                &&& new_data == sout.data
            }
            Err(e) => res.is_err() && res.unwrap_err() == e
        }
    }

    // prevent the body from seen
    #[verifier(opaque)]
    pub open spec fn prop_parse_well_behaved<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>) -> bool
    {
        forall |s: SpecStream| prop_parse_well_behaved_on(parser, s)
    }

    #[verifier(opaque)]
    pub open spec fn prop_serialize_well_behaved<T>(serializer: spec_fn(SpecStream, T) -> SpecSerializeResult) -> bool
    {
        forall |s: SpecStream, v: T| prop_serialize_well_behaved_on(serializer, s, v)
    }

    #[verifier(opaque)]
    pub open spec fn prop_serialize_deterministic<R>(serializer: spec_fn(SpecStream, R) -> SpecSerializeResult) -> bool
    {
        forall |s1: SpecStream, s2: SpecStream, v: R| prop_serialize_deterministic_on(serializer, s1, s2, v)
    }

    #[verifier(opaque)]
    pub open spec fn prop_parse_strong_prefix<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>) -> bool
    {
        forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(parser, s1, s2)
    }

    #[verifier(opaque)]
    pub open spec fn prop_parse_correct<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>, serializer: spec_fn(SpecStream, T) -> SpecSerializeResult) -> bool
    {
        forall |s: SpecStream, v: T| s.data.len() <= usize::MAX ==> prop_parse_correct_on(parser, serializer, s, v)
    }

    #[verifier(opaque)]
    pub open spec fn prop_parse_serialize_inverse<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>, serializer: spec_fn(SpecStream, T) -> SpecSerializeResult) -> bool
    {
        forall |s: SpecStream| prop_parse_serialize_inverse_on(parser, serializer, s)
    }

    #[verifier(opaque)]
    /// this property can actually be derived from the parse_serialize_inverse property (with deterministic serializers)
    /// ∀ s. serialize(parse(s)) == s
    /// ==>
    /// ∀ s1 s2.
    /// &&& serialize(parse(s1)) == s1 && serialize(parse(s2)) == s2
    /// &&& (parse(s1) == parse(s2) <==> serialize(parse(s1)) == serialize(parse(s2)) ==> s1 == s2)
    pub open spec fn prop_parse_nonmalleable<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>) -> bool
    {
        forall |s1: SpecStream, s2: SpecStream| prop_parse_nonmalleable_on(parser, s1, s2)
    }

    pub proof fn lemma_parse_serialize_inverse_implies_nonmalleable<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>, serializer: spec_fn(SpecStream, T) -> SpecSerializeResult)
        requires
            prop_parse_serialize_inverse(parser, serializer),
            prop_serialize_deterministic(serializer)
        ensures
            prop_parse_nonmalleable(parser)
    {
        reveal(prop_parse_serialize_inverse);
        reveal(prop_parse_nonmalleable);
        reveal(prop_serialize_deterministic);
        assert forall |s1: SpecStream, s2: SpecStream| prop_parse_nonmalleable_on(parser, s1, s2) by {
            lemma_parse_serialize_inverse_on(parser, serializer, s1);
            lemma_parse_serialize_inverse_on(parser, serializer, s2);
            if let (Ok((sout1, n1, x1)), Ok((sout2, n2, x2))) = (parser(s1), parser(s2)) {
                if x1 == x2 {
                    lemma_serialize_deterministic_on(serializer, s1, s2, x1);
                    assert(n1 == n2);
                    assert(s1.data.subrange(s1.start, s1.start + n1) =~= s2.data.subrange(s2.start, s2.start + n2));
                }
            }
        }
    }

    #[verifier(opaque)]
    pub open spec fn prop_parse_exec_spec_equiv<'a, T, P>(
        exec_parser: P,
        spec_parser: spec_fn(SpecStream) -> SpecParseResult<T::V>) -> bool
        where
            P: FnOnce(Stream<'a>) -> ParseResult<T>,
            T: DView,
    {
        &&& forall |s| #[trigger] exec_parser.requires((s,))
        &&& forall |s, res| #[trigger] exec_parser.ensures((s,), res) ==> prop_parse_exec_spec_equiv_on(s, res, spec_parser)
    }

    // #[verifier(opaque)]
    // pub open spec fn prop_serialize_exec_spec_equiv<T, P>(
    //     exec_serializer: P,
    //     spec_serializer: spec_fn(SpecStream, T::V) -> SpecSerializeResult) -> bool
    //     where
    //         P: FnOnce(SerializeStream, T) -> SerializeResult,
    //         T: std::fmt::Debug + DView,
    // {
    //     &&& forall |s, v| #[trigger] exec_serializer.requires((s, v))
    //     &&& forall |s, v, res| #[trigger] exec_serializer.ensures((s, v), res) ==> prop_serialize_exec_spec_equiv_on(s, v, res, spec_serializer)
    // }

    // for performance boost
    pub proof fn lemma_parse_well_behaved_on<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>, s: SpecStream)
        requires
            prop_parse_well_behaved(parser)
        ensures
            prop_parse_well_behaved_on(parser, s)
    {
        reveal(prop_parse_well_behaved);
    }

    pub proof fn lemma_serialize_well_behaved_on<T>(serializer: spec_fn(SpecStream, T) -> SpecSerializeResult, s: SpecStream, v: T)
        requires
            prop_serialize_well_behaved(serializer)
        ensures
            prop_serialize_well_behaved_on(serializer, s, v)
    {
        reveal(prop_serialize_well_behaved);
    }

    pub proof fn lemma_serialize_deterministic_on<T>(serializer: spec_fn(SpecStream, T) -> SpecSerializeResult, s1: SpecStream, s2: SpecStream, v: T)
        requires
            prop_serialize_deterministic(serializer)
        ensures
            prop_serialize_deterministic_on(serializer, s1, s2, v)
    {
        reveal(prop_serialize_deterministic);
    }

    pub proof fn lemma_parse_strong_prefix_on<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>, s1: SpecStream, s2: SpecStream)
        requires
            prop_parse_strong_prefix(parser)
        ensures
            prop_parse_strong_prefix_on(parser, s1, s2)
    {
        reveal(prop_parse_strong_prefix);
    }

    pub proof fn lemma_parse_correct_on<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>, serializer: spec_fn(SpecStream, T) -> SpecSerializeResult, s: SpecStream, v: T)
        requires
            prop_parse_correct(parser, serializer)
        ensures
            s.data.len() <= usize::MAX ==> prop_parse_correct_on(parser, serializer, s, v)
    {
        reveal(prop_parse_correct);
    }

    pub proof fn lemma_parse_serialize_inverse_on<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>, serializer: spec_fn(SpecStream, T) -> SpecSerializeResult, s: SpecStream)
        requires
            prop_parse_serialize_inverse(parser, serializer)
        ensures
            prop_parse_serialize_inverse_on(parser, serializer, s)
    {
        reveal(prop_parse_serialize_inverse);
    }

    pub proof fn lemma_parse_nonmalleable_on<T>(parser: spec_fn(SpecStream) -> SpecParseResult<T>, serializer: spec_fn(SpecStream, T) -> SpecSerializeResult, s1: SpecStream, s2: SpecStream)
        requires
            prop_parse_nonmalleable(parser)
        ensures
            prop_parse_nonmalleable_on(parser, s1, s2)
    {
        reveal(prop_parse_nonmalleable);
    }

    pub proof fn lemma_parse_exec_spec_equiv_on<'a, T, P>(
        exec_parser: P,
        spec_parser: spec_fn(SpecStream) -> SpecParseResult<T::V>,
        s: Stream, res: ParseResult<T>)
        where
            P: FnOnce(Stream<'a>) -> ParseResult<T>,
            T: DView,
        requires
            prop_parse_exec_spec_equiv(exec_parser, spec_parser),
            exec_parser.ensures((s,), res)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, spec_parser)
    {
        reveal(prop_parse_exec_spec_equiv);
    }

    // pub proof fn lemma_serialize_exec_spec_equiv_on<T, P>(
    //     exec_serializer: P,
    //     spec_serializer: spec_fn(SpecStream, T::V) -> SpecSerializeResult,
    //     s: SerializeStream, v: T, res: SerializeResult)
    //     where
    //         P: FnOnce(SerializeStream, T) -> SerializeResult,
    //         T: std::fmt::Debug + DView,
    //     requires
    //         prop_serialize_exec_spec_equiv(exec_serializer, spec_serializer),
    //         exec_serializer.ensures((s, v), res)
    //     ensures
    //         prop_serialize_exec_spec_equiv_on(s, v, res, spec_serializer)
    // {
    //     reveal(prop_serialize_exec_spec_equiv);
    // }
}

verus! {

    pub open spec fn spec_parse_u8_le(s: SpecStream) -> (res: SpecParseResult<u8>)
        recommends
            0 <= s.start < s.data.len(),
            s.data.len() >= 1
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 1 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 1,
                    ..s
                },
                1,
                s.data[s.start],
            ))
        }
    }

    pub open spec fn spec_parse_u16_le(s: SpecStream) -> (res: SpecParseResult<u16>)
        recommends
            0 <= s.start < s.data.len() - 1,
            s.data.len() >= 2
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 2 || s.start >= s.data.len() - 1 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 2,
                    ..s
                },
                2,
                spec_u16_from_le_bytes(
                    s.data.subrange(s.start, s.start + 2)
                )
            ))
        }
    }

    pub open spec fn spec_parse_u32_le(s: SpecStream) -> (res: SpecParseResult<u32>)
        recommends
            0 <= s.start < s.data.len() - 3,
            s.data.len() >= 4
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 4 || s.start >= s.data.len() - 3 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 4,
                    ..s
                },
                4,
                spec_u32_from_le_bytes(
                    s.data.subrange(s.start, s.start + 4)
                )
            ))
        }
    }

    pub open spec fn spec_parse_u64_le(s: SpecStream) -> (res: SpecParseResult<u64>)
        recommends
            0 <= s.start < s.data.len() - 7,
            s.data.len() >= 8
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 8 || s.start >= s.data.len() - 7 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 8,
                    ..s
                },
                8,
                spec_u64_from_le_bytes(
                    s.data.subrange(s.start, s.start + 8)
                )
            ))
        }
    }

    pub open spec fn spec_serialize_u8_le(s: SpecStream, v: u8) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len(),
            s.data.len() >= 1
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 1 || s.start >= s.data.len() {
            Err(SerializeError::NotEnoughSpace)
        } else {
            Ok((
                SpecStream {
                    data: s.data.update(s.start, v),
                    start: s.start + 1,
                },
                1
            ))
        }
    }

    pub open spec fn spec_serialize_u16_le(s: SpecStream, v: u16) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len() - 1,
            s.data.len() >= 2
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 2 || s.start >= s.data.len() - 1 {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let data = spec_u16_to_le_bytes(v);
            Ok((
                SpecStream {
                    data: s.data.update(s.start, data[0])
                                .update(s.start + 1, data[1]),
                    start: s.start + 2,
                },
                2
            ))
        }
    }

    pub open spec fn spec_serialize_u32_le(s: SpecStream, v: u32) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len() - 3,
            s.data.len() >= 4
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 4 || s.start >= s.data.len() - 3 {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let data = spec_u32_to_le_bytes(v);
            Ok((
                SpecStream {
                    data: s.data.update(s.start, data[0])
                                .update(s.start + 1, data[1])
                                .update(s.start + 2, data[2])
                                .update(s.start + 3, data[3]),
                    start: s.start + 4,
                },
                4
            ))
        }
    }

    pub open spec fn spec_serialize_u64_le(s: SpecStream, v: u64) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len() - 7,
            s.data.len() >= 8
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 8 || s.start >= s.data.len() - 7 {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let data = spec_u64_to_le_bytes(v);
            Ok((
                SpecStream {
                    data: s.data.update(s.start, data[0])
                                .update(s.start + 1, data[1])
                                .update(s.start + 2, data[2])
                                .update(s.start + 3, data[3])
                                .update(s.start + 4, data[4])
                                .update(s.start + 5, data[5])
                                .update(s.start + 6, data[6])
                                .update(s.start + 7, data[7]),
                    start: s.start + 8,
                },
                8
            ))
        }
    }


    pub exec fn parse_u8_le(s: Stream) -> (res: ParseResult<u8>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 1 {
            Err(ParseError::NotEnoughData)
        } else {
            let v = *slice_index_get(s.data, s.start); // &s.data[s.start];
            Ok((
                Stream {
                    start: s.start + 1,
                    ..s
                },
                1,
                v
            ))
        }
    }

    pub exec fn parse_u16_le(s: Stream) -> (res: ParseResult<u16>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u16_le(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 2 || s.start >= s.data.length() - 1 {
            Err(ParseError::NotEnoughData)
        } else {
            let data = slice_subrange(s.data, s.start, s.start + 2); // &s.data[s.start..s.start + 2];
            let v = u16_from_le_bytes(data);
            Ok((
                Stream {
                    start: s.start + 2,
                    ..s
                },
                2,
                v
            ))
        }
    }

    pub exec fn parse_u32_le(s: Stream) -> (res: ParseResult<u32>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u32_le(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 4 || s.start >= s.data.length() - 3 {
            Err(ParseError::NotEnoughData)
        } else {
            let data = slice_subrange(s.data, s.start, s.start + 4); // &s.data[s.start..s.start + 4];
            let v = u32_from_le_bytes(data);
            Ok((
                Stream {
                    start: s.start + 4,
                    ..s
                },
                4,
                v
            ))
        }
    }

    pub exec fn parse_u64_le(s: Stream) -> (res: ParseResult<u64>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u64_le(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 8 || s.start >= s.data.length() - 7 {
            Err(ParseError::NotEnoughData)
        } else {
            let data = slice_subrange(&s.data, s.start, s.start + 8); // &s.data[s.start..s.start + 8];
            let v = u64_from_le_bytes(data);
            Ok((
                Stream {
                    start: s.start + 8,
                    ..s
                },
                8,
                v
            ))
        }
    }

    pub exec fn serialize_u8_le(data: &mut [u8], start: usize, v: u8) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v, res, |s, v| spec_serialize_u8_le(s, v))
    {
        if start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if data.length() < 1 || start >= data.length() {
            Err(SerializeError::NotEnoughSpace)
        } else {
            data.set(start, v);
            Ok((
                start + 1,
                1
            ))
        }
    }

    pub exec fn serialize_u16_le(data: &mut [u8], start: usize, v: u16) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v, res, |s, v| spec_serialize_u16_le(s, v))
    {
        if start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if data.length() < 2 || start >= data.length() - 1  {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let bytes = u16_to_le_bytes(v);
            data.set(start, *vec_index(&bytes, 0)); // data[start] = bytes[0];
            data.set(start + 1, *vec_index(&bytes, 1)); // data[start + 1] = bytes[1];
            Ok((
                start + 2,
                2
            ))
        }
    }

    pub exec fn serialize_u32_le(data: &mut [u8], start: usize, v: u32) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v, res, |s, v| spec_serialize_u32_le(s, v))
    {
        if start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if data.length() < 4 || start >= data.length() - 3  {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let bytes = u32_to_le_bytes(v);
            data.set(start, *vec_index(&bytes, 0)); // data[start] = bytes[0];
            data.set(start + 1, *vec_index(&bytes, 1)); // data[start + 1] = bytes[1];
            data.set(start + 2, *vec_index(&bytes, 2)); // data[start + 2] = bytes[2];
            data.set(start + 3, *vec_index(&bytes, 3)); // data[start + 3] = bytes[3];
            Ok((
                start + 4,
                4
            ))
        }
    }

    pub exec fn serialize_u64_le(data: &mut [u8], start: usize, v: u64) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v, res, |s, v| spec_serialize_u64_le(s, v))
    {
        if start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if data.length() < 8 || start >= data.length() - 7  {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let bytes = u64_to_le_bytes(v);
            data.set(start, *vec_index(&bytes, 0));
            data.set(start + 1, *vec_index(&bytes, 1));
            data.set(start + 2, *vec_index(&bytes, 2));
            data.set(start + 3, *vec_index(&bytes, 3));
            data.set(start + 4, *vec_index(&bytes, 4));
            data.set(start + 5, *vec_index(&bytes, 5));
            data.set(start + 6, *vec_index(&bytes, 6));
            data.set(start + 7, *vec_index(&bytes, 7));
            Ok((
                start + 8,
                8
            ))
        }
    }

    pub proof fn lemma_parse_u8_le_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u8_le(s))
    {
        reveal(prop_parse_well_behaved::<u8>);
        let spec_parse_u8_le = |s| spec_parse_u8_le(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u8_le, s) by {
            lemma_parse_u8_le_well_behaved_on(s)
        }
    }

    pub proof fn lemma_parse_u16_le_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u16_le(s))
    {
        reveal(prop_parse_well_behaved::<u16>);
        let spec_parse_u16_le = |s| spec_parse_u16_le(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u16_le, s) by {
            lemma_parse_u16_le_well_behaved_on(s)
        }
    }

    pub proof fn lemma_parse_u32_le_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u32_le(s))
    {
        reveal(prop_parse_well_behaved::<u32>);
        let spec_parse_u32_le = |s| spec_parse_u32_le(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u32_le, s) by {
            lemma_parse_u32_le_well_behaved_on(s)
        }
    }

    pub proof fn lemma_parse_u64_le_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u64_le(s))
    {
        reveal(prop_parse_well_behaved::<u64>);
        let spec_parse_u64_le = |s| spec_parse_u64_le(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u64_le, s) by {
            lemma_parse_u64_le_well_behaved_on(s)
        }
    }

    pub proof fn lemma_serialize_u8_le_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u8_le(s, v))
    {
        reveal(prop_serialize_well_behaved::<u8>);
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u8_le, s, v) by {
            lemma_serialize_u8_le_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u16_le_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u16_le(s, v))
    {
        reveal(prop_serialize_well_behaved::<u16>);
        let spec_serialize_u16_le = |s, v| spec_serialize_u16_le(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u16_le, s, v) by {
            lemma_serialize_u16_le_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u32_le_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u32_le(s, v))
    {
        reveal(prop_serialize_well_behaved::<u32>);
        let spec_serialize_u32_le = |s, v| spec_serialize_u32_le(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u32_le, s, v) by {
            lemma_serialize_u32_le_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u64_le_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u64_le(s, v))
    {
        reveal(prop_serialize_well_behaved::<u64>);
        let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u64_le, s, v) by {
            lemma_serialize_u64_le_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u8_le_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_u8_le(s, v))
    {
        reveal(prop_serialize_deterministic::<u8>);
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u8_le, s1, s2, v) by {
            lemma_serialize_u8_le_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_serialize_u16_le_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_u16_le(s, v))
    {
        reveal(prop_serialize_deterministic::<u16>);
        let spec_serialize_u16_le = |s, v| spec_serialize_u16_le(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u16_le, s1, s2, v) by {
            lemma_serialize_u16_le_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_serialize_u32_le_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_u32_le(s, v))
    {
        reveal(prop_serialize_deterministic::<u32>);
        let spec_serialize_u32_le = |s, v| spec_serialize_u32_le(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u32_le, s1, s2, v) by {
            lemma_serialize_u32_le_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_serialize_u64_le_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_u64_le(s, v))
    {
        reveal(prop_serialize_deterministic::<u64>);
        let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u64_le, s1, s2, v) by {
            lemma_serialize_u64_le_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_parse_u8_le_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u8_le(s))
    {
        reveal(prop_parse_strong_prefix::<u8>);
        let spec_parse_u8_le = |s| spec_parse_u8_le(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u8_le, s1, s2) by {
            lemma_parse_u8_le_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u16_le_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u16_le(s))
    {
        reveal(prop_parse_strong_prefix::<u16>);
        let spec_parse_u16_le = |s| spec_parse_u16_le(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u16_le, s1, s2) by {
            lemma_parse_u16_le_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u32_le_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u32_le(s))
    {
        reveal(prop_parse_strong_prefix::<u32>);
        let spec_parse_u32_le = |s| spec_parse_u32_le(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u32_le, s1, s2) by {
            lemma_parse_u32_le_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u64_le_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u64_le(s))
    {
        reveal(prop_parse_strong_prefix::<u64>);
        let spec_parse_u64_le = |s| spec_parse_u64_le(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u64_le, s1, s2) by {
            lemma_parse_u64_le_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u8_le_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v))
    {
        reveal(prop_parse_correct::<u8>);
        let spec_parse_u8_le = |s| spec_parse_u8_le(s);
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u8_le, spec_serialize_u8_le, s, v) by {
            lemma_parse_u8_le_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u16_le_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v))
    {
        reveal(prop_parse_correct::<u16>);
        let spec_parse_u16_le = |s| spec_parse_u16_le(s);
        let spec_serialize_u16_le = |s, v| spec_serialize_u16_le(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u16_le, spec_serialize_u16_le, s, v) by {
            lemma_parse_u16_le_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u32_le_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v))
    {
        reveal(prop_parse_correct::<u32>);
        let spec_parse_u32_le = |s| spec_parse_u32_le(s);
        let spec_serialize_u32_le = |s, v| spec_serialize_u32_le(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u32_le, spec_serialize_u32_le, s, v) by {
            lemma_parse_u32_le_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u64_le_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v))
    {
        reveal(prop_parse_correct::<u64>);
        let spec_parse_u64_le = |s| spec_parse_u64_le(s);
        let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u64_le, spec_serialize_u64_le, s, v) by {
            lemma_parse_u64_le_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u8_le_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u8>);
        let spec_parse_u8_le = |s| spec_parse_u8_le(s);
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, s) by {
            lemma_parse_u8_le_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u16_le_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u16>);
        let spec_parse_u16_le = |s| spec_parse_u16_le(s);
        let spec_serialize_u16_le = |s, v| spec_serialize_u16_le(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u16_le, spec_serialize_u16_le, s) by {
            lemma_parse_u16_le_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u32_le_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u32>);
        let spec_parse_u32_le = |s| spec_parse_u32_le(s);
        let spec_serialize_u32_le = |s, v| spec_serialize_u32_le(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u32_le, spec_serialize_u32_le, s) by {
            lemma_parse_u32_le_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u64_le_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u64>);
        let spec_parse_u64_le = |s| spec_parse_u64_le(s);
        let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u64_le, spec_serialize_u64_le, s) by {
            lemma_parse_u64_le_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u8_le_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_u8_le(s))
    {
        lemma_parse_u8_le_serialize_inverse();
        lemma_serialize_u8_le_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v));
    }

    pub proof fn lemma_parse_u16_le_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_u16_le(s))
    {
        lemma_parse_u16_le_serialize_inverse();
        lemma_serialize_u16_le_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v));
    }

    pub proof fn lemma_parse_u32_le_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_u32_le(s))
    {
        lemma_parse_u32_le_serialize_inverse();
        lemma_serialize_u32_le_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v));
    }

    pub proof fn lemma_parse_u64_le_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_u64_le(s))
    {
        lemma_parse_u64_le_serialize_inverse();
        lemma_serialize_u64_le_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v));
    }

    pub proof fn lemma_parse_u8_le_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u8_le(s), s)
    {}

    pub proof fn lemma_parse_u16_le_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u16_le(s), s)
    {}

    pub proof fn lemma_parse_u32_le_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u32_le(s), s)
    {}

    pub proof fn lemma_parse_u64_le_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u64_le(s), s)
    {}

    pub proof fn lemma_parse_u8_le_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u8_le(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u8_le(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u8_le(s2) {
                    assert(n == 1);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            s1.data[s1.start]; {}
                            s1.data.subrange(s1.start, s1.start + 1)[0]; {}
                            s2.data.subrange(s2.start, s2.start + 1)[0]; {}
                            s2.data[s2.start]; {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_u16_le_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u16_le(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u16_le(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u16_le(s2) {
                    assert(n == 2);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            spec_u16_from_le_bytes(s1.data.subrange(s1.start, s1.start + 2)); {}
                            spec_u16_from_le_bytes(s2.data.subrange(s2.start, s2.start + 2)); {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_u32_le_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u32_le(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u32_le(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u32_le(s2) {
                    assert(n == 4);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            spec_u32_from_le_bytes(s1.data.subrange(s1.start, s1.start + 4)); {}
                            spec_u32_from_le_bytes(s2.data.subrange(s2.start, s2.start + 4)); {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_u64_le_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u64_le(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u64_le(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u64_le(s2) {
                    assert(n == 8);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            spec_u64_from_le_bytes(s1.data.subrange(s1.start, s1.start + 8)); {}
                            spec_u64_from_le_bytes(s2.data.subrange(s2.start, s2.start + 8)); {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_serialize_u8_le_well_behaved_on(s: SpecStream, v: u8)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u8_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u8_le(s, v) {
            assert(n == 1 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 1, s.data.len() as int) =~= s.data.subrange(s.start + 1, s.data.len() as int));
        }
    }

    pub proof fn lemma_serialize_u16_le_well_behaved_on(s: SpecStream, v: u16)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u16_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u16_le(s, v) {
            lemma_auto_spec_u16_to_from_le_bytes();
            assert(n == 2 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 2, s.data.len() as int) =~= s.data.subrange(s.start + 2, s.data.len() as int));
        }
    }

    pub proof fn lemma_serialize_u32_le_well_behaved_on(s: SpecStream, v: u32)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u32_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u32_le(s, v) {
            lemma_auto_spec_u32_to_from_le_bytes();
            assert(n == 4 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 4, s.data.len() as int) =~= s.data.subrange(s.start + 4, s.data.len() as int));
        }
    }

    pub proof fn lemma_serialize_u64_le_well_behaved_on(s: SpecStream, v: u64)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u64_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u64_le(s, v) {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(n == 8 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 8, s.data.len() as int) =~= s.data.subrange(s.start + 8, s.data.len() as int));
        }
    }

    pub proof fn lemma_serialize_u8_le_deterministic_on(s1: SpecStream, s2: SpecStream, v: u8)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_u8_le(s, v), s1, s2, v)
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_u8_le(s1, v), spec_serialize_u8_le(s2, v)) {
            assert(n1 == 1 && n2 == 1);
            assert(sout1.data.subrange(s1.start, s1.start + 1) =~= sout2.data.subrange(s2.start, s2.start + 1));
        }
    }

    pub proof fn lemma_serialize_u16_le_deterministic_on(s1: SpecStream, s2: SpecStream, v: u16)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_u16_le(s, v), s1, s2, v)
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_u16_le(s1, v), spec_serialize_u16_le(s2, v)) {
            lemma_auto_spec_u16_to_from_le_bytes();
            assert(n1 == 2 && n2 == 2);
            assert(sout1.data.subrange(s1.start, s1.start + 2) =~= sout2.data.subrange(s2.start, s2.start + 2));
        }
    }

    pub proof fn lemma_serialize_u32_le_deterministic_on(s1: SpecStream, s2: SpecStream, v: u32)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_u32_le(s, v), s1, s2, v)
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_u32_le(s1, v), spec_serialize_u32_le(s2, v)) {
            lemma_auto_spec_u32_to_from_le_bytes();
            assert(n1 == 4 && n2 == 4);
            assert(sout1.data.subrange(s1.start, s1.start + 4) =~= sout2.data.subrange(s2.start, s2.start + 4));
        }
    }

    pub proof fn lemma_serialize_u64_le_deterministic_on(s1: SpecStream, s2: SpecStream, v: u64)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_u64_le(s, v), s1, s2, v)
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_u64_le(s1, v), spec_serialize_u64_le(s2, v)) {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(n1 == 8 && n2 == 8);
            assert(sout1.data.subrange(s1.start, s1.start + 8) =~= sout2.data.subrange(s2.start, s2.start + 8));
        }
    }

    pub proof fn lemma_parse_u8_le_correct_on(s: SpecStream, v: u8)
        ensures
            prop_parse_correct_on(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v), s, v)
    {}

    pub proof fn lemma_parse_u16_le_correct_on(s: SpecStream, v: u16)
        ensures
            prop_parse_correct_on(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u16_le(s, v) {
            assert(sout.data.len() == s.data.len()) by { lemma_serialize_u16_le_well_behaved_on(s, v)}
            if let Ok((_, m, res)) = spec_parse_u16_le(SpecStream {start: s.start, ..sout}) {
                lemma_auto_spec_u16_to_from_le_bytes();
                assert(n == m);
                assert(res == spec_u16_from_le_bytes(sout.data.subrange(s.start, s.start + 2)));
                assert(sout.data.subrange(s.start, s.start + 2) =~= spec_u16_to_le_bytes(v));
                assert(v =~= res);
            }
        }
    }

    pub proof fn lemma_parse_u32_le_correct_on(s: SpecStream, v: u32)
        ensures
            prop_parse_correct_on(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u32_le(s, v) {
            assert(sout.data.len() == s.data.len()) by { lemma_serialize_u32_le_well_behaved_on(s, v)}
            if let Ok((_, m, res)) = spec_parse_u32_le(SpecStream {start: s.start, ..sout}) {
                lemma_auto_spec_u32_to_from_le_bytes();
                assert(n == m);
                assert(res == spec_u32_from_le_bytes(sout.data.subrange(s.start, s.start + 4)));
                assert(sout.data.subrange(s.start, s.start + 4) =~= spec_u32_to_le_bytes(v));
                assert(v =~= res);
            }
        }
    }

    pub proof fn lemma_parse_u64_le_correct_on(s: SpecStream, v: u64)
        ensures
            prop_parse_correct_on(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u64_le(s, v) {
            assert(sout.data.len() == s.data.len()) by { lemma_serialize_u64_le_well_behaved_on(s, v)}
            if let Ok((_, m, res)) = spec_parse_u64_le(SpecStream {start: s.start, ..sout}) {
                lemma_auto_spec_u64_to_from_le_bytes();
                assert(n == m);
                assert(res == spec_u64_from_le_bytes(sout.data.subrange(s.start, s.start + 8)));
                assert(sout.data.subrange(s.start, s.start + 8) =~= spec_u64_to_le_bytes(v));
                assert(v =~= res);
            }
        }
    }

    pub proof fn lemma_parse_u8_le_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u8_le(s) {
            if let Ok((sout, n)) = spec_serialize_u8_le(s, res) {
                assert(n == m && sout.data =~= s.data);
            }
        }
    }

    pub proof fn lemma_parse_u16_le_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u16_le(s) {
            if let Ok((sout, n)) = spec_serialize_u16_le(s, res) {
                assert(n == m && sout.data =~= s.data) by {
                    lemma_auto_spec_u16_to_from_le_bytes();
                }
            }
        }
    }

    pub proof fn lemma_parse_u32_le_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u32_le(s) {
            if let Ok((sout, n)) = spec_serialize_u32_le(s, res) {
                assert(n == m && sout.data =~= s.data) by {
                    lemma_auto_spec_u32_to_from_le_bytes();
                }
            }
        }
    }

    pub proof fn lemma_parse_u64_le_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u64_le(s) {
            if let Ok((sout, n)) = spec_serialize_u64_le(s, res) {
                assert(n == m && sout.data =~= s.data) by {
                    lemma_auto_spec_u64_to_from_le_bytes();
                }
            }
        }
    }

// Conversion between u16 and little-endian byte sequences

pub closed spec fn spec_u16_to_le_bytes(x: u16) -> Seq<u8>
{
  seq![
    (x & 0xff) as u8,
    ((x >> 8) & 0xff) as u8
  ]
}

pub closed spec fn spec_u16_from_le_bytes(s: Seq<u8>) -> u16
  recommends s.len() == 2
{
  (s[0] as u16) |
  (s[1] as u16) << 8
}

pub proof fn lemma_auto_spec_u16_to_from_le_bytes()
  ensures
    forall |x: u16|
    {
      &&& #[trigger] spec_u16_to_le_bytes(x).len() == 2
      &&& spec_u16_from_le_bytes(spec_u16_to_le_bytes(x)) == x
    },
    forall |s: Seq<u8>|
      s.len() == 2 ==> #[trigger] spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s,
{
  assert forall |x: u16|  {
    &&& #[trigger] spec_u16_to_le_bytes(x).len() == 2
    &&& spec_u16_from_le_bytes(spec_u16_to_le_bytes(x)) == x
  } by {
    let s = spec_u16_to_le_bytes(x);
    assert({
      &&& x & 0xff < 256
      &&& (x >> 8) & 0xff < 256
    }) by (bit_vector);

    assert(x == (
      (x & 0xff) |
      ((x >> 8) & 0xff) << 8)) by (bit_vector);
  };

  assert forall |s: Seq<u8>| s.len() == 2 implies #[trigger] spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s by {
    let x = spec_u16_from_le_bytes(s);
    let s0 = s[0] as u16;
    let s1 = s[1] as u16;

    assert(
      (
        (x == s0 | s1 << 8) &&
        (s0 < 256) &&
        (s1 < 256)
      ) ==>
      s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff)
    ) by (bit_vector);

    assert_seqs_equal!(spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s);
  }
}

#[verifier(external_body)]
pub exec fn u16_from_le_bytes(s: &[u8]) -> (x:u16)
  requires s.dview().len() == 2,
  ensures x == spec_u16_from_le_bytes(s.dview()),
{
  use core::convert::TryInto;
  u16::from_le_bytes(s.try_into().unwrap())
}


#[verifier(external_body)]
pub exec fn u16_to_le_bytes(x: u16) -> (s: alloc::vec::Vec<u8>)
  ensures
    s.dview() == spec_u16_to_le_bytes(x),
    s.dview().len() == 2,
{
  x.to_le_bytes().to_vec()
}

// Conversion between u32 and little-endian byte sequences

pub closed spec fn spec_u32_to_le_bytes(x: u32) -> Seq<u8>
{
  seq![
    (x & 0xff) as u8,
    ((x >> 8) & 0xff) as u8,
    ((x >> 16) & 0xff) as u8,
    ((x >> 24) & 0xff) as u8,
  ]
}

pub closed spec fn spec_u32_from_le_bytes(s: Seq<u8>) -> u32
  recommends s.len() == 4
{
  (s[0] as u32) |
  (s[1] as u32) << 8 |
  (s[2] as u32) << 16 |
  (s[3] as u32) << 24
}

#[verifier::spinoff_prover]
pub proof fn lemma_auto_spec_u32_to_from_le_bytes()
  ensures
    forall |x: u32|
    {
      &&& #[trigger] spec_u32_to_le_bytes(x).len() == 4
      &&& spec_u32_from_le_bytes(spec_u32_to_le_bytes(x)) == x
    },
    forall |s: Seq<u8>|
      s.len() == 4 ==> #[trigger] spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s,
{
  assert forall |x: u32|  {
    &&& #[trigger] spec_u32_to_le_bytes(x).len() == 4
    &&& spec_u32_from_le_bytes(spec_u32_to_le_bytes(x)) == x
  } by {
    let s = spec_u32_to_le_bytes(x);
    assert({
      &&& x & 0xff < 256
      &&& (x >> 8) & 0xff < 256
      &&& (x >> 16) & 0xff < 256
      &&& (x >> 24) & 0xff < 256
    }) by (bit_vector);

    assert(x == (
      (x & 0xff) |
      ((x >> 8) & 0xff) << 8 |
      ((x >> 16) & 0xff) << 16 |
      ((x >> 24) & 0xff) << 24)) by (bit_vector);
  };

  assert forall |s: Seq<u8>| s.len() == 4 implies #[trigger] spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s by {
    let x = spec_u32_from_le_bytes(s);
    let s0 = s[0] as u32;
    let s1 = s[1] as u32;
    let s2 = s[2] as u32;
    let s3 = s[3] as u32;

    assert(
      (
        (x == s0 | s1 << 8 | s2 << 16 | s3 << 24) &&
        (s0 < 256) &&
        (s1 < 256) &&
        (s2 < 256) &&
        (s3 < 256)
      ) ==>
      s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff) && s2 == ((x >> 16) & 0xff) && s3 == ((x >> 24) & 0xff)
    ) by (bit_vector);

    assert_seqs_equal!(spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s);
  }
}

#[verifier(external_body)]
pub exec fn u32_from_le_bytes(s: &[u8]) -> (x:u32)
  requires s.dview().len() == 4,
  ensures x == spec_u32_from_le_bytes(s.dview()),
{
  use core::convert::TryInto;
  u32::from_le_bytes(s.try_into().unwrap())
}


#[verifier(external_body)]
pub exec fn u32_to_le_bytes(x: u32) -> (s: alloc::vec::Vec<u8>)
  ensures
    s.dview() == spec_u32_to_le_bytes(x),
    s.dview().len() == 4,
{
  x.to_le_bytes().to_vec()
}

// Conversion between u64 and little-endian byte sequences

pub closed spec fn spec_u64_to_le_bytes(x: u64) -> Seq<u8>
{
  seq![
    (x & 0xff) as u8,
    ((x >> 8) & 0xff) as u8,
    ((x >> 16) & 0xff) as u8,
    ((x >> 24) & 0xff) as u8,
    ((x >> 32) & 0xff) as u8,
    ((x >> 40) & 0xff) as u8,
    ((x >> 48) & 0xff) as u8,
    ((x >> 56) & 0xff) as u8,
  ]
}

pub closed spec fn spec_u64_from_le_bytes(s: Seq<u8>) -> u64
  recommends s.len() == 8
{
  (s[0] as u64) |
  (s[1] as u64) << 8 |
  (s[2] as u64) << 16 |
  (s[3] as u64) << 24 |
  (s[4] as u64) << 32 |
  (s[5] as u64) << 40 |
  (s[6] as u64) << 48 |
  (s[7] as u64) << 56
}

pub proof fn lemma_auto_spec_u64_to_from_le_bytes()
  ensures
    forall |x: u64|
      #![trigger spec_u64_to_le_bytes(x)]
    {
      &&& spec_u64_to_le_bytes(x).len() == 8
      &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
    },
    forall |s: Seq<u8>|
      #![trigger spec_u64_to_le_bytes(spec_u64_from_le_bytes(s))]
      s.len() == 8 ==> spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s,
{
  assert forall |x: u64|  {
    &&& #[trigger] spec_u64_to_le_bytes(x).len() == 8
    &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
  } by {
    let s = spec_u64_to_le_bytes(x);
    assert({
      &&& x & 0xff < 256
      &&& (x >> 8) & 0xff < 256
      &&& (x >> 16) & 0xff < 256
      &&& (x >> 24) & 0xff < 256
      &&& (x >> 32) & 0xff < 256
      &&& (x >> 40) & 0xff < 256
      &&& (x >> 48) & 0xff < 256
      &&& (x >> 56) & 0xff < 256
    }) by (bit_vector);

    assert(x == (
      (x & 0xff) |
      ((x >> 8) & 0xff) << 8 |
      ((x >> 16) & 0xff) << 16 |
      ((x >> 24) & 0xff) << 24 |
      ((x >> 32) & 0xff) << 32 |
      ((x >> 40) & 0xff) << 40 |
      ((x >> 48) & 0xff) << 48 |
      ((x >> 56) & 0xff) << 56)) by (bit_vector);
  };

  assert forall |s: Seq<u8>| s.len() == 8 implies #[trigger] spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s by {
    let x = spec_u64_from_le_bytes(s);
    let s0 = s[0] as u64;
    let s1 = s[1] as u64;
    let s2 = s[2] as u64;
    let s3 = s[3] as u64;
    let s4 = s[4] as u64;
    let s5 = s[5] as u64;
    let s6 = s[6] as u64;
    let s7 = s[7] as u64;

    assert(
      (
        (x == s0 | s1 << 8 | s2 << 16 | s3 << 24 | s4 << 32 | s5 << 40 | s6 << 48 | s7 << 56) &&
        (s0 < 256) &&
        (s1 < 256) &&
        (s2 < 256) &&
        (s3 < 256) &&
        (s4 < 256) &&
        (s5 < 256) &&
        (s6 < 256) &&
        (s7 < 256)
      ) ==>
      s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff) && s2 == ((x >> 16) & 0xff) && s3 == ((x >> 24) & 0xff) && s4 == ((x >> 32) & 0xff) && s5 == ((x >> 40) & 0xff) && s6 == ((x >> 48) & 0xff) && s7 == ((x >> 56) & 0xff)
    ) by (bit_vector);

    assert_seqs_equal!(spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s);
  }
}

#[verifier(external_body)]
pub exec fn u64_from_le_bytes(s: &[u8]) -> (x:u64)
  requires s.dview().len() == 8,
  ensures x == spec_u64_from_le_bytes(s.dview()),
{
  use core::convert::TryInto;
  u64::from_le_bytes(s.try_into().unwrap())
}


#[verifier(external_body)]
pub exec fn u64_to_le_bytes(x: u64) -> (s: alloc::vec::Vec<u8>)
  ensures
    s.dview() == spec_u64_to_le_bytes(x),
    s.dview().len() == 8,
{
  x.to_le_bytes().to_vec()
}


} // verus

verus! {

    pub open spec fn spec_parse_pair<R1, R2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<R1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<R2>) ->
        spec_fn(SpecStream) -> SpecParseResult<(R1,R2)>
    {
        move |s| match parser1(s) {
            Ok((s, n, r1)) => match parser2(s) {
                Ok((s, m, r2)) => {
                    if n + m > usize::MAX {
                        Err(ParseError::IntegerOverflow)
                    } else {
                        Ok((s, n + m, (r1, r2)))
                    }
                }
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }

    pub open spec fn spec_serialize_pair<T1, T2>(
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult) ->
        spec_fn(SpecStream, (T1, T2)) -> SpecSerializeResult
    {
        move |s, v: (T1, T2)| match serializer1(s, v.0) {
            Ok((s, n)) => match serializer2(s, v.1) {
                Ok((s, m)) => {
                    if n + m > usize::MAX {
                        Err(SerializeError::IntegerOverflow)
                    } else {
                        Ok((s, n + m))
                    }
                }
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }

    pub exec fn parse_pair<'a, P1, P2, R1, R2>(
        exec_parser1: P1,
        exec_parser2: P2,
        Ghost(spec_parser1): Ghost<spec_fn(SpecStream) -> SpecParseResult<R1::V>>,
        Ghost(spec_parser2): Ghost<spec_fn(SpecStream) -> SpecParseResult<R2::V>>,
        s: Stream<'a>) -> (res: ParseResult<'a, (R1,R2)>)
        where
            R1: DView,
            R2: DView,
            P1: FnOnce(Stream<'a>) -> ParseResult<R1>,
            P2: FnOnce(Stream<'a>) -> ParseResult<R2>,
        requires
            prop_parse_exec_spec_equiv(exec_parser1, spec_parser1),
            prop_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        ensures
            prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2))
    {
        proof { reveal(prop_parse_exec_spec_equiv); }
        let res1 = exec_parser1(s);
        proof { lemma_parse_exec_spec_equiv_on(exec_parser1, spec_parser1, s, res1); }
        match res1 {
            Ok((s1, n1, r1)) => {
                let res2 = exec_parser2(s1);
                proof { lemma_parse_exec_spec_equiv_on(exec_parser2, spec_parser2, s1, res2); }
                match res2 {
                    Ok((s2, n2, r2)) => {
                        if n1 > usize::MAX - n2 {
                            Err(ParseError::IntegerOverflow)
                        } else {
                            Ok((s2, n1 + n2, (r1, r2)))
                        }
                    }
                    Err(e) => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    }

    pub proof fn lemma_parse_pair_correct<T1, T2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<T1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<T2>,
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult)
        requires
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2),
            prop_parse_well_behaved(parser1),
            prop_parse_strong_prefix(parser1),
            prop_parse_correct(parser1, serializer1),
            prop_parse_correct(parser2, serializer2)
        ensures
            prop_parse_correct(spec_parse_pair(parser1, parser2),
                                spec_serialize_pair(serializer1, serializer2))
    {
        reveal(prop_parse_correct);
        assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> prop_parse_correct_on(spec_parse_pair(parser1, parser2), spec_serialize_pair(serializer1, serializer2), s, v) by {
            if s.data.len() <= usize::MAX {
                lemma_parse_pair_correct_on(parser1, parser2, serializer1, serializer2, s, v);
            }
        }
    }

    pub proof fn lemma_parse_pair_serialize_inverse<T1, T2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<T1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<T2>,
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2),
            prop_serialize_well_behaved(serializer1),
            prop_parse_serialize_inverse(parser1, serializer1),
            prop_parse_serialize_inverse(parser2, serializer2)
        ensures
            prop_parse_serialize_inverse(spec_parse_pair(parser1, parser2),
                                    spec_serialize_pair(serializer1, serializer2))
    {
        reveal(prop_parse_serialize_inverse);
        assert forall |s: SpecStream| prop_parse_serialize_inverse_on(spec_parse_pair(parser1, parser2),
        spec_serialize_pair(serializer1, serializer2), s) by {
            lemma_parse_pair_serialize_inverse_on(parser1, parser2, serializer1, serializer2, s);
        }
    }

    pub proof fn lemma_parse_pair_well_behaved<R1, R2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<R1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<R2>)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2)
        ensures
            prop_parse_well_behaved(spec_parse_pair(parser1, parser2))
    {
        reveal(prop_parse_well_behaved);
        assert forall |s: SpecStream| prop_parse_well_behaved_on(spec_parse_pair(parser1, parser2), s) by {
            lemma_parse_pair_well_behaved_on(parser1, parser2, s);
        }
    }

    pub proof fn lemma_serialize_pair_well_behaved<T1, T2>(
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult)
        requires
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2)
        ensures
            prop_serialize_well_behaved(spec_serialize_pair(serializer1, serializer2))
    {
        reveal(prop_serialize_well_behaved);
        assert forall |s: SpecStream, v: (T1, T2)| prop_serialize_well_behaved_on(spec_serialize_pair(serializer1, serializer2), s, v) by {
            lemma_serialize_pair_well_behaved_on(serializer1, serializer2, s, v);
        }
    }

    pub proof fn lemma_serialize_pair_deterministic<T1, T2>(
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult)
        requires
            prop_serialize_deterministic(serializer1),
            prop_serialize_deterministic(serializer2),
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2)
        ensures
            prop_serialize_deterministic(spec_serialize_pair(serializer1, serializer2))
    {
        reveal(prop_serialize_deterministic);
        assert forall |s1, s2, v| prop_serialize_deterministic_on(spec_serialize_pair(serializer1, serializer2), s1, s2, v) by {
            lemma_serialize_pair_deterministic_on(serializer1, serializer2, s1, s2, v);
        }
    }

    pub proof fn lemma_parse_pair_strong_prefix<R1, R2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<R1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<R2>)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2),
            prop_parse_strong_prefix(parser1),
            prop_parse_strong_prefix(parser2),
        ensures
            prop_parse_strong_prefix(spec_parse_pair(parser1, parser2))
    {
        reveal(prop_parse_strong_prefix);
        assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_pair(parser1, parser2), s1, s2) by {
            lemma_parse_pair_strong_prefix_on(parser1, parser2, s1, s2);
        }
    }

    pub proof fn lemma_parse_pair_well_behaved_on<R1, R2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<R1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<R2>,
        s: SpecStream)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2)
        ensures
            prop_parse_well_behaved_on(spec_parse_pair(parser1, parser2), s)
    {
        if let Ok((s1, n1, _)) = parser1(s) {
            assert(
                s1.data == s.data &&
                s1.start == s.start + n1 &&
                0 <= s.start <= s1.start <= s.data.len()) by {
                    lemma_parse_well_behaved_on(parser1, s);
                }
            if let Ok((s2, n2, _)) = parser2(s1) {
                assert(
                    s2.data == s1.data &&
                    s2.start == s1.start + n2 &&
                    0 <= s1.start <= s2.start <= s1.data.len()) by {
                        lemma_parse_well_behaved_on(parser2, s1);
                    }
                if let Ok((sout, n, _)) = spec_parse_pair(parser1, parser2)(s) {
                    assert(n == n1 + n2);
                }
            }
        }
    }

    pub proof fn lemma_serialize_pair_well_behaved_on<T1, T2>(
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult,
        s: SpecStream, v: (T1, T2))
        requires
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2)
        ensures
            prop_serialize_well_behaved_on(spec_serialize_pair(serializer1, serializer2), s, v)
    {
        lemma_serialize_well_behaved_on(serializer1, s, v.0);
        if let Ok((s1, n1)) = serializer1(s, v.0) {
            assert(
                s1.data.len() == s.data.len()
                && 0 <= s.start <= s1.start <= s.data.len()
                && s1.start == s.start + n1
                && s1.data.subrange(0, s.start) == s.data.subrange(0, s.start)
                && s1.data.subrange(s.start + n1, s.data.len() as int) == s.data.subrange(s.start + n1, s.data.len() as int));
            lemma_serialize_well_behaved_on(serializer2, s1, v.1);
            if let Ok((s2, n2)) = serializer2(s1, v.1) {
                assert(
                    s2.data.len() == s1.data.len()
                    && 0 <= s1.start <= s2.start <= s1.data.len()
                    && s2.start == s1.start + n2
                    && s2.data.subrange(0, s1.start) == s1.data.subrange(0, s1.start)
                    && s2.data.subrange(s1.start + n2, s1.data.len() as int) == s1.data.subrange(s1.start + n2, s1.data.len() as int));
                if let Ok((sout, n)) = spec_serialize_pair(serializer1, serializer2)(s, v) {
                    // assert(n == n1 + n2);
                    // assert(s2 == sout);
                    assert(sout.data.len() == s.data.len());
                    assert(0 <= s.start <= sout.start <= s.data.len());
                    assert(sout.start == s.start + n);
                    assert(sout.data.subrange(0, s.start) == s.data.subrange(0, s.start)) by {
                        assert(s2.data.subrange(0, s1.start).subrange(0, s.start) =~= s2.data.subrange(0, s.start));
                        assert(s1.data.subrange(0, s1.start).subrange(0, s.start) =~= s1.data.subrange(0, s.start));
                    }
                    assert(sout.data.subrange(s.start + n, s.data.len() as int) == s.data.subrange(s.start + n, s.data.len() as int)) by {
                        assert(s1.data.subrange(s.start + n1, s.data.len() as int).subrange(n2 as int, s.data.len() - s.start - n1) =~= s1.data.subrange(s.start + n, s.data.len() as int));
                        assert(s.data.subrange(s.start + n1, s.data.len() as int).subrange(n2 as int, s.data.len() - s.start - n1) =~= s.data.subrange(s.start + n, s.data.len() as int));
                    }
                }
            }
        }
    }

    pub proof fn lemma_serialize_pair_deterministic_on<T1, T2>(
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult,
        s1: SpecStream, s2: SpecStream, v: (T1, T2))
        requires
            prop_serialize_deterministic(serializer1),
            prop_serialize_deterministic(serializer2),
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2)
        ensures
            prop_serialize_deterministic_on(spec_serialize_pair(serializer1, serializer2), s1, s2, v)
    {
        lemma_serialize_deterministic_on(serializer1, s1, s2, v.0);
        lemma_serialize_well_behaved_on(serializer1, s1, v.0);
        lemma_serialize_well_behaved_on(serializer1, s2, v.0);
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (serializer1(s1, v.0), serializer1(s2, v.0)) {
            lemma_serialize_deterministic_on(serializer2, sout1, sout2, v.1);
            lemma_serialize_well_behaved_on(serializer2, sout1, v.1);
            lemma_serialize_well_behaved_on(serializer2, sout2, v.1);
            if let (Ok((sout3, n3)), Ok((sout4, n4))) = (serializer2(sout1, v.1), serializer2(sout2, v.1)) {
                assert(n1 + n3 == n2 + n4);
                assert(sout3.data.subrange(s1.start, s1.start + n1 + n3) =~= sout4.data.subrange(s2.start, s2.start + n2 + n4)) by {
                    assert(sout1.data.subrange(0, s1.start + n1).subrange(s1.start, s1.start + n1) =~= sout1.data.subrange(s1.start, s1.start + n1));
                    assert(sout2.data.subrange(0, s2.start + n2).subrange(s2.start, s2.start + n2) =~= sout2.data.subrange(s2.start, s2.start + n2));
                    assert(sout3.data.subrange(0, s1.start + n1).subrange(s1.start, s1.start + n1) =~= sout3.data.subrange(s1.start, s1.start + n1));
                    assert(sout4.data.subrange(0, s2.start + n2).subrange(s2.start, s2.start + n2) =~= sout4.data.subrange(s2.start, s2.start + n2));

                    assert(sout3.data.subrange(s1.start, s1.start + n1) =~= sout4.data.subrange(s2.start, s2.start + n2));
                    assert(sout3.data.subrange(s1.start + n1, s1.start + n1 + n3) == sout4.data.subrange(s2.start + n2, s2.start + n2 + n4));

                    assert(sout3.data.subrange(s1.start, s1.start + n1 + n3) =~= sout3.data.subrange(s1.start, s1.start + n1) + sout3.data.subrange(s1.start + n1, s1.start + n1 + n3));
                    assert(sout4.data.subrange(s2.start, s2.start + n2 + n4) =~= sout4.data.subrange(s2.start, s2.start + n2) + sout4.data.subrange(s2.start + n2, s2.start + n2 + n4));
                }
            }
        }
    }

    pub proof fn lemma_parse_pair_strong_prefix_on<R1, R2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<R1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<R2>,
        s1: SpecStream, s2: SpecStream)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2),
            prop_parse_strong_prefix(parser1),
            prop_parse_strong_prefix(parser2),
        ensures
            prop_parse_strong_prefix_on(spec_parse_pair(parser1, parser2), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_pair(parser1, parser2)(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len() <= usize::MAX
            && 0 <= s2.start <= s2.start + n <= s2.data.len() <= usize::MAX
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                // assert(parser1(s1).is_ok());
                if let Ok((p1s1, n1, p1x1)) = parser1(s1) {
                    // assert(parser2(p1s1).is_ok());
                    if let Ok((p2s1, n2, p2x1)) = parser2(p1s1) {
                        assert(s1.data.subrange(s1.start, s1.start + n1) == s2.data.subrange(s2.start, s2.start + n1)) by {
                            assert(s1.data.subrange(s1.start, s1.start + n).subrange(0, n1 as int) =~= s1.data.subrange(s1.start, s1.start + n1));
                            assert(s2.data.subrange(s2.start, s2.start + n).subrange(0, n1 as int) =~= s2.data.subrange(s2.start, s2.start + n1));
                        }
                        lemma_parse_strong_prefix_on(parser1, s1, s2);
                        // assert(parser1(s2).is_ok());
                        if let Ok((p1s2, m1, p1x2)) = parser1(s2) {
                            lemma_parse_well_behaved_on(parser1, s1);
                            lemma_parse_well_behaved_on(parser1, s2);
                            // assert(p1s1.data == s1.data);
                            // assert(p1s2.data == s2.data);
                            // assert(p1s1.start == s1.start + n1);
                            // assert(p1s2.start == s2.start + n1);
                            // assert(n == n1 + n2);
                            assert(s1.data.subrange(s1.start + n1, s1.start + n1 + n2) == s2.data.subrange(s2.start + n1, s2.start + n1 + n2)) by {
                                assert(s1.data.subrange(s1.start, s1.start + n).subrange(n1 as int, n as int) =~= s1.data.subrange(s1.start + n1, s1.start + n1 + n2));
                                assert(s2.data.subrange(s2.start, s2.start + n).subrange(n1 as int, n as int) =~= s2.data.subrange(s2.start + n1, s2.start + n1 + n2));
                            }
                            assert(p1s1.data.subrange(p1s1.start, p1s1.start + n2) == p1s2.data.subrange(p1s2.start, p1s2.start + n2));
                            lemma_parse_strong_prefix_on(parser2, p1s1, p1s2);
                            // assert(parser2(p1s2).is_ok());
                            if let Ok((p2s2, m2, p2x2)) = parser2(p1s2) {
                                if let Ok((sout2, m, x2)) = spec_parse_pair(parser1, parser2)(s2) {
                                    assert(m == n && x2 == x1);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_pair_correct_on<T1, T2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<T1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<T2>,
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult,
        s: SpecStream, v: (T1, T2))
        requires
            s.data.len() <= usize::MAX,
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2),
            prop_parse_well_behaved(parser1),
            prop_parse_strong_prefix(parser1),
            prop_parse_correct(parser1, serializer1),
            prop_parse_correct(parser2, serializer2)
        ensures
            prop_parse_correct_on(spec_parse_pair(parser1, parser2),
                                spec_serialize_pair(serializer1, serializer2), s, v)
    {
        if let Ok((s1, n1)) = serializer1(s, v.0) {
            if let Ok((s2, n2)) = serializer2(s1, v.1) {
                lemma_serialize_well_behaved_on(serializer1, s, v.0);
                lemma_serialize_well_behaved_on(serializer2, s1, v.1);
                lemma_parse_correct_on(parser1, serializer1, s, v.0);
                if let Ok((s_c1, n_c1, r_c1)) = parser1(SpecStream {start: s.start, ..s1}) {
                    assert(n1 == n_c1 && r_c1 == v.0);
                    assert(s1.data.subrange(s.start, s.start + n_c1) == s2.data.subrange(s.start, s.start + n_c1)) by {
                        assert(s1.data.subrange(0, s.start + n1).subrange(s.start, s.start + n1) =~= s1.data.subrange(s.start, s.start + n1));
                        assert(s2.data.subrange(0, s.start + n1).subrange(s.start, s.start + n1) =~= s2.data.subrange(s.start, s.start + n1));
                    }
                    lemma_parse_strong_prefix_on(parser1, SpecStream {start: s.start, ..s1}, SpecStream {start: s.start, ..s2});
                    if let Ok((s3, m1, res1)) = parser1(SpecStream {start: s.start, ..s2}) {
                        assert(m1 == n_c1 && res1 == r_c1);
                        assert(m1 == n1 && res1 == v.0); // crucial fact 1
                        lemma_parse_well_behaved_on(parser1, SpecStream {start: s.start, ..s2});
                        assert(s3.data == s2.data && s3.start == s.start + m1); // crucial fact 2 (s3 == SpecStream {start: s1.start, ..s2})
                        lemma_parse_correct_on(parser2, serializer2, s1, v.1);
                        // if let Ok((s_c2, n_c2, r_c2)) = parser2(SpecStream {start: s1.start, ..s2}) {
                            // assert(n2 == n_c2 && r_c2 == v.1);
                            if let Ok((s4, m2, res2)) = parser2(s3) {
                                // assert(m2 == n_c2 && res2 == r_c2);
                                assert(m1 + m2 == n1 + n2);
                                assert(res1 == v.0 && res2 == v.1);
                            }
                        // }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_pair_serialize_inverse_on<T1, T2>(
        parser1: spec_fn(SpecStream) -> SpecParseResult<T1>,
        parser2: spec_fn(SpecStream) -> SpecParseResult<T2>,
        serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
        serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult,
        s: SpecStream)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2),
            prop_serialize_well_behaved(serializer1),
            prop_parse_serialize_inverse(parser1, serializer1),
            prop_parse_serialize_inverse(parser2, serializer2)
        ensures
            prop_parse_serialize_inverse_on(spec_parse_pair(parser1, parser2),
                                    spec_serialize_pair(serializer1, serializer2), s)
    {
        if let Ok((s1, n1, x1)) = parser1(s) {
            if let Ok((s2, n2, x2)) = parser2(s1) {
                lemma_parse_well_behaved_on(parser1, s);
                lemma_parse_well_behaved_on(parser2, s1);
                lemma_parse_serialize_inverse_on(parser1, serializer1, s);
                lemma_serialize_well_behaved_on(serializer1, s, x1);
                if let Ok((s3, m1)) = serializer1(s, x1) {
                    assert(m1 == n1 && s3.data == s.data);
                    lemma_parse_serialize_inverse_on(parser2, serializer2, s1);
                    if let Ok((s4, m2)) = serializer2(s3, x2) {
                        assert(m1 + m2 == n1 + n2);
                        assert(s4.data == s.data);
                    }
                }
            }
        }
    }
}

verus! {

    pub open spec fn spec_parse_repeat_n_rec<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        n: nat,
        s: SpecStream) -> SpecParseResult<Seq<R>>
        decreases n
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start > s.data.len() {
            Err(ParseError::Eof)
        } else if n == 0 {
            Ok((s, 0, seq![]))
        } else {
            match spec_parse_repeat_n_rec(parser, (n - 1) as nat, s) {
                Ok((s, k, rs)) => match parser(s) {
                    Ok((s, m, r)) => {
                        if m + k > usize::MAX {
                            Err(ParseError::IntegerOverflow)
                        } else {
                            Ok((s, m + k, rs.push(r))) // repeat_n(n) = repeat_n(n - 1).push(parse()) = repeat_n(n - 2).push(parse()).push(parse()) = ... = repeat_n(0).push(parse()).push(parse()).push(parse()) = seq![parse(), parse(), ..., parse()]
                        }
                    }
                    Err(e) => Err(e),
                },
                Err(e) => Err(e),
            }
        }
    }

    pub open spec fn spec_parse_repeat_n<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        n: nat) ->
        spec_fn(SpecStream) -> SpecParseResult<Seq<R>>
    {
        move |s| spec_parse_repeat_n_rec(parser, n, s)
    }

    pub open spec fn spec_serialize_repeat_n_rec<T>(
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s: SpecStream,
        vs: Seq<T>) -> SpecSerializeResult
        recommends
            vs.len() == n // otherwise cannot prove correctness
        decreases n
    {
        if vs.len() != n {
            Err(SerializeError::RepeatNMismatch)
        } else if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.start > s.data.len() {
            Err(SerializeError::NotEnoughSpace)
        } else if n == 0 {
            Ok((s, 0))
        } else {
            match spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1)) {
                Ok((s, k)) => match serializer(s, vs[vs.len() as int - 1]) {
                    Ok((s, m)) => {
                        if m + k > usize::MAX {
                            Err(SerializeError::IntegerOverflow)
                        } else {
                            Ok((s, m + k))
                        }
                    }
                    Err(e) => Err(e),
                },
                Err(e) => Err(e),
            }
        }
    }

    pub open spec fn spec_serialize_repeat_n<T>(
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat) ->
        spec_fn(SpecStream, Seq<T>) -> SpecSerializeResult
    {
        move |s, vs| spec_serialize_repeat_n_rec(serializer, n, s, vs)
    }

    pub exec fn parse_repeat_n<'a, P, R>(
        exec_parser: P,
        Ghost(spec_parser): Ghost<spec_fn(SpecStream) -> SpecParseResult<R::V>>,
        n: usize, s: Stream<'a>) -> (res: ParseResult<'a, Vec<R>>)
        where
            P: Fn(Stream<'a>) -> ParseResult<'a, R>,
            R: DView,
        requires
            prop_parse_exec_spec_equiv(exec_parser, spec_parser),
        ensures
            prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, n as nat))
    {
        proof { reveal(prop_parse_exec_spec_equiv); }

        if s.start < 0 {
            return Err(ParseError::NegativeIndex);
        } else if s.start > s.data.length() {
            return Err(ParseError::Eof);
        }

        let (mut xs, mut mut_s, mut i, mut m): (Vec<R>, Stream, usize, usize) = (vec_new(), s, 0, 0);
        let ghost res = Ok((mut_s, 0, xs));

        while i < n
            invariant
                0 <= i <= n,
                0 <= m <= usize::MAX,
                forall |s| #![auto] exec_parser.requires((s,)),
                res == Ok::<(Stream, usize, Vec<R>), ParseError>((mut_s, m, xs)),
                prop_parse_exec_spec_equiv(exec_parser, spec_parser),
                prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, i as nat)),
        {
            i = i + 1;
            let res1 = exec_parser(mut_s);
            proof { lemma_parse_exec_spec_equiv_on(exec_parser, spec_parser, mut_s, res1); }
            match res1 {
                Ok((s1, m1, r1)) => {
                    if m > usize::MAX - m1 {
                        proof { res = Err(ParseError::IntegerOverflow); }
                        proof { lemma_parse_repeat_n_rec_error_unrecoverable_on(spec_parser, i as nat, n as nat, s.dview()); }
                        assert(prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, n as nat)));
                        return Err(ParseError::IntegerOverflow);
                    } else {
                        vec_push(&mut xs, r1);
                        mut_s = s1;
                        m = m + m1;
                        proof { res = Ok((mut_s, m, xs)); }
                        assert(prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, i as nat)));
                    }
                }
                Err(e) => {
                    proof { res = Err(e); }
                    proof { lemma_parse_repeat_n_rec_error_unrecoverable_on(spec_parser, i as nat, n as nat, s.dview()); }
                    assert(prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, n as nat)));
                    return Err(e);
                }
            }
        }

        Ok((mut_s, m, xs))
    }

    proof fn lemma_parse_repeat_n_rec_error_unrecoverable_on<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        n1: nat, n2: nat, s: SpecStream)
        ensures
        n2 >= n1 ==> {
            if let Err(e1) = spec_parse_repeat_n_rec(parser, n1, s) {
                if let Err(e2) = spec_parse_repeat_n_rec(parser, n2, s) {
                    e1 == e2
                } else {
                    false
                }
            } else {
                true
            }
        }
        decreases n2
    {
        if n2 == n1 {}
        else if n2 > n1 {
            lemma_parse_repeat_n_rec_error_unrecoverable_on(parser, n1, (n2 - 1) as nat, s);
        }
    }

    proof fn lemma_serialize_repeat_n_rec_error_unrecoverable_on<T>(
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n1: nat, n2: nat, s: SpecStream, vs1: Seq<T>, vs2: Seq<T>)
        requires
            n2 >= n1,
            vs1.len() == n1,
            vs2.len() == n2,
            vs1 == vs2.subrange(0, n1 as int),
        ensures
            if let Err(e1) = spec_serialize_repeat_n_rec(serializer, n1, s, vs1) {
                if let Err(e2) = spec_serialize_repeat_n_rec(serializer, n2, s, vs2) {
                    e1 == e2
                } else {
                    false
                }
            } else {
                true
            }
        decreases n2, vs2.len()
    {
        if n2 == n1 {
            assert(vs1 =~= vs2);
        }
        else if n2 > n1 {
            assert(vs1 =~= vs2.subrange(0, vs2.len() as int - 1).subrange(0, n1 as int));
            lemma_serialize_repeat_n_rec_error_unrecoverable_on(serializer, n1, (n2 - 1) as nat, s, vs1, vs2.subrange(0, vs2.len() as int - 1));
        }
    }

    pub proof fn spec_parse_repeat_n_rec_step<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        n: nat, s: SpecStream)
        ensures
            s.start < 0 ==> spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(ParseError::NegativeIndex),
            s.start > s.data.len() ==> spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(ParseError::Eof),
            0 <= s.start <= s.data.len() ==> {
                &&& n == 0 ==> spec_parse_repeat_n_rec(parser, n, s) == Ok::<(SpecStream, nat, Seq<R>), ParseError>((s, 0, seq![]))
                &&& n > 0 ==> match spec_parse_repeat_n_rec(parser, (n - 1) as nat, s) {
                    Err(e) => spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(e),
                    Ok((s0, m, rs)) => match parser(s0) {
                        Err(e) => spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(e),
                        Ok((s1, k, r)) => {
                            if m + k > usize::MAX {
                                spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(ParseError::IntegerOverflow)
                            } else {
                                spec_parse_repeat_n_rec(parser, n, s) == Ok::<(SpecStream, nat, Seq<R>), ParseError>((s1, m + k, rs.push(r)))
                            }
                        }
                    }
                }
            }
    {}

    pub proof fn lemma_parse_repeat_n_correct<T>(
        parser: spec_fn(SpecStream) -> SpecParseResult<T>,
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_parse_well_behaved(parser),
            prop_serialize_well_behaved(serializer),
            prop_parse_strong_prefix(parser),
            prop_parse_correct(parser, serializer)
        ensures
            prop_parse_correct(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n))
    {
        reveal(prop_parse_correct);
        assert forall |s: SpecStream, vs: Seq<T>| s.data.len() <= usize::MAX ==> prop_parse_correct_on(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n), s, vs) by {
            if s.data.len() <= usize::MAX {
                lemma_parse_repeat_n_correct_on(parser, serializer, n, s, vs);
            }
        }
    }

    pub proof fn lemma_parse_repeat_n_serialize_inverse<T>(
        parser: spec_fn(SpecStream) -> SpecParseResult<T>,
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_parse_well_behaved(parser),
            prop_serialize_well_behaved(serializer),
            prop_parse_serialize_inverse(parser, serializer)
        ensures
            prop_parse_serialize_inverse(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n))
    {
        reveal(prop_parse_serialize_inverse);
        assert forall |s: SpecStream| prop_parse_serialize_inverse_on(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n), s) by {
            lemma_parse_repeat_n_serialize_inverse_on(parser, serializer, n, s);
        }
    }

    pub proof fn lemma_parse_repeat_n_well_behaved<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        n: nat)
        requires
            prop_parse_well_behaved(parser)
        ensures
            prop_parse_well_behaved(spec_parse_repeat_n(parser, n)),
            forall |s| {
                if let Ok((_, _, res)) = #[trigger] spec_parse_repeat_n(parser, n)(s) {
                    res.len() == n
                } else {
                    true
                }
            }
        decreases n
    {
        reveal(prop_parse_well_behaved);
        assert forall |s:SpecStream| prop_parse_well_behaved_on(spec_parse_repeat_n(parser, n), s) by {
            lemma_parse_repeat_n_well_behaved_on(parser, n, s);
        }
        assert forall |s:SpecStream| {
            if let Ok((_, _, res)) = #[trigger] spec_parse_repeat_n(parser, n)(s) {
                res.len() == n
            } else {
                true
            }
        } by {
            lemma_parse_repeat_n_well_behaved_on(parser, n, s);
        }
    }

    pub proof fn lemma_serialize_repeat_n_well_behaved<T>(
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_serialize_well_behaved(serializer),
        ensures
            prop_serialize_well_behaved(spec_serialize_repeat_n(serializer, n))
    {
        reveal(prop_serialize_well_behaved);
        assert forall |s:SpecStream, vs: Seq<T>| prop_serialize_well_behaved_on(spec_serialize_repeat_n(serializer, n), s, vs) by {
            lemma_serialize_repeat_n_well_behaved_on(serializer, n, s, vs);
        }
    }

    pub proof fn lemma_serialize_repeat_n_deterministic<T>(
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_serialize_well_behaved(serializer),
            prop_serialize_deterministic(serializer)
        ensures
            prop_serialize_deterministic(spec_serialize_repeat_n(serializer, n))
    {
        reveal(prop_serialize_deterministic);
        assert forall |s1, s2, v| prop_serialize_deterministic_on(spec_serialize_repeat_n(serializer, n), s1, s2, v) by {
            lemma_serialize_repeat_n_deterministic_on(serializer, n, s1, s2, v);
        }
    }

    pub proof fn lemma_parse_repeat_n_nonmalleable<T>(
        parser: spec_fn(SpecStream) -> SpecParseResult<T>,
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_parse_serialize_inverse(spec_parse_repeat_n(parser, n),
                                        spec_serialize_repeat_n(serializer, n)),
            prop_serialize_deterministic(spec_serialize_repeat_n(serializer, n)),
        ensures
            prop_parse_nonmalleable(spec_parse_repeat_n(parser, n))
    {
        lemma_parse_serialize_inverse_implies_nonmalleable(spec_parse_repeat_n(parser, n),
                                        spec_serialize_repeat_n(serializer, n));
    }

    pub proof fn lemma_parse_repeat_n_strong_prefix<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        n: nat)
        requires
            prop_parse_well_behaved(parser),
            prop_parse_strong_prefix(parser),
        ensures
            prop_parse_strong_prefix(spec_parse_repeat_n(parser, n))
    {
        reveal(prop_parse_strong_prefix);
        assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_repeat_n(parser, n), s1, s2) by {
            lemma_parse_repeat_n_strong_prefix_on(s1, s2, parser, n);
        }
    }

    pub proof fn lemma_parse_repeat_n_correct_on<T>(
        parser: spec_fn(SpecStream) -> SpecParseResult<T>,
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s: SpecStream,
        vs: Seq<T>)
        requires
            s.data.len() <= usize::MAX,
            prop_parse_well_behaved(parser),
            prop_serialize_well_behaved(serializer),
            prop_parse_strong_prefix(parser),
            prop_parse_correct(parser, serializer)
        ensures
            prop_parse_correct_on(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n), s, vs)
        decreases n, vs.len()
    {
        if vs.len() != n {
        } else if s.start < 0 {
        } else if s.start > s.data.len() {
        } else if n == 0 {
            assert(vs =~= seq![]);
        } else {
            // induction
            lemma_parse_repeat_n_correct_on(parser, serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1));
            lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1));
            if let Ok((s0, n0)) = spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1)) {
                lemma_serialize_well_behaved_on(serializer, s0, vs[vs.len() as int - 1]);
                if let Ok((s1, n1)) = serializer(s0, vs[vs.len() as int - 1]) {
                    assert(s0.data.subrange(s.start, s.start + n0) == s1.data.subrange(s.start, s.start + n0)) by {
                        assert(s0.data.subrange(0, s0.start).subrange(s.start, s.start + n0) =~= s0.data.subrange(s.start, s.start + n0));
                        assert(s1.data.subrange(0, s0.start).subrange(s.start, s.start + n0) =~= s1.data.subrange(s.start, s.start + n0));
                    }
                    lemma_parse_repeat_n_strong_prefix(parser, (n - 1) as nat);
                    lemma_parse_strong_prefix_on(spec_parse_repeat_n(parser, (n - 1) as nat), SpecStream { start: s.start, ..s0 }, SpecStream { start: s.start, ..s1 });
                    lemma_parse_correct_on(parser, serializer, s0, vs[vs.len() as int - 1]);
                    lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, SpecStream { start: s.start, ..s1 });
                    if let Ok((s2, n2, x0)) = spec_parse_repeat_n_rec(parser, (n - 1) as nat, SpecStream { start: s.start, ..s1 }) {
                        if let Ok((s3, n3, x1)) = parser(s2) {
                            assert(n3 == n1 && x1 == vs[vs.len() as int - 1]);
                            assert(n2 + n3 == n0 + n1);
                            assert(x0 == vs.subrange(0, vs.len() as int - 1));
                            assert(x0.push(x1) =~= vs);
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_repeat_n_serialize_inverse_on<T>(
        parser: spec_fn(SpecStream) -> SpecParseResult<T>,
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s: SpecStream)
        requires
            prop_parse_well_behaved(parser),
            prop_serialize_well_behaved(serializer),
            prop_parse_serialize_inverse(parser, serializer)
        ensures
            prop_parse_serialize_inverse_on(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n), s)
        decreases n
    {
        if s.start < 0 {
        } else if s.start > s.data.len() {
        } else if n == 0 {
        } else {
            // induction
            lemma_parse_repeat_n_serialize_inverse_on(parser, serializer, (n - 1) as nat, s);
            lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, s);
            if let Ok((s0, n0, x0)) = spec_parse_repeat_n_rec(parser, (n - 1) as nat, s) {
                lemma_parse_well_behaved_on(parser, s0);
                if let Ok((s1, n1, x1)) = parser(s0) {
                    assert(x0.push(x1).subrange(0, x0.push(x1).len() as int - 1) =~= x0);
                    lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s, x0);
                    if let Ok((s2, n2)) = spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s, x0) {
                        lemma_serialize_well_behaved_on(serializer, s2, x1);
                        lemma_parse_serialize_inverse_on(parser, serializer, s0);
                        assert(s2 == s0);
                        if let Ok((s3, n3)) = serializer(s2, x1) {
                            assert(n0 + n1 == n2 + n3);
                            assert(s3.data == s.data);
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_repeat_n_well_behaved_on<R>(
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        n: nat,
        s: SpecStream)
        requires
            prop_parse_well_behaved(parser)
        ensures
            prop_parse_well_behaved_on(spec_parse_repeat_n(parser, n), s)
            &&
            if let Ok((_, _, res)) = spec_parse_repeat_n(parser, n)(s) {
                res.len() == n
            } else {
                true
            }
        decreases n
    {
        if n == 0 {
        } else {
            match spec_parse_repeat_n(parser, n)(s) {
                Ok((sout, n_total, res)) => {
                    assert(
                        sout.data == s.data &&
                        sout.start == s.start + n_total &&
                        0 <= s.start <= sout.start <= s.data.len() &&
                        res.len() == n) by {
                            if let Ok((s1, n1, res1)) = spec_parse_repeat_n(parser, (n - 1) as nat)(s) {
                                assert(
                                    s1.data == s.data &&
                                    s1.start == s.start + n1 &&
                                    0 <= s.start <= s1.start <= s.data.len() &&
                                    res1.len() == n - 1) by { // induction on n
                                    lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, s);
                                }
                                if let Ok((s2, n2, res2)) = parser(s1) {
                                    assert(
                                        s2.data == s1.data &&
                                        s2.start == s1.start + n2 &&
                                        0 <= s1.start <= s2.start <= s1.data.len()) by {
                                            lemma_parse_well_behaved_on(parser, s1);
                                        }
                                    assert(
                                        sout == s2 &&
                                        n_total == n1 + n2 &&
                                        res == res1.push(res2) &&
                                        res.len() == n
                                    );
                                }
                            }
                        }
                }
                Err(_) => {}
            }
        }
    }

    pub proof fn lemma_serialize_repeat_n_well_behaved_on<T>(
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s: SpecStream,
        vs: Seq<T>)
        requires
            prop_serialize_well_behaved(serializer),
        ensures
            prop_serialize_well_behaved_on(spec_serialize_repeat_n(serializer, n), s, vs)
        decreases n
    {
        if vs.len() != n {}
        else if s.start < 0 {}
        else if s.start > s.data.len() {}
        else if n == 0 {}
        else {
            lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1));
            match spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1)) {
                Ok((s1, n1)) =>
                {
                    assert(s.start + n1 == s1.start);
                    assert(s1.data.subrange(0, s.start) == s.data.subrange(0, s.start));
                    assert(s1.data.subrange(s.start + n1, s.data.len() as int) == s.data.subrange(s.start + n1, s.data.len() as int));
                    lemma_serialize_well_behaved_on(serializer, s1, vs[vs.len() as int - 1]);
                    match serializer(s1, vs[vs.len() as int - 1]) {
                        Ok((s2, n2)) => {
                            assert(s1.start + n2 == s2.start);
                            assert(s2.data.subrange(0, s1.start) == s1.data.subrange(0, s1.start));
                            assert(s2.data.subrange(s1.start + n2, s.data.len() as int) == s1.data.subrange(s1.start + n2, s.data.len() as int));

                            assert(s.start + n1 + n2 == s2.start);
                            assert(s2.data.subrange(0, s.start) == s.data.subrange(0, s.start)) by {
                                assert(s2.data.subrange(0, s1.start).subrange(0, s.start) =~= s2.data.subrange(0, s.start));
                                assert(s1.data.subrange(0, s1.start).subrange(0, s.start) =~= s.data.subrange(0, s.start));
                            }
                            assert(s2.data.subrange(s.start + n1 + n2, s.data.len() as int) == s.data.subrange(s.start + n1 + n2, s.data.len() as int)) by {
                                assert(s1.data.subrange(s.start + n1, s.data.len() as int).subrange(n2 as int, s.data.len() - s.start - n1) =~= s1.data.subrange(s.start + n1 + n2, s.data.len() as int));
                                assert(s.data.subrange(s.start + n1, s.data.len() as int).subrange(n2 as int, s.data.len() - s.start - n1) =~= s.data.subrange(s.start + n1 + n2, s.data.len() as int));
                            }
                        }
                        Err(e) => {}
                    }
                },
                Err(e) => {}
            }
        }
    }

    pub proof fn lemma_serialize_repeat_n_deterministic_on<T>(
        serializer: spec_fn(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s1: SpecStream,
        s2: SpecStream,
        vs: Seq<T>)
        requires
            prop_serialize_well_behaved(serializer),
            prop_serialize_deterministic(serializer)
        ensures
            prop_serialize_deterministic_on(spec_serialize_repeat_n(serializer, n), s1, s2, vs)
        decreases n, vs.len()
    {
        if let (Ok((sn1, m1)), Ok((sn2, m2))) = (spec_serialize_repeat_n(serializer, n)(s1, vs), spec_serialize_repeat_n(serializer, n)(s2, vs))
        {
            if vs.len() != n {}
            else if s1.start < 0 || s2.start < 0 {}
            else if s1.start > s1.data.len() || s2.start > s2.data.len() {}
            else if n == 0 {}
            else {
                // induction on n
                lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s1, vs.subrange(0, vs.len() as int - 1));
                lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s2, vs.subrange(0, vs.len() as int - 1));
                lemma_serialize_repeat_n_deterministic_on(serializer, (n - 1) as nat, s1, s2, vs.subrange(0, vs.len() as int - 1));
                if let (Ok((snn1, nn1)), Ok((snn2, nn2))) = (spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s1, vs.subrange(0, vs.len() as int - 1)), spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s2, vs.subrange(0, vs.len() as int - 1))) {
                    assert(nn1 == nn2);
                    assert(snn1.data.subrange(s1.start, s1.start + nn1) == snn2.data.subrange(s2.start, s2.start + nn2));

                    lemma_serialize_well_behaved_on(serializer, snn1, vs[vs.len() as int - 1]);
                    lemma_serialize_well_behaved_on(serializer, snn2, vs[vs.len() as int - 1]);
                    lemma_serialize_deterministic_on(serializer, snn1, snn2, vs[vs.len() as int - 1]);
                    if let Ok((sout1, n1)) = serializer(snn1, vs[vs.len() as int - 1]) {
                        if let Ok((sout2, n2)) = serializer(snn2, vs[vs.len() as int - 1]) {
                            assert(n1 + nn1 == n2 + nn2);
                            assert(sout1.data.subrange(snn1.start, snn1.start + n1) == sout2.data.subrange(snn2.start, snn2.start + n2));

                            assert(sout1.data.subrange(s1.start, s1.start + n1 + nn1) == sout2.data.subrange(s2.start, s2.start + n2 + nn2)) by {
                                assert(sout1.data.subrange(s1.start, s1.start + n1 + nn1) =~= sout1.data.subrange(s1.start, s1.start + nn1) + sout1.data.subrange(s1.start + nn1, s1.start + n1 + nn1));
                                assert(sout2.data.subrange(s2.start, s2.start + n2 + nn2) =~= sout2.data.subrange(s2.start, s2.start + nn2) + sout2.data.subrange(s2.start + nn2, s2.start + n2 + nn2));

                                assert(sout1.data.subrange(s1.start, s1.start + nn1) =~= sout1.data.subrange(0, s1.start + nn1).subrange(s1.start, s1.start + nn1));
                                assert(sout2.data.subrange(s2.start, s2.start + nn2) =~= sout2.data.subrange(0, s2.start + nn2).subrange(s2.start, s2.start + nn2));

                                assert(snn1.data.subrange(s1.start, s1.start + nn1) =~= snn1.data.subrange(0, s1.start + nn1).subrange(s1.start, s1.start + nn1));
                                assert(snn2.data.subrange(s2.start, s2.start + nn2) =~= snn2.data.subrange(0, s2.start + nn2).subrange(s2.start, s2.start + nn2));
                            }
                        }
                    }
                }
            }
        assert(m1 == m2);
        assert(sn1.data.subrange(s1.start, s1.start + m1) =~= sn2.data.subrange(s2.start, s2.start + m2));
        }
    }


    pub proof fn lemma_parse_repeat_n_strong_prefix_on<R>(
        s1: SpecStream,
        s2: SpecStream,
        parser: spec_fn(SpecStream) -> SpecParseResult<R>,
        n: nat)
        requires
            prop_parse_well_behaved(parser),
            prop_parse_strong_prefix(parser),
        ensures
            prop_parse_strong_prefix_on(spec_parse_repeat_n(parser, n), s1, s2)
        decreases n
    {
        if let Ok((sout1, n1, x1)) = spec_parse_repeat_n(parser, n)(s1) {
            if 0 <= s1.start <= s1.start + n1 <= s1.data.len() <= usize::MAX
            && 0 <= s2.start <= s2.start + n1 <= s2.data.len() <= usize::MAX
            && s1.data.subrange(s1.start, s1.start + n1) == s2.data.subrange(s2.start, s2.start + n1) {
                if n == 0 {
                } else {
                    // induction on n
                    lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, s1);
                    lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, s2);
                    lemma_parse_repeat_n_strong_prefix_on(s1, s2, parser, (n - 1) as nat);
                    if let Ok((sn1, nn1, xn1)) = spec_parse_repeat_n_rec(parser, (n - 1) as nat, s1) {
                        assert(s1.data.subrange(s1.start, s1.start + nn1) == s2.data.subrange(s2.start, s2.start + nn1)) by {
                            assert(s1.data.subrange(s1.start, s1.start + n1).subrange(0, nn1 as int) =~= s1.data.subrange(s1.start, s1.start + nn1));
                            assert(s2.data.subrange(s2.start, s2.start + n1).subrange(0, nn1 as int) =~= s2.data.subrange(s2.start, s2.start + nn1));
                        }
                        if let Ok((sn2, nn2, xn2)) = spec_parse_repeat_n_rec(parser, (n - 1) as nat, s2) {
                            assert(nn1 == nn2 && xn1 == xn2);
                            lemma_parse_well_behaved_on(parser, sn1);
                            lemma_parse_well_behaved_on(parser, sn2);
                            lemma_parse_strong_prefix_on(parser, sn1, sn2);
                            if let Ok((sn1_, nn1_, xn1_)) = parser(sn1) {
                                // assert(n1 == nn1 + nn1_);
                                assert(s1.data.subrange(s1.start + nn1, s1.start + n1) == s2.data.subrange(s2.start + nn1, s2.start + n1)) by {
                                    assert(s1.data.subrange(s1.start, s1.start + n1).subrange(nn1 as int, n1 as int) =~= s1.data.subrange(s1.start + nn1, s1.start + n1));
                                    assert(s2.data.subrange(s2.start, s2.start + n1).subrange(nn1 as int, n1 as int) =~= s2.data.subrange(s2.start + nn1, s2.start + n1));
                                }
                                assert(sn1.data.subrange(sn1.start, sn1.start + nn1_) == sn2.data.subrange(sn2.start, sn2.start + nn1_));
                                if let Ok((sn2_, nn2_, xn2_)) = parser(sn2) {
                                    assert(nn1_ == nn2_ && xn1_ == xn2_);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

verus! {
    pub open spec fn spec_parse_bytes(s: SpecStream, n: nat) -> SpecParseResult<Seq<u8>>
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start > s.data.len() {
            Err(ParseError::Eof) // don't fail when start == data.len(), which is different from the uint parsers
        } else if s.start + n > usize::MAX {
            Err(ParseError::IntegerOverflow)
        } else if s.start + n > s.data.len() {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + n as int,
                    ..s
                },
                n,
                s.data.subrange(s.start, s.start + n as int),
            ))
        }
    }

    pub open spec fn spec_serialize_bytes(s: SpecStream, v: Seq<u8>, n: nat) -> SpecSerializeResult
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.start + v.len() > usize::MAX {
            Err(SerializeError::IntegerOverflow)
        } else if s.start + v.len() > s.data.len() {
            Err(SerializeError::NotEnoughSpace)
        } else if v.len() != n {
            Err(SerializeError::BytesLengthMismatch)
        } else {
            Ok((
                SpecStream {
                    start: s.start + n as int,
                    data: s.data.subrange(0, s.start) + v + s.data.subrange(s.start + n as int, s.data.len() as int),
                },
                n,
            ))
        }
    }

    pub exec fn parse_bytes(s: Stream, n: usize) -> (res: ParseResult<&[u8]>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_bytes(s, n as nat))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start > s.data.length() {
            Err(ParseError::Eof)
        } else if s.start > usize::MAX - n {
            Err(ParseError::IntegerOverflow)
        } else if s.start + n > s.data.length() {
            Err(ParseError::NotEnoughData)
        } else {
            let data = slice_subrange(s.data, s.start, s.start + n);
            Ok((
                Stream {
                    start: s.start + n,
                    ..s
                },
                n,
                data,
            ))
        }
    }

    pub exec fn serialize_bytes(data: &mut [u8], start: usize, v: &[u8], n: usize) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_bytes(s, v, n as nat))
    {
        let ghost old_data = data.dview();
        if start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if start > usize::MAX - v.length() {
            Err(SerializeError::IntegerOverflow)
        } else if start + v.length() > data.length() {
            Err(SerializeError::NotEnoughSpace)
        } else if v.length() != n {
            Err(SerializeError::BytesLengthMismatch)
        } else {
            let mut i = start;
            let mut j = 0;

            while j < n
                invariant
                    v.dview().len() == n,
                    i - start == j,
                    data.dview().len() == old(data).dview().len(), // critical!
                    0 <= start <= i <= start + n <= data.dview().len() <= usize::MAX,
                    forall |k| 0 <= k < start ==> data.dview()[k] == old(data).dview()[k], // data[0..start] == old(data)[0..start]
                    forall |k| start <= k < start + j ==> data.dview()[k] == v.dview()[k - start], // data[start..start + j] == v[0..j]
                    forall |k| start + n <= k < data.dview().len() ==> data.dview()[k] == old(data).dview()[k], // data[start + n..] == old(data)[start + n..]
            {
                data.set(i, *slice_index_get(v, j)); // data[i] = v[j];
                i = i + 1;
                j = j + 1;
            }
            let ghost spec_res = spec_serialize_bytes(SpecStream {
                data: old_data,
                start: start as int,
            }, v.dview(), n as nat);
            // assert(spec_res.is_ok() && spec_res.unwrap().1 == n && spec_res.unwrap().0.start == (start + n) as int);
            let ghost spec_data = spec_res.unwrap().0.data;
            assert(spec_data == data.dview());
            Ok((
                start + n,
                n,
            ))
        }
    }

    pub proof fn lemma_parse_bytes_well_behaved(n: nat)
        ensures
            prop_parse_well_behaved(|s| spec_parse_bytes(s, n))
    {
        reveal(prop_parse_well_behaved);
        let spec_parse_bytes = |s| spec_parse_bytes(s, n);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_bytes, s) by {
            lemma_parse_bytes_well_behaved_on(s, n)
        }
    }

    pub proof fn lemma_serialize_bytes_well_behaved(n: nat)
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_bytes(s, v, n))
    {
        reveal(prop_serialize_well_behaved);
        let spec_serialize_bytes = |s, v| spec_serialize_bytes(s, v, n);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_bytes, s, v) by {
            lemma_serialize_bytes_well_behaved_on(s, v, n)
        }
    }

    pub proof fn lemma_serialize_bytes_deterministic(n: nat)
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_bytes(s, v, n))
    {
        reveal(prop_serialize_deterministic);
        let spec_serialize_bytes = |s, v| spec_serialize_bytes(s, v, n);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_bytes, s1, s2, v) by {
            lemma_serialize_bytes_deterministic_on(s1, s2, v, n)
        }
    }

    pub proof fn lemma_parse_bytes_strong_prefix(n: nat)
        ensures
            prop_parse_strong_prefix(|s| spec_parse_bytes(s, n))
    {
        reveal(prop_parse_strong_prefix);
        let spec_parse_bytes = |s| spec_parse_bytes(s, n);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_bytes, s1, s2) by {
            lemma_parse_bytes_strong_prefix_on(s1, s2, n)
        }
    }

    pub proof fn lemma_parse_bytes_correct(n: nat)
        ensures
            prop_parse_correct(|s| spec_parse_bytes(s, n), |s, v| spec_serialize_bytes(s, v, n))
    {
        reveal(prop_parse_correct::<Seq<u8>>);
        let spec_parse_bytes = |s| spec_parse_bytes(s, n);
        let spec_serialize_bytes = |s, v| spec_serialize_bytes(s, v, n);
        assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_bytes, spec_serialize_bytes, s, v) by {
            if s.data.len() <= usize::MAX {
                lemma_parse_bytes_correct_on(s, v, n)
            }
        }
    }

    pub proof fn lemma_parse_bytes_serialize_inverse(n: nat)
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_bytes(s, n), |s, v| spec_serialize_bytes(s, v, n))
    {
        reveal(prop_parse_serialize_inverse::<Seq<u8>>);
        let spec_parse_bytes = |s| spec_parse_bytes(s, n);
        let spec_serialize_bytes = |s, v| spec_serialize_bytes(s, v, n);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_bytes, spec_serialize_bytes, s) by {
            lemma_parse_bytes_serialize_inverse_on(s, n)
        }
    }

    pub proof fn lemma_parse_bytes_nonmalleable(n: nat)
        ensures
            prop_parse_nonmalleable(|s| spec_parse_bytes(s, n))
    {
        lemma_parse_bytes_serialize_inverse(n);
        lemma_serialize_bytes_deterministic(n);
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_bytes(s, n), |s, v| spec_serialize_bytes(s, v, n));
    }


    pub proof fn lemma_parse_bytes_well_behaved_on(s: SpecStream, n: nat)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_bytes(s, n), s)
    {}

    pub proof fn lemma_serialize_bytes_well_behaved_on(s: SpecStream, v: Seq<u8>, n: nat)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_bytes(s, v, n), s, v)
    {
        if let Ok((sout, m)) = spec_serialize_bytes(s, v, n) {
            assert(m == n);
            assert(sout.data.len() =~= s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + m, s.data.len() as int) =~= s.data.subrange(s.start + m, s.data.len() as int));
        }
    }

    pub proof fn lemma_serialize_bytes_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>, n: nat)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_bytes(s, v, n), s1, s2, v)
    {
        let n = v.len();
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_bytes(s1, v, n), spec_serialize_bytes(s2, v, n)) {
            assert(n1 == n && n2 == n);
            assert(sout1.data.subrange(s1.start, s1.start + n) =~= sout2.data.subrange(s2.start, s2.start + n));
        }
    }

    pub proof fn lemma_parse_bytes_strong_prefix_on(s1: SpecStream, s2: SpecStream, n: nat)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_bytes(s, n), s1, s2)
    {
        if let Ok((sout1, m1, x1)) = spec_parse_bytes(s1, n) {
            if 0 <= s1.start <= s1.start + m1 <= s1.data.len() <= usize::MAX
            && 0 <= s2.start <= s2.start + m1 <= s2.data.len() <= usize::MAX
            && s1.data.subrange(s1.start, s1.start + m1) == s2.data.subrange(s2.start, s2.start + m1) {
                if let Ok((sout2, m2, x2)) = spec_parse_bytes(s2, m1) {
                    assert(m1 == m2);
                    assert(x1 == x2);
                }
            }
        }
    }

    pub proof fn lemma_parse_bytes_correct_on(s: SpecStream, v: Seq<u8>, n: nat)
        requires s.data.len() <= usize::MAX,
        ensures
            prop_parse_correct_on(|s| spec_parse_bytes(s, n), |s, v| spec_serialize_bytes(s, v, n), s, v)
    {
        if let Ok((sout, m1)) = spec_serialize_bytes(s, v, n) {
            if let Ok((_, m2, res)) = spec_parse_bytes(SpecStream {start: s.start, ..sout}, n) {
                assert(m1 == m2);
                assert(res =~= v);
            }
        }
    }

    pub proof fn lemma_parse_bytes_serialize_inverse_on(s: SpecStream, n: nat)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_bytes(s, n), |s, v| spec_serialize_bytes(s, v, n), s)
    {
        if let Ok((sout, m1, x)) = spec_parse_bytes(s, n) {
            if let Ok((sout2, m2)) = spec_serialize_bytes(s, x, m1) {
                assert(m1 == m2);
                assert(sout.data =~= sout2.data);
            }
        }
    }

}

verus! {

    /// A parser that consumes the rest of the input.
    pub open spec fn spec_parse_tail(s: SpecStream) -> SpecParseResult<Seq<u8>>
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.data.len() > usize::MAX {
            Err(ParseError::IntegerOverflow)
        } else if s.start > s.data.len() {
            Err(ParseError::Eof) // don't fail when start == data.len(), which is different from the uint parsers
        } else {
            let n = s.data.len() as int;
            Ok((
                SpecStream {
                    start: n,
                    ..s
                },
                (n - s.start) as nat,
                s.data.subrange(s.start, n),
            ))
        }
    }

    pub open spec fn spec_serialize_tail(s: SpecStream, v: Seq<u8>) -> SpecSerializeResult
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.start + v.len() > usize::MAX {
            Err(SerializeError::IntegerOverflow)
        } else if s.start + v.len() > s.data.len() {
            Err(SerializeError::NotEnoughSpace)
        } else if v.len() != s.data.len() - s.start {
            Err(SerializeError::TailLengthMismatch)
        } else {
            let n = v.len() as int;
            Ok((
                SpecStream {
                    start: s.start + n,
                    data: s.data.subrange(0, s.start) + v,
                },
                n as nat,
            ))
        }
    }

    pub exec fn parse_tail(s: Stream) -> (res: ParseResult<&[u8]>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_tail(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start > s.data.length() {
            Err(ParseError::Eof)
        } else {
            let n = s.data.length();
            let data = slice_subrange(s.data, s.start, n);
            Ok((
                Stream {
                    start: n,
                    ..s
                },
                n - s.start,
                data,
            ))
        }
    }

    pub exec fn serialize_tail(data: &mut [u8], start: usize, v: &[u8]) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_tail(s, v))
    {
        let ghost old_data = data.dview();
        if start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if start > usize::MAX - v.length() {
            Err(SerializeError::IntegerOverflow)
        } else if start + v.length() > data.length() {
            Err(SerializeError::NotEnoughSpace)
        } else if v.length() != data.length() - start {
            Err(SerializeError::TailLengthMismatch)
        } else {
            let n = v.length();
            let mut i = start;
            let mut j = 0;

            while j < n
                invariant
                    v.dview().len() == n,
                    i - start == j,
                    data.dview().len() == old(data).dview().len(),
                    0 <= start <= i <= start + n <= data.dview().len() <= usize::MAX,
                    forall |k| 0 <= k < start ==> data.dview()[k] == old(data).dview()[k], // data[0..start] == old(data)[0..start]
                    forall |k| start <= k < start + j ==> data.dview()[k] == v.dview()[k - start], // data[start..start + j] == v[0..j]
            {
                data.set(i, *slice_index_get(v, j)); // data[i] = v[j];
                i = i + 1;
                j = j + 1;
            }
            let ghost spec_res = spec_serialize_tail(SpecStream {
                data: old_data,
                start: start as int,
            }, v.dview());
            let ghost spec_data = spec_res.unwrap().0.data;
            assert(spec_data == data.dview());
            Ok((
                start + n,
                n,
            ))
        }
    }

    pub proof fn lemma_parse_tail_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_tail(s))
    {
        reveal(prop_parse_well_behaved::<Seq<u8>>);
        let spec_parse_tail = |s| spec_parse_tail(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_tail, s) by {
            lemma_parse_tail_well_behaved_on(s)
        }
    }

    pub proof fn lemma_serialize_tail_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_tail(s, v))
    {
        reveal(prop_serialize_well_behaved::<Seq<u8>>);
        let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_tail, s, v) by {
            lemma_serialize_tail_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_tail_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_tail(s, v))
    {
        reveal(prop_serialize_deterministic::<Seq<u8>>);
        let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_tail, s1, s2, v) by {
            lemma_serialize_tail_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_parse_tail_correct()
        ensures
            prop_parse_correct(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v))
    {
        reveal(prop_parse_correct::<Seq<u8>>);
        let spec_parse_tail = |s| spec_parse_tail(s);
        let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
        assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_tail, spec_serialize_tail, s, v) by {
            if s.data.len() <= usize::MAX {
                lemma_parse_tail_correct_on(s, v)
            }
        }
    }

    pub proof fn lemma_parse_tail_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v))
    {
        reveal(prop_parse_serialize_inverse::<Seq<u8>>);
        let spec_parse_tail = |s| spec_parse_tail(s);
        let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_tail, spec_serialize_tail, s) by {
            lemma_parse_tail_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_tail_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_tail(s))
    {
        lemma_parse_tail_serialize_inverse();
        lemma_serialize_tail_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v));
    }

    proof fn lemma_parse_tail_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_tail(s), s)
    {}

    proof fn lemma_serialize_tail_well_behaved_on(s: SpecStream, v: Seq<u8>)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_tail(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_tail(s, v) {
            assert(n == v.len());
            assert(sout.data.len() =~= s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + n, s.data.len() as int) =~= s.data.subrange(s.start + n, s.data.len() as int));
        }
    }

    proof fn lemma_serialize_tail_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_tail(s, v), s1, s2, v)
    {
        let n = v.len();
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_tail(s1, v), spec_serialize_tail(s2, v)) {
            assert(n1 == n && n2 == n);
            assert(sout1.data.subrange(s1.start, s1.start + n) =~= sout2.data.subrange(s2.start, s2.start + n));
        }
    }

    proof fn lemma_parse_tail_correct_on(s: SpecStream, v: Seq<u8>)
        requires s.data.len() <= usize::MAX,
        ensures
            prop_parse_correct_on(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_tail(s, v) {
            if let Ok((_, m, res)) = spec_parse_tail(SpecStream {start: s.start, ..sout}) {
                assert(n == m);
                assert(res =~= v);
            }
        }
    }

    proof fn lemma_parse_tail_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v), s)
    {
        if let Ok((sout, n, x)) = spec_parse_tail(s) {
            if let Ok((sout2, m)) = spec_serialize_tail(s, x) {
                assert(n == m);
                assert(sout.data =~= sout2.data);
            } else {
                assert(false);
            }
        }
    }
}

// secret parsers and serializers

verus! {

    #[verifier(opaque)]
    pub open spec fn prop_sec_parse_exec_spec_equiv<T, P>(
        exec_parser: P,
        spec_parser: spec_fn(SpecStream) -> SpecParseResult<T::V>) -> bool
        where
            P: FnOnce(SecStream) -> SecParseResult<T>,
            T: DView,
    {
        &&& forall |s| #[trigger] exec_parser.requires((s,))
        &&& forall |s, res| #[trigger] exec_parser.ensures((s,), res) ==> prop_sec_parse_exec_spec_equiv_on(s, res, spec_parser)
    }

    #[verifier(opaque)]
    pub open spec fn prop_sec_serialize_exec_spec_equiv<T, P>(
        exec_serializer: P,
        spec_serializer: spec_fn(SpecStream, T::V) -> SpecSerializeResult) -> bool
        where
            P: FnOnce(SecStream, T) -> SecSerializeResult,
            T: std::fmt::Debug + DView,
    {
        &&& forall |s, v| #[trigger] exec_serializer.requires((s, v))
        &&& forall |s, v, res| #[trigger] exec_serializer.ensures((s, v), res) ==> prop_sec_serialize_exec_spec_equiv_on(s, v, res, spec_serializer)
    }


    pub proof fn lemma_sec_parse_exec_spec_equiv_on<T, P>(
        exec_parser: P,
        spec_parser: spec_fn(SpecStream) -> SpecParseResult<T::V>,
        s: SecStream, res: SecParseResult<T>)
        where
            P: FnOnce(SecStream) -> SecParseResult<T>,
            T: DView,
        requires
            prop_sec_parse_exec_spec_equiv(exec_parser, spec_parser),
            exec_parser.ensures((s,), res)
        ensures
            prop_sec_parse_exec_spec_equiv_on(s, res, spec_parser)
    {
        reveal(prop_sec_parse_exec_spec_equiv);
    }

    pub proof fn lemma_sec_serialize_exec_spec_equiv_on<T, P>(
        exec_serializer: P,
        spec_serializer: spec_fn(SpecStream, T::V) -> SpecSerializeResult,
        s: SecStream, v: T, res: SecSerializeResult)
        where
            P: FnOnce(SecStream, T) -> SecSerializeResult,
            T: std::fmt::Debug + DView,
        requires
            prop_sec_serialize_exec_spec_equiv(exec_serializer, spec_serializer),
            exec_serializer.ensures((s, v), res)
        ensures
            prop_sec_serialize_exec_spec_equiv_on(s, v, res, spec_serializer)
    {
        reveal(prop_sec_serialize_exec_spec_equiv);
    }


    // would be great if Verus supports impl DView<V = SpecStream>

    pub open spec fn prop_sec_parse_exec_spec_equiv_on<T: DView>(
        s: SecStream,
        res: SecParseResult<T>,
        spec_parser: spec_fn(SpecStream) -> SpecParseResult<T::V>) -> bool
    {
        match spec_parser(s.dview()) {
            Ok((sout, sn, sx)) => {
                if let Ok((s, n, x)) = res {
                    &&& s.dview() == sout
                    &&& n == sn
                    &&& x.dview() == sx
                } else {
                    false
                }
            }
            Err(e) => {
                if let Err(e2) = res {
                    e == e2
                } else {
                    false
                }
            }
        }
    }

    pub open spec fn prop_sec_serialize_exec_spec_equiv_on<T: DView>(
        s: SecStream,
        v: T,
        res: SecSerializeResult,
        spec_serializer: spec_fn(SpecStream, T::V) -> SpecSerializeResult) -> bool
        where T: std::fmt::Debug + DView
    {
        match spec_serializer(s.dview(), v.dview()) {
            Ok((sout, sn)) => {
                &&& res.is_ok()
                &&& res.unwrap().0.dview() == sout
                &&& res.unwrap().1 == sn
            }
            Err(e) => res.is_err() && res.unwrap_err() == e
        }
    }

}

verus! {
    pub exec fn sec_parse_pair<P1, P2, R1, R2>(
        exec_parser1: P1,
        exec_parser2: P2,
        Ghost(spec_parser1): Ghost<spec_fn(SpecStream) -> SpecParseResult<R1::V>>,
        Ghost(spec_parser2): Ghost<spec_fn(SpecStream) -> SpecParseResult<R2::V>>,
        s: SecStream) -> (res: SecParseResult<(R1,R2)>)
        where
            R1: DView,
            R2: DView,
            P1: FnOnce(SecStream) -> SecParseResult<R1>,
            P2: FnOnce(SecStream) -> SecParseResult<R2>,
        requires
            prop_sec_parse_exec_spec_equiv(exec_parser1, spec_parser1),
            prop_sec_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        ensures
            prop_sec_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2))
        // prop_parse_exec_spec_equiv(parse_pair(exec_parser1, exec_parser2, spec_parser1, spec_parser2), spec_parse_pair(spec_parser1, spec_parser2))
    {
        proof { reveal(prop_sec_parse_exec_spec_equiv); }
        let res1 = exec_parser1(s);
        proof { lemma_sec_parse_exec_spec_equiv_on(exec_parser1, spec_parser1, s, res1); }
        match res1 {
            Ok((s1, n1, r1)) => {
                let res2 = exec_parser2(s1);
                proof { lemma_sec_parse_exec_spec_equiv_on(exec_parser2, spec_parser2, s1, res2); }
                match res2 {
                    Ok((s2, n2, r2)) => {
                        if n1 > usize::MAX - n2 {
                            Err(ParseError::IntegerOverflow)
                        } else {
                            Ok((s2, n1 + n2, (r1, r2)))
                        }
                    }
                    Err(e) => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    }

    pub exec fn sec_serialize_pair<S1, S2, T1, T2>(
        exec_serializer1: S1,
        exec_serializer2: S2,
        Ghost(spec_serializer1): Ghost<spec_fn(SpecStream, T1::V) -> SpecSerializeResult>,
        Ghost(spec_serializer2): Ghost<spec_fn(SpecStream, T2::V) -> SpecSerializeResult>,
        s: SecStream, v: (T1, T2)) -> (res: SecSerializeResult)
        where
            S1: FnOnce(SecStream, T1) -> SecSerializeResult,
            S2: FnOnce(SecStream, T2) -> SecSerializeResult,
            T1: std::fmt::Debug + DView,
            T2: std::fmt::Debug + DView,
        requires
            prop_sec_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
            prop_sec_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
        ensures
            prop_sec_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serializer1, spec_serializer2))
    {
        proof { reveal(prop_sec_serialize_exec_spec_equiv); }
        let res1 = exec_serializer1(s, v.0);
        proof { lemma_sec_serialize_exec_spec_equiv_on(exec_serializer1, spec_serializer1, s, v.0, res1); }
        match res1 {
            Ok((s, n)) => {
                let res2 = exec_serializer2(s, v.1);
                proof { lemma_sec_serialize_exec_spec_equiv_on(exec_serializer2, spec_serializer2, s, v.1, res2); }
                match res2 {
                    Ok((s, m)) => {
                        if n > usize::MAX - m {
                            Err(SerializeError::IntegerOverflow)
                        } else {
                            Ok((s, n + m))
                        }
                    }
                    Err(e) => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    }

}

verus! {

    pub exec fn parse_sec_bytes(s: SecStream, n: usize) -> (res: SecParseResult<SecBytes>)
        ensures
            prop_sec_parse_exec_spec_equiv_on(s, res, |s| spec_parse_bytes(s, n as nat))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start > s.data.length() {
            Err(ParseError::Eof)
        } else if s.start > usize::MAX - n {
            Err(ParseError::IntegerOverflow)
        } else if s.start + n > s.data.length() {
            Err(ParseError::NotEnoughData)
        } else {
            let data = s.data.subrange(s.start, s.start + n);
            Ok((
                SecStream {
                    start: s.start + n,
                    ..s
                },
                n,
                data,
            ))
        }
    }

    pub exec fn serialize_sec_bytes(s: SecStream, v: SecBytes, n: usize) -> (res: SecSerializeResult)
        ensures
            prop_sec_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_bytes(s, v, n as nat))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.start > usize::MAX - v.length() {
            Err(SerializeError::IntegerOverflow)
        } else if s.start + v.length() > s.data.length() {
            Err(SerializeError::NotEnoughSpace)
        } else if v.length() != n {
            Err(SerializeError::BytesLengthMismatch)
        } else {
            let mut data = s.data.subrange(0, s.start);
            let mut rem = s.data.subrange(s.start + n, s.data.length());
            let mut v = v;
            data.append(&mut v);
            data.append(&mut rem);
            Ok((
                SecStream {
                    start: s.start + n,
                    data,
                },
                n,
            ))
        }
    }

    pub exec fn sec_parse_tail(s: SecStream) -> (res: SecParseResult<SecBytes>)
        ensures
            prop_sec_parse_exec_spec_equiv_on(s, res, |s| spec_parse_tail(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start > s.data.length() {
            Err(ParseError::Eof)
        } else {
            let n = s.data.length();
            // data is the rest of the input starting from s.start
            let data = s.data.subrange(s.start, n);
            Ok((
                SecStream {
                    start: n,
                    ..s
                },
                (n - s.start),
                data,
            ))
        }
    }

    pub exec fn sec_serialize_tail(s: SecStream, v: SecBytes) -> (res: SecSerializeResult)
        ensures
            prop_sec_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_tail(s, v))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.start > usize::MAX - v.length() {
            Err(SerializeError::IntegerOverflow)
        } else if s.start + v.length() > s.data.length() {
            Err(SerializeError::NotEnoughSpace)
        } else if v.length() != s.data.length() - s.start {
            Err(SerializeError::TailLengthMismatch)
        } else {
            let n = v.length();

            let mut data = s.data.subrange(0, s.start);
            let mut v = v;
            data.append(&mut v);
            Ok((
                SecStream {
                    start: s.start + n,
                    data
                },
                n,
            ))
        }
    }
}
verus!{

pub open spec fn spec_parse_u8_le_1(s: SpecStream) -> SpecParseResult<u8>
{
    match spec_parse_u8_le(s) {
        Ok((s, n, v)) => {
            if v == 1 {
                Ok((s, n, v))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub open spec fn spec_serialize_u8_le_1(s: SpecStream, v: u8) -> SpecSerializeResult
{
    if v == 1 {
        spec_serialize_u8_le(s, v)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub exec fn parse_u8_le_1(s: Stream) -> (res: ParseResult<u8>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le_1(s))
{
    let (s, n, v) = parse_u8_le(s)?;
    if v == 1 {
        Ok((s, n, v))
    } else {
        Err(ParseError::ConstMismatch)
    }
}

pub exec fn serialize_u8_le_1(data: &mut [u8], start: usize, v: u8) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v, res, |s, v| spec_serialize_u8_le_1(s, v))
{
    if v == 1 {
        serialize_u8_le(data, start, v)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub proof fn lemma_parse_u8_le_1_well_behaved()
    ensures
        prop_parse_well_behaved(|s| spec_parse_u8_le_1(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u8_le_1, s) by {
        lemma_parse_u8_le_well_behaved_on(s)
    }
}

pub proof fn lemma_serialize_u8_le_1_well_behaved()
    ensures
        prop_serialize_well_behaved(|s, v| spec_serialize_u8_le_1(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u8_le_1, s, v) by {
        lemma_serialize_u8_le_well_behaved_on(s, v)
    }
}

pub proof fn lemma_serialize_u8_le_1_deterministic()
    ensures
        prop_serialize_deterministic(|s, v| spec_serialize_u8_le_1(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u8_le_1, s1, s2, v) by {
        lemma_serialize_u8_le_deterministic_on(s1, s2, v)
    }
}

pub proof fn lemma_parse_u8_le_1_strong_prefix()
    ensures
        prop_parse_strong_prefix(|s| spec_parse_u8_le_1(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u8_le_1, s1, s2) by {
        lemma_parse_u8_le_strong_prefix_on(s1, s2)
    }
}

pub proof fn lemma_parse_u8_le_1_correct()
    ensures
        prop_parse_correct(|s| spec_parse_u8_le_1(s), |s, v| spec_serialize_u8_le_1(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u8_le_1, spec_serialize_u8_le_1, s, v) by {
        lemma_parse_u8_le_correct_on(s, v)
    }
}

pub proof fn lemma_parse_u8_le_1_serialize_inverse()
    ensures
        prop_parse_serialize_inverse(|s| spec_parse_u8_le_1(s), |s, v| spec_serialize_u8_le_1(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u8_le_1, spec_serialize_u8_le_1, s) by {
        lemma_parse_u8_le_serialize_inverse_on(s)
    }
}

pub proof fn lemma_parse_u8_le_1_nonmalleable()
    ensures
        prop_parse_nonmalleable(|s| spec_parse_u8_le_1(s))
{
    lemma_parse_u8_le_1_serialize_inverse();
    lemma_serialize_u8_le_1_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u8_le_1(s), |s, v| spec_serialize_u8_le_1(s, v));
}


pub open spec fn spec_parse_3_bytes_5058554103549626993(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    match spec_parse_bytes(s, 3) {
        Ok((s, n, xs)) => {
            if xs == seq![0u8, 0u8, 0u8] {
                Ok((s, n, xs))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub open spec fn spec_serialize_3_bytes_5058554103549626993(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    if vs == seq![0u8, 0u8, 0u8] {
        spec_serialize_bytes(s, vs, 3)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}


pub proof fn lemma_parse_3_bytes_5058554103549626993_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_3_bytes_5058554103549626993(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_3_bytes_5058554103549626993, s) by {
        lemma_parse_3_bytes_5058554103549626993_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_3_bytes_5058554103549626993_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_3_bytes_5058554103549626993 = |s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_3_bytes_5058554103549626993, s, vs) by {
        lemma_serialize_3_bytes_5058554103549626993_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_3_bytes_5058554103549626993_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_3_bytes_5058554103549626993(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_3_bytes_5058554103549626993, s1, s2, v) by {
        lemma_serialize_3_bytes_5058554103549626993_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_3_bytes_5058554103549626993_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_3_bytes_5058554103549626993(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_3_bytes_5058554103549626993, s1, s2) by {
        lemma_parse_3_bytes_5058554103549626993_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_3_bytes_5058554103549626993_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_3_bytes_5058554103549626993(s), |s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_serialize_3_bytes_5058554103549626993 = |s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_3_bytes_5058554103549626993, spec_serialize_3_bytes_5058554103549626993, s) by {
        lemma_parse_3_bytes_5058554103549626993_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_3_bytes_5058554103549626993_correct()
    ensures prop_parse_correct(|s| spec_parse_3_bytes_5058554103549626993(s), |s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_serialize_3_bytes_5058554103549626993 = |s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs);
    assert forall |s: SpecStream, vs| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_3_bytes_5058554103549626993, spec_serialize_3_bytes_5058554103549626993, s, vs) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_3_bytes_5058554103549626993_correct_on(s, vs);
        }
    }
}

proof fn lemma_parse_3_bytes_5058554103549626993_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_3_bytes_5058554103549626993(s), s)
{
    lemma_parse_bytes_well_behaved_on(s, 3)
}

proof fn lemma_serialize_3_bytes_5058554103549626993_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs), s, vs)
{
    lemma_serialize_bytes_well_behaved_on(s, vs, 3)
}

proof fn lemma_serialize_3_bytes_5058554103549626993_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_3_bytes_5058554103549626993(s, v), s1, s2, v)
{
    lemma_serialize_bytes_deterministic_on(s1, s2, v, 3)
}

proof fn lemma_parse_3_bytes_5058554103549626993_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_3_bytes_5058554103549626993(s), s1, s2)
{
    lemma_parse_bytes_strong_prefix_on(s1, s2, 3)
}

proof fn lemma_parse_3_bytes_5058554103549626993_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_3_bytes_5058554103549626993(s), |s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs), s)
{
    lemma_parse_bytes_serialize_inverse_on(s, 3)
}

proof fn lemma_parse_3_bytes_5058554103549626993_correct_on(s: SpecStream, vs: Seq<u8>)
    requires s.data.len() <= usize::MAX,
    ensures prop_parse_correct_on(|s| spec_parse_3_bytes_5058554103549626993(s), |s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs), s, vs)
{
    lemma_parse_bytes_correct_on(s, vs, 3)
}

pub exec fn slice_u8_check_5058554103549626993(xs : &[u8]) -> (res : bool)
    requires xs.dview().len() == 3
    ensures res <==> xs.dview() == seq![0u8, 0u8, 0u8]
{
    let constant: [u8; 3] = [0u8, 0u8, 0u8];
    assert(constant.view() =~= seq![0u8, 0u8, 0u8]);
    let mut i = 0;
    while i < 3
        invariant
            0 <= i <= 3,
            constant@ == seq![0u8, 0u8, 0u8],
            xs.dview().len() == 3,
            xs.dview().subrange(0, i as int) =~= constant@.subrange(0, i as int),
    {
        let (constant_i, xi) = (*array_index_get(&constant, i), *slice_index_get(&xs, i));
        if constant_i == xi {
            i = i + 1;
            assert(xs.dview().subrange(0, i as int) =~= xs.dview().subrange(0, i as int - 1).push(xi));
        } else {
            return false;
        }
    }
    assert(xs.dview() =~= seq![0u8, 0u8, 0u8]) by {
        assert(xs.dview().subrange(0, 3) =~= xs.dview());
    }

    true
}

pub exec fn parse_3_bytes_5058554103549626993(s: Stream) -> (res: ParseResult<&[u8]>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_3_bytes_5058554103549626993(s)),
        res.is_ok() ==> res.unwrap().2.dview() == seq![0u8, 0u8, 0u8]
{
    let (s0, n, xs) = parse_bytes(s, 3)?;
    assert(xs.dview().len() == 3);

    if slice_u8_check_5058554103549626993(xs) {
        Ok((s0, n, xs))
    } else {
        Err(ParseError::ConstMismatch)
    }
}

pub exec fn serialize_3_bytes_5058554103549626993(data: &mut [u8], start: usize, vs: &[u8]) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), vs.dview(), res, |s, vs| spec_serialize_3_bytes_5058554103549626993(s, vs))
{
    if vs.length() == 3 && slice_u8_check_5058554103549626993(vs) {
        serialize_bytes(data, start, vs, 3)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub open spec fn spec_parse_4_bytes(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    spec_parse_bytes(s, 4)
}

pub open spec fn spec_serialize_4_bytes(s: SpecStream, v: Seq<u8>) -> SpecSerializeResult
{
    spec_serialize_bytes(s, v, 4)
}

pub proof fn lemma_parse_4_bytes_well_behaved()
    ensures
        prop_parse_well_behaved(|s| spec_parse_4_bytes(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_4_bytes, s) by {
        lemma_parse_4_bytes_well_behaved_on(s)
    }
}

pub proof fn lemma_serialize_4_bytes_well_behaved()
    ensures
        prop_serialize_well_behaved(|s, v| spec_serialize_4_bytes(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_4_bytes, s, v) by {
        lemma_serialize_4_bytes_well_behaved_on(s, v)
    }
}

pub proof fn lemma_serialize_4_bytes_deterministic()
    ensures
        prop_serialize_deterministic(|s, v| spec_serialize_4_bytes(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_4_bytes, s1, s2, v) by {
        lemma_serialize_4_bytes_deterministic_on(s1, s2, v)
    }
}

pub proof fn lemma_parse_4_bytes_strong_prefix()
    ensures
        prop_parse_strong_prefix(|s| spec_parse_4_bytes(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_4_bytes, s1, s2) by {
        lemma_parse_4_bytes_strong_prefix_on(s1, s2)
    }
}

pub proof fn lemma_parse_4_bytes_correct()
    ensures
        prop_parse_correct(|s| spec_parse_4_bytes(s), |s, v| spec_serialize_4_bytes(s, v))
{
    reveal(prop_parse_correct::<Seq<u8>>);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_4_bytes, spec_serialize_4_bytes, s, v) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_4_bytes_correct_on(s, v)
        }
    }
}

pub proof fn lemma_parse_4_bytes_serialize_inverse()
    ensures
        prop_parse_serialize_inverse(|s| spec_parse_4_bytes(s), |s, v| spec_serialize_4_bytes(s, v))
{
    reveal(prop_parse_serialize_inverse::<Seq<u8>>);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_4_bytes, spec_serialize_4_bytes, s) by {
        lemma_parse_4_bytes_serialize_inverse_on(s)
    }
}

pub proof fn lemma_parse_4_bytes_nonmalleable()
    ensures
        prop_parse_nonmalleable(|s| spec_parse_4_bytes(s))
{
    lemma_parse_4_bytes_serialize_inverse();
    lemma_serialize_4_bytes_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_4_bytes(s), |s, v| spec_serialize_4_bytes(s, v));
}


proof fn lemma_parse_4_bytes_well_behaved_on(s: SpecStream)
    ensures
        prop_parse_well_behaved_on(|s| spec_parse_4_bytes(s), s)
{
    lemma_parse_bytes_well_behaved_on(s, 4);
}

proof fn lemma_serialize_4_bytes_well_behaved_on(s: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_well_behaved_on(|s, v| spec_serialize_4_bytes(s, v), s, v)
{
    lemma_serialize_bytes_well_behaved_on(s, v, 4);
}

proof fn lemma_serialize_4_bytes_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_deterministic_on(|s, v| spec_serialize_4_bytes(s, v), s1, s2, v)
{
    lemma_serialize_bytes_deterministic_on(s1, s2, v, 4);
}

proof fn lemma_parse_4_bytes_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures
        prop_parse_strong_prefix_on(|s| spec_parse_4_bytes(s), s1, s2)
{
    lemma_parse_bytes_strong_prefix_on(s1, s2, 4);
}

proof fn lemma_parse_4_bytes_correct_on(s: SpecStream, v: Seq<u8>)
    requires s.data.len() <= usize::MAX,
    ensures
        prop_parse_correct_on(|s| spec_parse_4_bytes(s), |s, v| spec_serialize_4_bytes(s, v), s, v)
{
    lemma_parse_bytes_correct_on(s, v, 4);
}

proof fn lemma_parse_4_bytes_serialize_inverse_on(s: SpecStream)
    ensures
        prop_parse_serialize_inverse_on(|s| spec_parse_4_bytes(s), |s, v| spec_serialize_4_bytes(s, v), s)
{
    lemma_parse_bytes_serialize_inverse_on(s, 4);
}

pub exec fn parse_4_bytes(s: Stream) -> (res: ParseResult<&[u8]>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_bytes(s))
{
    parse_bytes(s, 4)
}
pub exec fn serialize_4_bytes(data: &mut [u8], start: usize, v: &[u8]) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_bytes(s, v, 4 as nat))
{
    serialize_bytes(data, start, v, 4)
}

            
pub open spec fn spec_parse_32_bytes(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    spec_parse_bytes(s, 32)
}

pub open spec fn spec_serialize_32_bytes(s: SpecStream, v: Seq<u8>) -> SpecSerializeResult
{
    spec_serialize_bytes(s, v, 32)
}

pub proof fn lemma_parse_32_bytes_well_behaved()
    ensures
        prop_parse_well_behaved(|s| spec_parse_32_bytes(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_32_bytes, s) by {
        lemma_parse_32_bytes_well_behaved_on(s)
    }
}

pub proof fn lemma_serialize_32_bytes_well_behaved()
    ensures
        prop_serialize_well_behaved(|s, v| spec_serialize_32_bytes(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_32_bytes, s, v) by {
        lemma_serialize_32_bytes_well_behaved_on(s, v)
    }
}

pub proof fn lemma_serialize_32_bytes_deterministic()
    ensures
        prop_serialize_deterministic(|s, v| spec_serialize_32_bytes(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_32_bytes, s1, s2, v) by {
        lemma_serialize_32_bytes_deterministic_on(s1, s2, v)
    }
}

pub proof fn lemma_parse_32_bytes_strong_prefix()
    ensures
        prop_parse_strong_prefix(|s| spec_parse_32_bytes(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_32_bytes, s1, s2) by {
        lemma_parse_32_bytes_strong_prefix_on(s1, s2)
    }
}

pub proof fn lemma_parse_32_bytes_correct()
    ensures
        prop_parse_correct(|s| spec_parse_32_bytes(s), |s, v| spec_serialize_32_bytes(s, v))
{
    reveal(prop_parse_correct::<Seq<u8>>);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_32_bytes, spec_serialize_32_bytes, s, v) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_32_bytes_correct_on(s, v)
        }
    }
}

pub proof fn lemma_parse_32_bytes_serialize_inverse()
    ensures
        prop_parse_serialize_inverse(|s| spec_parse_32_bytes(s), |s, v| spec_serialize_32_bytes(s, v))
{
    reveal(prop_parse_serialize_inverse::<Seq<u8>>);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_32_bytes, spec_serialize_32_bytes, s) by {
        lemma_parse_32_bytes_serialize_inverse_on(s)
    }
}

pub proof fn lemma_parse_32_bytes_nonmalleable()
    ensures
        prop_parse_nonmalleable(|s| spec_parse_32_bytes(s))
{
    lemma_parse_32_bytes_serialize_inverse();
    lemma_serialize_32_bytes_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_32_bytes(s), |s, v| spec_serialize_32_bytes(s, v));
}


proof fn lemma_parse_32_bytes_well_behaved_on(s: SpecStream)
    ensures
        prop_parse_well_behaved_on(|s| spec_parse_32_bytes(s), s)
{
    lemma_parse_bytes_well_behaved_on(s, 32);
}

proof fn lemma_serialize_32_bytes_well_behaved_on(s: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_well_behaved_on(|s, v| spec_serialize_32_bytes(s, v), s, v)
{
    lemma_serialize_bytes_well_behaved_on(s, v, 32);
}

proof fn lemma_serialize_32_bytes_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_deterministic_on(|s, v| spec_serialize_32_bytes(s, v), s1, s2, v)
{
    lemma_serialize_bytes_deterministic_on(s1, s2, v, 32);
}

proof fn lemma_parse_32_bytes_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures
        prop_parse_strong_prefix_on(|s| spec_parse_32_bytes(s), s1, s2)
{
    lemma_parse_bytes_strong_prefix_on(s1, s2, 32);
}

proof fn lemma_parse_32_bytes_correct_on(s: SpecStream, v: Seq<u8>)
    requires s.data.len() <= usize::MAX,
    ensures
        prop_parse_correct_on(|s| spec_parse_32_bytes(s), |s, v| spec_serialize_32_bytes(s, v), s, v)
{
    lemma_parse_bytes_correct_on(s, v, 32);
}

proof fn lemma_parse_32_bytes_serialize_inverse_on(s: SpecStream)
    ensures
        prop_parse_serialize_inverse_on(|s| spec_parse_32_bytes(s), |s, v| spec_serialize_32_bytes(s, v), s)
{
    lemma_parse_bytes_serialize_inverse_on(s, 32);
}

pub exec fn parse_32_bytes(s: Stream) -> (res: ParseResult<&[u8]>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_32_bytes(s))
{
    parse_bytes(s, 32)
}
pub exec fn serialize_32_bytes(data: &mut [u8], start: usize, v: &[u8]) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_bytes(s, v, 32 as nat))
{
    serialize_bytes(data, start, v, 32)
}

            
pub open spec fn spec_parse_48_bytes(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    spec_parse_bytes(s, 48)
}

pub open spec fn spec_serialize_48_bytes(s: SpecStream, v: Seq<u8>) -> SpecSerializeResult
{
    spec_serialize_bytes(s, v, 48)
}

pub proof fn lemma_parse_48_bytes_well_behaved()
    ensures
        prop_parse_well_behaved(|s| spec_parse_48_bytes(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_48_bytes, s) by {
        lemma_parse_48_bytes_well_behaved_on(s)
    }
}

pub proof fn lemma_serialize_48_bytes_well_behaved()
    ensures
        prop_serialize_well_behaved(|s, v| spec_serialize_48_bytes(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_48_bytes, s, v) by {
        lemma_serialize_48_bytes_well_behaved_on(s, v)
    }
}

pub proof fn lemma_serialize_48_bytes_deterministic()
    ensures
        prop_serialize_deterministic(|s, v| spec_serialize_48_bytes(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_48_bytes, s1, s2, v) by {
        lemma_serialize_48_bytes_deterministic_on(s1, s2, v)
    }
}

pub proof fn lemma_parse_48_bytes_strong_prefix()
    ensures
        prop_parse_strong_prefix(|s| spec_parse_48_bytes(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_48_bytes, s1, s2) by {
        lemma_parse_48_bytes_strong_prefix_on(s1, s2)
    }
}

pub proof fn lemma_parse_48_bytes_correct()
    ensures
        prop_parse_correct(|s| spec_parse_48_bytes(s), |s, v| spec_serialize_48_bytes(s, v))
{
    reveal(prop_parse_correct::<Seq<u8>>);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_48_bytes, spec_serialize_48_bytes, s, v) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_48_bytes_correct_on(s, v)
        }
    }
}

pub proof fn lemma_parse_48_bytes_serialize_inverse()
    ensures
        prop_parse_serialize_inverse(|s| spec_parse_48_bytes(s), |s, v| spec_serialize_48_bytes(s, v))
{
    reveal(prop_parse_serialize_inverse::<Seq<u8>>);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_48_bytes, spec_serialize_48_bytes, s) by {
        lemma_parse_48_bytes_serialize_inverse_on(s)
    }
}

pub proof fn lemma_parse_48_bytes_nonmalleable()
    ensures
        prop_parse_nonmalleable(|s| spec_parse_48_bytes(s))
{
    lemma_parse_48_bytes_serialize_inverse();
    lemma_serialize_48_bytes_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_48_bytes(s), |s, v| spec_serialize_48_bytes(s, v));
}


proof fn lemma_parse_48_bytes_well_behaved_on(s: SpecStream)
    ensures
        prop_parse_well_behaved_on(|s| spec_parse_48_bytes(s), s)
{
    lemma_parse_bytes_well_behaved_on(s, 48);
}

proof fn lemma_serialize_48_bytes_well_behaved_on(s: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_well_behaved_on(|s, v| spec_serialize_48_bytes(s, v), s, v)
{
    lemma_serialize_bytes_well_behaved_on(s, v, 48);
}

proof fn lemma_serialize_48_bytes_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_deterministic_on(|s, v| spec_serialize_48_bytes(s, v), s1, s2, v)
{
    lemma_serialize_bytes_deterministic_on(s1, s2, v, 48);
}

proof fn lemma_parse_48_bytes_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures
        prop_parse_strong_prefix_on(|s| spec_parse_48_bytes(s), s1, s2)
{
    lemma_parse_bytes_strong_prefix_on(s1, s2, 48);
}

proof fn lemma_parse_48_bytes_correct_on(s: SpecStream, v: Seq<u8>)
    requires s.data.len() <= usize::MAX,
    ensures
        prop_parse_correct_on(|s| spec_parse_48_bytes(s), |s, v| spec_serialize_48_bytes(s, v), s, v)
{
    lemma_parse_bytes_correct_on(s, v, 48);
}

proof fn lemma_parse_48_bytes_serialize_inverse_on(s: SpecStream)
    ensures
        prop_parse_serialize_inverse_on(|s| spec_parse_48_bytes(s), |s, v| spec_serialize_48_bytes(s, v), s)
{
    lemma_parse_bytes_serialize_inverse_on(s, 48);
}

pub exec fn parse_48_bytes(s: Stream) -> (res: ParseResult<&[u8]>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_48_bytes(s))
{
    parse_bytes(s, 48)
}
pub exec fn serialize_48_bytes(data: &mut [u8], start: usize, v: &[u8]) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_bytes(s, v, 48 as nat))
{
    serialize_bytes(data, start, v, 48)
}

            
pub open spec fn spec_parse_28_bytes(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    spec_parse_bytes(s, 28)
}

pub open spec fn spec_serialize_28_bytes(s: SpecStream, v: Seq<u8>) -> SpecSerializeResult
{
    spec_serialize_bytes(s, v, 28)
}

pub proof fn lemma_parse_28_bytes_well_behaved()
    ensures
        prop_parse_well_behaved(|s| spec_parse_28_bytes(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_28_bytes, s) by {
        lemma_parse_28_bytes_well_behaved_on(s)
    }
}

pub proof fn lemma_serialize_28_bytes_well_behaved()
    ensures
        prop_serialize_well_behaved(|s, v| spec_serialize_28_bytes(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_28_bytes, s, v) by {
        lemma_serialize_28_bytes_well_behaved_on(s, v)
    }
}

pub proof fn lemma_serialize_28_bytes_deterministic()
    ensures
        prop_serialize_deterministic(|s, v| spec_serialize_28_bytes(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_28_bytes, s1, s2, v) by {
        lemma_serialize_28_bytes_deterministic_on(s1, s2, v)
    }
}

pub proof fn lemma_parse_28_bytes_strong_prefix()
    ensures
        prop_parse_strong_prefix(|s| spec_parse_28_bytes(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_28_bytes, s1, s2) by {
        lemma_parse_28_bytes_strong_prefix_on(s1, s2)
    }
}

pub proof fn lemma_parse_28_bytes_correct()
    ensures
        prop_parse_correct(|s| spec_parse_28_bytes(s), |s, v| spec_serialize_28_bytes(s, v))
{
    reveal(prop_parse_correct::<Seq<u8>>);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_28_bytes, spec_serialize_28_bytes, s, v) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_28_bytes_correct_on(s, v)
        }
    }
}

pub proof fn lemma_parse_28_bytes_serialize_inverse()
    ensures
        prop_parse_serialize_inverse(|s| spec_parse_28_bytes(s), |s, v| spec_serialize_28_bytes(s, v))
{
    reveal(prop_parse_serialize_inverse::<Seq<u8>>);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_28_bytes, spec_serialize_28_bytes, s) by {
        lemma_parse_28_bytes_serialize_inverse_on(s)
    }
}

pub proof fn lemma_parse_28_bytes_nonmalleable()
    ensures
        prop_parse_nonmalleable(|s| spec_parse_28_bytes(s))
{
    lemma_parse_28_bytes_serialize_inverse();
    lemma_serialize_28_bytes_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_28_bytes(s), |s, v| spec_serialize_28_bytes(s, v));
}


proof fn lemma_parse_28_bytes_well_behaved_on(s: SpecStream)
    ensures
        prop_parse_well_behaved_on(|s| spec_parse_28_bytes(s), s)
{
    lemma_parse_bytes_well_behaved_on(s, 28);
}

proof fn lemma_serialize_28_bytes_well_behaved_on(s: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_well_behaved_on(|s, v| spec_serialize_28_bytes(s, v), s, v)
{
    lemma_serialize_bytes_well_behaved_on(s, v, 28);
}

proof fn lemma_serialize_28_bytes_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_deterministic_on(|s, v| spec_serialize_28_bytes(s, v), s1, s2, v)
{
    lemma_serialize_bytes_deterministic_on(s1, s2, v, 28);
}

proof fn lemma_parse_28_bytes_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures
        prop_parse_strong_prefix_on(|s| spec_parse_28_bytes(s), s1, s2)
{
    lemma_parse_bytes_strong_prefix_on(s1, s2, 28);
}

proof fn lemma_parse_28_bytes_correct_on(s: SpecStream, v: Seq<u8>)
    requires s.data.len() <= usize::MAX,
    ensures
        prop_parse_correct_on(|s| spec_parse_28_bytes(s), |s, v| spec_serialize_28_bytes(s, v), s, v)
{
    lemma_parse_bytes_correct_on(s, v, 28);
}

proof fn lemma_parse_28_bytes_serialize_inverse_on(s: SpecStream)
    ensures
        prop_parse_serialize_inverse_on(|s| spec_parse_28_bytes(s), |s, v| spec_serialize_28_bytes(s, v), s)
{
    lemma_parse_bytes_serialize_inverse_on(s, 28);
}

pub exec fn parse_28_bytes(s: Stream) -> (res: ParseResult<&[u8]>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_28_bytes(s))
{
    parse_bytes(s, 28)
}
pub exec fn serialize_28_bytes(data: &mut [u8], start: usize, v: &[u8]) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_bytes(s, v, 28 as nat))
{
    serialize_bytes(data, start, v, 28)
}

            
pub open spec fn spec_parse_16_bytes(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    spec_parse_bytes(s, 16)
}

pub open spec fn spec_serialize_16_bytes(s: SpecStream, v: Seq<u8>) -> SpecSerializeResult
{
    spec_serialize_bytes(s, v, 16)
}

pub proof fn lemma_parse_16_bytes_well_behaved()
    ensures
        prop_parse_well_behaved(|s| spec_parse_16_bytes(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_16_bytes, s) by {
        lemma_parse_16_bytes_well_behaved_on(s)
    }
}

pub proof fn lemma_serialize_16_bytes_well_behaved()
    ensures
        prop_serialize_well_behaved(|s, v| spec_serialize_16_bytes(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_16_bytes, s, v) by {
        lemma_serialize_16_bytes_well_behaved_on(s, v)
    }
}

pub proof fn lemma_serialize_16_bytes_deterministic()
    ensures
        prop_serialize_deterministic(|s, v| spec_serialize_16_bytes(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_16_bytes, s1, s2, v) by {
        lemma_serialize_16_bytes_deterministic_on(s1, s2, v)
    }
}

pub proof fn lemma_parse_16_bytes_strong_prefix()
    ensures
        prop_parse_strong_prefix(|s| spec_parse_16_bytes(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_16_bytes, s1, s2) by {
        lemma_parse_16_bytes_strong_prefix_on(s1, s2)
    }
}

pub proof fn lemma_parse_16_bytes_correct()
    ensures
        prop_parse_correct(|s| spec_parse_16_bytes(s), |s, v| spec_serialize_16_bytes(s, v))
{
    reveal(prop_parse_correct::<Seq<u8>>);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_16_bytes, spec_serialize_16_bytes, s, v) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_16_bytes_correct_on(s, v)
        }
    }
}

pub proof fn lemma_parse_16_bytes_serialize_inverse()
    ensures
        prop_parse_serialize_inverse(|s| spec_parse_16_bytes(s), |s, v| spec_serialize_16_bytes(s, v))
{
    reveal(prop_parse_serialize_inverse::<Seq<u8>>);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_16_bytes, spec_serialize_16_bytes, s) by {
        lemma_parse_16_bytes_serialize_inverse_on(s)
    }
}

pub proof fn lemma_parse_16_bytes_nonmalleable()
    ensures
        prop_parse_nonmalleable(|s| spec_parse_16_bytes(s))
{
    lemma_parse_16_bytes_serialize_inverse();
    lemma_serialize_16_bytes_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_16_bytes(s), |s, v| spec_serialize_16_bytes(s, v));
}


proof fn lemma_parse_16_bytes_well_behaved_on(s: SpecStream)
    ensures
        prop_parse_well_behaved_on(|s| spec_parse_16_bytes(s), s)
{
    lemma_parse_bytes_well_behaved_on(s, 16);
}

proof fn lemma_serialize_16_bytes_well_behaved_on(s: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_well_behaved_on(|s, v| spec_serialize_16_bytes(s, v), s, v)
{
    lemma_serialize_bytes_well_behaved_on(s, v, 16);
}

proof fn lemma_serialize_16_bytes_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures
        prop_serialize_deterministic_on(|s, v| spec_serialize_16_bytes(s, v), s1, s2, v)
{
    lemma_serialize_bytes_deterministic_on(s1, s2, v, 16);
}

proof fn lemma_parse_16_bytes_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures
        prop_parse_strong_prefix_on(|s| spec_parse_16_bytes(s), s1, s2)
{
    lemma_parse_bytes_strong_prefix_on(s1, s2, 16);
}

proof fn lemma_parse_16_bytes_correct_on(s: SpecStream, v: Seq<u8>)
    requires s.data.len() <= usize::MAX,
    ensures
        prop_parse_correct_on(|s| spec_parse_16_bytes(s), |s, v| spec_serialize_16_bytes(s, v), s, v)
{
    lemma_parse_bytes_correct_on(s, v, 16);
}

proof fn lemma_parse_16_bytes_serialize_inverse_on(s: SpecStream)
    ensures
        prop_parse_serialize_inverse_on(|s| spec_parse_16_bytes(s), |s, v| spec_serialize_16_bytes(s, v), s)
{
    lemma_parse_bytes_serialize_inverse_on(s, 16);
}

pub exec fn parse_16_bytes(s: Stream) -> (res: ParseResult<&[u8]>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_16_bytes(s))
{
    parse_bytes(s, 16)
}
pub exec fn serialize_16_bytes(data: &mut [u8], start: usize, v: &[u8]) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_bytes(s, v, 16 as nat))
{
    serialize_bytes(data, start, v, 16)
}

            pub struct SpecMsg1 {
    ty: u8,
    reserved: Seq<u8>,
    sender: Seq<u8>,
    ephemeral: Seq<u8>,
    static_: Seq<u8>,
    timestamp: Seq<u8>,
    mac1: Seq<u8>,
    mac2: Seq<u8>,

}
pub struct Msg1 {
    ty: u8,
    reserved: Vec<u8>,
    sender: Vec<u8>,
    ephemeral: Vec<u8>,
    static_: Vec<u8>,
    timestamp: Vec<u8>,
    mac1: Vec<u8>,
    mac2: Vec<u8>,

}

pub open spec fn spec_parse_8_fold<R1, R2, R3, R4, R5, R6, R7, R8>(
    parser1: spec_fn(SpecStream) -> SpecParseResult<R1>,
    parser2: spec_fn(SpecStream) -> SpecParseResult<R2>,
    parser3: spec_fn(SpecStream) -> SpecParseResult<R3>,
    parser4: spec_fn(SpecStream) -> SpecParseResult<R4>,
    parser5: spec_fn(SpecStream) -> SpecParseResult<R5>,
    parser6: spec_fn(SpecStream) -> SpecParseResult<R6>,
    parser7: spec_fn(SpecStream) -> SpecParseResult<R7>,
    parser8: spec_fn(SpecStream) -> SpecParseResult<R8>) -> spec_fn(SpecStream) -> SpecParseResult<(((((((R1, R2), R3), R4), R5), R6), R7), R8)>
{
    spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(parser1, parser2), parser3), parser4), parser5), parser6), parser7), parser8)
}



pub open spec fn spec_serialize_8_fold<T1, T2, T3, T4, T5, T6, T7, T8>(
    serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
    serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult,
    serializer3: spec_fn(SpecStream, T3) -> SpecSerializeResult,
    serializer4: spec_fn(SpecStream, T4) -> SpecSerializeResult,
    serializer5: spec_fn(SpecStream, T5) -> SpecSerializeResult,
    serializer6: spec_fn(SpecStream, T6) -> SpecSerializeResult,
    serializer7: spec_fn(SpecStream, T7) -> SpecSerializeResult,
    serializer8: spec_fn(SpecStream, T8) -> SpecSerializeResult) -> spec_fn(SpecStream, (((((((T1, T2), T3), T4), T5), T6), T7), T8)) -> SpecSerializeResult
{
    spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(serializer1, serializer2), serializer3), serializer4), serializer5), serializer6), serializer7), serializer8)
}


pub exec fn parse_8_fold<'a, P1, P2, P3, P4, P5, P6, P7, P8, R1, R2, R3, R4, R5, R6, R7, R8>(
    exec_parser1: P1,
    exec_parser2: P2,
    exec_parser3: P3,
    exec_parser4: P4,
    exec_parser5: P5,
    exec_parser6: P6,
    exec_parser7: P7,
    exec_parser8: P8,
    Ghost(spec_parser1): Ghost<spec_fn(SpecStream) -> SpecParseResult<R1::V>>,
    Ghost(spec_parser2): Ghost<spec_fn(SpecStream) -> SpecParseResult<R2::V>>,
    Ghost(spec_parser3): Ghost<spec_fn(SpecStream) -> SpecParseResult<R3::V>>,
    Ghost(spec_parser4): Ghost<spec_fn(SpecStream) -> SpecParseResult<R4::V>>,
    Ghost(spec_parser5): Ghost<spec_fn(SpecStream) -> SpecParseResult<R5::V>>,
    Ghost(spec_parser6): Ghost<spec_fn(SpecStream) -> SpecParseResult<R6::V>>,
    Ghost(spec_parser7): Ghost<spec_fn(SpecStream) -> SpecParseResult<R7::V>>,
    Ghost(spec_parser8): Ghost<spec_fn(SpecStream) -> SpecParseResult<R8::V>>,
    s: Stream<'a>) -> (res: ParseResult<(((((((R1, R2), R3), R4), R5), R6), R7), R8)>)
    where
    R1: DView,
    P1: FnOnce(Stream<'a>) -> ParseResult<R1>,
    R2: DView,
    P2: FnOnce(Stream<'a>) -> ParseResult<R2>,
    R3: DView,
    P3: FnOnce(Stream<'a>) -> ParseResult<R3>,
    R4: DView,
    P4: FnOnce(Stream<'a>) -> ParseResult<R4>,
    R5: DView,
    P5: FnOnce(Stream<'a>) -> ParseResult<R5>,
    R6: DView,
    P6: FnOnce(Stream<'a>) -> ParseResult<R6>,
    R7: DView,
    P7: FnOnce(Stream<'a>) -> ParseResult<R7>,
    R8: DView,
    P8: FnOnce(Stream<'a>) -> ParseResult<R8>,
    requires
        prop_parse_exec_spec_equiv(exec_parser1, spec_parser1),
        prop_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        prop_parse_exec_spec_equiv(exec_parser3, spec_parser3),
        prop_parse_exec_spec_equiv(exec_parser4, spec_parser4),
        prop_parse_exec_spec_equiv(exec_parser5, spec_parser5),
        prop_parse_exec_spec_equiv(exec_parser6, spec_parser6),
        prop_parse_exec_spec_equiv(exec_parser7, spec_parser7),
        prop_parse_exec_spec_equiv(exec_parser8, spec_parser8),
    ensures
        prop_parse_exec_spec_equiv_on(s, res, spec_parse_8_fold(spec_parser1, spec_parser2, spec_parser3, spec_parser4, spec_parser5, spec_parser6, spec_parser7, spec_parser8))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_2_fold = |s| -> (res: ParseResult<(R1, R2)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2)), { parse_pair(exec_parser1, exec_parser2, Ghost(spec_parser1), Ghost(spec_parser2), s) };
    let parse_3_fold = |s| -> (res: ParseResult<((R1, R2), R3)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), { parse_pair(parse_2_fold, exec_parser3, Ghost(spec_parse_pair(spec_parser1, spec_parser2)), Ghost(spec_parser3), s) };
    let parse_4_fold = |s| -> (res: ParseResult<(((R1, R2), R3), R4)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4)), { parse_pair(parse_3_fold, exec_parser4, Ghost(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), Ghost(spec_parser4), s) };
    let parse_5_fold = |s| -> (res: ParseResult<((((R1, R2), R3), R4), R5)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4), spec_parser5)), { parse_pair(parse_4_fold, exec_parser5, Ghost(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4)), Ghost(spec_parser5), s) };
    let parse_6_fold = |s| -> (res: ParseResult<(((((R1, R2), R3), R4), R5), R6)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4), spec_parser5), spec_parser6)), { parse_pair(parse_5_fold, exec_parser6, Ghost(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4), spec_parser5)), Ghost(spec_parser6), s) };
    let parse_7_fold = |s| -> (res: ParseResult<((((((R1, R2), R3), R4), R5), R6), R7)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4), spec_parser5), spec_parser6), spec_parser7)), { parse_pair(parse_6_fold, exec_parser7, Ghost(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4), spec_parser5), spec_parser6)), Ghost(spec_parser7), s) };
    parse_pair(parse_7_fold, exec_parser8, Ghost(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4), spec_parser5), spec_parser6), spec_parser7)), Ghost(spec_parser8), s)
}


pub open spec fn spec_parse_msg1(s: SpecStream) -> SpecParseResult<(((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)>
{
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);

    spec_parse_8_fold(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993, spec_parse_4_bytes, spec_parse_32_bytes, spec_parse_48_bytes, spec_parse_28_bytes, spec_parse_16_bytes, spec_parse_16_bytes)(s)
}

pub open spec fn spec_serialize_msg1(s: SpecStream, v: (((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);

    spec_serialize_8_fold(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993, spec_serialize_4_bytes, spec_serialize_32_bytes, spec_serialize_48_bytes, spec_serialize_28_bytes, spec_serialize_16_bytes, spec_serialize_16_bytes)(s, v)
}

pub proof fn lemma_parse_msg1_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_msg1(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_msg1 = |s| spec_parse_msg1(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_msg1, s) by {
        lemma_parse_msg1_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_msg1_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_msg1(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_msg1 = |s, v| spec_serialize_msg1(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_msg1, s, v) by {
        lemma_serialize_msg1_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_msg1_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_msg1(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_msg1 = |s, v| spec_serialize_msg1(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_msg1, s1, s2, v) by {
        lemma_serialize_msg1_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_msg1_correct()
    ensures prop_parse_correct(|s| spec_parse_msg1(s), |s, v| spec_serialize_msg1(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_msg1 = |s| spec_parse_msg1(s);
    let spec_serialize_msg1 = |s, v| spec_serialize_msg1(s, v);
    assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_msg1, spec_serialize_msg1, s, v) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_msg1_correct_on(s, v);
        }
    }
}

pub proof fn lemma_parse_msg1_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_msg1(s), |s, v| spec_serialize_msg1(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_msg1 = |s| spec_parse_msg1(s);
    let spec_serialize_msg1 = |s, v| spec_serialize_msg1(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_msg1, spec_serialize_msg1, s) by {
        lemma_parse_msg1_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_msg1_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_msg1(s))
{
    lemma_parse_msg1_serialize_inverse();
    lemma_serialize_msg1_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_msg1(s), |s, v| spec_serialize_msg1(s, v));
}

pub proof fn lemma_parse_msg1_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_msg1(s), s)
{
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    lemma_parse_u8_le_1_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_32_bytes_well_behaved();
    lemma_parse_48_bytes_well_behaved();
    lemma_parse_28_bytes_well_behaved();
    lemma_parse_16_bytes_well_behaved();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes);
    lemma_parse_pair_well_behaved_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes), spec_parse_16_bytes, s);
}

pub proof fn lemma_serialize_msg1_well_behaved_on(s: SpecStream, v: (((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_msg1(s, v), s, v)
{
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    lemma_serialize_u8_le_1_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_32_bytes_well_behaved();
    lemma_serialize_48_bytes_well_behaved();
    lemma_serialize_28_bytes_well_behaved();
    lemma_serialize_16_bytes_well_behaved();
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_well_behaved_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes, s, v);
}

pub proof fn lemma_serialize_msg1_deterministic_on(s1: SpecStream, s2: SpecStream, v: (((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_msg1(s, v), s1, s2, v)
{
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    lemma_serialize_u8_le_1_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_32_bytes_well_behaved();
    lemma_serialize_48_bytes_well_behaved();
    lemma_serialize_28_bytes_well_behaved();
    lemma_serialize_16_bytes_well_behaved();
    lemma_serialize_u8_le_1_deterministic();
    lemma_serialize_3_bytes_5058554103549626993_deterministic();
    lemma_serialize_4_bytes_deterministic();
    lemma_serialize_32_bytes_deterministic();
    lemma_serialize_48_bytes_deterministic();
    lemma_serialize_28_bytes_deterministic();
    lemma_serialize_16_bytes_deterministic();
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_deterministic(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_deterministic_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes, s1, s2, v);
}

pub proof fn lemma_parse_msg1_correct_on(s: SpecStream, v: (((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    requires s.data.len() <= usize::MAX,
    ensures prop_parse_correct_on(|s| spec_parse_msg1(s), |s, v| spec_serialize_msg1(s, v), s, v)
{
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    lemma_serialize_u8_le_1_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_32_bytes_well_behaved();
    lemma_serialize_48_bytes_well_behaved();
    lemma_serialize_28_bytes_well_behaved();
    lemma_serialize_16_bytes_well_behaved();
    lemma_parse_u8_le_1_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_32_bytes_well_behaved();
    lemma_parse_48_bytes_well_behaved();
    lemma_parse_28_bytes_well_behaved();
    lemma_parse_16_bytes_well_behaved();
    lemma_parse_u8_le_1_strong_prefix();
    lemma_parse_3_bytes_5058554103549626993_strong_prefix();
    lemma_parse_4_bytes_strong_prefix();
    lemma_parse_32_bytes_strong_prefix();
    lemma_parse_48_bytes_strong_prefix();
    lemma_parse_28_bytes_strong_prefix();
    lemma_parse_16_bytes_strong_prefix();
    lemma_parse_u8_le_1_correct();
    lemma_parse_3_bytes_5058554103549626993_correct();
    lemma_parse_4_bytes_correct();
    lemma_parse_32_bytes_correct();
    lemma_parse_48_bytes_correct();
    lemma_parse_28_bytes_correct();
    lemma_parse_16_bytes_correct();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_strong_prefix(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_correct(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993, spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes, spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_correct_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes, s, v);
}

pub proof fn lemma_parse_msg1_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_msg1(s), |s, v| spec_serialize_msg1(s, v), s)
{
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    let spec_serialize_u8_le_1 = |s, v| spec_serialize_u8_le_1(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_48_bytes = |s, v| spec_serialize_48_bytes(s, v);
    let spec_serialize_28_bytes = |s, v| spec_serialize_28_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    lemma_parse_u8_le_1_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_32_bytes_well_behaved();
    lemma_parse_48_bytes_well_behaved();
    lemma_parse_28_bytes_well_behaved();
    lemma_parse_16_bytes_well_behaved();
    lemma_serialize_u8_le_1_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_32_bytes_well_behaved();
    lemma_serialize_48_bytes_well_behaved();
    lemma_serialize_28_bytes_well_behaved();
    lemma_serialize_16_bytes_well_behaved();
    lemma_parse_u8_le_1_serialize_inverse();
    lemma_parse_3_bytes_5058554103549626993_serialize_inverse();
    lemma_parse_4_bytes_serialize_inverse();
    lemma_parse_32_bytes_serialize_inverse();
    lemma_parse_48_bytes_serialize_inverse();
    lemma_parse_28_bytes_serialize_inverse();
    lemma_parse_16_bytes_serialize_inverse();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_serialize_inverse(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993, spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes, spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_serialize_inverse_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_1, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_48_bytes), spec_serialize_28_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes, s);
}

pub proof fn lemma_parse_msg1_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_msg1(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_msg1 = |s| spec_parse_msg1(s);
    assert forall |s1, s2| prop_parse_strong_prefix_on(spec_parse_msg1, s1, s2) by {
        lemma_parse_msg1_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_msg1_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_msg1(s), s1, s2)
{
    let spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    let spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    lemma_parse_u8_le_1_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_32_bytes_well_behaved();
    lemma_parse_48_bytes_well_behaved();
    lemma_parse_28_bytes_well_behaved();
    lemma_parse_16_bytes_well_behaved();
    lemma_parse_u8_le_1_strong_prefix();
    lemma_parse_3_bytes_5058554103549626993_strong_prefix();
    lemma_parse_4_bytes_strong_prefix();
    lemma_parse_32_bytes_strong_prefix();
    lemma_parse_48_bytes_strong_prefix();
    lemma_parse_28_bytes_strong_prefix();
    lemma_parse_16_bytes_strong_prefix();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_strong_prefix(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes);
    lemma_parse_pair_strong_prefix_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_1, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_48_bytes), spec_parse_28_bytes), spec_parse_16_bytes), spec_parse_16_bytes, s1, s2);
}

pub exec fn parse_msg1(s: Stream) -> (res: ParseResult<(((((((u8, &[u8]), &[u8]), &[u8]), &[u8]), &[u8]), &[u8]), &[u8])>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_msg1(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let ghost spec_parse_u8_le_1 = |s| spec_parse_u8_le_1(s);
    let ghost spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let ghost spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let ghost spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let ghost spec_parse_48_bytes = |s| spec_parse_48_bytes(s);
    let ghost spec_parse_28_bytes = |s| spec_parse_28_bytes(s);
    let ghost spec_parse_16_bytes = |s| spec_parse_16_bytes(s);

    parse_8_fold(parse_u8_le_1, parse_3_bytes_5058554103549626993, parse_4_bytes, parse_32_bytes, parse_48_bytes, parse_28_bytes, parse_16_bytes, parse_16_bytes, Ghost(spec_parse_u8_le_1), Ghost(spec_parse_3_bytes_5058554103549626993), Ghost(spec_parse_4_bytes), Ghost(spec_parse_32_bytes), Ghost(spec_parse_48_bytes), Ghost(spec_parse_28_bytes), Ghost(spec_parse_16_bytes), Ghost(spec_parse_16_bytes), s)
}
pub exec fn serialize_msg1(data: &mut [u8], start: usize, v: (((((((u8, &[u8]), &[u8]), &[u8]), &[u8]), &[u8]), &[u8]), &[u8])) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_msg1(s, v))
{
    let (((((((v0, v1), v2), v3), v4), v5), v6), v7) = v;
    let (new_start, n0) = serialize_u8_le_1(data, start, v0)?;

let (new_start, n1) = serialize_3_bytes_5058554103549626993(data, new_start, v1)?;
    if n0 > usize::MAX - n1 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n2) = serialize_4_bytes(data, new_start, v2)?;
    if n0 + n1 > usize::MAX - n2 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n3) = serialize_32_bytes(data, new_start, v3)?;
    if n0 + n1 + n2 > usize::MAX - n3 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n4) = serialize_48_bytes(data, new_start, v4)?;
    if n0 + n1 + n2 + n3 > usize::MAX - n4 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n5) = serialize_28_bytes(data, new_start, v5)?;
    if n0 + n1 + n2 + n3 + n4 > usize::MAX - n5 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n6) = serialize_16_bytes(data, new_start, v6)?;
    if n0 + n1 + n2 + n3 + n4 + n5 > usize::MAX - n6 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n7) = serialize_16_bytes(data, new_start, v7)?;
    if n0 + n1 + n2 + n3 + n4 + n5 + n6 > usize::MAX - n7 { return Err(SerializeError::IntegerOverflow) }
    Ok((new_start, n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7))
}

                    
pub open spec fn spec_parse_u8_le_2(s: SpecStream) -> SpecParseResult<u8>
{
    match spec_parse_u8_le(s) {
        Ok((s, n, v)) => {
            if v == 2 {
                Ok((s, n, v))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub open spec fn spec_serialize_u8_le_2(s: SpecStream, v: u8) -> SpecSerializeResult
{
    if v == 2 {
        spec_serialize_u8_le(s, v)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub exec fn parse_u8_le_2(s: Stream) -> (res: ParseResult<u8>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le_2(s))
{
    let (s, n, v) = parse_u8_le(s)?;
    if v == 2 {
        Ok((s, n, v))
    } else {
        Err(ParseError::ConstMismatch)
    }
}

pub exec fn serialize_u8_le_2(data: &mut [u8], start: usize, v: u8) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v, res, |s, v| spec_serialize_u8_le_2(s, v))
{
    if v == 2 {
        serialize_u8_le(data, start, v)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub proof fn lemma_parse_u8_le_2_well_behaved()
    ensures
        prop_parse_well_behaved(|s| spec_parse_u8_le_2(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u8_le_2, s) by {
        lemma_parse_u8_le_well_behaved_on(s)
    }
}

pub proof fn lemma_serialize_u8_le_2_well_behaved()
    ensures
        prop_serialize_well_behaved(|s, v| spec_serialize_u8_le_2(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u8_le_2, s, v) by {
        lemma_serialize_u8_le_well_behaved_on(s, v)
    }
}

pub proof fn lemma_serialize_u8_le_2_deterministic()
    ensures
        prop_serialize_deterministic(|s, v| spec_serialize_u8_le_2(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u8_le_2, s1, s2, v) by {
        lemma_serialize_u8_le_deterministic_on(s1, s2, v)
    }
}

pub proof fn lemma_parse_u8_le_2_strong_prefix()
    ensures
        prop_parse_strong_prefix(|s| spec_parse_u8_le_2(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u8_le_2, s1, s2) by {
        lemma_parse_u8_le_strong_prefix_on(s1, s2)
    }
}

pub proof fn lemma_parse_u8_le_2_correct()
    ensures
        prop_parse_correct(|s| spec_parse_u8_le_2(s), |s, v| spec_serialize_u8_le_2(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u8_le_2, spec_serialize_u8_le_2, s, v) by {
        lemma_parse_u8_le_correct_on(s, v)
    }
}

pub proof fn lemma_parse_u8_le_2_serialize_inverse()
    ensures
        prop_parse_serialize_inverse(|s| spec_parse_u8_le_2(s), |s, v| spec_serialize_u8_le_2(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u8_le_2, spec_serialize_u8_le_2, s) by {
        lemma_parse_u8_le_serialize_inverse_on(s)
    }
}

pub proof fn lemma_parse_u8_le_2_nonmalleable()
    ensures
        prop_parse_nonmalleable(|s| spec_parse_u8_le_2(s))
{
    lemma_parse_u8_le_2_serialize_inverse();
    lemma_serialize_u8_le_2_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u8_le_2(s), |s, v| spec_serialize_u8_le_2(s, v));
}
pub struct SpecMsg2 {
    ty: u8,
    reserved: Seq<u8>,
    sender: Seq<u8>,
    receiver: Seq<u8>,
    ephemeral: Seq<u8>,
    empty: Seq<u8>,
    mac1: Seq<u8>,
    mac2: Seq<u8>,

}
pub struct Msg2 {
    ty: u8,
    reserved: Vec<u8>,
    sender: Vec<u8>,
    receiver: Vec<u8>,
    ephemeral: Vec<u8>,
    empty: Vec<u8>,
    mac1: Vec<u8>,
    mac2: Vec<u8>,

}

pub open spec fn spec_parse_msg2(s: SpecStream) -> SpecParseResult<(((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)>
{
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);

    spec_parse_8_fold(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993, spec_parse_4_bytes, spec_parse_4_bytes, spec_parse_32_bytes, spec_parse_16_bytes, spec_parse_16_bytes, spec_parse_16_bytes)(s)
}

pub open spec fn spec_serialize_msg2(s: SpecStream, v: (((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);

    spec_serialize_8_fold(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993, spec_serialize_4_bytes, spec_serialize_4_bytes, spec_serialize_32_bytes, spec_serialize_16_bytes, spec_serialize_16_bytes, spec_serialize_16_bytes)(s, v)
}

pub proof fn lemma_parse_msg2_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_msg2(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_msg2 = |s| spec_parse_msg2(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_msg2, s) by {
        lemma_parse_msg2_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_msg2_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_msg2(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_msg2 = |s, v| spec_serialize_msg2(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_msg2, s, v) by {
        lemma_serialize_msg2_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_msg2_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_msg2(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_msg2 = |s, v| spec_serialize_msg2(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_msg2, s1, s2, v) by {
        lemma_serialize_msg2_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_msg2_correct()
    ensures prop_parse_correct(|s| spec_parse_msg2(s), |s, v| spec_serialize_msg2(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_msg2 = |s| spec_parse_msg2(s);
    let spec_serialize_msg2 = |s, v| spec_serialize_msg2(s, v);
    assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_msg2, spec_serialize_msg2, s, v) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_msg2_correct_on(s, v);
        }
    }
}

pub proof fn lemma_parse_msg2_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_msg2(s), |s, v| spec_serialize_msg2(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_msg2 = |s| spec_parse_msg2(s);
    let spec_serialize_msg2 = |s, v| spec_serialize_msg2(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_msg2, spec_serialize_msg2, s) by {
        lemma_parse_msg2_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_msg2_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_msg2(s))
{
    lemma_parse_msg2_serialize_inverse();
    lemma_serialize_msg2_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_msg2(s), |s, v| spec_serialize_msg2(s, v));
}

pub proof fn lemma_parse_msg2_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_msg2(s), s)
{
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    lemma_parse_u8_le_2_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_32_bytes_well_behaved();
    lemma_parse_16_bytes_well_behaved();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes);
    lemma_parse_pair_well_behaved_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes), spec_parse_16_bytes, s);
}

pub proof fn lemma_serialize_msg2_well_behaved_on(s: SpecStream, v: (((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_msg2(s, v), s, v)
{
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    lemma_serialize_u8_le_2_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_32_bytes_well_behaved();
    lemma_serialize_16_bytes_well_behaved();
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_well_behaved_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes, s, v);
}

pub proof fn lemma_serialize_msg2_deterministic_on(s1: SpecStream, s2: SpecStream, v: (((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_msg2(s, v), s1, s2, v)
{
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    lemma_serialize_u8_le_2_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_32_bytes_well_behaved();
    lemma_serialize_16_bytes_well_behaved();
    lemma_serialize_u8_le_2_deterministic();
    lemma_serialize_3_bytes_5058554103549626993_deterministic();
    lemma_serialize_4_bytes_deterministic();
    lemma_serialize_32_bytes_deterministic();
    lemma_serialize_16_bytes_deterministic();
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_deterministic(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes);
    lemma_serialize_pair_deterministic_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes, s1, s2, v);
}

pub proof fn lemma_parse_msg2_correct_on(s: SpecStream, v: (((((((u8, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    requires s.data.len() <= usize::MAX,
    ensures prop_parse_correct_on(|s| spec_parse_msg2(s), |s, v| spec_serialize_msg2(s, v), s, v)
{
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    lemma_serialize_u8_le_2_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_32_bytes_well_behaved();
    lemma_serialize_16_bytes_well_behaved();
    lemma_parse_u8_le_2_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_32_bytes_well_behaved();
    lemma_parse_16_bytes_well_behaved();
    lemma_parse_u8_le_2_strong_prefix();
    lemma_parse_3_bytes_5058554103549626993_strong_prefix();
    lemma_parse_4_bytes_strong_prefix();
    lemma_parse_32_bytes_strong_prefix();
    lemma_parse_16_bytes_strong_prefix();
    lemma_parse_u8_le_2_correct();
    lemma_parse_3_bytes_5058554103549626993_correct();
    lemma_parse_4_bytes_correct();
    lemma_parse_32_bytes_correct();
    lemma_parse_16_bytes_correct();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_strong_prefix(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_correct(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993, spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes, spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_correct_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes, s, v);
}

pub proof fn lemma_parse_msg2_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_msg2(s), |s, v| spec_serialize_msg2(s, v), s)
{
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    let spec_serialize_u8_le_2 = |s, v| spec_serialize_u8_le_2(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_32_bytes = |s, v| spec_serialize_32_bytes(s, v);
    let spec_serialize_16_bytes = |s, v| spec_serialize_16_bytes(s, v);
    lemma_parse_u8_le_2_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_32_bytes_well_behaved();
    lemma_parse_16_bytes_well_behaved();
    lemma_serialize_u8_le_2_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_32_bytes_well_behaved();
    lemma_serialize_16_bytes_well_behaved();
    lemma_parse_u8_le_2_serialize_inverse();
    lemma_parse_3_bytes_5058554103549626993_serialize_inverse();
    lemma_parse_4_bytes_serialize_inverse();
    lemma_parse_32_bytes_serialize_inverse();
    lemma_parse_16_bytes_serialize_inverse();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_serialize_inverse(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993, spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes, spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes);
    lemma_parse_pair_serialize_inverse_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes), spec_parse_16_bytes, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_2, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_4_bytes), spec_serialize_32_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes), spec_serialize_16_bytes, s);
}

pub proof fn lemma_parse_msg2_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_msg2(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_msg2 = |s| spec_parse_msg2(s);
    assert forall |s1, s2| prop_parse_strong_prefix_on(spec_parse_msg2, s1, s2) by {
        lemma_parse_msg2_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_msg2_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_msg2(s), s1, s2)
{
    let spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let spec_parse_16_bytes = |s| spec_parse_16_bytes(s);
    lemma_parse_u8_le_2_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_32_bytes_well_behaved();
    lemma_parse_16_bytes_well_behaved();
    lemma_parse_u8_le_2_strong_prefix();
    lemma_parse_3_bytes_5058554103549626993_strong_prefix();
    lemma_parse_4_bytes_strong_prefix();
    lemma_parse_32_bytes_strong_prefix();
    lemma_parse_16_bytes_strong_prefix();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_strong_prefix(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes);
    lemma_parse_pair_strong_prefix_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_2, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_4_bytes), spec_parse_32_bytes), spec_parse_16_bytes), spec_parse_16_bytes), spec_parse_16_bytes, s1, s2);
}

pub exec fn parse_msg2(s: Stream) -> (res: ParseResult<(((((((u8, &[u8]), &[u8]), &[u8]), &[u8]), &[u8]), &[u8]), &[u8])>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_msg2(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let ghost spec_parse_u8_le_2 = |s| spec_parse_u8_le_2(s);
    let ghost spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let ghost spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let ghost spec_parse_32_bytes = |s| spec_parse_32_bytes(s);
    let ghost spec_parse_16_bytes = |s| spec_parse_16_bytes(s);

    parse_8_fold(parse_u8_le_2, parse_3_bytes_5058554103549626993, parse_4_bytes, parse_4_bytes, parse_32_bytes, parse_16_bytes, parse_16_bytes, parse_16_bytes, Ghost(spec_parse_u8_le_2), Ghost(spec_parse_3_bytes_5058554103549626993), Ghost(spec_parse_4_bytes), Ghost(spec_parse_4_bytes), Ghost(spec_parse_32_bytes), Ghost(spec_parse_16_bytes), Ghost(spec_parse_16_bytes), Ghost(spec_parse_16_bytes), s)
}
pub exec fn serialize_msg2(data: &mut [u8], start: usize, v: (((((((u8, &[u8]), &[u8]), &[u8]), &[u8]), &[u8]), &[u8]), &[u8])) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_msg2(s, v))
{
    let (((((((v0, v1), v2), v3), v4), v5), v6), v7) = v;
    let (new_start, n0) = serialize_u8_le_2(data, start, v0)?;

let (new_start, n1) = serialize_3_bytes_5058554103549626993(data, new_start, v1)?;
    if n0 > usize::MAX - n1 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n2) = serialize_4_bytes(data, new_start, v2)?;
    if n0 + n1 > usize::MAX - n2 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n3) = serialize_4_bytes(data, new_start, v3)?;
    if n0 + n1 + n2 > usize::MAX - n3 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n4) = serialize_32_bytes(data, new_start, v4)?;
    if n0 + n1 + n2 + n3 > usize::MAX - n4 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n5) = serialize_16_bytes(data, new_start, v5)?;
    if n0 + n1 + n2 + n3 + n4 > usize::MAX - n5 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n6) = serialize_16_bytes(data, new_start, v6)?;
    if n0 + n1 + n2 + n3 + n4 + n5 > usize::MAX - n6 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n7) = serialize_16_bytes(data, new_start, v7)?;
    if n0 + n1 + n2 + n3 + n4 + n5 + n6 > usize::MAX - n7 { return Err(SerializeError::IntegerOverflow) }
    Ok((new_start, n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7))
}

                    
pub open spec fn spec_parse_u8_le_4(s: SpecStream) -> SpecParseResult<u8>
{
    match spec_parse_u8_le(s) {
        Ok((s, n, v)) => {
            if v == 4 {
                Ok((s, n, v))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub open spec fn spec_serialize_u8_le_4(s: SpecStream, v: u8) -> SpecSerializeResult
{
    if v == 4 {
        spec_serialize_u8_le(s, v)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub exec fn parse_u8_le_4(s: Stream) -> (res: ParseResult<u8>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le_4(s))
{
    let (s, n, v) = parse_u8_le(s)?;
    if v == 4 {
        Ok((s, n, v))
    } else {
        Err(ParseError::ConstMismatch)
    }
}

pub exec fn serialize_u8_le_4(data: &mut [u8], start: usize, v: u8) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v, res, |s, v| spec_serialize_u8_le_4(s, v))
{
    if v == 4 {
        serialize_u8_le(data, start, v)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub proof fn lemma_parse_u8_le_4_well_behaved()
    ensures
        prop_parse_well_behaved(|s| spec_parse_u8_le_4(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u8_le_4, s) by {
        lemma_parse_u8_le_well_behaved_on(s)
    }
}

pub proof fn lemma_serialize_u8_le_4_well_behaved()
    ensures
        prop_serialize_well_behaved(|s, v| spec_serialize_u8_le_4(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u8_le_4, s, v) by {
        lemma_serialize_u8_le_well_behaved_on(s, v)
    }
}

pub proof fn lemma_serialize_u8_le_4_deterministic()
    ensures
        prop_serialize_deterministic(|s, v| spec_serialize_u8_le_4(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u8_le_4, s1, s2, v) by {
        lemma_serialize_u8_le_deterministic_on(s1, s2, v)
    }
}

pub proof fn lemma_parse_u8_le_4_strong_prefix()
    ensures
        prop_parse_strong_prefix(|s| spec_parse_u8_le_4(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u8_le_4, s1, s2) by {
        lemma_parse_u8_le_strong_prefix_on(s1, s2)
    }
}

pub proof fn lemma_parse_u8_le_4_correct()
    ensures
        prop_parse_correct(|s| spec_parse_u8_le_4(s), |s, v| spec_serialize_u8_le_4(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u8_le_4, spec_serialize_u8_le_4, s, v) by {
        lemma_parse_u8_le_correct_on(s, v)
    }
}

pub proof fn lemma_parse_u8_le_4_serialize_inverse()
    ensures
        prop_parse_serialize_inverse(|s| spec_parse_u8_le_4(s), |s, v| spec_serialize_u8_le_4(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u8_le_4, spec_serialize_u8_le_4, s) by {
        lemma_parse_u8_le_serialize_inverse_on(s)
    }
}

pub proof fn lemma_parse_u8_le_4_nonmalleable()
    ensures
        prop_parse_nonmalleable(|s| spec_parse_u8_le_4(s))
{
    lemma_parse_u8_le_4_serialize_inverse();
    lemma_serialize_u8_le_4_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u8_le_4(s), |s, v| spec_serialize_u8_le_4(s, v));
}
pub struct SpecTransp {
    ty: u8,
    reserved: Seq<u8>,
    receiver: Seq<u8>,
    counter: u64,
    packet: Seq<u8>,

}
pub struct Transp {
    ty: u8,
    reserved: Vec<u8>,
    receiver: Vec<u8>,
    counter: u64,
    packet: Vec<u8>,

}

pub open spec fn spec_parse_5_fold<R1, R2, R3, R4, R5>(
    parser1: spec_fn(SpecStream) -> SpecParseResult<R1>,
    parser2: spec_fn(SpecStream) -> SpecParseResult<R2>,
    parser3: spec_fn(SpecStream) -> SpecParseResult<R3>,
    parser4: spec_fn(SpecStream) -> SpecParseResult<R4>,
    parser5: spec_fn(SpecStream) -> SpecParseResult<R5>) -> spec_fn(SpecStream) -> SpecParseResult<((((R1, R2), R3), R4), R5)>
{
    spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(parser1, parser2), parser3), parser4), parser5)
}



pub open spec fn spec_serialize_5_fold<T1, T2, T3, T4, T5>(
    serializer1: spec_fn(SpecStream, T1) -> SpecSerializeResult,
    serializer2: spec_fn(SpecStream, T2) -> SpecSerializeResult,
    serializer3: spec_fn(SpecStream, T3) -> SpecSerializeResult,
    serializer4: spec_fn(SpecStream, T4) -> SpecSerializeResult,
    serializer5: spec_fn(SpecStream, T5) -> SpecSerializeResult) -> spec_fn(SpecStream, ((((T1, T2), T3), T4), T5)) -> SpecSerializeResult
{
    spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(serializer1, serializer2), serializer3), serializer4), serializer5)
}


pub exec fn parse_5_fold<'a, P1, P2, P3, P4, P5, R1, R2, R3, R4, R5>(
    exec_parser1: P1,
    exec_parser2: P2,
    exec_parser3: P3,
    exec_parser4: P4,
    exec_parser5: P5,
    Ghost(spec_parser1): Ghost<spec_fn(SpecStream) -> SpecParseResult<R1::V>>,
    Ghost(spec_parser2): Ghost<spec_fn(SpecStream) -> SpecParseResult<R2::V>>,
    Ghost(spec_parser3): Ghost<spec_fn(SpecStream) -> SpecParseResult<R3::V>>,
    Ghost(spec_parser4): Ghost<spec_fn(SpecStream) -> SpecParseResult<R4::V>>,
    Ghost(spec_parser5): Ghost<spec_fn(SpecStream) -> SpecParseResult<R5::V>>,
    s: Stream<'a>) -> (res: ParseResult<((((R1, R2), R3), R4), R5)>)
    where
    R1: DView,
    P1: FnOnce(Stream<'a>) -> ParseResult<R1>,
    R2: DView,
    P2: FnOnce(Stream<'a>) -> ParseResult<R2>,
    R3: DView,
    P3: FnOnce(Stream<'a>) -> ParseResult<R3>,
    R4: DView,
    P4: FnOnce(Stream<'a>) -> ParseResult<R4>,
    R5: DView,
    P5: FnOnce(Stream<'a>) -> ParseResult<R5>,
    requires
        prop_parse_exec_spec_equiv(exec_parser1, spec_parser1),
        prop_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        prop_parse_exec_spec_equiv(exec_parser3, spec_parser3),
        prop_parse_exec_spec_equiv(exec_parser4, spec_parser4),
        prop_parse_exec_spec_equiv(exec_parser5, spec_parser5),
    ensures
        prop_parse_exec_spec_equiv_on(s, res, spec_parse_5_fold(spec_parser1, spec_parser2, spec_parser3, spec_parser4, spec_parser5))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_2_fold = |s| -> (res: ParseResult<(R1, R2)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2)), { parse_pair(exec_parser1, exec_parser2, Ghost(spec_parser1), Ghost(spec_parser2), s) };
    let parse_3_fold = |s| -> (res: ParseResult<((R1, R2), R3)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), { parse_pair(parse_2_fold, exec_parser3, Ghost(spec_parse_pair(spec_parser1, spec_parser2)), Ghost(spec_parser3), s) };
    let parse_4_fold = |s| -> (res: ParseResult<(((R1, R2), R3), R4)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4)), { parse_pair(parse_3_fold, exec_parser4, Ghost(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), Ghost(spec_parser4), s) };
    parse_pair(parse_4_fold, exec_parser5, Ghost(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4)), Ghost(spec_parser5), s)
}


pub open spec fn spec_parse_transp(s: SpecStream) -> SpecParseResult<((((u8, Seq<u8>), Seq<u8>), u64), Seq<u8>)>
{
    let spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_u64_le = |s| spec_parse_u64_le(s);
    let spec_parse_tail = |s| spec_parse_tail(s);

    spec_parse_5_fold(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993, spec_parse_4_bytes, spec_parse_u64_le, spec_parse_tail)(s)
}

pub open spec fn spec_serialize_transp(s: SpecStream, v: ((((u8, Seq<u8>), Seq<u8>), u64), Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);

    spec_serialize_5_fold(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993, spec_serialize_4_bytes, spec_serialize_u64_le, spec_serialize_tail)(s, v)
}

pub proof fn lemma_parse_transp_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_transp(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_transp = |s| spec_parse_transp(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_transp, s) by {
        lemma_parse_transp_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_transp_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_transp(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_transp = |s, v| spec_serialize_transp(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_transp, s, v) by {
        lemma_serialize_transp_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_transp_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_transp(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_transp = |s, v| spec_serialize_transp(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_transp, s1, s2, v) by {
        lemma_serialize_transp_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_transp_correct()
    ensures prop_parse_correct(|s| spec_parse_transp(s), |s, v| spec_serialize_transp(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_transp = |s| spec_parse_transp(s);
    let spec_serialize_transp = |s, v| spec_serialize_transp(s, v);
    assert forall |s: SpecStream, v| s.data.len() <= usize::MAX ==> #[trigger] prop_parse_correct_on(spec_parse_transp, spec_serialize_transp, s, v) by {
        if s.data.len() <= usize::MAX {
            lemma_parse_transp_correct_on(s, v);
        }
    }
}

pub proof fn lemma_parse_transp_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_transp(s), |s, v| spec_serialize_transp(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_transp = |s| spec_parse_transp(s);
    let spec_serialize_transp = |s, v| spec_serialize_transp(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_transp, spec_serialize_transp, s) by {
        lemma_parse_transp_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_transp_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_transp(s))
{
    lemma_parse_transp_serialize_inverse();
    lemma_serialize_transp_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_transp(s), |s, v| spec_serialize_transp(s, v));
}

pub proof fn lemma_parse_transp_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_transp(s), s)
{
    let spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_u64_le = |s| spec_parse_u64_le(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    lemma_parse_u8_le_4_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_u64_le_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le);
    lemma_parse_pair_well_behaved_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le), spec_parse_tail, s);
}

pub proof fn lemma_serialize_transp_well_behaved_on(s: SpecStream, v: ((((u8, Seq<u8>), Seq<u8>), u64), Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_transp(s, v), s, v)
{
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_u8_le_4_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_u64_le_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le);
    lemma_serialize_pair_well_behaved_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le), spec_serialize_tail, s, v);
}

pub proof fn lemma_serialize_transp_deterministic_on(s1: SpecStream, s2: SpecStream, v: ((((u8, Seq<u8>), Seq<u8>), u64), Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_transp(s, v), s1, s2, v)
{
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_u8_le_4_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_u64_le_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_serialize_u8_le_4_deterministic();
    lemma_serialize_3_bytes_5058554103549626993_deterministic();
    lemma_serialize_4_bytes_deterministic();
    lemma_serialize_u64_le_deterministic();
    lemma_serialize_tail_deterministic();
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_deterministic(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le);
    lemma_serialize_pair_deterministic_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le), spec_serialize_tail, s1, s2, v);
}

pub proof fn lemma_parse_transp_correct_on(s: SpecStream, v: ((((u8, Seq<u8>), Seq<u8>), u64), Seq<u8>))
    requires s.data.len() <= usize::MAX,
    ensures prop_parse_correct_on(|s| spec_parse_transp(s), |s, v| spec_serialize_transp(s, v), s, v)
{
    let spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_u64_le = |s| spec_parse_u64_le(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_u8_le_4_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_u64_le_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_parse_u8_le_4_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_u64_le_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_parse_u8_le_4_strong_prefix();
    lemma_parse_3_bytes_5058554103549626993_strong_prefix();
    lemma_parse_4_bytes_strong_prefix();
    lemma_parse_u64_le_strong_prefix();
    
    lemma_parse_u8_le_4_correct();
    lemma_parse_3_bytes_5058554103549626993_correct();
    lemma_parse_4_bytes_correct();
    lemma_parse_u64_le_correct();
    lemma_parse_tail_correct();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_strong_prefix(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993);
    lemma_parse_pair_correct(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993, spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes, spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le, spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le);
    lemma_parse_pair_correct_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le), spec_parse_tail, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le), spec_serialize_tail, s, v);
}

pub proof fn lemma_parse_transp_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_transp(s), |s, v| spec_serialize_transp(s, v), s)
{
    let spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    let spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let spec_parse_u64_le = |s| spec_parse_u64_le(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    let spec_serialize_u8_le_4 = |s, v| spec_serialize_u8_le_4(s, v);
    let spec_serialize_3_bytes_5058554103549626993 = |s, v| spec_serialize_3_bytes_5058554103549626993(s, v);
    let spec_serialize_4_bytes = |s, v| spec_serialize_4_bytes(s, v);
    let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_parse_u8_le_4_well_behaved();
    lemma_parse_3_bytes_5058554103549626993_well_behaved();
    lemma_parse_4_bytes_well_behaved();
    lemma_parse_u64_le_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_serialize_u8_le_4_well_behaved();
    lemma_serialize_3_bytes_5058554103549626993_well_behaved();
    lemma_serialize_4_bytes_well_behaved();
    lemma_serialize_u64_le_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_parse_u8_le_4_serialize_inverse();
    lemma_parse_3_bytes_5058554103549626993_serialize_inverse();
    lemma_parse_4_bytes_serialize_inverse();
    lemma_parse_u64_le_serialize_inverse();
    lemma_parse_tail_serialize_inverse();
    lemma_parse_pair_well_behaved(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993);
    lemma_serialize_pair_well_behaved(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_serialize_inverse(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993, spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes, spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le, spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le);
    lemma_parse_pair_serialize_inverse_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_u8_le_4, spec_parse_3_bytes_5058554103549626993), spec_parse_4_bytes), spec_parse_u64_le), spec_parse_tail, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_u8_le_4, spec_serialize_3_bytes_5058554103549626993), spec_serialize_4_bytes), spec_serialize_u64_le), spec_serialize_tail, s);
}
pub exec fn parse_transp(s: Stream) -> (res: ParseResult<((((u8, &[u8]), &[u8]), u64), &[u8])>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_transp(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let ghost spec_parse_u8_le_4 = |s| spec_parse_u8_le_4(s);
    let ghost spec_parse_3_bytes_5058554103549626993 = |s| spec_parse_3_bytes_5058554103549626993(s);
    let ghost spec_parse_4_bytes = |s| spec_parse_4_bytes(s);
    let ghost spec_parse_u64_le = |s| spec_parse_u64_le(s);
    let ghost spec_parse_tail = |s| spec_parse_tail(s);

    parse_5_fold(parse_u8_le_4, parse_3_bytes_5058554103549626993, parse_4_bytes, parse_u64_le, parse_tail, Ghost(spec_parse_u8_le_4), Ghost(spec_parse_3_bytes_5058554103549626993), Ghost(spec_parse_4_bytes), Ghost(spec_parse_u64_le), Ghost(spec_parse_tail), s)
}
pub exec fn serialize_transp(data: &mut [u8], start: usize, v: ((((u8, &[u8]), &[u8]), u64), &[u8])) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(old(data).dview(), start, data.dview(), v.dview(), res, |s, v| spec_serialize_transp(s, v))
{
    let ((((v0, v1), v2), v3), v4) = v;
    let (new_start, n0) = serialize_u8_le_4(data, start, v0)?;

let (new_start, n1) = serialize_3_bytes_5058554103549626993(data, new_start, v1)?;
    if n0 > usize::MAX - n1 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n2) = serialize_4_bytes(data, new_start, v2)?;
    if n0 + n1 > usize::MAX - n2 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n3) = serialize_u64_le(data, new_start, v3)?;
    if n0 + n1 + n2 > usize::MAX - n3 { return Err(SerializeError::IntegerOverflow) }
let (new_start, n4) = serialize_tail(data, new_start, v4)?;
    if n0 + n1 + n2 + n3 > usize::MAX - n4 { return Err(SerializeError::IntegerOverflow) }
    Ok((new_start, n0 + n1 + n2 + n3 + n4))
}

                    
fn main() {}
}
