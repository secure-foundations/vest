# ! [allow (warnings)] use vest_lib::combinators::mapped::spec::* ;
use vest_lib::combinators::* ;
use vest_lib::combinators::recursive::* ;
use Sum::Inl as L ;
use Sum::Inr as R ;
use vest_lib::Never ;
use vest_lib::core::exec::input::{
    InputBuf,
    InputSlice
}
;
use vest_lib::core::exec::output::OutputBuf ;
use vest_lib::core::exec::parser::* ;
use vest_lib::core::exec::serializer::* ;
use vest_lib::core::exec::ParseError ;
use vest_lib::core::exec::bytes_eq ;
use vest_lib::core::{
    proof::*,
    spec::*
}
;
use vest_lib::primitives::btcvarint::VarInt ;
use vest_lib::primitives::leb128::ULeb128 ;
use vstd::prelude::* ;
verus! {
// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `table_entry`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct TableEntry<'i> {
    pub key: &'i [u8],
    pub value_len: u32,
    pub value: &'i [u8],
}
# [verifier::ext_equal]
pub struct TableEntrySpec < T0 = Seq < u8 >, T1 = u32, T2 = Seq < u8 > > {
    pub key: T0,
    pub value_len: T1,
    pub value: T2,
}
pub type TableEntryInner = (Seq < u8 >, (u32, Seq < u8 >)) ;
impl<'i> DeepView for TableEntry<'i> {
    type V = TableEntrySpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        TableEntrySpec {
            key: self.key.deep_view(),
            value_len: self.value_len.deep_view(),
            value: self.value.deep_view(),
        }
    }
}
impl<'i> TableEntry<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().key == self.key.deep_view(),
    self.deep_view().value_len == self.value_len.deep_view(),
    self.deep_view().value == self.value.deep_view(),
    {
        reveal(< TableEntry as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > TableEntrySpec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (key,
        (value_len,
        value)) = input ;
        Self {
            key,
            value_len,
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            key,
            value_len,
            value
        }
        = self ;
        (key,
        (value_len,
        value))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TableEntrySpec::from_structural) ;
        reveal(TableEntrySpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TableEntrySpec::from_structural) ;
        reveal(TableEntrySpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            key,
            value_len,
            value
        }
        => (key,
        (value_len,
        value)),
    }
   ,
    {
        reveal(TableEntrySpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TableEntryForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TableEntryReverse ;
impl SpecMap for TableEntryForward {
    type Input = TableEntryInner ;
    type Output = TableEntrySpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TableEntrySpec::from_structural (input)
    }
}
impl SpecMap for TableEntryReverse {
    type Input = TableEntrySpec ;
    type Output = TableEntryInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `table`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct Table<'i> {
    pub id: u64,
    pub entry_count: u32,
    pub entries: Vec < TableEntry<'i> >,
}
# [verifier::ext_equal]
pub struct TableSpec < T0 = u64, T1 = u32, T2 = Seq < TableEntrySpec > > {
    pub id: T0,
    pub entry_count: T1,
    pub entries: T2,
}
pub type TableInner = (u64, (u32, Seq < TableEntrySpec >)) ;
impl<'i> DeepView for Table<'i> {
    type V = TableSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        TableSpec {
            id: self.id.deep_view(),
            entry_count: self.entry_count.deep_view(),
            entries: self.entries.deep_view(),
        }
    }
}
impl<'i> Table<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().id == self.id.deep_view(),
    self.deep_view().entry_count == self.entry_count.deep_view(),
    self.deep_view().entries == self.entries.deep_view(),
    {
        reveal(< Table as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > TableSpec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (id,
        (entry_count,
        entries)) = input ;
        Self {
            id,
            entry_count,
            entries
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            id,
            entry_count,
            entries
        }
        = self ;
        (id,
        (entry_count,
        entries))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TableSpec::from_structural) ;
        reveal(TableSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TableSpec::from_structural) ;
        reveal(TableSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            id,
            entry_count,
            entries
        }
        => (id,
        (entry_count,
        entries)),
    }
   ,
    {
        reveal(TableSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TableForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TableReverse ;
impl SpecMap for TableForward {
    type Input = TableInner ;
    type Output = TableSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TableSpec::from_structural (input)
    }
}
impl SpecMap for TableReverse {
    type Input = TableSpec ;
    type Output = TableInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `table_entry`."]
# [derive (Clone, Copy)]
pub struct TableEntryFmt ;

pub type TableEntryFmtSpec = Named < Mapped < Pair < Fixed < 32 >, Bind < U32Be, spec_fn (u32) -> Varied < u32 > > >, BiMap < TableEntryForward, TableEntryReverse >> > ;

impl TableEntryFmt {
    # [doc = "specification constructor for `table_entry`."] pub open spec fn spec_inner() -> TableEntryFmtSpec {
        Named ("table_entry",
        Mapped {
            inner: Pair (Fixed::< 32 >,
            Bind (U32Be,
            | value_len: u32 | Varied (value_len))),
            mapper: BiMap (TableEntryForward,
            TableEntryReverse),
        }
        )
    }
}


# [doc = "named format combinator for `table`."]
# [derive (Clone, Copy)]
pub struct TableFmt ;

pub type TableFmtSpec = Named < Mapped < Pair < U64Be, Bind < U32Be, spec_fn (u32) -> RepeatN < TableEntryFmt, u32 > > >, BiMap < TableForward, TableReverse >> > ;

impl TableFmt {
    # [doc = "specification constructor for `table`."] pub open spec fn spec_inner() -> TableFmtSpec {
        Named ("table",
        Mapped {
            inner: Pair (U64Be,
            Bind (U32Be,
            | entry_count: u32 | RepeatN (entry_count,
            TableEntryFmt))),
            mapper: BiMap (TableForward,
            TableReverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for TableEntryFmt {
        type PVal = TableEntrySpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TableEntryFmt {
        type Val = TableEntrySpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TableEntryFmt {
        type SValue = TableEntrySpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TableEntryFmt {
        type SVal = TableEntrySpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TableEntryFmt {
        type T = TableEntrySpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TableFmt {
        type PVal = TableSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TableFmt {
        type Val = TableSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TableFmt {
        type SValue = TableSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TableFmt {
        type SVal = TableSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TableFmt {
        type T = TableSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }
}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;
    broadcast use {
        vest_lib::combinators::disjoint::disjointness_lemmas,
        TableEntrySpec::lemma_from_into,
        TableEntrySpec::lemma_into_from,
        TableSpec::lemma_from_into,
        TableSpec::lemma_into_from,
    };

    impl SafeParser for TableEntryFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TableEntryFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TableEntryFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecParser>::spec_parse) ;
            reveal(< TableEntryFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TableEntryInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TableEntrySpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecParser>::spec_parse) ;
            reveal(< TableEntryFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TableEntryInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TableEntrySpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TableEntryFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TableEntryFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TableEntryFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TableEntryFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TableEntryFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TableEntryFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecParser>::spec_parse) ;
            reveal(< TableEntryFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TableEntryFmt as Consistency>::consistent) ;
            reveal(< TableEntryFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TableEntrySpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TableEntrySpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TableEntryFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TableEntryInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TableEntrySpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TableEntryFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TableEntryFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TableEntryFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TableEntryFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TableEntryFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TableEntryFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TableFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TableFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TableFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TableFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TableFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TableFmt as SpecParser>::spec_parse) ;
            reveal(< TableFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TableInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TableSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TableFmt as SpecParser>::spec_parse) ;
            reveal(< TableFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TableInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TableSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TableFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TableFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TableFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TableFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TableFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TableFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TableFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TableFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TableFmt as SpecParser>::spec_parse) ;
            reveal(< TableFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TableFmt as Consistency>::consistent) ;
            reveal(< TableFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TableSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TableSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TableFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TableFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TableInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TableSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TableFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TableFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TableFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TableFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TableFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TableFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }
}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for TableEntryFmt {
        type PT = TableEntry<'i>;

        fn min_byte_len(&self) -> usize {
            36
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TableEntryFmt as SpecParser>::spec_parse);
            reveal(<TableEntry as DeepView>::deep_view);
            reveal(TableEntrySpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, key) = (Fixed::< 32 >).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, value_len) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, value) = (Varied (value_len)).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = TableEntry {
                key,
                value_len,
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TableEntry<'i>> for TableEntryFmt {
        fn serialize_into(&self, v: &TableEntry<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TableEntryFmt as SpecSerializer>::spec_serialize);
            reveal(<TableEntryFmt as SpecByteLen>::byte_len);
            reveal(<TableEntry as DeepView>::deep_view);
            reveal(TableEntrySpec::into_structural);
            let ghost old_obuf = obuf@;

            let TableEntry {
                key,
                value_len,
                value,
            } = v;
            Fixed::< 32 >.serialize_into(* key, obuf);
            U32Be.serialize_into(value_len, obuf);
            Varied (*value_len).serialize_into(*value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TableEntry<'i>> for TableEntryFmt {
        fn prepare(&self, v: &TableEntry<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TableEntryFmt as SpecByteLen>::byte_len);
            reveal(<TableEntry as DeepView>::deep_view);
            reveal(TableEntrySpec::into_structural);
            let TableEntry {
                key,
                value_len,
                value,
            } = v;
            let l1 = (Fixed::< 32 >).prepare (key) ?;
            let l2 = (U32Be).prepare (value_len) ?;
            let l3 = (Varied (*value_len)).prepare (value) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for TableFmt {
        type PT = Table<'i>;

        fn min_byte_len(&self) -> usize {
            12
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TableFmt as SpecParser>::spec_parse);
            reveal(<Table as DeepView>::deep_view);
            reveal(TableSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, id) = (U64Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, entry_count) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, entries) = (RepeatN (entry_count, TableEntryFmt)).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Table {
                id,
                entry_count,
                entries,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Table<'i>> for TableFmt {
        fn serialize_into(&self, v: &Table<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TableFmt as SpecSerializer>::spec_serialize);
            reveal(<TableFmt as SpecByteLen>::byte_len);
            reveal(<Table as DeepView>::deep_view);
            reveal(TableSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Table {
                id,
                entry_count,
                entries,
            } = v;
            U64Be.serialize_into(id, obuf);
            U32Be.serialize_into(entry_count, obuf);
            RepeatN (* entry_count, TableEntryFmt).serialize_into(entries, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Table<'i>> for TableFmt {
        fn prepare(&self, v: &Table<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TableFmt as SpecByteLen>::byte_len);
            reveal(<Table as DeepView>::deep_view);
            reveal(TableSpec::into_structural);
            let Table {
                id,
                entry_count,
                entries,
            } = v;
            let l1 = (U64Be).prepare (id) ?;
            let l2 = (U32Be).prepare (entry_count) ?;
            let l3 = (RepeatN (* entry_count, TableEntryFmt)).prepare (entries) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
