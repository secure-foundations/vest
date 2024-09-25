use crate::properties::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Spec version of [`Depend`].
pub struct SpecDepend<Fst, Snd> where Fst: SecureSpecCombinator, Snd: SpecCombinator {
    /// combinators that contain dependencies
    pub fst: Fst,
    /// closure that captures dependencies and maps them to the dependent combinators
    pub snd: spec_fn(Fst::SpecResult) -> Snd,
}

impl<Fst, Snd> SpecCombinator for SpecDepend<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SpecCombinator,
 {
    type SpecResult = (Fst::SpecResult, Snd::SpecResult);

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if Fst::spec_is_prefix_secure() {
            if let Ok((n, v1)) = self.fst.spec_parse(s) {
                let snd = (self.snd)(v1);
                if let Ok((m, v2)) = snd.spec_parse(s.subrange(n as int, s.len() as int)) {
                    if n <= usize::MAX - m {
                        Ok(((n + m) as usize, (v1, v2)))
                    } else {
                        Err(())
                    }
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        if let Ok((n, v1)) = self.fst.spec_parse(s) {
            let snd = (self.snd)(v1);
            if let Ok((m, v2)) = snd.spec_parse(s.subrange(n as int, s.len() as int)) {
                self.fst.spec_parse_wf(s);
                snd.spec_parse_wf(s.subrange(n as int, s.len() as int));
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if Fst::spec_is_prefix_secure() {
            if let Ok(buf1) = self.fst.spec_serialize(v.0) {
                let snd = (self.snd)(v.0);
                if let Ok(buf2) = snd.spec_serialize(v.1) {
                    if buf1.len() + buf2.len() <= usize::MAX {
                        Ok(buf1.add(buf2))
                    } else {
                        Err(())
                    }
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }
}

impl<Fst, Snd> SecureSpecCombinator for SpecDepend<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator,
 {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok((buf)) = self.spec_serialize(v) {
            let buf0 = self.fst.spec_serialize(v.0).unwrap();
            let buf1 = (self.snd)(v.0).spec_serialize(v.1).unwrap();
            self.fst.theorem_serialize_parse_roundtrip(v.0);
            self.fst.lemma_prefix_secure(buf0, buf1);
            (self.snd)(v.0).theorem_serialize_parse_roundtrip(v.1);
            assert(buf0.add(buf1).subrange(buf0.len() as int, buf.len() as int) == buf1);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((nm, (v0, v1))) = self.spec_parse(buf) {
            let (n, v0_) = self.fst.spec_parse(buf).unwrap();
            self.fst.spec_parse_wf(buf);
            let buf0 = buf.subrange(0, n as int);
            let buf1 = buf.subrange(n as int, buf.len() as int);
            assert(buf == buf0.add(buf1));
            self.fst.theorem_parse_serialize_roundtrip(buf);
            let (m, v1_) = (self.snd)(v0).spec_parse(buf1).unwrap();
            (self.snd)(v0).theorem_parse_serialize_roundtrip(buf1);
            (self.snd)(v0).spec_parse_wf(buf1);
            let buf2 = self.spec_serialize((v0, v1)).unwrap();
            assert(buf2 == buf.subrange(0, nm as int));
        } else {
        }
    }

    open spec fn spec_is_prefix_secure() -> bool {
        Fst::spec_is_prefix_secure() && Snd::spec_is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        if Fst::spec_is_prefix_secure() && Snd::spec_is_prefix_secure() {
            if let Ok((nm, (v0, v1))) = self.spec_parse(buf) {
                let (n, _) = self.fst.spec_parse(buf).unwrap();
                self.fst.spec_parse_wf(buf);
                let buf0 = buf.subrange(0, n as int);
                let buf1 = buf.subrange(n as int, buf.len() as int);
                self.fst.lemma_prefix_secure(buf0, buf1);
                self.fst.lemma_prefix_secure(buf0, buf1.add(s2));
                self.fst.lemma_prefix_secure(buf, s2);
                let snd = (self.snd)(v0);
                let (m, v1_) = snd.spec_parse(buf1).unwrap();
                assert(buf.add(s2).subrange(0, n as int) == buf0);
                assert(buf.add(s2).subrange(n as int, buf.add(s2).len() as int) == buf1.add(s2));
                snd.lemma_prefix_secure(buf1, s2);
            } else {
            }
        } else {
        }
    }
}

/// Combinator that sequentially applies two combinators, where the second combinator depends on
/// the result of the first one.
pub struct Depend<Fst, Snd, F> where
    Fst: Combinator,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
    F: for <'a>Fn(Fst::Result<'a>) -> Snd,
 {
    /// combinators that contain dependencies
    pub fst: Fst,
    /// closure that captures dependencies and maps them to the dependent combinators
    pub snd: F,
    /// spec closure for well-formedness
    pub spec_snd: Ghost<spec_fn(<Fst::Owned as View>::V) -> Snd::V>,
}

impl<Fst, Snd, F> Depend<Fst, Snd, F> where
    Fst: Combinator,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
    F: for <'a>Fn(Fst::Result<'a>) -> Snd,
 {
    /// well-formed [`DepPair`] should have its clousre [`snd`] well-formed w.r.t. [`spec_snd`]
    pub open spec fn wf(&self) -> bool {
        let Ghost(spec_snd_dep) = self.spec_snd;
        &&& forall|i| #[trigger] (self.snd).requires((i,))
        &&& forall|i, snd| (self.snd).ensures((i,), snd) ==> spec_snd_dep(i@) == snd@
    }
}

impl<Fst, Snd, F> View for Depend<Fst, Snd, F> where
    Fst: Combinator,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
    F: for <'a>Fn(Fst::Result<'a>) -> Snd,
 {
    type V = SpecDepend<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        let Ghost(spec_snd) = self.spec_snd;
        SpecDepend { fst: self.fst@, snd: spec_snd }
    }
}

impl<Fst, Snd, F> Combinator for Depend<Fst, Snd, F> where
    Fst: Combinator,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
    F: for <'a>Fn(Fst::Result<'a>) -> Snd,
    for <'a>Fst::Result<'a>: Copy,
 {
    type Result<'a> = (Fst::Result<'a>, Snd::Result<'a>);

    type Owned = (Fst::Owned, Snd::Owned);

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        Fst::exec_is_prefix_secure() && Snd::exec_is_prefix_secure()
    }

    open spec fn parse_requires(&self) -> bool {
        &&& self.wf()
        &&& self.fst.parse_requires()
        &&& forall|i, snd| (self.snd).ensures((i,), snd) ==> snd.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        if Fst::exec_is_prefix_secure() {
            let (n, v1) = self.fst.parse(s)?;
            let s_ = slice_subrange(s, n, s.len());
            let snd = (self.snd)(v1);
            let (m, v2) = snd.parse(s_)?;
            if n <= usize::MAX - m {
                Ok(((n + m), (v1, v2)))
            } else {
                Err(ParseError::SizeOverflow)
            }
        } else {
            Err(ParseError::DependFstNotPrefixSecure)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& self.wf()
        &&& self.fst.serialize_requires()
        &&& forall|i, snd| (self.snd).ensures((i,), snd) ==> snd.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if Fst::exec_is_prefix_secure() {
            let n = self.fst.serialize(v.0, data, pos)?;
            if n <= usize::MAX - pos && n + pos <= data.len() {
                let snd = (self.snd)(v.0);
                let m = snd.serialize(v.1, data, pos + n)?;
                if m <= usize::MAX - n {
                    assert(data@.subrange(pos as int, pos + n + m as int) == self@.spec_serialize(
                        v@,
                    ).unwrap());
                    assert(data@ == seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));
                    Ok(n + m)
                } else {
                    Err(SerializeError::SizeOverflow)
                }
            } else {
                Err(SerializeError::InsufficientBuffer)
            }
        } else {
            Err(SerializeError::DependFstNotPrefixSecure)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::properties::*;
    use crate::regular::{
        and_then::AndThen,
        bytes::Bytes,
        bytes_n::BytesN,
        choice::*,
        cond::Cond,
        depend::{Depend, SpecDepend},
        map::*,
        tail::Tail,
        uints::{U16, U32, U8},
    };
    use vstd::prelude::*;

    /// somewhat more complex TLV example
    /// should be generated from the following vest code:
    /// ```vest
    /// msg1 = {
    ///   a: u8,
    ///   b: u16,
    ///   c: [u8; 3],
    ///   data: Tail,
    /// }
    ///
    /// msg2 = {
    ///   a: u8,
    ///   b: u16,
    ///   c: u32,
    /// }
    ///
    /// msg3 = {
    ///   data: [u8; 6],
    /// }
    ///
    /// msg_type = enum {
    ///   Msg1 = 1,
    ///   Msg2 = 2,
    ///   Msg3 = 3,
    /// }
    ///
    /// tlv = {
    ///   @tag: msg_type,
    ///   @len: u8,
    ///   content: [u8; @len] >>= choose(@tag) {
    ///     Msg1 => msg1,
    ///     Msg2 => msg2,
    ///     Msg3 => msg3,
    ///   },
    ///   rest: Tail,
    /// }
    /// ```
    /// Message type 1
    pub struct SpecMsg1 {
        pub a: u8,
        pub b: u16,
        pub c: Seq<u8>,
        pub d: Seq<u8>,
    }

    pub type SpecMsg1Inner = (((u8, u16), Seq<u8>), Seq<u8>);

    pub struct Msg1<'a> {
        pub a: u8,
        pub b: u16,
        pub c: &'a [u8],
        pub d: &'a [u8],
    }

    pub struct Msg1Owned {
        pub a: u8,
        pub b: u16,
        pub c: Vec<u8>,
        pub d: Vec<u8>,
    }

    pub type Msg1Inner<'a> = (((u8, u16), &'a [u8]), &'a [u8]);

    pub type Msg1InnerOwned = (((u8, u16), Vec<u8>), Vec<u8>);

    impl View for Msg1<'_> {
        type V = SpecMsg1;

        open spec fn view(&self) -> Self::V {
            SpecMsg1 { a: self.a, b: self.b, c: self.c@, d: self.d@ }
        }
    }

    impl View for Msg1Owned {
        type V = SpecMsg1;

        open spec fn view(&self) -> Self::V {
            SpecMsg1 { a: self.a, b: self.b, c: self.c@, d: self.d@ }
        }
    }

    impl SpecFrom<SpecMsg1> for SpecMsg1Inner {
        open spec fn spec_from(t: SpecMsg1) -> SpecMsg1Inner {
            (((t.a, t.b), t.c), t.d)
        }
    }

    impl SpecFrom<SpecMsg1Inner> for SpecMsg1 {
        open spec fn spec_from(e: SpecMsg1Inner) -> SpecMsg1 {
            let (((a, b), c), d) = e;
            SpecMsg1 { a, b, c, d }
        }
    }

    impl<'a> From<Msg1<'a>> for Msg1Inner<'a> {
        fn ex_from(e: Msg1) -> (res: Msg1Inner) {
            (((e.a, e.b), e.c), e.d)
        }
    }

    impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
        fn ex_from(e: Msg1Inner) -> (res: Msg1) {
            let (((a, b), c), d) = e;
            Msg1 { a, b, c, d }
        }
    }

    impl From<Msg1Owned> for Msg1InnerOwned {
        fn ex_from(e: Msg1Owned) -> (res: Msg1InnerOwned) {
            (((e.a, e.b), e.c), e.d)
        }
    }

    impl From<Msg1InnerOwned> for Msg1Owned {
        fn ex_from(e: Msg1InnerOwned) -> (res: Msg1Owned) {
            let (((a, b), c), d) = e;
            Msg1Owned { a, b, c, d }
        }
    }

    pub struct Msg1Mapper;

    impl View for Msg1Mapper {
        type V = Self;

        open spec fn view(&self) -> Self::V {
            *self
        }
    }

    impl SpecIso for Msg1Mapper {
        type Src = SpecMsg1Inner;

        type Dst = SpecMsg1;

        proof fn spec_iso(s: SpecMsg1Inner) {
        }

        proof fn spec_iso_rev(s: SpecMsg1) {
        }
    }

    impl Iso for Msg1Mapper {
        type Src<'a> = Msg1Inner<'a>;

        type Dst<'a> = Msg1<'a>;

        type SrcOwned = Msg1InnerOwned;

        type DstOwned = Msg1Owned;
    }

    /// Message type 2
    pub struct Msg2 {
        pub a: u8,
        pub b: u16,
        pub c: u32,
    }

    pub type Msg2Inner = ((u8, u16), u32);

    impl View for Msg2 {
        type V = Msg2;

        open spec fn view(&self) -> Self::V {
            *self
        }
    }

    impl SpecFrom<Msg2> for Msg2Inner {
        open spec fn spec_from(t: Msg2) -> Msg2Inner {
            ((t.a, t.b), t.c)
        }
    }

    impl From<Msg2> for Msg2Inner {
        fn ex_from(e: Msg2) -> (res: Msg2Inner) {
            ((e.a, e.b), e.c)
        }
    }

    impl SpecFrom<Msg2Inner> for Msg2 {
        open spec fn spec_from(e: Msg2Inner) -> Msg2 {
            let ((a, b), c) = e;
            Msg2 { a, b, c }
        }
    }

    impl From<Msg2Inner> for Msg2 {
        fn ex_from(e: Msg2Inner) -> (res: Msg2) {
            let ((a, b), c) = e;
            Msg2 { a, b, c }
        }
    }

    pub struct Msg2Mapper;

    impl View for Msg2Mapper {
        type V = Self;

        open spec fn view(&self) -> Self::V {
            *self
        }
    }

    impl SpecIso for Msg2Mapper {
        type Src = Msg2Inner;

        type Dst = Msg2;

        proof fn spec_iso(s: Msg2Inner) {
        }

        proof fn spec_iso_rev(s: Msg2) {
        }
    }

    impl Iso for Msg2Mapper {
        type Src<'a> = Msg2Inner;

        type Dst<'a> = Msg2;

        type SrcOwned = Msg2Inner;

        type DstOwned = Msg2;
    }

    /// Message type 3
    pub struct SpecMsg3 {
        pub a: Seq<u8>,
    }

    pub type SpecMsg3Inner = (Seq<u8>);

    pub struct Msg3<'a> {
        pub a: &'a [u8],
    }

    pub struct Msg3Owned {
        pub a: Vec<u8>,
    }

    pub type Msg3Inner<'a> = (&'a [u8]);

    pub type Msg3InnerOwned = (Vec<u8>);

    impl View for Msg3<'_> {
        type V = SpecMsg3;

        open spec fn view(&self) -> Self::V {
            SpecMsg3 { a: self.a@ }
        }
    }

    impl View for Msg3Owned {
        type V = SpecMsg3;

        open spec fn view(&self) -> Self::V {
            SpecMsg3 { a: self.a@ }
        }
    }

    impl SpecFrom<SpecMsg3> for SpecMsg3Inner {
        open spec fn spec_from(e: SpecMsg3) -> SpecMsg3Inner {
            e.a
        }
    }

    impl SpecFrom<SpecMsg3Inner> for SpecMsg3 {
        open spec fn spec_from(e: SpecMsg3Inner) -> SpecMsg3 {
            SpecMsg3 { a: e }
        }
    }

    impl<'a> From<Msg3<'a>> for Msg3Inner<'a> {
        fn ex_from(e: Msg3) -> (res: Msg3Inner) {
            e.a
        }
    }

    impl<'a> From<Msg3Inner<'a>> for Msg3<'a> {
        fn ex_from(e: Msg3Inner) -> (res: Msg3) {
            Msg3 { a: e }
        }
    }

    impl From<Msg3Owned> for Msg3InnerOwned {
        fn ex_from(e: Msg3Owned) -> (res: Msg3InnerOwned) {
            (e.a)
        }
    }

    impl From<Msg3InnerOwned> for Msg3Owned {
        fn ex_from(e: Msg3InnerOwned) -> (res: Msg3Owned) {
            Msg3Owned { a: e }
        }
    }

    pub struct Msg3Mapper;

    impl View for Msg3Mapper {
        type V = Self;

        open spec fn view(&self) -> Self::V {
            *self
        }
    }

    impl SpecIso for Msg3Mapper {
        type Src = SpecMsg3Inner;

        type Dst = SpecMsg3;

        proof fn spec_iso(s: SpecMsg3Inner) {
        }

        proof fn spec_iso_rev(s: SpecMsg3) {
        }
    }

    impl Iso for Msg3Mapper {
        type Src<'a> = Msg3Inner<'a>;

        type Dst<'a> = Msg3<'a>;

        type SrcOwned = Msg3InnerOwned;

        type DstOwned = Msg3Owned;
    }

    /// Message type tlv content
    pub enum SpecTlvContent {
        M1(SpecMsg1),
        M2(Msg2),
        M3(SpecMsg3),
    }

    pub type SpecTlvContentInner = ord_choice_result!(SpecMsg1, Msg2, SpecMsg3);

    pub enum TlvContent<'a> {
        M1(Msg1<'a>),
        M2(Msg2),
        M3(Msg3<'a>),
    }

    pub enum TlvContentOwned {
        M1(Msg1Owned),
        M2(Msg2),
        M3(Msg3Owned),
    }

    pub type TlvContentInner<'a> = ord_choice_result!(Msg1<'a>, Msg2, Msg3<'a>);
    pub type TlvContentOwnedInner = ord_choice_result!(Msg1Owned, Msg2, Msg3Owned);

    impl View for TlvContent<'_> {
        type V = SpecTlvContent;

        open spec fn view(&self) -> Self::V {
            match self {
                TlvContent::M1(m) => SpecTlvContent::M1(m@),
                TlvContent::M2(m) => SpecTlvContent::M2(m@),
                TlvContent::M3(m) => SpecTlvContent::M3(m@),
            }
        }
    }

    impl View for TlvContentOwned {
        type V = SpecTlvContent;

        open spec fn view(&self) -> Self::V {
            match self {
                TlvContentOwned::M1(m) => SpecTlvContent::M1(m@),
                TlvContentOwned::M2(m) => SpecTlvContent::M2(m@),
                TlvContentOwned::M3(m) => SpecTlvContent::M3(m@),
            }
        }
    }

    impl SpecFrom<SpecTlvContent> for SpecTlvContentInner {
        open spec fn spec_from(e: SpecTlvContent) -> SpecTlvContentInner {
            match e {
                SpecTlvContent::M1(m) => inj_ord_choice_result!(m, *, *),
                SpecTlvContent::M2(m) => inj_ord_choice_result!(*, m, *),
                SpecTlvContent::M3(m) => inj_ord_choice_result!(*, *, m),
            }
        }
    }

    impl SpecFrom<SpecTlvContentInner> for SpecTlvContent {
        open spec fn spec_from(e: SpecTlvContentInner) -> SpecTlvContent {
            match e {
                inj_ord_choice_pat!(m, *, *) => SpecTlvContent::M1(m),
                inj_ord_choice_pat!(*, m, *) => SpecTlvContent::M2(m),
                inj_ord_choice_pat!(*, *, m) => SpecTlvContent::M3(m),
            }
        }
    }

    impl<'a> From<TlvContent<'a>> for TlvContentInner<'a> {
        fn ex_from(e: TlvContent) -> (res: TlvContentInner) {
            match e {
                TlvContent::M1(m) => inj_ord_choice_result!(m, *, *),
                TlvContent::M2(m) => inj_ord_choice_result!(*, m, *),
                TlvContent::M3(m) => inj_ord_choice_result!(*, *, m),
            }
        }
    }

    impl<'a> From<TlvContentInner<'a>> for TlvContent<'a> {
        fn ex_from(e: TlvContentInner) -> (res: TlvContent) {
            match e {
                inj_ord_choice_pat!(m, *, *) => TlvContent::M1(m),
                inj_ord_choice_pat!(*, m, *) => TlvContent::M2(m),
                inj_ord_choice_pat!(*, *, m) => TlvContent::M3(m),
            }
        }
    }

    impl From<TlvContentOwned> for TlvContentOwnedInner {
        fn ex_from(e: TlvContentOwned) -> (res: TlvContentOwnedInner) {
            match e {
                TlvContentOwned::M1(m) => inj_ord_choice_result!(m, *, *),
                TlvContentOwned::M2(m) => inj_ord_choice_result!(*, m, *),
                TlvContentOwned::M3(m) => inj_ord_choice_result!(*, *, m),
            }
        }
    }

    impl From<TlvContentOwnedInner> for TlvContentOwned {
        fn ex_from(e: TlvContentOwnedInner) -> (res: TlvContentOwned) {
            match e {
                inj_ord_choice_pat!(m, *, *) => TlvContentOwned::M1(m),
                inj_ord_choice_pat!(*, m, *) => TlvContentOwned::M2(m),
                inj_ord_choice_pat!(*, *, m) => TlvContentOwned::M3(m),
            }
        }
    }

    pub struct TlvContentMapper;

    impl View for TlvContentMapper {
        type V = Self;

        open spec fn view(&self) -> Self::V {
            *self
        }
    }

    impl SpecIso for TlvContentMapper {
        type Src = SpecTlvContentInner;

        type Dst = SpecTlvContent;

        proof fn spec_iso(s: SpecTlvContentInner) {
        }

        proof fn spec_iso_rev(s: SpecTlvContent) {
        }
    }

    impl Iso for TlvContentMapper {
        type Src<'a> = TlvContentInner<'a>;

        type Dst<'a> = TlvContent<'a>;

        type SrcOwned = TlvContentOwnedInner;

        type DstOwned = TlvContentOwned;
    }

    /// TLV
    pub struct SpecTlv {
        pub tag: u8,
        pub len: u8,
        pub content: SpecTlvContent,
        pub rest: Seq<u8>,
    }

    pub type SpecTlvInner = ((u8, u8), (SpecTlvContent, Seq<u8>));

    pub struct Tlv<'a> {
        pub tag: u8,
        pub len: u8,
        pub content: TlvContent<'a>,
        pub rest: &'a [u8],
    }

    pub type TlvInner<'a> = ((u8, u8), (TlvContent<'a>, &'a [u8]));

    pub struct TlvOwned {
        pub tag: u8,
        pub len: u8,
        pub content: TlvContentOwned,
        pub rest: Vec<u8>,
    }

    pub type TlvInnerOwned = ((u8, u8), (TlvContentOwned, Vec<u8>));

    impl View for Tlv<'_> {
        type V = SpecTlv;

        open spec fn view(&self) -> Self::V {
            SpecTlv { tag: self.tag, len: self.len, content: self.content@, rest: self.rest@ }
        }
    }

    impl View for TlvOwned {
        type V = SpecTlv;

        open spec fn view(&self) -> Self::V {
            SpecTlv { tag: self.tag, len: self.len, content: self.content@, rest: self.rest@ }
        }
    }

    impl SpecFrom<SpecTlv> for SpecTlvInner {
        open spec fn spec_from(e: SpecTlv) -> SpecTlvInner {
            ((e.tag, e.len), (e.content, e.rest))
        }
    }

    impl SpecFrom<SpecTlvInner> for SpecTlv {
        open spec fn spec_from(e: SpecTlvInner) -> SpecTlv {
            let ((tag, len), (content, rest)) = e;
            SpecTlv { tag, len, content, rest }
        }
    }

    impl<'a> From<Tlv<'a>> for TlvInner<'a> {
        fn ex_from(e: Tlv) -> (res: TlvInner) {
            ((e.tag, e.len), (e.content, e.rest))
        }
    }

    impl<'a> From<TlvInner<'a>> for Tlv<'a> {
        fn ex_from(e: TlvInner) -> (res: Tlv) {
            let ((tag, len), (content, rest)) = e;
            Tlv { tag, len, content, rest }
        }
    }

    impl From<TlvOwned> for TlvInnerOwned {
        fn ex_from(e: TlvOwned) -> (res: TlvInnerOwned) {
            ((e.tag, e.len), (e.content, e.rest))
        }
    }

    impl From<TlvInnerOwned> for TlvOwned {
        fn ex_from(e: TlvInnerOwned) -> (res: TlvOwned) {
            let ((tag, len), (content, rest)) = e;
            TlvOwned { tag, len, content, rest }
        }
    }

    pub struct TlvMapper;

    impl View for TlvMapper {
        type V = Self;

        open spec fn view(&self) -> Self::V {
            *self
        }
    }

    impl SpecIso for TlvMapper {
        type Src = SpecTlvInner;

        type Dst = SpecTlv;

        proof fn spec_iso(s: SpecTlvInner) {
        }

        proof fn spec_iso_rev(s: SpecTlv) {
        }
    }

    impl Iso for TlvMapper {
        type Src<'a> = TlvInner<'a>;

        type Dst<'a> = Tlv<'a>;

        type SrcOwned = TlvInnerOwned;

        type DstOwned = TlvOwned;
    }

    type Msg1Combinator = Mapped<(((U8, U16), Bytes), Tail), Msg1Mapper>;

    type Msg2Combinator = Mapped<((U8, U16), U32), Msg2Mapper>;

    type Msg3Combinator = Mapped<BytesN<6>, Msg3Mapper>;

    type TlvContentCombinator = AndThen<
        Bytes,
        Mapped<
            ord_choice_type!(Cond<Msg1Combinator>, Cond<Msg2Combinator>, Cond<Msg3Combinator>),
            TlvContentMapper,
        >,
    >;

    type TlvCombinator = Mapped<SpecDepend<(U8, U8), (TlvContentCombinator, Tail)>, TlvMapper>;

    // type TlvCombinator = Mapped<Depend<(U8, U8), (TlvContentCombinator, Tail), impl Fn((u8, u8)) -> (TlvContentCombinator, Tail)>, TlvMapper>;
    pub open spec fn spec_msg1() -> Msg1Combinator {
        Mapped { inner: (((U8, U16), Bytes(3)), Tail), mapper: Msg1Mapper }
    }

    pub open spec fn spec_msg2() -> Msg2Combinator {
        Mapped { inner: ((U8, U16), U32), mapper: Msg2Mapper }
    }

    pub open spec fn spec_msg3() -> Msg3Combinator {
        Mapped { inner: BytesN::<6>, mapper: Msg3Mapper }
    }

    pub open spec fn spec_tlv_content(tag: u8, len: u8) -> TlvContentCombinator {
        AndThen(
            Bytes(len as usize),
            Mapped {
                inner: ord_choice!(
                    Cond { cond: tag == 1, inner: spec_msg1() },
                    Cond { cond: tag == 2, inner: spec_msg2() },
                    Cond { cond: tag == 3, inner: spec_msg3() },
                ),
                mapper: TlvContentMapper,
            },
        )
    }

    pub open spec fn spec_tlv() -> TlvCombinator {
        let fst = (U8, U8);
        let snd = |deps|
            {
                let (tag, len) = deps;
                (spec_tlv_content(tag, len), Tail)
            };
        Mapped { inner: SpecDepend { fst, snd }, mapper: TlvMapper }
    }

    pub fn msg1() -> (o: Msg1Combinator)
        ensures
            o@ == spec_msg1(),
    {
        Mapped { inner: (((U8, U16), Bytes(3)), Tail), mapper: Msg1Mapper }
    }

    pub fn msg2() -> (o: Msg2Combinator)
        ensures
            o@ == spec_msg2(),
    {
        Mapped { inner: ((U8, U16), U32), mapper: Msg2Mapper }
    }

    pub fn msg3() -> (o: Msg3Combinator)
        ensures
            o@ == spec_msg3(),
    {
        Mapped { inner: BytesN::<6>, mapper: Msg3Mapper }
    }

    fn tlv_content(tag: u8, len: u8) -> (o: TlvContentCombinator)
        ensures
            o@ == spec_tlv_content(tag@, len@),
    {
        AndThen(
            Bytes(len as usize),
            Mapped {
                inner: ord_choice!(
                    Cond { cond: tag == 1, inner: msg1() },
                    Cond { cond: tag == 2, inner: msg2() },
                    Cond { cond: tag == 3, inner: msg3() },
                ),
                mapper: TlvContentMapper,
            },
        )
    }

    pub open spec fn spec_msg1_parse(i: Seq<u8>) -> Result<(usize, SpecMsg1), ()> {
        spec_msg1().spec_parse(i)
    }

    pub open spec fn spec_msg1_serialize(msg: SpecMsg1) -> Result<Seq<u8>, ()> {
        spec_msg1().spec_serialize(msg)
    }

    pub open spec fn spec_msg2_parse(i: Seq<u8>) -> Result<(usize, Msg2), ()> {
        spec_msg2().spec_parse(i)
    }

    pub open spec fn spec_msg2_serialize(msg: Msg2) -> Result<Seq<u8>, ()> {
        spec_msg2().spec_serialize(msg)
    }

    pub open spec fn spec_msg3_parse(i: Seq<u8>) -> Result<(usize, SpecMsg3), ()> {
        spec_msg3().spec_parse(i)
    }

    pub open spec fn spec_msg3_serialize(msg: SpecMsg3) -> Result<Seq<u8>, ()> {
        spec_msg3().spec_serialize(msg)
    }

    pub open spec fn spec_tlv_content_parse(i: Seq<u8>, tag: u8, len: u8) -> Result<
        (usize, SpecTlvContent),
        (),
    > {
        spec_tlv_content(tag, len).spec_parse(i)
    }

    pub open spec fn spec_tlv_content_serialize(msg: SpecTlvContent, tag: u8, len: u8) -> Result<
        Seq<u8>,
        (),
    > {
        spec_tlv_content(tag, len).spec_serialize(msg)
    }

    pub open spec fn spec_tlv_parse(i: Seq<u8>) -> Result<(usize, SpecTlv), ()> {
        spec_tlv().spec_parse(i)
    }

    pub open spec fn spec_tlv_serialize(msg: SpecTlv) -> Result<Seq<u8>, ()> {
        spec_tlv().spec_serialize(msg)
    }

    pub fn msg1_parse(i: &[u8]) -> (o: Result<(usize, Msg1<'_>), ParseError>)
        ensures
            o matches Ok(r) ==> spec_msg1_parse(i@) matches Ok(r_) && r@ == r_,
    {
        msg1().parse(i)
    }

    pub fn msg1_serialize(msg: Msg1<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
        ensures
            o matches Ok(n) ==> {
                &&& spec_msg1_serialize(msg@) matches Ok(buf)
                &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
            },
    {
        msg1().serialize(msg, data, pos)
    }

    pub fn msg2_parse(i: &[u8]) -> (o: Result<(usize, Msg2), ParseError>)
        ensures
            o matches Ok(r) ==> spec_msg2_parse(i@) matches Ok(r_) && r@ == r_,
    {
        msg2().parse(i)
    }

    pub fn msg2_serialize(msg: Msg2, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
        ensures
            o matches Ok(n) ==> {
                &&& spec_msg2_serialize(msg@) matches Ok(buf)
                &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
            },
    {
        msg2().serialize(msg, data, pos)
    }

    pub fn msg3_parse(i: &[u8]) -> (o: Result<(usize, Msg3<'_>), ParseError>)
        ensures
            o matches Ok(r) ==> spec_msg3_parse(i@) matches Ok(r_) && r@ == r_,
    {
        msg3().parse(i)
    }

    pub fn msg3_serialize(msg: Msg3<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
        ensures
            o matches Ok(n) ==> {
                &&& spec_msg3_serialize(msg@) matches Ok(buf)
                &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
            },
    {
        msg3().serialize(msg, data, pos)
    }

    fn tlv_content_parse(i: &[u8], tag: u8, len: u8) -> (o: Result<(usize, TlvContent<'_>), ParseError>)
        ensures
            o matches Ok(r) ==> spec_tlv_content_parse(i@, tag@, len@) matches Ok(r_) && r@ == r_,
    {
        tlv_content(tag, len).parse(i)
    }

    fn tlv_content_serialize(
        msg: TlvContent<'_>,
        data: &mut Vec<u8>,
        pos: usize,
        tag: u8,
        len: u8,
    ) -> (o: Result<usize, SerializeError>)
        ensures
            o matches Ok(n) ==> {
                &&& spec_tlv_content_serialize(msg@, tag@, len@) matches Ok(buf)
                &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
            },
    {
        tlv_content(tag, len).serialize(msg, data, pos)
    }

    pub fn tlv_parse(i: &[u8]) -> (o: Result<(usize, Tlv<'_>), ParseError>)
        ensures
            o matches Ok(r) ==> spec_tlv_parse(i@) matches Ok(r_) && r@ == r_,
    {
        let ghost spec_snd = |deps|
            {
                let (tag, len) = deps;
                (spec_tlv_content(tag, len), Tail)
            };
        let fst = (U8, U8);
        let snd = |deps: (u8, u8)| -> (o: (TlvContentCombinator, Tail))
            ensures
                o@ == spec_snd(deps@),
            {
                let (tag, len) = deps;
                (tlv_content(tag, len), Tail)
            };
        Mapped { inner: Depend { fst, snd, spec_snd: Ghost(spec_snd) }, mapper: TlvMapper }.parse(i)
    }

    pub fn tlv_serialize(msg: Tlv<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
        ensures
            o matches Ok(n) ==> {
                &&& spec_tlv_serialize(msg@) matches Ok(buf)
                &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
            },
    {
        let ghost spec_snd = |deps|
            {
                let (tag, len) = deps;
                (spec_tlv_content(tag, len), Tail)
            };
        let fst = (U8, U8);
        let snd = |deps: (u8, u8)| -> (o: (TlvContentCombinator, Tail))
            ensures
                o@ == spec_snd(deps@),
            {
                let (tag, len) = deps;
                (tlv_content(tag, len), Tail)
            };
        Mapped {
            inner: Depend { fst, snd, spec_snd: Ghost(spec_snd) },
            mapper: TlvMapper,
        }.serialize(msg, data, pos)
    }

    // use crate::regular::{uints::{U8, U16, U32, U64}, bytes::Bytes, and_then::AndThen, tag::Tag};
    // use super::*;
    //
    // spec fn spec_dep(input: Seq<u8>) -> Result<(usize, ((u8, (u16, u32)), ((), Seq<u8>))), ()> {
    //     let msg = SpecDepend {
    //         fst: (U8, (U16, U32)),
    //         snd: |deps|
    //             {
    //                 let (a, (_b, c)): (u8, (u16, u32)) = deps;
    //                 (Bytes(a as usize).spec_and_then(Tag::spec_new(U64, 99999)), Bytes(c as usize))
    //             },
    //     };
    //     msg.spec_parse(input)
    // }
    //
    // fn dep(input: &[u8]) -> (o: Result<(usize, ((u8, (u16, u32)), ((), &[u8]))), ()>)
    //     ensures
    //         o is Ok ==> o.unwrap()@ == spec_dep(input@).unwrap(),
    // {
    //     let ghost spec_snd = |deps|
    //         {
    //             let (a, (_b, c)): (u8, (u16, u32)) = deps;
    //             (Bytes(a as usize).spec_and_then(Tag::spec_new(U64, 99999)), Bytes(c as usize))
    //         };
    //     let msg = Depend {
    //         fst: (U8, (U16, U32)),
    //         snd: (|deps| -> (o: (AndThen<Bytes, Tag<U64, u64>>, Bytes))
    //             ensures
    //                 o@ == spec_snd(deps@),
    //             {
    //                 let (a, (_b, c)): (u8, (u16, u32)) = deps;
    //                 (Bytes(a as usize).and_then(Tag::new(U64, 99999)), Bytes(c as usize))
    //             }),
    //         spec_snd: Ghost(spec_snd),
    //     };
    //     msg.parse(input)
    // }

}

} // verus!
