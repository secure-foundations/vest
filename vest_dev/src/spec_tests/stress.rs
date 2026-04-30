use crate::combinators::refined::exec::*;
use crate::combinators::*;
use crate::core::exec::fns::{FnPred, MapRef, Pred};
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::parser::{PResult, Parser};
use crate::core::exec::ParseError;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;
use vest_lib::macros::with_deep_view_and_mapper;

with_deep_view_and_mapper! {
    pub struct PerfHeader<'i> {
        pub version: u8,
        pub flags: u8,
        pub token: &'i [u8],
    }

    #[verifier::ext_equal]
    pub struct PerfHeaderSpec {
        pub version: u8,
        pub flags: u8,
        pub token: Seq<u8>,
    }

    type PerfHeaderInner;
    pub struct PerfHeaderMapper;
}

with_deep_view_and_mapper! {
    pub struct PerfPayload<'i> {
        pub code: u8,
        pub counter: u16,
        pub blob: &'i [u8],
    }

    #[verifier::ext_equal]
    pub struct PerfPayloadSpec {
        pub code: u8,
        pub counter: u16,
        pub blob: Seq<u8>,
    }

    type PerfPayloadInner;
    pub struct PerfPayloadMapper;
}

with_deep_view_and_mapper! {
    pub enum PerfBody20<'i> {
        Tag1(PerfPayload<'i>),
        Tag2(PerfPayload<'i>),
        Tag3(PerfPayload<'i>),
        Tag4(PerfPayload<'i>),
        Tag5(PerfPayload<'i>),
        Tag6(PerfPayload<'i>),
        Tag7(PerfPayload<'i>),
        Tag8(PerfPayload<'i>),
        Tag9(PerfPayload<'i>),
        Tag10(PerfPayload<'i>),
        Tag11(PerfPayload<'i>),
        Tag12(PerfPayload<'i>),
        Tag13(PerfPayload<'i>),
        Tag14(PerfPayload<'i>),
        Tag15(PerfPayload<'i>),
        Tag16(PerfPayload<'i>),
        Tag17(PerfPayload<'i>),
        Tag18(PerfPayload<'i>),
        Tag19(PerfPayload<'i>),
        Tag20(PerfPayload<'i>),
    }

    #[verifier::ext_equal]
    pub enum PerfBody20Spec {
        Tag1(PerfPayloadSpec),
        Tag2(PerfPayloadSpec),
        Tag3(PerfPayloadSpec),
        Tag4(PerfPayloadSpec),
        Tag5(PerfPayloadSpec),
        Tag6(PerfPayloadSpec),
        Tag7(PerfPayloadSpec),
        Tag8(PerfPayloadSpec),
        Tag9(PerfPayloadSpec),
        Tag10(PerfPayloadSpec),
        Tag11(PerfPayloadSpec),
        Tag12(PerfPayloadSpec),
        Tag13(PerfPayloadSpec),
        Tag14(PerfPayloadSpec),
        Tag15(PerfPayloadSpec),
        Tag16(PerfPayloadSpec),
        Tag17(PerfPayloadSpec),
        Tag18(PerfPayloadSpec),
        Tag19(PerfPayloadSpec),
        Tag20(PerfPayloadSpec),
    }

    type PerfBody20Inner;
    pub struct PerfBody20Mapper;
}

with_deep_view_and_mapper! {
    pub struct PerfMessage20<'i> {
        pub header: PerfHeader<'i>,
        pub body: PerfBody20<'i>,
        pub checksum01: u16,
        pub checksum02: u16,
        pub checksum03: u16,
        pub checksum04: u16,
        pub checksum05: u16,
        pub checksum06: u16,
        pub checksum07: u16,
        pub checksum08: u16,
        pub checksum09: u16,
        pub checksum10: u16,
        pub checksum11: u16,
        pub checksum12: u16,
        pub checksum13: u16,
        pub checksum14: u16,
        pub checksum15: u16,
        pub checksum16: u16,
        pub checksum17: u16,
        pub checksum18: u16,
    }

    #[verifier::ext_equal]
    pub struct PerfMessage20Spec {
        pub header: PerfHeaderSpec,
        pub body: PerfBody20Spec,
        pub checksum01: u16,
        pub checksum02: u16,
        pub checksum03: u16,
        pub checksum04: u16,
        pub checksum05: u16,
        pub checksum06: u16,
        pub checksum07: u16,
        pub checksum08: u16,
        pub checksum09: u16,
        pub checksum10: u16,
        pub checksum11: u16,
        pub checksum12: u16,
        pub checksum13: u16,
        pub checksum14: u16,
        pub checksum15: u16,
        pub checksum16: u16,
        pub checksum17: u16,
        pub checksum18: u16,
    }

    type PerfMessage20Inner;
    pub struct PerfMessage20Mapper;
}

with_deep_view_and_mapper! {
    pub struct PerfPair20<'i> {
        pub left: PerfMessage20<'i>,
        pub right: PerfMessage20<'i>,
    }

    #[verifier::ext_equal]
    pub struct PerfPair20Spec {
        pub left: PerfMessage20Spec,
        pub right: PerfMessage20Spec,
    }

    type PerfPair20Inner;
    pub struct PerfPair20Mapper;
}

verus! {


// Larger nominal-format experiments for verification-performance exploration.

pub struct PerfU16LeFmt;

impl SpecParser for PerfU16LeFmt {
    type PVal = u16;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if ibuf.len() < 2 {
            None
        } else {
            Some((2, (ibuf[0] as u16) | ((ibuf[1] as u16) << 8)))
        }
    }
}

impl SafeParser for PerfU16LeFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<PerfU16LeFmt as SpecParser>::spec_parse);
    }
}

impl Consistency for PerfU16LeFmt {
    type Val = u16;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl<'i> Parser<&'i [u8]> for PerfU16LeFmt {
    type PT = u16;

    #[verifier::external_body]
    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Fixed::<2>.parse(ibuf)?;
        let value = u16::from_le_bytes([bytes[0], bytes[1]]);
        Ok((n, value))
    }
}


pub open spec fn perf_header_fmt() -> Mapped<Pair<U8, Pair<U8, Fixed<2>>>, PerfHeaderMapper> {
    Mapped { inner: Pair(U8, Pair(U8, Fixed::<2>)), mapper: PerfHeaderMapper }
}

pub struct PerfHeaderFmt;

impl SpecParser for PerfHeaderFmt {
    type PVal = PerfHeaderSpec;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        perf_header_fmt().spec_parse(ibuf)
    }
}

impl SafeParser for PerfHeaderFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<PerfHeaderFmt as SpecParser>::spec_parse);
        perf_header_fmt().lemma_parse_safe(ibuf);
    }
}

impl<'i> Parser<&'i [u8]> for PerfHeaderFmt {
    type PT = PerfHeader<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(<PerfHeaderFmt as SpecParser>::spec_parse);
        let (n1, version) = U8.parse(ibuf)?;
        let (n2, flags) = U8.parse(&ibuf.skip(n1))?;
        let (n3, token) = Fixed::<2>.parse(&ibuf.skip(n1 + n2))?;
        let total_n = n1 + n2 + n3;
        let value = PerfHeader { version, flags, token };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, value.deep_view())));
        Ok((total_n, value))
    }
}


pub open spec fn perf_payload_fmt() -> Mapped<Pair<U8, Pair<PerfU16LeFmt, Fixed<3>>>, PerfPayloadMapper> {
    Mapped { inner: Pair(U8, Pair(PerfU16LeFmt, Fixed::<3>)), mapper: PerfPayloadMapper }
}

pub struct PerfPayloadFmt;

impl SpecParser for PerfPayloadFmt {
    type PVal = PerfPayloadSpec;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        perf_payload_fmt().spec_parse(ibuf)
    }
}

impl SafeParser for PerfPayloadFmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<PerfPayloadFmt as SpecParser>::spec_parse);
        perf_payload_fmt().lemma_parse_safe(ibuf);
    }
}

impl<'i> Parser<&'i [u8]> for PerfPayloadFmt {
    type PT = PerfPayload<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(<PerfPayloadFmt as SpecParser>::spec_parse);
        let _total_len = ibuf.len();
        let (n1, code) = U8.parse(ibuf)?;
        let (n2, counter) = PerfU16LeFmt.parse(&ibuf.skip(n1))?;
        let (n3, blob) = Fixed::<3>.parse(&ibuf.skip(n1 + n2))?;
        let total_n = n1 + n2 + n3;
        let value = PerfPayload { code, counter, blob };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, value.deep_view())));
        Ok((total_n, value))
    }
}


type PerfBody20Choice =
    Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, Choice<WithPrefixTag<U8, PerfPayloadFmt>, WithPrefixTag<U8, PerfPayloadFmt>>>>>>>>>>>>>>>>>>>>;

pub open spec fn perf_body20_fmt() -> Mapped<PerfBody20Choice, PerfBody20Mapper> {
    #[verusfmt::skip]
    Mapped {
        inner: Choice(WithPrefixTag(U8, 1u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 2u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 3u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 4u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 5u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 6u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 7u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 8u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 9u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 10u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 11u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 12u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 13u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 14u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 15u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 16u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 17u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 18u8, PerfPayloadFmt), Choice(WithPrefixTag(U8, 19u8, PerfPayloadFmt), WithPrefixTag(U8, 20u8, PerfPayloadFmt)))))))))))))))))))),
        mapper: PerfBody20Mapper,
    }
}

pub struct PerfBody20Fmt;

impl SpecParser for PerfBody20Fmt {
    type PVal = PerfBody20Spec;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        perf_body20_fmt().spec_parse(ibuf)
    }
}

impl SafeParser for PerfBody20Fmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<PerfBody20Fmt as SpecParser>::spec_parse);
        perf_body20_fmt().lemma_parse_safe(ibuf);
    }
}

impl<'i> Parser<&'i [u8]> for PerfBody20Fmt {
    type PT = PerfBody20<'i>;

    #[verifier::spinoff_prover]
    #[verifier::rlimit(400)]
    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(<PerfBody20Fmt as SpecParser>::spec_parse);
        let _total_len = ibuf.len();
        let (n1, tag) = U8.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        let (n2, value) = match tag {
            1 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag1(payload))
            }
            2 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag2(payload))
            }
            3 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag3(payload))
            }
            4 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag4(payload))
            }
            5 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag5(payload))
            }
            6 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag6(payload))
            }
            7 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag7(payload))
            }
            8 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag8(payload))
            }
            9 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag9(payload))
            }
            10 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag10(payload))
            }
            11 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag11(payload))
            }
            12 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag12(payload))
            }
            13 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag13(payload))
            }
            14 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag14(payload))
            }
            15 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag15(payload))
            }
            16 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag16(payload))
            }
            17 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag17(payload))
            }
            18 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag18(payload))
            }
            19 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag19(payload))
            }
            20 => {
                let (n2, payload) = PerfPayloadFmt.parse(&rest)?;
                (n2, PerfBody20::Tag20(payload))
            }
            _ => return Err(ParseError::invalid_tag()),
        };
        let total_n = n1 + n2;
        assert(self.spec_parse(ibuf@) == Some((total_n as int, value.deep_view())));
        Ok((total_n, value))
    }
}


type PerfMessage20Chain =
    Pair<PerfHeaderFmt, Pair<PerfBody20Fmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, Pair<PerfU16LeFmt, PerfU16LeFmt>>>>>>>>>>>>>>>>>>>;

pub open spec fn perf_message20_fmt() -> Mapped<PerfMessage20Chain, PerfMessage20Mapper> {
    Mapped {
        inner: Pair(PerfHeaderFmt, Pair(PerfBody20Fmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, Pair(PerfU16LeFmt, PerfU16LeFmt))))))))))))))))))),
        mapper: PerfMessage20Mapper,
    }
}

pub struct PerfMessage20Fmt;

impl SpecParser for PerfMessage20Fmt {
    type PVal = PerfMessage20Spec;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        perf_message20_fmt().spec_parse(ibuf)
    }
}

impl SafeParser for PerfMessage20Fmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<PerfMessage20Fmt as SpecParser>::spec_parse);
        perf_message20_fmt().lemma_parse_safe(ibuf);
    }
}

impl<'i> Parser<&'i [u8]> for PerfMessage20Fmt {
    type PT = PerfMessage20<'i>;

    #[verifier::spinoff_prover]
    #[verifier::rlimit(400)]
    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(<PerfMessage20Fmt as SpecParser>::spec_parse);
        let _total_len = ibuf.len();
        let (n1, header) = PerfHeaderFmt.parse(ibuf)?;
        let rest1 = ibuf.skip(n1);
        let (n2, body) = PerfBody20Fmt.parse(&rest1)?;
        let rest2 = rest1.skip(n2);
        let (n3, checksum01) = PerfU16LeFmt.parse(&rest2)?;
        let rest3 = rest2.skip(n3);
        let (n4, checksum02) = PerfU16LeFmt.parse(&rest3)?;
        let rest4 = rest3.skip(n4);
        let (n5, checksum03) = PerfU16LeFmt.parse(&rest4)?;
        let rest5 = rest4.skip(n5);
        let (n6, checksum04) = PerfU16LeFmt.parse(&rest5)?;
        let rest6 = rest5.skip(n6);
        let (n7, checksum05) = PerfU16LeFmt.parse(&rest6)?;
        let rest7 = rest6.skip(n7);
        let (n8, checksum06) = PerfU16LeFmt.parse(&rest7)?;
        let rest8 = rest7.skip(n8);
        let (n9, checksum07) = PerfU16LeFmt.parse(&rest8)?;
        let rest9 = rest8.skip(n9);
        let (n10, checksum08) = PerfU16LeFmt.parse(&rest9)?;
        let rest10 = rest9.skip(n10);
        let (n11, checksum09) = PerfU16LeFmt.parse(&rest10)?;
        let rest11 = rest10.skip(n11);
        let (n12, checksum10) = PerfU16LeFmt.parse(&rest11)?;
        let rest12 = rest11.skip(n12);
        let (n13, checksum11) = PerfU16LeFmt.parse(&rest12)?;
        let rest13 = rest12.skip(n13);
        let (n14, checksum12) = PerfU16LeFmt.parse(&rest13)?;
        let rest14 = rest13.skip(n14);
        let (n15, checksum13) = PerfU16LeFmt.parse(&rest14)?;
        let rest15 = rest14.skip(n15);
        let (n16, checksum14) = PerfU16LeFmt.parse(&rest15)?;
        let rest16 = rest15.skip(n16);
        let (n17, checksum15) = PerfU16LeFmt.parse(&rest16)?;
        let rest17 = rest16.skip(n17);
        let (n18, checksum16) = PerfU16LeFmt.parse(&rest17)?;
        let rest18 = rest17.skip(n18);
        let (n19, checksum17) = PerfU16LeFmt.parse(&rest18)?;
        let rest19 = rest18.skip(n19);
        let (n20, checksum18) = PerfU16LeFmt.parse(&rest19)?;
        let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 + n11 + n12 + n13 + n14 + n15 + n16 + n17 + n18 + n19 + n20;
        let value = PerfMessage20 {
            header,
            body,
            checksum01,
            checksum02,
            checksum03,
            checksum04,
            checksum05,
            checksum06,
            checksum07,
            checksum08,
            checksum09,
            checksum10,
            checksum11,
            checksum12,
            checksum13,
            checksum14,
            checksum15,
            checksum16,
            checksum17,
            checksum18,
        };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, value.deep_view())));
        Ok((total_n, value))
    }
}


pub open spec fn perf_pair20_fmt() -> Mapped<Pair<PerfMessage20Fmt, PerfMessage20Fmt>, PerfPair20Mapper> {
    Mapped { inner: Pair(PerfMessage20Fmt, PerfMessage20Fmt), mapper: PerfPair20Mapper }
}

pub struct PerfPair20Fmt;

impl SpecParser for PerfPair20Fmt {
    type PVal = PerfPair20Spec;

    #[verifier::opaque]
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        perf_pair20_fmt().spec_parse(ibuf)
    }
}

impl SafeParser for PerfPair20Fmt {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        reveal(<PerfPair20Fmt as SpecParser>::spec_parse);
        perf_pair20_fmt().lemma_parse_safe(ibuf);
    }
}

impl<'i> Parser<&'i [u8]> for PerfPair20Fmt {
    type PT = PerfPair20<'i>;

    #[verifier::spinoff_prover]
    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(<PerfPair20Fmt as SpecParser>::spec_parse);
        let _total_len = ibuf.len();
        let (n1, left) = PerfMessage20Fmt.parse(ibuf)?;
        let (n2, right) = PerfMessage20Fmt.parse(&ibuf.skip(n1))?;
        let total_n = n1 + n2;
        let value = PerfPair20 { left, right };
        assert(self.spec_parse(ibuf@) == Some((total_n as int, value.deep_view())));
        Ok((total_n, value))
    }
}

} // verus!
