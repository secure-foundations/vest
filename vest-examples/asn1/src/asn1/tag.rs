use super::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Combinator for ASN.1 tags
#[derive(Debug, View)]
pub struct ASN1Tag;

#[derive(Debug)]
pub struct TagValue {
    pub class: TagClass,
    pub form: TagForm,

    /// Currently we only support tag numbers up to 31
    /// Larger tag numbers require the long form of tags
    pub num: u8,
}

impl View for TagValue {
    type V = TagValue;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

#[derive(Debug)]
pub enum TagClass {
    Universal,
    Application,
    ContextSpecific,
    Private,
}

#[derive(Debug)]
pub enum TagForm {
    Primitive,
    Constructed,
}

impl TagValue {
    #[inline(always)]
    pub fn eq(self, other: TagValue) -> (res: bool)
        ensures res == (self == other)
    {
        // TODO: fix this once Verus supports equality for enum
        (match (self.class, other.class) {
            (TagClass::Universal, TagClass::Universal) => true,
            (TagClass::Application, TagClass::Application) => true,
            (TagClass::ContextSpecific, TagClass::ContextSpecific) => true,
            (TagClass::Private, TagClass::Private) => true,
            _ => false,
        }) && (match (self.form, other.form) {
            (TagForm::Primitive, TagForm::Primitive) => true,
            (TagForm::Constructed, TagForm::Constructed) => true,
            _ => false,
        }) && self.num == other.num
    }

    /// TODO: fix after Verus supports Clone
    #[inline(always)]
    pub fn clone(&self) -> (res: TagValue)
        ensures res == *self
    {
        TagValue {
            class: match self.class {
                TagClass::Universal => TagClass::Universal,
                TagClass::Application => TagClass::Application,
                TagClass::ContextSpecific => TagClass::ContextSpecific,
                TagClass::Private => TagClass::Private,
            },
            form: match self.form {
                TagForm::Primitive => TagForm::Primitive,
                TagForm::Constructed => TagForm::Constructed,
            },
            num: self.num,
        }
    }
}

impl SpecCombinator for ASN1Tag {
    type Type = TagValue;

    open spec fn wf(&self, v: Self::Type) -> bool {
        v.num <= 0b11111
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if s.len() == 0 {
            None
        } else {
            let class_num = s[0] >> 6 & 0b11;
            let class = if class_num == 0 {
                TagClass::Universal
            } else if class_num == 1 {
                TagClass::Application
            } else if class_num == 2 {
                TagClass::ContextSpecific
            } else {
                TagClass::Private
            };

            let form_num = s[0] >> 5 & 1;
            let form = if form_num == 0 {
                TagForm::Primitive
            } else {
                TagForm::Constructed
            };

            Some((1, TagValue {
                class,
                form,
                num: s[0] & 0b11111,
            }))
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        let class: u8 = match v.class {
            TagClass::Universal => 0,
            TagClass::Application => 1,
            TagClass::ContextSpecific => 2,
            _ => 3,
        };

        let form: u8 = match v.form {
            TagForm::Primitive => 0,
            _ => 1,
        };

        if v.num > 0b11111 {
            seq![]
        } else {
            seq![(class << 6) | (form << 5) | (v.num & 0b11111)]
        }
    }
}

impl SecureSpecCombinator for ASN1Tag {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if !self.wf(v) {
            return;
        }

        let class_num: u8 = match v.class {
            TagClass::Universal => 0,
            TagClass::Application => 1,
            TagClass::ContextSpecific => 2,
            _ => 3,
        };

        let form_num: u8 = match v.form {
            TagForm::Primitive => 0,
            _ => 1,
        };

        let num = v.num;

        // Restate parse(serialize(v)) = v, but purely in BV
        assert(
            0 <= class_num < 4 &&
            0 <= form_num < 2 &&
            0 <= num <= 0b11111 ==> {
            let ser = (class_num << 6) | (form_num << 5) | (num & 0b11111);
            &&& ser >> 6 & 0b11 == class_num
            &&& ser >> 5 & 1 == form_num
            &&& ser & 0b11111 == num
        }) by (bit_vector);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if buf.len() > 0 {
            let tag = buf[0];

            // Restate serialize(parse(v)) = v, but purely in BV
            assert(
                (tag >> 6 & 0b11) << 6 | (tag >> 5 & 1) << 5 | ((tag & 0b11111) & 0b11111) == tag
            ) by (bit_vector);

            // Some bound facts
            assert(tag >> 6 & 0b11 < 4) by (bit_vector);
            assert(tag >> 5 & 1 < 2) by (bit_vector);
            assert(tag & 0b11111 <= 0b11111) by (bit_vector);

            if let Some((n, v)) = self.spec_parse(buf) {
                let ser = self.spec_serialize(v);
                assert(ser =~= buf.subrange(0, 1));
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ASN1Tag {
    type Type = TagValue;
    type SType = TagValue;

    fn length(&self, v: Self::SType) -> usize {
        if v.num > 0b11111 {
            0
        } else {
            1
        }
    }

    #[inline]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        if s.len() == 0 {
            return Err(ParseError::UnexpectedEndOfInput);
        } else {
            let class_num = s[0] >> 6 & 0b11;
            let class = if class_num == 0 {
                TagClass::Universal
            } else if class_num == 1 {
                TagClass::Application
            } else if class_num == 2 {
                TagClass::ContextSpecific
            } else {
                TagClass::Private
            };

            let form_num = s[0] >> 5 & 1;
            let form = if form_num == 0 {
                TagForm::Primitive
            } else {
                TagForm::Constructed
            };

            Ok((1, TagValue {
                class,
                form,
                num: s[0] & 0b11111,
            }))
        }
    }

    #[inline]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let class: u8 = match v.class {
            TagClass::Universal => 0,
            TagClass::Application => 1,
            TagClass::ContextSpecific => 2,
            _ => 3,
        };

        let form: u8 = match v.form {
            TagForm::Primitive => 0,
            _ => 1,
        };

        if v.num > 0b11111 {
            return Err(SerializeError::Other("Invalid tag number".to_string()));
        }

        if pos < data.len() {
            let tag = (class << 6) | (form << 5) | (v.num & 0b11111);
            data.set(pos, tag);
            assert(data@ == seq_splice(old(data)@, pos, seq![tag]));
            Ok(1)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

/// A trait for combinators to mark their original tags
/// (e.g. 0x02 for INTEGER)
///
/// Can be overwritten by explicit or implicit tagging
pub trait ASN1Tagged
{
    spec fn spec_tag(&self) -> TagValue;
    fn tag(&self) -> (res: TagValue)
        ensures res == self.spec_tag();
}

/// An additional property that if an ASN1Tagged
/// implements View, then the viewed version preserves the tag
pub trait ViewWithASN1Tagged: View + ASN1Tagged where
    Self::V: ASN1Tagged,
{
    proof fn lemma_view_preserves_tag(&self)
        ensures self@.spec_tag() == self.spec_tag();
}

/// A combinator wrapper that also emits a tag before
/// parsing/serializing the inner value
#[derive(Debug)]
pub struct ASN1<T>(pub T);

impl<T: View> View for ASN1<T> {
    type V = ASN1<T::V>;

    open spec fn view(&self) -> Self::V {
        ASN1(self.0.view())
    }
}

impl<T: ASN1Tagged> ASN1Tagged for ASN1<T> {
    open spec fn spec_tag(&self) -> TagValue {
        self.0.spec_tag()
    }

    #[inline(always)]
    fn tag(&self) -> TagValue {
        self.0.tag()
    }
}

impl<T: ASN1Tagged + ViewWithASN1Tagged> ViewWithASN1Tagged for ASN1<T> where
    T::V: ASN1Tagged,
{
    proof fn lemma_view_preserves_tag(&self) {
        self.0.lemma_view_preserves_tag();
    }
}

impl<T: ASN1Tagged + SpecCombinator> SpecCombinator for ASN1<T> {
    type Type = <T as SpecCombinator>::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v) && ASN1Tag.wf(self.0.spec_tag())
    }
    
    open spec fn requires(&self) -> bool {
        self.0.requires()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match (ASN1Tag, self.0).spec_parse(s) {
            Some((n, (tag, v))) =>
                if tag == self.0.spec_tag() {
                    Some((n, v))
                } else {
                    None
                }
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        (ASN1Tag, self.0).spec_serialize((self.0.spec_tag(), v))
    }
}

impl<T: ASN1Tagged + SecureSpecCombinator> SecureSpecCombinator for ASN1<T> {
    open spec fn is_prefix_secure() -> bool {
        T::is_prefix_secure()
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        (ASN1Tag, self.0).theorem_serialize_parse_roundtrip((self.0.spec_tag(), v));
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (ASN1Tag, self.0).theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        (ASN1Tag, self.0).lemma_prefix_secure(s1, s2);
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        (ASN1Tag, self.0).lemma_parse_length(s);
    }
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        (ASN1Tag, self.0).lemma_parse_productive(s);
    }
}

impl<'a, T> Combinator<'a, &'a [u8], Vec<u8>> for ASN1<T> where
    T: ASN1Tagged
        + SpecCombinator
        + ViewWithASN1Tagged
        + for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type> + ASN1Tagged,
    for<'x> <T as Combinator<'x, &'x [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type>,
{
    type Type = <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType;

    fn length(&self, v: Self::SType) -> usize {
        let len = self.0.length(v);
        1 + len
    }

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires() && ASN1Tag.ex_requires()
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        proof {
            self.0.lemma_view_preserves_tag();
        }

        let (n, (tag, v)) = (ASN1Tag, &self.0).parse(s)?;
        if tag.eq(self.0.tag()) {
            Ok((n, v))
        } else {
            Err(ParseError::Other("Unmatching tags".to_string()))
        }
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        proof {
            self.0.lemma_view_preserves_tag();
        }

        (ASN1Tag, &self.0).serialize((self.0.tag(), v), data, pos)
    }
}

/// If T1 and T2 have different tags, then their tagged encodings are disjoint
impl<T1, T2> DisjointFrom<ASN1<T1>> for ASN1<T2> where
    T1: ASN1Tagged + SpecCombinator,
    T2: ASN1Tagged + SpecCombinator,
{
    open spec fn disjoint_from(&self, other: &ASN1<T1>) -> bool {
        self.0.spec_tag() != other.0.spec_tag()
    }

    proof fn parse_disjoint_on(&self, other: &ASN1<T1>, buf: Seq<u8>) {}
}

/// If T1 and T2 have different tags, then (T1, ...) is disjoint from T2
impl<T1, T2, S> DisjointFrom<(ASN1<T1>, S)> for ASN1<T2> where
    T1: ASN1Tagged + SecureSpecCombinator,
    T2: ASN1Tagged + SpecCombinator,
    S: SpecCombinator,
{
    open spec fn disjoint_from(&self, other: &(ASN1<T1>, S)) -> bool {
        self.0.spec_tag() != other.0.0.spec_tag()
    }

    proof fn parse_disjoint_on(&self, other: &(ASN1<T1>, S), buf: Seq<u8>) {}
}

impl<T> DisjointFrom<ASN1<T>> for End where
    T: ASN1Tagged + SpecCombinator,
{
    open spec fn disjoint_from(&self, other: &ASN1<T>) -> bool { true }
    proof fn parse_disjoint_on(&self, other: &ASN1<T>, buf: Seq<u8>) {}
}

impl<T1, T2> DisjointFrom<ASN1<T1>> for Cond<ASN1<T2>> where
    T1: ASN1Tagged + SpecCombinator,
    T2: ASN1Tagged + SpecCombinator,
 {
    open spec fn disjoint_from(&self, other: &ASN1<T1>) -> bool {
        self.inner.0.spec_tag() != other.0.spec_tag()
    }

    proof fn parse_disjoint_on(&self, other: &ASN1<T1>, buf: Seq<u8>) {}
}

impl<T1, T2> DisjointFrom<Cached<ASN1<T1>>> for ASN1<T2> where
    T1: ASN1Tagged + SpecCombinator,
    T2: ASN1Tagged + SpecCombinator,
{
    open spec fn disjoint_from(&self, other: &Cached<ASN1<T1>>) -> bool {
        self.0.spec_tag() != other.0.0.spec_tag()
    }

    proof fn parse_disjoint_on(&self, other: &Cached<ASN1<T1>>, buf: Seq<u8>) {}
}

/// Macro to generate a ASN1Tagged and ViewWithASN1Tagged trait impl
#[allow(unused_macros)]
#[macro_export]
macro_rules! asn1_tagged {
    ($ty:ident, $tag:expr) => {
        ::vstd::prelude::verus! {
            impl ASN1Tagged for $ty {
                open spec fn spec_tag(&self) -> TagValue {
                    $tag
                }

                fn tag(&self) -> TagValue {
                    $tag
                }
            }

            impl ViewWithASN1Tagged for $ty {
                proof fn lemma_view_preserves_tag(&self) {}
            }
        }
    };
}
pub use asn1_tagged;

/// Tags of common ASN.1 types
#[allow(unused_macros)]
macro_rules! tag_of {
    (BOOLEAN) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x01,
        }
    };

    (INTEGER) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x02,
        }
    };

    (BIT_STRING) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x03,
        }
    };

    (OCTET_STRING) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x04,
        }
    };

    (NULL) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x05,
        }
    };

    (OBJECT_IDENTIFIER) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x06,
        }
    };

    (SEQUENCE) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }
    };

    (SET) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x11,
        }
    };

    (UTF8_STRING) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x0c,
        }
    };

    (PRINTABLE_STRING) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x13,
        }
    };

    (TELETEX_STRING) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x14,
        }
    };

    (IA5_STRING) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x16,
        }
    };

    (UNIVERSAL_STRING) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x1c,
        }
    };

    (BMP_STRING) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x1e,
        }
    };

    (UTC_TIME) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x17,
        }
    };

    (GENERALIZED_TIME) => {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x18,
        }
    };

    (IMPLICIT $num:literal) => {
        TagValue {
            class: TagClass::ContextSpecific,
            form: TagForm::Primitive,
            num: $num,
        }
    };

    (EXPLICIT $num:literal) => {
        TagValue {
            class: TagClass::ContextSpecific,
            form: TagForm::Constructed,
            num: $num,
        }
    };
}
pub(crate) use tag_of;

/// Placeholder to parse a TLV tuple as OctetString
/// with the provided tag
#[allow(unused_macros)]
macro_rules! placeholder {
    ($($tag:tt)*) => {
        ASN1(ImplicitTag(tag_of!($($tag)*), OctetString))
    };
}
pub(crate) use placeholder;

#[allow(unused_macros)]
macro_rules! placeholder_type {
    () => { ASN1<ImplicitTag<OctetString>> };
}
pub(crate) use placeholder_type;

// #[allow(unused_macros)]
// macro_rules! implicit_tag {
//     ($num:literal, $inner:expr) => {
//         ImplicitTag(TagValue {
//             class: TagClass::ContextSpecific,
//             form: TagForm::Primitive,
//             num: $num,
//         }, $inner)
//     };
// }
// pub(crate) use implicit_tag;

// #[allow(unused_macros)]
// macro_rules! explicit_tag {
//     ($num:literal, $inner:expr) => {
//         ExplicitTag(TagValue {
//             class: TagClass::ContextSpecific,
//             form: TagForm::Constructed,
//             num: $num,
//         }, ASN1($inner))
//     };
// }
// pub(crate) use explicit_tag;

}
