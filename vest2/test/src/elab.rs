# ! [allow (warnings)] use vest_lib2 :: combinators :: mapped :: spec :: * ;
use vest_lib2 :: combinators :: * ;
use vest_lib2 :: core :: exec :: input :: {
    InputBuf ,
    InputSlice
}
;
use vest_lib2 :: core :: exec :: parser :: * ;
use vest_lib2 :: core :: exec :: serializer :: * ;
use vest_lib2 :: core :: exec :: ParseError ;
use vest_lib2 :: core :: {
    proof :: * ,
    spec :: *
}
;
use vest_lib2 :: primitives :: btcvarint :: VarInt ;
use vest_lib2 :: primitives :: leb128 :: ULeb128 ;
use vstd :: prelude :: * ;
verus! {
    // ============================================================
    // Data Types
    // ============================================================
    # [doc = "data type for `content_0`."]
    pub type Content0 < 'i > = & 'i [u8] ;
    pub type Content0Spec = Seq < u8 > ;


    # [doc = "data type for `content_type`."]
    # [repr (u8)]
    # [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
    pub enum ContentType {
        C0 = 0 ,
        C1 = 1 ,
        C2 = 2 ,
        Unknown (u8) ,
    }
    pub type ContentTypeSpec = ContentType ;
    pub type ContentTypeInner = Sum < u8 , u8 > ;
    impl DeepView for ContentType {
        type V = ContentTypeSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match * self {
                ContentType :: C0 => ContentTypeSpec :: C0 ,
                ContentType :: C1 => ContentTypeSpec :: C1 ,
                ContentType :: C2 => ContentTypeSpec :: C2 ,
                ContentType :: Unknown (v) => ContentTypeSpec :: Unknown (v) ,
            }
        }
    }

    # [doc = "data type for `msg_c_f4`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum MsgCF4 < 'i > {
        C0 (Content0 < 'i >) ,
        C1 (u16) ,
        C2 (u32) ,
        Default (& 'i [u8]) ,
    }
    # [verifier :: ext_equal]
    pub enum MsgCF4Spec {
        C0 (Content0Spec) ,
        C1 (u16) ,
        C2 (u32) ,
        Default (Seq < u8 >) ,
    }
    pub type MsgCF4Inner = Sum < Content0Spec , Sum < u16 , Sum < u32 , Seq < u8 > > > > ;
    impl < 'i > DeepView for MsgCF4 < 'i > {
        type V = MsgCF4Spec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                MsgCF4 :: C0 (v) => MsgCF4Spec :: C0 (v . deep_view ()) ,
                MsgCF4 :: C1 (v) => MsgCF4Spec :: C1 (v . deep_view ()) ,
                MsgCF4 :: C2 (v) => MsgCF4Spec :: C2 (v . deep_view ()) ,
                MsgCF4 :: Default (v) => MsgCF4Spec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `msg_d`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct MsgD {
        pub f1 : [u8 ;
        4] ,
        pub f2 : u16 ,
        pub c : [u8 ;
        5] ,
    }
    # [verifier :: ext_equal]
    pub struct MsgDSpec {
        pub f1 : Seq < u8 > ,
        pub f2 : u16 ,
        pub c : Seq < u8 > ,
    }
    pub type MsgDInner = (Seq < u8 > , (u16 , Seq < u8 >)) ;
    impl DeepView for MsgD {
        type V = MsgDSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MsgDSpec {
                f1 : self . f1 . deep_view () ,
                f2 : self . f2 . deep_view () ,
                c : self . c . deep_view () ,
            }
        }
    }

    # [doc = "data type for `msg_b`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct MsgB {
        pub f1 : MsgD ,
    }
    # [verifier :: ext_equal]
    pub struct MsgBSpec {
        pub f1 : MsgDSpec ,
    }
    pub type MsgBInner = MsgDSpec ;
    impl DeepView for MsgB {
        type V = MsgBSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MsgBSpec {
                f1 : self . f1 . deep_view () ,
            }
        }
    }

    # [doc = "data type for `msg_a`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct MsgA < 'i > {
        pub f1 : MsgB ,
        pub f2 : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct MsgASpec {
        pub f1 : MsgBSpec ,
        pub f2 : Seq < u8 > ,
    }
    pub type MsgAInner = (MsgBSpec , Seq < u8 >) ;
    impl < 'i > DeepView for MsgA < 'i > {
        type V = MsgASpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MsgASpec {
                f1 : self . f1 . deep_view () ,
                f2 : self . f2 . deep_view () ,
            }
        }
    }

    # [doc = "data type for `msg_c`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct MsgC < 'i > {
        pub f2 : ContentType ,
        pub f3 : u32 ,
        pub f4 : MsgCF4 < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct MsgCSpec {
        pub f2 : ContentTypeSpec ,
        pub f3 : u32 ,
        pub f4 : MsgCF4Spec ,
    }
    pub type MsgCInner = (ContentTypeSpec , (u32 , MsgCF4Spec)) ;
    impl < 'i > DeepView for MsgC < 'i > {
        type V = MsgCSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MsgCSpec {
                f2 : self . f2 . deep_view () ,
                f3 : self . f3 . deep_view () ,
                f4 : self . f4 . deep_view () ,
            }
        }
    }

    # [doc = "data type for `F5`."]
    pub type F5 = [u8 ;
    5] ;
    pub type F5Spec = Seq < u8 > ;

    // ============================================================
    // Format Specifications
    // ============================================================
    # [doc = "named format combinator for `content_0`."]
    pub struct Content0Fmt {
        pub num : u32 ,
    }

    pub type Content0FmtSpec = Named < Varied < usize > > ;

    # [doc = "specification constructor for `content_0`."]
    pub open spec fn content_0_fmt (num : u32) -> Content0FmtSpec {
        Named ("content_0" ,
        Varied ((num as usize)))
    }


    # [doc = "named format combinator for `content_type`."]
    pub struct ContentTypeFmt ;

    pub type ContentTypeFmtSpec = Named < Mapped < Choice < Refined < U8 , PredFnSpec < u8 >> , Refined < U8 , PredFnSpec < u8 >> > , FnSpecMapper < ContentTypeInner , ContentTypeSpec >> > ;

    # [doc = "specification constructor for `content_type`."]
    pub open spec fn content_type_fmt () -> ContentTypeFmtSpec {
        Named ("content_type" ,
        Mapped {
            inner : Choice (Refined (U8 ,
            | x : u8 | x == 0 || x == 1 || x == 2) ,
            Refined (U8 ,
            | x : u8 | x != 0 && x != 1 && x != 2)) ,
            mapper : (| parsed : ContentTypeInner | -> ContentTypeSpec {
                match parsed {
                    Sum :: Inl (x) => match x {
                        0 => ContentTypeSpec :: C0 ,
                        1 => ContentTypeSpec :: C1 ,
                        2 => ContentTypeSpec :: C2 ,
                        _ => arbitrary () ,
                    }
                    ,
                    Sum :: Inr (x) => ContentTypeSpec :: Unknown (x) ,
                }
            }
            ,
            | value : ContentTypeSpec | -> ContentTypeInner {
                match value {
                    ContentTypeSpec :: C0 => Sum :: Inl (0) ,
                    ContentTypeSpec :: C1 => Sum :: Inl (1) ,
                    ContentTypeSpec :: C2 => Sum :: Inl (2) ,
                    ContentTypeSpec :: Unknown (x) => Sum :: Inr (x) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `msg_c_f4`."]
    pub struct MsgCF4Fmt {
        pub f2 : ContentType ,
        pub f3 : u32 ,
    }

    pub type MsgCF4FmtSpec = Named < Mapped < Sum < Content0Fmt , Sum < U16Be , Sum < U32Be , Tail > > > , FnSpecMapper < MsgCF4Inner , MsgCF4Spec >> > ;

    # [doc = "specification constructor for `msg_c_f4`."]
    pub open spec fn msg_c_f4_fmt (f2 : ContentTypeSpec , f3 : u32) -> MsgCF4FmtSpec {
        Named ("msg_c_f4" ,
        Mapped {
            inner : match f2 {
                ContentTypeSpec :: C0 => Sum :: Inl (Content0Fmt {
                    num : f3
                }
                ) ,
                ContentTypeSpec :: C1 => Sum :: Inr (Sum :: Inl (U16Be)) ,
                ContentTypeSpec :: C2 => Sum :: Inr (Sum :: Inr (Sum :: Inl (U32Be))) ,
                _ => Sum :: Inr (Sum :: Inr (Sum :: Inr (Tail))) ,
            }
            ,
            mapper : (| parsed : MsgCF4Inner | -> MsgCF4Spec {
                match parsed {
                    Sum :: Inl (v) => MsgCF4Spec :: C0 (v) ,
                    Sum :: Inr (Sum :: Inl (v)) => MsgCF4Spec :: C1 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inl (v))) => MsgCF4Spec :: C2 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (v))) => MsgCF4Spec :: Default (v) ,
                }
            }
            ,
            | value : MsgCF4Spec | -> MsgCF4Inner {
                match value {
                    MsgCF4Spec :: C0 (v) => Sum :: Inl (v) ,
                    MsgCF4Spec :: C1 (v) => Sum :: Inr (Sum :: Inl (v)) ,
                    MsgCF4Spec :: C2 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inl (v))) ,
                    MsgCF4Spec :: Default (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (v))) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `msg_d`."]
    pub struct MsgDFmt ;

    pub type MsgDFmtSpec = Named < Mapped < Pair < Const < Fixed < 4 > , Seq < u8 >> , Pair < Const < U16Be , u16 > , Const < Fixed < 5 > , Seq < u8 >> > > , FnSpecMapper < MsgDInner , MsgDSpec >> > ;

    # [doc = "specification constructor for `msg_d`."]
    pub open spec fn msg_d_fmt () -> MsgDFmtSpec {
        Named ("msg_d" ,
        Mapped {
            inner : Pair (Const (Fixed :: < 4 > ,
            seq ! [1u8 ;
            4]) ,
            Pair (Const (U16Be ,
            4660) ,
            Const (Fixed :: < 5 > ,
            seq ! [1u8 ;
            5]))) ,
            mapper : (| parsed : MsgDInner | -> MsgDSpec {
                let (f1 ,
                (f2 ,
                c)) = parsed ;
                MsgDSpec {
                    f1 ,
                    f2 ,
                    c
                }
            }
            ,
            | value : MsgDSpec | -> MsgDInner {
                let MsgDSpec {
                    f1 ,
                    f2 ,
                    c
                }
                = value ;
                (f1 ,
                (f2 ,
                c))
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `msg_b`."]
    pub struct MsgBFmt ;

    pub type MsgBFmtSpec = Named < Mapped < MsgDFmt , FnSpecMapper < MsgBInner , MsgBSpec >> > ;

    # [doc = "specification constructor for `msg_b`."]
    pub open spec fn msg_b_fmt () -> MsgBFmtSpec {
        Named ("msg_b" ,
        Mapped {
            inner : MsgDFmt ,
            mapper : (| parsed : MsgBInner | -> MsgBSpec {
                let f1 = parsed ;
                MsgBSpec {
                    f1
                }
            }
            ,
            | value : MsgBSpec | -> MsgBInner {
                let MsgBSpec {
                    f1
                }
                = value ;
                f1
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `msg_a`."]
    pub struct MsgAFmt ;

    pub type MsgAFmtSpec = Named < Mapped < Pair < MsgBFmt , Tail > , FnSpecMapper < MsgAInner , MsgASpec >> > ;

    # [doc = "specification constructor for `msg_a`."]
    pub open spec fn msg_a_fmt () -> MsgAFmtSpec {
        Named ("msg_a" ,
        Mapped {
            inner : Pair (MsgBFmt ,
            Tail) ,
            mapper : (| parsed : MsgAInner | -> MsgASpec {
                let (f1 ,
                f2) = parsed ;
                MsgASpec {
                    f1 ,
                    f2
                }
            }
            ,
            | value : MsgASpec | -> MsgAInner {
                let MsgASpec {
                    f1 ,
                    f2
                }
                = value ;
                (f1 ,
                f2)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `msg_c`."]
    pub struct MsgCFmt ;

    pub type MsgCFmtSpec = Named < Mapped < Bind < ContentTypeFmt , spec_fn (ContentTypeSpec) -> Bind < U24Be , spec_fn (u32) -> ExactLen < MsgCF4Fmt , usize > > > , FnSpecMapper < MsgCInner , MsgCSpec >> > ;

    # [doc = "specification constructor for `msg_c`."]
    pub open spec fn msg_c_fmt () -> MsgCFmtSpec {
        Named ("msg_c" ,
        Mapped {
            inner : Bind (ContentTypeFmt ,
            | f2 : ContentTypeSpec | Bind (U24Be ,
            | f3 : u32 | ExactLen ((f3 as usize) ,
            MsgCF4Fmt {
                f2 ,
                f3
            }
            ))) ,
            mapper : (| parsed : MsgCInner | -> MsgCSpec {
                let (f2 ,
                (f3 ,
                f4)) = parsed ;
                MsgCSpec {
                    f2 ,
                    f3 ,
                    f4
                }
            }
            ,
            | value : MsgCSpec | -> MsgCInner {
                let MsgCSpec {
                    f2 ,
                    f3 ,
                    f4
                }
                = value ;
                (f2 ,
                (f3 ,
                f4))
            }
            )
        }
        )
    }


    // TODO(specs): emit const-format spec wrappers for F5

    // ============================================================
    // Derived Parser, Serializer, Length, and Consistency Specifications
    // ============================================================
    mod derived_specs {
        use super::*;

        impl SpecParser for Content0Fmt {
            type PVal = Content0Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                content_0_fmt (self . num . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for Content0Fmt {
            type Val = Content0Spec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                content_0_fmt (self . num . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for Content0Fmt {
            type SValue = Content0Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                content_0_fmt (self . num . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Content0Fmt {
            type SVal = Content0Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                content_0_fmt (self . num . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for Content0Fmt {
            type T = Content0Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                content_0_fmt (self . num . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for ContentTypeFmt {
            type PVal = ContentTypeSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                content_type_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for ContentTypeFmt {
            type Val = ContentTypeSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                content_type_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for ContentTypeFmt {
            type SValue = ContentTypeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                content_type_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for ContentTypeFmt {
            type SVal = ContentTypeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                content_type_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for ContentTypeFmt {
            type T = ContentTypeSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                content_type_fmt () . byte_len (v)
            }
        }

        impl SpecParser for MsgCF4Fmt {
            type PVal = MsgCF4Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for MsgCF4Fmt {
            type Val = MsgCF4Spec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for MsgCF4Fmt {
            type SValue = MsgCF4Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MsgCF4Fmt {
            type SVal = MsgCF4Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for MsgCF4Fmt {
            type T = MsgCF4Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for MsgDFmt {
            type PVal = MsgDSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                msg_d_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for MsgDFmt {
            type Val = MsgDSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                msg_d_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for MsgDFmt {
            type SValue = MsgDSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                msg_d_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MsgDFmt {
            type SVal = MsgDSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                msg_d_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for MsgDFmt {
            type T = MsgDSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                msg_d_fmt () . byte_len (v)
            }
        }

        impl SpecParser for MsgBFmt {
            type PVal = MsgBSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                msg_b_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for MsgBFmt {
            type Val = MsgBSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                msg_b_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for MsgBFmt {
            type SValue = MsgBSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                msg_b_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MsgBFmt {
            type SVal = MsgBSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                msg_b_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for MsgBFmt {
            type T = MsgBSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                msg_b_fmt () . byte_len (v)
            }
        }

        impl SpecParser for MsgAFmt {
            type PVal = MsgASpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                msg_a_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for MsgAFmt {
            type Val = MsgASpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                msg_a_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for MsgAFmt {
            type SValue = MsgASpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                msg_a_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MsgAFmt {
            type SVal = MsgASpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                msg_a_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for MsgAFmt {
            type T = MsgASpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                msg_a_fmt () . byte_len (v)
            }
        }

        impl SpecParser for MsgCFmt {
            type PVal = MsgCSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                msg_c_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for MsgCFmt {
            type Val = MsgCSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                msg_c_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for MsgCFmt {
            type SValue = MsgCSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                msg_c_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MsgCFmt {
            type SVal = MsgCSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                msg_c_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for MsgCFmt {
            type T = MsgCSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                msg_c_fmt () . byte_len (v)
            }
        }

        // TODO(derived-specs): emit const-format trait wrappers for F5
    }

    // ============================================================
    // Proven Format Properties
    // ============================================================
    mod derived_proofs {
        use super::*;
        broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        impl SafeParser for Content0Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Content0Fmt as SpecParser > :: spec_parse) ;
                content_0_fmt (self . num . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Content0Fmt {
            open spec fn productive_inv (& self) -> bool {
                content_0_fmt (self . num . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Content0Fmt as SpecParser > :: spec_parse) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Content0Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Content0Fmt as SpecParser > :: spec_parse) ;
                reveal (< Content0Fmt as SpecByteLen > :: byte_len) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Content0Fmt as SpecParser > :: spec_parse) ;
                reveal (< Content0Fmt as Consistency > :: consistent) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for Content0Fmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Content0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Content0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Content0Fmt as SpecByteLen > :: byte_len) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for Content0Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Content0Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Content0Fmt as SpecByteLen > :: byte_len) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Content0Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Content0Fmt as SpecParser > :: spec_parse) ;
                reveal (< Content0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Content0Fmt as Consistency > :: consistent) ;
                reveal (< Content0Fmt as SpecByteLen > :: byte_len) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Content0Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Content0Fmt as SpecParser > :: spec_parse) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for Content0Fmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< Content0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Content0Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for Content0Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Content0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Content0Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = content_0_fmt (self . num . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for ContentTypeFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecParser > :: spec_parse) ;
                content_type_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for ContentTypeFmt {
            open spec fn productive_inv (& self) -> bool {
                content_type_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecParser > :: spec_parse) ;
                let fmt = content_type_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for ContentTypeFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecParser > :: spec_parse) ;
                reveal (< ContentTypeFmt as SpecByteLen > :: byte_len) ;
                let fmt = content_type_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecParser > :: spec_parse) ;
                reveal (< ContentTypeFmt as Consistency > :: consistent) ;
                let fmt = content_type_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for ContentTypeFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = content_type_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ContentTypeFmt as SpecByteLen > :: byte_len) ;
                let fmt = content_type_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for ContentTypeFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< ContentTypeFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< ContentTypeFmt as SpecByteLen > :: byte_len) ;
                let fmt = content_type_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for ContentTypeFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecParser > :: spec_parse) ;
                reveal (< ContentTypeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ContentTypeFmt as Consistency > :: consistent) ;
                reveal (< ContentTypeFmt as SpecByteLen > :: byte_len) ;
                let fmt = content_type_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for ContentTypeFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecParser > :: spec_parse) ;
                let fmt = content_type_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for ContentTypeFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< ContentTypeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ContentTypeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = content_type_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for ContentTypeFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< ContentTypeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ContentTypeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = content_type_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MsgCF4Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgCF4Fmt as SpecParser > :: spec_parse) ;
                msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MsgCF4Fmt {
            open spec fn productive_inv (& self) -> bool {
                msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MsgCF4Fmt as SpecParser > :: spec_parse) ;
                let fmt = msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MsgCF4Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgCF4Fmt as SpecParser > :: spec_parse) ;
                reveal (< MsgCF4Fmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgCF4Fmt as SpecParser > :: spec_parse) ;
                reveal (< MsgCF4Fmt as Consistency > :: consistent) ;
                let fmt = msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for MsgCF4Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MsgCF4Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MsgCF4Fmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MsgCF4Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MsgCF4Fmt as SpecParser > :: spec_parse) ;
                reveal (< MsgCF4Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgCF4Fmt as Consistency > :: consistent) ;
                reveal (< MsgCF4Fmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MsgCF4Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MsgCF4Fmt as SpecParser > :: spec_parse) ;
                let fmt = msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for MsgCF4Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MsgCF4Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgCF4Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = msg_c_f4_fmt (self . f2 . deep_view () ,
                self . f3 . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MsgDFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgDFmt as SpecParser > :: spec_parse) ;
                msg_d_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MsgDFmt {
            open spec fn productive_inv (& self) -> bool {
                msg_d_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MsgDFmt as SpecParser > :: spec_parse) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MsgDFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgDFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgDFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgDFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgDFmt as Consistency > :: consistent) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MsgDFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MsgDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MsgDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgDFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for MsgDFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MsgDFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MsgDFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MsgDFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MsgDFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgDFmt as Consistency > :: consistent) ;
                reveal (< MsgDFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MsgDFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MsgDFmt as SpecParser > :: spec_parse) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for MsgDFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< MsgDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgDFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for MsgDFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MsgDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgDFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = msg_d_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MsgBFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgBFmt as SpecParser > :: spec_parse) ;
                msg_b_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MsgBFmt {
            open spec fn productive_inv (& self) -> bool {
                msg_b_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MsgBFmt as SpecParser > :: spec_parse) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MsgBFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgBFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgBFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgBFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgBFmt as Consistency > :: consistent) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MsgBFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MsgBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MsgBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgBFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for MsgBFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MsgBFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MsgBFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MsgBFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MsgBFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgBFmt as Consistency > :: consistent) ;
                reveal (< MsgBFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MsgBFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MsgBFmt as SpecParser > :: spec_parse) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for MsgBFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< MsgBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgBFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for MsgBFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MsgBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgBFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = msg_b_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MsgAFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgAFmt as SpecParser > :: spec_parse) ;
                msg_a_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MsgAFmt {
            open spec fn productive_inv (& self) -> bool {
                msg_a_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MsgAFmt as SpecParser > :: spec_parse) ;
                let fmt = msg_a_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MsgAFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgAFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgAFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_a_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgAFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgAFmt as Consistency > :: consistent) ;
                let fmt = msg_a_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for MsgAFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MsgAFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MsgAFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_a_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MsgAFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MsgAFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgAFmt as Consistency > :: consistent) ;
                reveal (< MsgAFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_a_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MsgAFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MsgAFmt as SpecParser > :: spec_parse) ;
                let fmt = msg_a_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for MsgAFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MsgAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgAFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = msg_a_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MsgCFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgCFmt as SpecParser > :: spec_parse) ;
                msg_c_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MsgCFmt {
            open spec fn productive_inv (& self) -> bool {
                msg_c_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MsgCFmt as SpecParser > :: spec_parse) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MsgCFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgCFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgCFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgCFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgCFmt as Consistency > :: consistent) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MsgCFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MsgCFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MsgCFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgCFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for MsgCFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MsgCFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MsgCFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MsgCFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MsgCFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgCFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgCFmt as Consistency > :: consistent) ;
                reveal (< MsgCFmt as SpecByteLen > :: byte_len) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MsgCFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MsgCFmt as SpecParser > :: spec_parse) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for MsgCFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< MsgCFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgCFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for MsgCFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MsgCFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgCFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = msg_c_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        // TODO(proofs): emit const-format proof wrappers for F5
    }

    // ============================================================
    // Executable Implementations
    // ============================================================
    // TODO(execs): emit Parser / Serializer / Prepare impls for Content0


    // TODO(execs): emit Parser / Serializer / Prepare impls for ContentType


    // TODO(execs): emit Parser / Serializer / Prepare impls for MsgCF4


    // TODO(execs): emit Parser / Serializer / Prepare impls for MsgD


    // TODO(execs): emit Parser / Serializer / Prepare impls for MsgB


    // TODO(execs): emit Parser / Serializer / Prepare impls for MsgA


    // TODO(execs): emit Parser / Serializer / Prepare impls for MsgC


    // TODO(execs): emit const-format exec wrappers for F5
}

