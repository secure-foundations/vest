# ! [allow (warnings)] use vest_lib2 :: combinators :: mapped :: spec :: * ;
use vest_lib2 :: combinators :: * ;
use Sum :: Inl as L ;
use Sum :: Inr as R ;
use vest_lib2 :: core :: exec :: {
    DeepEq ,
    SelfView
}
;
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
use vest_lib2 :: macros :: impl_self_view_for ;
use vstd :: prelude :: * ;
verus! {
    // ============================================================
    // Data Types
    // ============================================================
    # [doc = "data type for `msg5_content`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub enum Msg5Content < 'i > {
        Variant1 (u16) ,
        Default (& 'i [u8]) ,
    }
    # [verifier :: ext_equal]
    pub enum Msg5ContentSpec {
        Variant1 (u16) ,
        Default (Seq < u8 >) ,
    }
    pub type Msg5ContentInner = Sum < u16 , Seq < u8 > > ;
    impl < 'i > DeepView for Msg5Content < 'i > {
        type V = Msg5ContentSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                Msg5Content :: Variant1 (v) => Msg5ContentSpec :: Variant1 (v . deep_view ()) ,
                Msg5Content :: Default (v) => Msg5ContentSpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `hello_retry_request`."]
    pub type HelloRetryRequest = u16 ;
    pub type HelloRetryRequestSpec = u16 ;


    # [doc = "data type for `server_hello`."]
    pub type ServerHello = u32 ;
    pub type ServerHelloSpec = u32 ;


    # [doc = "data type for `msg1_payload`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    # [verifier :: ext_equal]
    pub enum Msg1Payload {
        Variant1 (HelloRetryRequest) ,
        Default (ServerHello) ,
    }
    pub type Msg1PayloadSpec = Msg1Payload ;
    pub type Msg1PayloadInner = Sum < HelloRetryRequestSpec , ServerHelloSpec > ;
    impl DeepView for Msg1Payload {
        type V = Self ;
        open spec fn deep_view (& self) -> Self :: V {
            * self
        }
    }

    # [doc = "data type for `msg4_content`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub enum Msg4Content < 'i > {
        Variant1 (u16) ,
        Default (& 'i [u8]) ,
    }
    # [verifier :: ext_equal]
    pub enum Msg4ContentSpec {
        Variant1 (u16) ,
        Default (Seq < u8 >) ,
    }
    pub type Msg4ContentInner = Sum < u16 , Seq < u8 > > ;
    impl < 'i > DeepView for Msg4Content < 'i > {
        type V = Msg4ContentSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                Msg4Content :: Variant1 (v) => Msg4ContentSpec :: Variant1 (v . deep_view ()) ,
                Msg4Content :: Default (v) => Msg4ContentSpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `msg3_content`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub enum Msg3Content < 'i > {
        Variant1 (u16) ,
        Variant2 (u32) ,
        Variant3 (u32) ,
        Default (& 'i [u8]) ,
    }
    # [verifier :: ext_equal]
    pub enum Msg3ContentSpec {
        Variant1 (u16) ,
        Variant2 (u32) ,
        Variant3 (u32) ,
        Default (Seq < u8 >) ,
    }
    pub type Msg3ContentInner = Sum < u16 , Sum < u32 , Sum < u32 , Seq < u8 > > > > ;
    impl < 'i > DeepView for Msg3Content < 'i > {
        type V = Msg3ContentSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                Msg3Content :: Variant1 (v) => Msg3ContentSpec :: Variant1 (v . deep_view ()) ,
                Msg3Content :: Variant2 (v) => Msg3ContentSpec :: Variant2 (v . deep_view ()) ,
                Msg3Content :: Variant3 (v) => Msg3ContentSpec :: Variant3 (v . deep_view ()) ,
                Msg3Content :: Default (v) => Msg3ContentSpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `msg3`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct Msg3 < 'i > {
        pub i : u8 ,
        pub content : Msg3Content < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct Msg3Spec {
        pub i : u8 ,
        pub content : Msg3ContentSpec ,
    }
    pub type Msg3Inner = (u8 , Msg3ContentSpec) ;
    impl < 'i > DeepView for Msg3 < 'i > {
        type V = Msg3Spec ;
        open spec fn deep_view (& self) -> Self :: V {
            Msg3Spec {
                i : self . i . deep_view () ,
                content : self . content . deep_view () ,
            }
        }
    }

    # [doc = "data type for `msg5`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct Msg5 < 'i > {
        pub i : u64 ,
        pub content : Msg5Content < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct Msg5Spec {
        pub i : u64 ,
        pub content : Msg5ContentSpec ,
    }
    pub type Msg5Inner = (u64 , Msg5ContentSpec) ;
    impl < 'i > DeepView for Msg5 < 'i > {
        type V = Msg5Spec ;
        open spec fn deep_view (& self) -> Self :: V {
            Msg5Spec {
                i : self . i . deep_view () ,
                content : self . content . deep_view () ,
            }
        }
    }

    # [doc = "data type for `msg2_content`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    # [verifier :: ext_equal]
    pub enum Msg2Content {
        Variant1 (u16) ,
        Default (u32) ,
    }
    pub type Msg2ContentSpec = Msg2Content ;
    pub type Msg2ContentInner = Sum < u16 , u32 > ;
    impl DeepView for Msg2Content {
        type V = Self ;
        open spec fn deep_view (& self) -> Self :: V {
            * self
        }
    }

    # [doc = "data type for `msg1`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct Msg1 < 'i > {
        pub b : & 'i [u8] ,
        pub payload : Msg1Payload ,
    }
    # [verifier :: ext_equal]
    pub struct Msg1Spec {
        pub b : Seq < u8 > ,
        pub payload : Msg1PayloadSpec ,
    }
    pub type Msg1Inner = (Seq < u8 > , Msg1PayloadSpec) ;
    impl < 'i > DeepView for Msg1 < 'i > {
        type V = Msg1Spec ;
        open spec fn deep_view (& self) -> Self :: V {
            Msg1Spec {
                b : self . b . deep_view () ,
                payload : self . payload . deep_view () ,
            }
        }
    }

    # [doc = "data type for `msg2`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct Msg2 < 'i > {
        pub b : & 'i [u8] ,
        pub content : Msg2Content ,
    }
    # [verifier :: ext_equal]
    pub struct Msg2Spec {
        pub b : Seq < u8 > ,
        pub content : Msg2ContentSpec ,
    }
    pub type Msg2Inner = (Seq < u8 > , Msg2ContentSpec) ;
    impl < 'i > DeepView for Msg2 < 'i > {
        type V = Msg2Spec ;
        open spec fn deep_view (& self) -> Self :: V {
            Msg2Spec {
                b : self . b . deep_view () ,
                content : self . content . deep_view () ,
            }
        }
    }

    # [doc = "data type for `msg4`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct Msg4 < 'i > {
        pub i : u32 ,
        pub content : Msg4Content < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct Msg4Spec {
        pub i : u32 ,
        pub content : Msg4ContentSpec ,
    }
    pub type Msg4Inner = (u32 , Msg4ContentSpec) ;
    impl < 'i > DeepView for Msg4 < 'i > {
        type V = Msg4Spec ;
        open spec fn deep_view (& self) -> Self :: V {
            Msg4Spec {
                i : self . i . deep_view () ,
                content : self . content . deep_view () ,
            }
        }
    }

    // ============================================================
    // Format Specifications
    // ============================================================
    # [doc = "named format combinator for `msg5_content`."]
    # [derive (Clone , Copy)]
    pub struct Msg5ContentFmt {
        i : u64 ,
    }
    impl Msg5ContentFmt {
        # [verifier :: type_invariant] spec fn wf (& self) -> bool {
            true
        }
        pub closed spec fn i_spec (& self) -> u64 {
            self . i . deep_view ()
        }
        pub closed spec fn spec (i : u64) -> Self {
            Msg5ContentFmt {
                i
            }
        }
    }

    pub type Msg5ContentFmtSpec = Named < Mapped < Sum < U16Le , Tail > , FnSpecMapper < Msg5ContentInner , Msg5ContentSpec >> > ;

    impl Msg5ContentFmt {
        # [doc = "specification constructor for `msg5_content`."] pub open spec fn spec_inner (i : u64) -> Msg5ContentFmtSpec {
            Named ("msg5_content" ,
            Mapped {
                inner : match i {
                    1 => L (U16Le) ,
                    _ => R (Tail) ,
                }
                ,
                mapper : (| parsed : Msg5ContentInner | -> Msg5ContentSpec {
                    match parsed {
                        L (v) => Msg5ContentSpec :: Variant1 (v) ,
                        R (v) => Msg5ContentSpec :: Default (v) ,
                    }
                }
                ,
                | value : Msg5ContentSpec | -> Msg5ContentInner {
                    match value {
                        Msg5ContentSpec :: Variant1 (v) => L (v) ,
                        Msg5ContentSpec :: Default (v) => R (v) ,
                    }
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `hello_retry_request`."]
    # [derive (Clone , Copy)]
    pub struct HelloRetryRequestFmt ;

    pub type HelloRetryRequestFmtSpec = Named < U16Le > ;

    impl HelloRetryRequestFmt {
        # [doc = "specification constructor for `hello_retry_request`."] pub open spec fn spec_inner () -> HelloRetryRequestFmtSpec {
            Named ("hello_retry_request" ,
            U16Le)
        }
    }


    # [doc = "named format combinator for `server_hello`."]
    # [derive (Clone , Copy)]
    pub struct ServerHelloFmt ;

    pub type ServerHelloFmtSpec = Named < U32Le > ;

    impl ServerHelloFmt {
        # [doc = "specification constructor for `server_hello`."] pub open spec fn spec_inner () -> ServerHelloFmtSpec {
            Named ("server_hello" ,
            U32Le)
        }
    }


    # [doc = "named format combinator for `msg1_payload`."]
    # [derive (Clone , Copy)]
    pub struct Msg1PayloadFmt < 'i > {
        b : & 'i [u8] ,
    }
    impl < 'i > Msg1PayloadFmt < 'i > {
        # [verifier :: type_invariant] spec fn wf (& self) -> bool {
            true
        }
        pub closed spec fn b_spec (& self) -> Seq < u8 > {
            self . b . deep_view ()
        }
        pub closed spec fn spec (b : & 'i [u8]) -> Self {
            Msg1PayloadFmt {
                b
            }
        }
    }

    pub type Msg1PayloadFmtSpec = Named < Mapped < Sum < HelloRetryRequestFmt , ServerHelloFmt > , FnSpecMapper < Msg1PayloadInner , Msg1PayloadSpec >> > ;

    impl < 'i > Msg1PayloadFmt < 'i > {
        # [doc = "specification constructor for `msg1_payload`."] pub open spec fn spec_inner (b : Seq < u8 >) -> Msg1PayloadFmtSpec {
            Named ("msg1_payload" ,
            Mapped {
                inner : match b {
                    x if x == [0xcfu8 , 0x21u8 , 0xadu8 , 0x74u8 , 0xe5u8 , 0x9au8 , 0x61u8 , 0x11u8 , 0xbeu8 , 0x1du8 , 0x8cu8 , 0x02u8 , 0x1eu8 , 0x65u8 , 0xb8u8 , 0x91u8 , 0xc2u8 , 0xa2u8 , 0x11u8 , 0x16u8 , 0x7au8 , 0xbbu8 , 0x8cu8 , 0x5eu8 , 0x07u8 , 0x9eu8 , 0x09u8 , 0xe2u8 , 0xc8u8 , 0xa8u8 , 0x33u8 , 0x9cu8] . deep_view () => L (HelloRetryRequestFmt) ,
                    _ => R (ServerHelloFmt) ,
                }
                ,
                mapper : (| parsed : Msg1PayloadInner | -> Msg1PayloadSpec {
                    match parsed {
                        L (v) => Msg1PayloadSpec :: Variant1 (v) ,
                        R (v) => Msg1PayloadSpec :: Default (v) ,
                    }
                }
                ,
                | value : Msg1PayloadSpec | -> Msg1PayloadInner {
                    match value {
                        Msg1PayloadSpec :: Variant1 (v) => L (v) ,
                        Msg1PayloadSpec :: Default (v) => R (v) ,
                    }
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg4_content`."]
    # [derive (Clone , Copy)]
    pub struct Msg4ContentFmt {
        i : u32 ,
    }
    impl Msg4ContentFmt {
        # [verifier :: type_invariant] spec fn wf (& self) -> bool {
            true
        }
        pub closed spec fn i_spec (& self) -> u32 {
            self . i . deep_view ()
        }
        pub closed spec fn spec (i : u32) -> Self {
            Msg4ContentFmt {
                i
            }
        }
    }

    pub type Msg4ContentFmtSpec = Named < Mapped < Sum < U16Le , Tail > , FnSpecMapper < Msg4ContentInner , Msg4ContentSpec >> > ;

    impl Msg4ContentFmt {
        # [doc = "specification constructor for `msg4_content`."] pub open spec fn spec_inner (i : u32) -> Msg4ContentFmtSpec {
            Named ("msg4_content" ,
            Mapped {
                inner : match i {
                    1 => L (U16Le) ,
                    _ => R (Tail) ,
                }
                ,
                mapper : (| parsed : Msg4ContentInner | -> Msg4ContentSpec {
                    match parsed {
                        L (v) => Msg4ContentSpec :: Variant1 (v) ,
                        R (v) => Msg4ContentSpec :: Default (v) ,
                    }
                }
                ,
                | value : Msg4ContentSpec | -> Msg4ContentInner {
                    match value {
                        Msg4ContentSpec :: Variant1 (v) => L (v) ,
                        Msg4ContentSpec :: Default (v) => R (v) ,
                    }
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg3_content`."]
    # [derive (Clone , Copy)]
    pub struct Msg3ContentFmt {
        i : u8 ,
    }
    impl Msg3ContentFmt {
        # [verifier :: type_invariant] spec fn wf (& self) -> bool {
            true
        }
        pub closed spec fn i_spec (& self) -> u8 {
            self . i . deep_view ()
        }
        pub closed spec fn spec (i : u8) -> Self {
            Msg3ContentFmt {
                i
            }
        }
    }

    pub type Msg3ContentFmtSpec = Named < Mapped < Sum < U16Le , Sum < U32Le , Sum < U32Le , Tail > > > , FnSpecMapper < Msg3ContentInner , Msg3ContentSpec >> > ;

    impl Msg3ContentFmt {
        # [doc = "specification constructor for `msg3_content`."] pub open spec fn spec_inner (i : u8) -> Msg3ContentFmtSpec {
            Named ("msg3_content" ,
            Mapped {
                inner : match i {
                    1 => L (U16Le) ,
                    2 => R (L (U32Le)) ,
                    3 => R (R (L (U32Le))) ,
                    _ => R (R (R (Tail))) ,
                }
                ,
                mapper : (| parsed : Msg3ContentInner | -> Msg3ContentSpec {
                    match parsed {
                        L (v) => Msg3ContentSpec :: Variant1 (v) ,
                        R (L (v)) => Msg3ContentSpec :: Variant2 (v) ,
                        R (R (L (v))) => Msg3ContentSpec :: Variant3 (v) ,
                        R (R (R (v))) => Msg3ContentSpec :: Default (v) ,
                    }
                }
                ,
                | value : Msg3ContentSpec | -> Msg3ContentInner {
                    match value {
                        Msg3ContentSpec :: Variant1 (v) => L (v) ,
                        Msg3ContentSpec :: Variant2 (v) => R (L (v)) ,
                        Msg3ContentSpec :: Variant3 (v) => R (R (L (v))) ,
                        Msg3ContentSpec :: Default (v) => R (R (R (v))) ,
                    }
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg3`."]
    # [derive (Clone , Copy)]
    pub struct Msg3Fmt ;

    pub type Msg3FmtSpec = Named < Mapped < Bind < U8 , spec_fn (u8) -> Msg3ContentFmt > , FnSpecMapper < Msg3Inner , Msg3Spec >> > ;

    impl Msg3Fmt {
        # [doc = "specification constructor for `msg3`."] pub open spec fn spec_inner () -> Msg3FmtSpec {
            Named ("msg3" ,
            Mapped {
                inner : Bind (U8 ,
                | i : u8 | Msg3ContentFmt :: spec (i)) ,
                mapper : (| parsed : Msg3Inner | -> Msg3Spec {
                    let (i ,
                    content) = parsed ;
                    Msg3Spec {
                        i ,
                        content
                    }
                }
                ,
                | value : Msg3Spec | -> Msg3Inner {
                    let Msg3Spec {
                        i ,
                        content
                    }
                    = value ;
                    (i ,
                    content)
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg5`."]
    # [derive (Clone , Copy)]
    pub struct Msg5Fmt ;

    pub type Msg5FmtSpec = Named < Mapped < Bind < VarInt < true > , spec_fn (u64) -> Msg5ContentFmt > , FnSpecMapper < Msg5Inner , Msg5Spec >> > ;

    impl Msg5Fmt {
        # [doc = "specification constructor for `msg5`."] pub open spec fn spec_inner () -> Msg5FmtSpec {
            Named ("msg5" ,
            Mapped {
                inner : Bind (VarInt :: < true > ,
                | i : u64 | Msg5ContentFmt :: spec (i)) ,
                mapper : (| parsed : Msg5Inner | -> Msg5Spec {
                    let (i ,
                    content) = parsed ;
                    Msg5Spec {
                        i ,
                        content
                    }
                }
                ,
                | value : Msg5Spec | -> Msg5Inner {
                    let Msg5Spec {
                        i ,
                        content
                    }
                    = value ;
                    (i ,
                    content)
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg2_content`."]
    # [derive (Clone , Copy)]
    pub struct Msg2ContentFmt < 'i > {
        b : & 'i [u8] ,
    }
    impl < 'i > Msg2ContentFmt < 'i > {
        # [verifier :: type_invariant] spec fn wf (& self) -> bool {
            true
        }
        pub closed spec fn b_spec (& self) -> Seq < u8 > {
            self . b . deep_view ()
        }
        pub closed spec fn spec (b : & 'i [u8]) -> Self {
            Msg2ContentFmt {
                b
            }
        }
    }

    pub type Msg2ContentFmtSpec = Named < Mapped < Sum < U16Le , U32Le > , FnSpecMapper < Msg2ContentInner , Msg2ContentSpec >> > ;

    impl < 'i > Msg2ContentFmt < 'i > {
        # [doc = "specification constructor for `msg2_content`."] pub open spec fn spec_inner (b : Seq < u8 >) -> Msg2ContentFmtSpec {
            Named ("msg2_content" ,
            Mapped {
                inner : match b {
                    x if x == [0x16u8 , 0x03u8 , 0x01u8] . deep_view () => L (U16Le) ,
                    _ => R (U32Le) ,
                }
                ,
                mapper : (| parsed : Msg2ContentInner | -> Msg2ContentSpec {
                    match parsed {
                        L (v) => Msg2ContentSpec :: Variant1 (v) ,
                        R (v) => Msg2ContentSpec :: Default (v) ,
                    }
                }
                ,
                | value : Msg2ContentSpec | -> Msg2ContentInner {
                    match value {
                        Msg2ContentSpec :: Variant1 (v) => L (v) ,
                        Msg2ContentSpec :: Default (v) => R (v) ,
                    }
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg1`."]
    # [derive (Clone , Copy)]
    pub struct Msg1Fmt ;

    pub type Msg1FmtSpec = Named < Mapped < Bind < Fixed < 32 > , spec_fn (Seq < u8 >) -> Msg1PayloadFmtSpec > , FnSpecMapper < Msg1Inner , Msg1Spec >> > ;

    impl Msg1Fmt {
        # [doc = "specification constructor for `msg1`."] pub open spec fn spec_inner () -> Msg1FmtSpec {
            Named ("msg1" ,
            Mapped {
                inner : Bind (Fixed :: < 32 > ,
                | b : Seq < u8 > | Msg1PayloadFmt :: spec_inner (b)) ,
                mapper : (| parsed : Msg1Inner | -> Msg1Spec {
                    let (b ,
                    payload) = parsed ;
                    Msg1Spec {
                        b ,
                        payload
                    }
                }
                ,
                | value : Msg1Spec | -> Msg1Inner {
                    let Msg1Spec {
                        b ,
                        payload
                    }
                    = value ;
                    (b ,
                    payload)
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg2`."]
    # [derive (Clone , Copy)]
    pub struct Msg2Fmt ;

    pub type Msg2FmtSpec = Named < Mapped < Bind < Fixed < 3 > , spec_fn (Seq < u8 >) -> Msg2ContentFmtSpec > , FnSpecMapper < Msg2Inner , Msg2Spec >> > ;

    impl Msg2Fmt {
        # [doc = "specification constructor for `msg2`."] pub open spec fn spec_inner () -> Msg2FmtSpec {
            Named ("msg2" ,
            Mapped {
                inner : Bind (Fixed :: < 3 > ,
                | b : Seq < u8 > | Msg2ContentFmt :: spec_inner (b)) ,
                mapper : (| parsed : Msg2Inner | -> Msg2Spec {
                    let (b ,
                    content) = parsed ;
                    Msg2Spec {
                        b ,
                        content
                    }
                }
                ,
                | value : Msg2Spec | -> Msg2Inner {
                    let Msg2Spec {
                        b ,
                        content
                    }
                    = value ;
                    (b ,
                    content)
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg4`."]
    # [derive (Clone , Copy)]
    pub struct Msg4Fmt ;

    pub type Msg4FmtSpec = Named < Mapped < Bind < U24Le , spec_fn (u32) -> Msg4ContentFmt > , FnSpecMapper < Msg4Inner , Msg4Spec >> > ;

    impl Msg4Fmt {
        # [doc = "specification constructor for `msg4`."] pub open spec fn spec_inner () -> Msg4FmtSpec {
            Named ("msg4" ,
            Mapped {
                inner : Bind (U24Le ,
                | i : u32 | Msg4ContentFmt :: spec (i)) ,
                mapper : (| parsed : Msg4Inner | -> Msg4Spec {
                    let (i ,
                    content) = parsed ;
                    Msg4Spec {
                        i ,
                        content
                    }
                }
                ,
                | value : Msg4Spec | -> Msg4Inner {
                    let Msg4Spec {
                        i ,
                        content
                    }
                    = value ;
                    (i ,
                    content)
                }
                )
            }
            )
        }
    }

    // ============================================================
    // Derived Parser, Serializer, Length, and Consistency Specifications
    // ============================================================
    mod derived_specs {
        use super::*;

        impl SpecParser for Msg5ContentFmt {
            type PVal = Msg5ContentSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg5ContentFmt :: spec_inner (self . i_spec ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for Msg5ContentFmt {
            type Val = Msg5ContentSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg5ContentFmt :: spec_inner (self . i_spec ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for Msg5ContentFmt {
            type SValue = Msg5ContentSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg5ContentFmt :: spec_inner (self . i_spec ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Msg5ContentFmt {
            type SVal = Msg5ContentSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg5ContentFmt :: spec_inner (self . i_spec ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for Msg5ContentFmt {
            type T = Msg5ContentSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg5ContentFmt :: spec_inner (self . i_spec ()) . byte_len (v)
            }
        }

        impl SpecParser for HelloRetryRequestFmt {
            type PVal = HelloRetryRequestSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                HelloRetryRequestFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for HelloRetryRequestFmt {
            type Val = HelloRetryRequestSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                HelloRetryRequestFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for HelloRetryRequestFmt {
            type SValue = HelloRetryRequestSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                HelloRetryRequestFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for HelloRetryRequestFmt {
            type SVal = HelloRetryRequestSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                HelloRetryRequestFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for HelloRetryRequestFmt {
            type T = HelloRetryRequestSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                HelloRetryRequestFmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for ServerHelloFmt {
            type PVal = ServerHelloSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                ServerHelloFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for ServerHelloFmt {
            type Val = ServerHelloSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                ServerHelloFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for ServerHelloFmt {
            type SValue = ServerHelloSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                ServerHelloFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for ServerHelloFmt {
            type SVal = ServerHelloSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                ServerHelloFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for ServerHelloFmt {
            type T = ServerHelloSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                ServerHelloFmt :: spec_inner () . byte_len (v)
            }
        }

        impl < 'i > SpecParser for Msg1PayloadFmt < 'i > {
            type PVal = Msg1PayloadSpec ;
            open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg1PayloadFmt :: spec_inner (self . b_spec ()) . spec_parse (ibuf)
            }
        }
        impl < 'i > Consistency for Msg1PayloadFmt < 'i > {
            type Val = Msg1PayloadSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg1PayloadFmt :: spec_inner (self . b_spec ()) . consistent (v)
            }
        }
        impl < 'i > SpecSerializerDps for Msg1PayloadFmt < 'i > {
            type SValue = Msg1PayloadSpec ;
            open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg1PayloadFmt :: spec_inner (self . b_spec ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl < 'i > SpecSerializer for Msg1PayloadFmt < 'i > {
            type SVal = Msg1PayloadSpec ;
            open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg1PayloadFmt :: spec_inner (self . b_spec ()) . spec_serialize (v)
            }
        }
        impl < 'i > SpecByteLen for Msg1PayloadFmt < 'i > {
            type T = Msg1PayloadSpec ;
            open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg1PayloadFmt :: spec_inner (self . b_spec ()) . byte_len (v)
            }
        }

        impl SpecParser for Msg4ContentFmt {
            type PVal = Msg4ContentSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg4ContentFmt :: spec_inner (self . i_spec ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for Msg4ContentFmt {
            type Val = Msg4ContentSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg4ContentFmt :: spec_inner (self . i_spec ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for Msg4ContentFmt {
            type SValue = Msg4ContentSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg4ContentFmt :: spec_inner (self . i_spec ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Msg4ContentFmt {
            type SVal = Msg4ContentSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg4ContentFmt :: spec_inner (self . i_spec ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for Msg4ContentFmt {
            type T = Msg4ContentSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg4ContentFmt :: spec_inner (self . i_spec ()) . byte_len (v)
            }
        }

        impl SpecParser for Msg3ContentFmt {
            type PVal = Msg3ContentSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg3ContentFmt :: spec_inner (self . i_spec ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for Msg3ContentFmt {
            type Val = Msg3ContentSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg3ContentFmt :: spec_inner (self . i_spec ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for Msg3ContentFmt {
            type SValue = Msg3ContentSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg3ContentFmt :: spec_inner (self . i_spec ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Msg3ContentFmt {
            type SVal = Msg3ContentSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg3ContentFmt :: spec_inner (self . i_spec ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for Msg3ContentFmt {
            type T = Msg3ContentSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg3ContentFmt :: spec_inner (self . i_spec ()) . byte_len (v)
            }
        }

        impl SpecParser for Msg3Fmt {
            type PVal = Msg3Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg3Fmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for Msg3Fmt {
            type Val = Msg3Spec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg3Fmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for Msg3Fmt {
            type SValue = Msg3Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg3Fmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Msg3Fmt {
            type SVal = Msg3Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg3Fmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for Msg3Fmt {
            type T = Msg3Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg3Fmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for Msg5Fmt {
            type PVal = Msg5Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg5Fmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for Msg5Fmt {
            type Val = Msg5Spec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg5Fmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for Msg5Fmt {
            type SValue = Msg5Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg5Fmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Msg5Fmt {
            type SVal = Msg5Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg5Fmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for Msg5Fmt {
            type T = Msg5Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg5Fmt :: spec_inner () . byte_len (v)
            }
        }

        impl < 'i > SpecParser for Msg2ContentFmt < 'i > {
            type PVal = Msg2ContentSpec ;
            open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg2ContentFmt :: spec_inner (self . b_spec ()) . spec_parse (ibuf)
            }
        }
        impl < 'i > Consistency for Msg2ContentFmt < 'i > {
            type Val = Msg2ContentSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg2ContentFmt :: spec_inner (self . b_spec ()) . consistent (v)
            }
        }
        impl < 'i > SpecSerializerDps for Msg2ContentFmt < 'i > {
            type SValue = Msg2ContentSpec ;
            open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg2ContentFmt :: spec_inner (self . b_spec ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl < 'i > SpecSerializer for Msg2ContentFmt < 'i > {
            type SVal = Msg2ContentSpec ;
            open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg2ContentFmt :: spec_inner (self . b_spec ()) . spec_serialize (v)
            }
        }
        impl < 'i > SpecByteLen for Msg2ContentFmt < 'i > {
            type T = Msg2ContentSpec ;
            open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg2ContentFmt :: spec_inner (self . b_spec ()) . byte_len (v)
            }
        }

        impl SpecParser for Msg1Fmt {
            type PVal = Msg1Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg1Fmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for Msg1Fmt {
            type Val = Msg1Spec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg1Fmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for Msg1Fmt {
            type SValue = Msg1Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg1Fmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Msg1Fmt {
            type SVal = Msg1Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg1Fmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for Msg1Fmt {
            type T = Msg1Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg1Fmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for Msg2Fmt {
            type PVal = Msg2Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg2Fmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for Msg2Fmt {
            type Val = Msg2Spec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg2Fmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for Msg2Fmt {
            type SValue = Msg2Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg2Fmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Msg2Fmt {
            type SVal = Msg2Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg2Fmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for Msg2Fmt {
            type T = Msg2Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg2Fmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for Msg4Fmt {
            type PVal = Msg4Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                Msg4Fmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for Msg4Fmt {
            type Val = Msg4Spec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                Msg4Fmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for Msg4Fmt {
            type SValue = Msg4Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                Msg4Fmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for Msg4Fmt {
            type SVal = Msg4Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                Msg4Fmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for Msg4Fmt {
            type T = Msg4Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                Msg4Fmt :: spec_inner () . byte_len (v)
            }
        }
    }

    // ============================================================
    // Proven Format Properties
    // ============================================================
    mod derived_proofs {
        use super::*;
        broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        impl SafeParser for Msg5ContentFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg5ContentFmt as SpecParser > :: spec_parse) ;
                Msg5ContentFmt :: spec_inner (self . i_spec ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Msg5ContentFmt {
            open spec fn productive_inv (& self) -> bool {
                Msg5ContentFmt :: spec_inner (self . i_spec ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg5ContentFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg5ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Msg5ContentFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg5ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg5ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg5ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg5ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg5ContentFmt as Consistency > :: consistent) ;
                let fmt = Msg5ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for Msg5ContentFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg5ContentFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg5ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg5ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Msg5ContentFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg5ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg5ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg5ContentFmt as Consistency > :: consistent) ;
                reveal (< Msg5ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg5ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Msg5ContentFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg5ContentFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg5ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for Msg5ContentFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg5ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg5ContentFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg5ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for HelloRetryRequestFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecParser > :: spec_parse) ;
                HelloRetryRequestFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for HelloRetryRequestFmt {
            open spec fn productive_inv (& self) -> bool {
                HelloRetryRequestFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecParser > :: spec_parse) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for HelloRetryRequestFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecParser > :: spec_parse) ;
                reveal (< HelloRetryRequestFmt as SpecByteLen > :: byte_len) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecParser > :: spec_parse) ;
                reveal (< HelloRetryRequestFmt as Consistency > :: consistent) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for HelloRetryRequestFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HelloRetryRequestFmt as SpecByteLen > :: byte_len) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for HelloRetryRequestFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< HelloRetryRequestFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< HelloRetryRequestFmt as SpecByteLen > :: byte_len) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for HelloRetryRequestFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecParser > :: spec_parse) ;
                reveal (< HelloRetryRequestFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HelloRetryRequestFmt as Consistency > :: consistent) ;
                reveal (< HelloRetryRequestFmt as SpecByteLen > :: byte_len) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for HelloRetryRequestFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecParser > :: spec_parse) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for HelloRetryRequestFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< HelloRetryRequestFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HelloRetryRequestFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for HelloRetryRequestFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< HelloRetryRequestFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HelloRetryRequestFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = HelloRetryRequestFmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for ServerHelloFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecParser > :: spec_parse) ;
                ServerHelloFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for ServerHelloFmt {
            open spec fn productive_inv (& self) -> bool {
                ServerHelloFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecParser > :: spec_parse) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for ServerHelloFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecParser > :: spec_parse) ;
                reveal (< ServerHelloFmt as SpecByteLen > :: byte_len) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecParser > :: spec_parse) ;
                reveal (< ServerHelloFmt as Consistency > :: consistent) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for ServerHelloFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ServerHelloFmt as SpecByteLen > :: byte_len) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for ServerHelloFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< ServerHelloFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< ServerHelloFmt as SpecByteLen > :: byte_len) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for ServerHelloFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecParser > :: spec_parse) ;
                reveal (< ServerHelloFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ServerHelloFmt as Consistency > :: consistent) ;
                reveal (< ServerHelloFmt as SpecByteLen > :: byte_len) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for ServerHelloFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecParser > :: spec_parse) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for ServerHelloFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< ServerHelloFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ServerHelloFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for ServerHelloFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< ServerHelloFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ServerHelloFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = ServerHelloFmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl < 'i > SafeParser for Msg1PayloadFmt < 'i > {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecParser > :: spec_parse) ;
                Msg1PayloadFmt :: spec_inner (self . b_spec ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl < 'i > Productive for Msg1PayloadFmt < 'i > {
            open spec fn productive_inv (& self) -> bool {
                Msg1PayloadFmt :: spec_inner (self . b_spec ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl < 'i > SoundParser for Msg1PayloadFmt < 'i > {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg1PayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg1PayloadFmt as Consistency > :: consistent) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl < 'i > NonTailFmt for Msg1PayloadFmt < 'i > {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg1PayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl < 'i > GoodSerializer for Msg1PayloadFmt < 'i > {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg1PayloadFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg1PayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl < 'i > SPRoundTripDps for Msg1PayloadFmt < 'i > {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg1PayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg1PayloadFmt as Consistency > :: consistent) ;
                reveal (< Msg1PayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl < 'i > NonMalleable for Msg1PayloadFmt < 'i > {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl < 'i > EquivSerializersGeneral for Msg1PayloadFmt < 'i > {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< Msg1PayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg1PayloadFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl < 'i > EquivSerializers for Msg1PayloadFmt < 'i > {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg1PayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg1PayloadFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg1PayloadFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for Msg4ContentFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg4ContentFmt as SpecParser > :: spec_parse) ;
                Msg4ContentFmt :: spec_inner (self . i_spec ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Msg4ContentFmt {
            open spec fn productive_inv (& self) -> bool {
                Msg4ContentFmt :: spec_inner (self . i_spec ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg4ContentFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg4ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Msg4ContentFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg4ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg4ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg4ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg4ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg4ContentFmt as Consistency > :: consistent) ;
                let fmt = Msg4ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for Msg4ContentFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg4ContentFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg4ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg4ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Msg4ContentFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg4ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg4ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg4ContentFmt as Consistency > :: consistent) ;
                reveal (< Msg4ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg4ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Msg4ContentFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg4ContentFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg4ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for Msg4ContentFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg4ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg4ContentFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg4ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for Msg3ContentFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg3ContentFmt as SpecParser > :: spec_parse) ;
                Msg3ContentFmt :: spec_inner (self . i_spec ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Msg3ContentFmt {
            open spec fn productive_inv (& self) -> bool {
                Msg3ContentFmt :: spec_inner (self . i_spec ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg3ContentFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg3ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Msg3ContentFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg3ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg3ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg3ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg3ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg3ContentFmt as Consistency > :: consistent) ;
                let fmt = Msg3ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for Msg3ContentFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg3ContentFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg3ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg3ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Msg3ContentFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg3ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg3ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg3ContentFmt as Consistency > :: consistent) ;
                reveal (< Msg3ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg3ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Msg3ContentFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg3ContentFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg3ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for Msg3ContentFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg3ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg3ContentFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg3ContentFmt :: spec_inner (self . i_spec ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for Msg3Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg3Fmt as SpecParser > :: spec_parse) ;
                Msg3Fmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Msg3Fmt {
            open spec fn productive_inv (& self) -> bool {
                Msg3Fmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg3Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg3Fmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Msg3Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg3Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg3Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg3Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg3Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg3Fmt as Consistency > :: consistent) ;
                let fmt = Msg3Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for Msg3Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg3Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg3Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg3Fmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Msg3Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg3Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg3Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg3Fmt as Consistency > :: consistent) ;
                reveal (< Msg3Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg3Fmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Msg3Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg3Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg3Fmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for Msg3Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg3Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg3Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg3Fmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for Msg5Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg5Fmt as SpecParser > :: spec_parse) ;
                Msg5Fmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Msg5Fmt {
            open spec fn productive_inv (& self) -> bool {
                Msg5Fmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg5Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg5Fmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Msg5Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg5Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg5Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg5Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg5Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg5Fmt as Consistency > :: consistent) ;
                let fmt = Msg5Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for Msg5Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg5Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg5Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg5Fmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Msg5Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg5Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg5Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg5Fmt as Consistency > :: consistent) ;
                reveal (< Msg5Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg5Fmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Msg5Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg5Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg5Fmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for Msg5Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg5Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg5Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg5Fmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl < 'i > SafeParser for Msg2ContentFmt < 'i > {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecParser > :: spec_parse) ;
                Msg2ContentFmt :: spec_inner (self . b_spec ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl < 'i > Productive for Msg2ContentFmt < 'i > {
            open spec fn productive_inv (& self) -> bool {
                Msg2ContentFmt :: spec_inner (self . b_spec ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl < 'i > SoundParser for Msg2ContentFmt < 'i > {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg2ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg2ContentFmt as Consistency > :: consistent) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl < 'i > NonTailFmt for Msg2ContentFmt < 'i > {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg2ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl < 'i > GoodSerializer for Msg2ContentFmt < 'i > {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg2ContentFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg2ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl < 'i > SPRoundTripDps for Msg2ContentFmt < 'i > {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecParser > :: spec_parse) ;
                reveal (< Msg2ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg2ContentFmt as Consistency > :: consistent) ;
                reveal (< Msg2ContentFmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl < 'i > NonMalleable for Msg2ContentFmt < 'i > {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecParser > :: spec_parse) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl < 'i > EquivSerializersGeneral for Msg2ContentFmt < 'i > {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< Msg2ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg2ContentFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl < 'i > EquivSerializers for Msg2ContentFmt < 'i > {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg2ContentFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg2ContentFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg2ContentFmt :: spec_inner (self . b_spec ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for Msg1Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecParser > :: spec_parse) ;
                Msg1Fmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Msg1Fmt {
            open spec fn productive_inv (& self) -> bool {
                Msg1Fmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Msg1Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg1Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg1Fmt as Consistency > :: consistent) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for Msg1Fmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg1Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for Msg1Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg1Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg1Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Msg1Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg1Fmt as Consistency > :: consistent) ;
                reveal (< Msg1Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Msg1Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for Msg1Fmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< Msg1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg1Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for Msg1Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg1Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg1Fmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for Msg2Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecParser > :: spec_parse) ;
                Msg2Fmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Msg2Fmt {
            open spec fn productive_inv (& self) -> bool {
                Msg2Fmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Msg2Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg2Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg2Fmt as Consistency > :: consistent) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for Msg2Fmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg2Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for Msg2Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg2Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg2Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Msg2Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg2Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg2Fmt as Consistency > :: consistent) ;
                reveal (< Msg2Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Msg2Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for Msg2Fmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< Msg2Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg2Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for Msg2Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg2Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg2Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg2Fmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for Msg4Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg4Fmt as SpecParser > :: spec_parse) ;
                Msg4Fmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for Msg4Fmt {
            open spec fn productive_inv (& self) -> bool {
                Msg4Fmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< Msg4Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg4Fmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for Msg4Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg4Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg4Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg4Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< Msg4Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg4Fmt as Consistency > :: consistent) ;
                let fmt = Msg4Fmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for Msg4Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< Msg4Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< Msg4Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg4Fmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for Msg4Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< Msg4Fmt as SpecParser > :: spec_parse) ;
                reveal (< Msg4Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg4Fmt as Consistency > :: consistent) ;
                reveal (< Msg4Fmt as SpecByteLen > :: byte_len) ;
                let fmt = Msg4Fmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for Msg4Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< Msg4Fmt as SpecParser > :: spec_parse) ;
                let fmt = Msg4Fmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for Msg4Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< Msg4Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< Msg4Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = Msg4Fmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }
    }

    // ============================================================
    // Executable Implementations
    // ============================================================
    mod exec_impls {
        use super::*;

        impl < 'i > Parser < & 'i [u8] > for Msg5ContentFmt {
            type PT = Msg5Content < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg5ContentFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                proof {
                    use_type_invariant(self);
                }

                let (n , v) = match self . i {
            1 => {
                let (n ,
                v) = (U16Le) . parse (& rest) ? ;
                (n ,
                Msg5Content :: Variant1 (v))
            }
            ,
            _ => {
                let (n ,
                v) = (Tail) . parse (& rest) ? ;
                (n ,
                Msg5Content :: Default (v))
            }
            ,
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for HelloRetryRequestFmt {
            type PT = HelloRetryRequest ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< HelloRetryRequestFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n , v) = (U16Le) . parse (ibuf) ? ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for ServerHelloFmt {
            type PT = ServerHello ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< ServerHelloFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n , v) = (U32Le) . parse (ibuf) ? ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg1PayloadFmt < 'i > {
            type PT = Msg1Payload ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg1PayloadFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                proof {
                    use_type_invariant(self);
                }

                let (n , v) = match self . b {
            x if x . deep_eq (& [0xcf , 0x21 , 0xad , 0x74 , 0xe5 , 0x9a , 0x61 , 0x11 , 0xbe , 0x1d , 0x8c , 0x02 , 0x1e , 0x65 , 0xb8 , 0x91 , 0xc2 , 0xa2 , 0x11 , 0x16 , 0x7a , 0xbb , 0x8c , 0x5e , 0x07 , 0x9e , 0x09 , 0xe2 , 0xc8 , 0xa8 , 0x33 , 0x9c]) => {
                let (n ,
                v) = (HelloRetryRequestFmt) . parse (& rest) ? ;
                (n ,
                Msg1Payload :: Variant1 (v))
            }
            ,
            _ => {
                let (n ,
                v) = (ServerHelloFmt) . parse (& rest) ? ;
                (n ,
                Msg1Payload :: Default (v))
            }
            ,
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg4ContentFmt {
            type PT = Msg4Content < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg4ContentFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                proof {
                    use_type_invariant(self);
                }

                let (n , v) = match self . i {
            1 => {
                let (n ,
                v) = (U16Le) . parse (& rest) ? ;
                (n ,
                Msg4Content :: Variant1 (v))
            }
            ,
            _ => {
                let (n ,
                v) = (Tail) . parse (& rest) ? ;
                (n ,
                Msg4Content :: Default (v))
            }
            ,
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg3ContentFmt {
            type PT = Msg3Content < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg3ContentFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                proof {
                    use_type_invariant(self);
                }

                let (n , v) = match self . i {
            1 => {
                let (n ,
                v) = (U16Le) . parse (& rest) ? ;
                (n ,
                Msg3Content :: Variant1 (v))
            }
            ,
            2 => {
                let (n ,
                v) = (U32Le) . parse (& rest) ? ;
                (n ,
                Msg3Content :: Variant2 (v))
            }
            ,
            3 => {
                let (n ,
                v) = (U32Le) . parse (& rest) ? ;
                (n ,
                Msg3Content :: Variant3 (v))
            }
            ,
            _ => {
                let (n ,
                v) = (Tail) . parse (& rest) ? ;
                (n ,
                Msg3Content :: Default (v))
            }
            ,
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg3Fmt {
            type PT = Msg3 < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg3Fmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n1 , i) = (U8) . parse (& rest) ? ;
                let rest = rest.skip(n1);
                let (n2 , content) = (Msg3ContentFmt {
            i : i
        }
        ) . parse (& rest) ? ;
                let rest = rest.skip(n2);
                let total_n = n1 + n2;
                let final_v = Msg3 {
            i ,
            content
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
                Ok((total_n, final_v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg5Fmt {
            type PT = Msg5 < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg5Fmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n1 , i) = (VarInt :: < true >) . parse (& rest) ? ;
                let rest = rest.skip(n1);
                let (n2 , content) = (Msg5ContentFmt {
            i : i
        }
        ) . parse (& rest) ? ;
                let rest = rest.skip(n2);
                let total_n = n1 + n2;
                let final_v = Msg5 {
            i ,
            content
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
                Ok((total_n, final_v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg2ContentFmt < 'i > {
            type PT = Msg2Content ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg2ContentFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                proof {
                    use_type_invariant(self);
                }

                let (n , v) = match self . b {
            x if x . deep_eq (& [0x16 , 0x03 , 0x01]) => {
                let (n ,
                v) = (U16Le) . parse (& rest) ? ;
                (n ,
                Msg2Content :: Variant1 (v))
            }
            ,
            _ => {
                let (n ,
                v) = (U32Le) . parse (& rest) ? ;
                (n ,
                Msg2Content :: Default (v))
            }
            ,
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg1Fmt {
            type PT = Msg1 < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg1Fmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n1 , b) = (Fixed :: < 32 >) . parse (& rest) ? ;
                let rest = rest.skip(n1);
                let (n2 , payload) = (Msg1PayloadFmt {
            b : b
        }
        ) . parse (& rest) ? ;
                let rest = rest.skip(n2);
                let total_n = n1 + n2;
                let final_v = Msg1 {
            b ,
            payload
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
                Ok((total_n, final_v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg2Fmt {
            type PT = Msg2 < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg2Fmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n1 , b) = (Fixed :: < 3 >) . parse (& rest) ? ;
                let rest = rest.skip(n1);
                let (n2 , content) = (Msg2ContentFmt {
            b : b
        }
        ) . parse (& rest) ? ;
                let rest = rest.skip(n2);
                let total_n = n1 + n2;
                let final_v = Msg2 {
            b ,
            content
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
                Ok((total_n, final_v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for Msg4Fmt {
            type PT = Msg4 < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< Msg4Fmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n1 , i) = (U24Le) . parse (& rest) ? ;
                let rest = rest.skip(n1);
                let (n2 , content) = (Msg4ContentFmt {
            i : i
        }
        ) . parse (& rest) ? ;
                let rest = rest.skip(n2);
                let total_n = n1 + n2;
                let final_v = Msg4 {
            i ,
            content
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
                Ok((total_n, final_v))
            }
        }

    }
}

