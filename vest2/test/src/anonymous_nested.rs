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
    # [doc = "data type for `capture_param_and_local_x_a_payload`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum CaptureParamAndLocalXAPayload < 'i > {
        C (& 'i [u8]) ,
        D (& 'i [u8]) ,
    }
    # [verifier :: ext_equal]
    pub enum CaptureParamAndLocalXAPayloadSpec {
        C (Seq < u8 >) ,
        D (Seq < u8 >) ,
    }
    pub type CaptureParamAndLocalXAPayloadInner = Sum < Seq < u8 > , Seq < u8 > > ;
    impl < 'i > DeepView for CaptureParamAndLocalXAPayload < 'i > {
        type V = CaptureParamAndLocalXAPayloadSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                CaptureParamAndLocalXAPayload :: C (v) => CaptureParamAndLocalXAPayloadSpec :: C (v . deep_view ()) ,
                CaptureParamAndLocalXAPayload :: D (v) => CaptureParamAndLocalXAPayloadSpec :: D (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `capture_param_and_local_x_a`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct CaptureParamAndLocalXA < 'i > {
        pub len : u8 ,
        pub payload : CaptureParamAndLocalXAPayload < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct CaptureParamAndLocalXASpec {
        pub len : u8 ,
        pub payload : CaptureParamAndLocalXAPayloadSpec ,
    }
    pub type CaptureParamAndLocalXAInner = (u8 , CaptureParamAndLocalXAPayloadSpec) ;
    impl < 'i > DeepView for CaptureParamAndLocalXA < 'i > {
        type V = CaptureParamAndLocalXASpec ;
        open spec fn deep_view (& self) -> Self :: V {
            CaptureParamAndLocalXASpec {
                len : self . len . deep_view () ,
                payload : self . payload . deep_view () ,
            }
        }
    }

    # [doc = "data type for `capture_param_and_local_x_b_y`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum CaptureParamAndLocalXBY {
        Variant1 (u8) ,
        Default (u16) ,
    }
    # [verifier :: ext_equal]
    pub enum CaptureParamAndLocalXBYSpec {
        Variant1 (u8) ,
        Default (u16) ,
    }
    pub type CaptureParamAndLocalXBYInner = Sum < u8 , u16 > ;
    impl DeepView for CaptureParamAndLocalXBY {
        type V = CaptureParamAndLocalXBYSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                CaptureParamAndLocalXBY :: Variant1 (v) => CaptureParamAndLocalXBYSpec :: Variant1 (v . deep_view ()) ,
                CaptureParamAndLocalXBY :: Default (v) => CaptureParamAndLocalXBYSpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `capture_param_and_local_x_b`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct CaptureParamAndLocalXB {
        pub tag : u8 ,
        pub y : CaptureParamAndLocalXBY ,
    }
    # [verifier :: ext_equal]
    pub struct CaptureParamAndLocalXBSpec {
        pub tag : u8 ,
        pub y : CaptureParamAndLocalXBYSpec ,
    }
    pub type CaptureParamAndLocalXBInner = (u8 , CaptureParamAndLocalXBYSpec) ;
    impl DeepView for CaptureParamAndLocalXB {
        type V = CaptureParamAndLocalXBSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            CaptureParamAndLocalXBSpec {
                tag : self . tag . deep_view () ,
                y : self . y . deep_view () ,
            }
        }
    }

    # [doc = "data type for `capture_param_and_local_x`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum CaptureParamAndLocalX < 'i > {
        A (CaptureParamAndLocalXA < 'i >) ,
        B (CaptureParamAndLocalXB) ,
    }
    # [verifier :: ext_equal]
    pub enum CaptureParamAndLocalXSpec {
        A (CaptureParamAndLocalXASpec) ,
        B (CaptureParamAndLocalXBSpec) ,
    }
    pub type CaptureParamAndLocalXInner = Sum < CaptureParamAndLocalXASpec , CaptureParamAndLocalXBSpec > ;
    impl < 'i > DeepView for CaptureParamAndLocalX < 'i > {
        type V = CaptureParamAndLocalXSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                CaptureParamAndLocalX :: A (v) => CaptureParamAndLocalXSpec :: A (v . deep_view ()) ,
                CaptureParamAndLocalX :: B (v) => CaptureParamAndLocalXSpec :: B (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `nested_inner_choice_x_a`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum NestedInnerChoiceXA {
        C (u8) ,
        D (u16) ,
    }
    # [verifier :: ext_equal]
    pub enum NestedInnerChoiceXASpec {
        C (u8) ,
        D (u16) ,
    }
    pub type NestedInnerChoiceXAInner = Sum < u8 , u16 > ;
    impl DeepView for NestedInnerChoiceXA {
        type V = NestedInnerChoiceXASpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                NestedInnerChoiceXA :: C (v) => NestedInnerChoiceXASpec :: C (v . deep_view ()) ,
                NestedInnerChoiceXA :: D (v) => NestedInnerChoiceXASpec :: D (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `capture_outer_and_local_payload_anon_inner_body_choice1`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct CaptureOuterAndLocalPayloadAnonInnerBodyChoice1 < 'i > {
        pub count : u8 ,
        pub items : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec {
        pub count : u8 ,
        pub items : Seq < u8 > ,
    }
    pub type CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner = (u8 , Seq < u8 >) ;
    impl < 'i > DeepView for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1 < 'i > {
        type V = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec ;
        open spec fn deep_view (& self) -> Self :: V {
            CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec {
                count : self . count . deep_view () ,
                items : self . items . deep_view () ,
            }
        }
    }

    # [doc = "data type for `capture_outer_and_local_payload_anon_inner_body`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum CaptureOuterAndLocalPayloadAnonInnerBody < 'i > {
        Variant1 (& 'i [u8]) ,
        Default (CaptureOuterAndLocalPayloadAnonInnerBodyChoice1 < 'i >) ,
    }
    # [verifier :: ext_equal]
    pub enum CaptureOuterAndLocalPayloadAnonInnerBodySpec {
        Variant1 (Seq < u8 >) ,
        Default (CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec) ,
    }
    pub type CaptureOuterAndLocalPayloadAnonInnerBodyInner = Sum < Seq < u8 > , CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec > ;
    impl < 'i > DeepView for CaptureOuterAndLocalPayloadAnonInnerBody < 'i > {
        type V = CaptureOuterAndLocalPayloadAnonInnerBodySpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                CaptureOuterAndLocalPayloadAnonInnerBody :: Variant1 (v) => CaptureOuterAndLocalPayloadAnonInnerBodySpec :: Variant1 (v . deep_view ()) ,
                CaptureOuterAndLocalPayloadAnonInnerBody :: Default (v) => CaptureOuterAndLocalPayloadAnonInnerBodySpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `capture_outer_and_local_payload`."]
    pub type CaptureOuterAndLocalPayload < 'i > = (u8 , CaptureOuterAndLocalPayloadAnonInnerBody < 'i >) ;
    pub type CaptureOuterAndLocalPayloadSpec = (u8 , CaptureOuterAndLocalPayloadAnonInnerBodySpec) ;


    # [doc = "data type for `capture_outer_and_local`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct CaptureOuterAndLocal < 'i > {
        pub frame_len : u8 ,
        pub payload : CaptureOuterAndLocalPayload < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct CaptureOuterAndLocalSpec {
        pub frame_len : u8 ,
        pub payload : CaptureOuterAndLocalPayloadSpec ,
    }
    pub type CaptureOuterAndLocalInner = (u8 , CaptureOuterAndLocalPayloadSpec) ;
    impl < 'i > DeepView for CaptureOuterAndLocal < 'i > {
        type V = CaptureOuterAndLocalSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            CaptureOuterAndLocalSpec {
                frame_len : self . frame_len . deep_view () ,
                payload : self . payload . deep_view () ,
            }
        }
    }

    # [doc = "data type for `nested_inner_struct_anon_inner`."]
    pub type NestedInnerStructAnonInner < 'i > = (u8 , & 'i [u8]) ;
    pub type NestedInnerStructAnonInnerSpec = (u8 , Seq < u8 >) ;


    # [doc = "data type for `capture_local_in_anon_struct_wrapper_value_choice0`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct CaptureLocalInAnonStructWrapperValueChoice0 < 'i > {
        pub len : u8 ,
        pub bytes : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct CaptureLocalInAnonStructWrapperValueChoice0Spec {
        pub len : u8 ,
        pub bytes : Seq < u8 > ,
    }
    pub type CaptureLocalInAnonStructWrapperValueChoice0Inner = (u8 , Seq < u8 >) ;
    impl < 'i > DeepView for CaptureLocalInAnonStructWrapperValueChoice0 < 'i > {
        type V = CaptureLocalInAnonStructWrapperValueChoice0Spec ;
        open spec fn deep_view (& self) -> Self :: V {
            CaptureLocalInAnonStructWrapperValueChoice0Spec {
                len : self . len . deep_view () ,
                bytes : self . bytes . deep_view () ,
            }
        }
    }

    # [doc = "data type for `capture_local_in_anon_struct_wrapper_value`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum CaptureLocalInAnonStructWrapperValue < 'i > {
        Variant1 (CaptureLocalInAnonStructWrapperValueChoice0 < 'i >) ,
        Default (u16) ,
    }
    # [verifier :: ext_equal]
    pub enum CaptureLocalInAnonStructWrapperValueSpec {
        Variant1 (CaptureLocalInAnonStructWrapperValueChoice0Spec) ,
        Default (u16) ,
    }
    pub type CaptureLocalInAnonStructWrapperValueInner = Sum < CaptureLocalInAnonStructWrapperValueChoice0Spec , u16 > ;
    impl < 'i > DeepView for CaptureLocalInAnonStructWrapperValue < 'i > {
        type V = CaptureLocalInAnonStructWrapperValueSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                CaptureLocalInAnonStructWrapperValue :: Variant1 (v) => CaptureLocalInAnonStructWrapperValueSpec :: Variant1 (v . deep_view ()) ,
                CaptureLocalInAnonStructWrapperValue :: Default (v) => CaptureLocalInAnonStructWrapperValueSpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `nested_inner_choice_x`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum NestedInnerChoiceX {
        A (NestedInnerChoiceXA) ,
        B (u32) ,
    }
    # [verifier :: ext_equal]
    pub enum NestedInnerChoiceXSpec {
        A (NestedInnerChoiceXASpec) ,
        B (u32) ,
    }
    pub type NestedInnerChoiceXInner = Sum < NestedInnerChoiceXASpec , u32 > ;
    impl DeepView for NestedInnerChoiceX {
        type V = NestedInnerChoiceXSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                NestedInnerChoiceX :: A (v) => NestedInnerChoiceXSpec :: A (v . deep_view ()) ,
                NestedInnerChoiceX :: B (v) => NestedInnerChoiceXSpec :: B (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `nested_inner_choice`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct NestedInnerChoice {
        pub x : NestedInnerChoiceX ,
    }
    # [verifier :: ext_equal]
    pub struct NestedInnerChoiceSpec {
        pub x : NestedInnerChoiceXSpec ,
    }
    pub type NestedInnerChoiceInner = NestedInnerChoiceXSpec ;
    impl DeepView for NestedInnerChoice {
        type V = NestedInnerChoiceSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            NestedInnerChoiceSpec {
                x : self . x . deep_view () ,
            }
        }
    }

    # [doc = "data type for `capture_param_and_local`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct CaptureParamAndLocal < 'i > {
        pub x : CaptureParamAndLocalX < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct CaptureParamAndLocalSpec {
        pub x : CaptureParamAndLocalXSpec ,
    }
    pub type CaptureParamAndLocalInner = CaptureParamAndLocalXSpec ;
    impl < 'i > DeepView for CaptureParamAndLocal < 'i > {
        type V = CaptureParamAndLocalSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            CaptureParamAndLocalSpec {
                x : self . x . deep_view () ,
            }
        }
    }

    # [doc = "data type for `nested_inner_struct`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct NestedInnerStruct < 'i > {
        pub len : u32 ,
        pub inner : NestedInnerStructAnonInner < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct NestedInnerStructSpec {
        pub len : u32 ,
        pub inner : NestedInnerStructAnonInnerSpec ,
    }
    pub type NestedInnerStructInner = (u32 , NestedInnerStructAnonInnerSpec) ;
    impl < 'i > DeepView for NestedInnerStruct < 'i > {
        type V = NestedInnerStructSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            NestedInnerStructSpec {
                len : self . len . deep_view () ,
                inner : self . inner . deep_view () ,
            }
        }
    }

    # [doc = "data type for `c_or_d`."]
    # [repr (u8)]
    # [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
    pub enum COrD {
        C = 1 ,
        D = 2 ,
    }
    pub type COrDSpec = COrD ;
    pub type COrDInner = u8 ;
    impl DeepView for COrD {
        type V = COrDSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match * self {
                COrD :: C => COrDSpec :: C ,
                COrD :: D => COrDSpec :: D ,
            }
        }
    }

    # [doc = "data type for `capture_local_in_anon_struct_wrapper`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct CaptureLocalInAnonStructWrapper < 'i > {
        pub tag : u8 ,
        pub value : CaptureLocalInAnonStructWrapperValue < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct CaptureLocalInAnonStructWrapperSpec {
        pub tag : u8 ,
        pub value : CaptureLocalInAnonStructWrapperValueSpec ,
    }
    pub type CaptureLocalInAnonStructWrapperInner = (u8 , CaptureLocalInAnonStructWrapperValueSpec) ;
    impl < 'i > DeepView for CaptureLocalInAnonStructWrapper < 'i > {
        type V = CaptureLocalInAnonStructWrapperSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            CaptureLocalInAnonStructWrapperSpec {
                tag : self . tag . deep_view () ,
                value : self . value . deep_view () ,
            }
        }
    }

    # [doc = "data type for `capture_local_in_anon_struct`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct CaptureLocalInAnonStruct < 'i > {
        pub wrapper : CaptureLocalInAnonStructWrapper < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct CaptureLocalInAnonStructSpec {
        pub wrapper : CaptureLocalInAnonStructWrapperSpec ,
    }
    pub type CaptureLocalInAnonStructInner = CaptureLocalInAnonStructWrapperSpec ;
    impl < 'i > DeepView for CaptureLocalInAnonStruct < 'i > {
        type V = CaptureLocalInAnonStructSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            CaptureLocalInAnonStructSpec {
                wrapper : self . wrapper . deep_view () ,
            }
        }
    }

    # [doc = "data type for `a_or_b`."]
    # [repr (u8)]
    # [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
    pub enum AOrB {
        A = 1 ,
        B = 2 ,
    }
    pub type AOrBSpec = AOrB ;
    pub type AOrBInner = u8 ;
    impl DeepView for AOrB {
        type V = AOrBSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match * self {
                AOrB :: A => AOrBSpec :: A ,
                AOrB :: B => AOrBSpec :: B ,
            }
        }
    }

    // ============================================================
    // Format Specifications
    // ============================================================
    # [doc = "named format combinator for `capture_param_and_local_x_a_payload`."]
    pub struct CaptureParamAndLocalXAPayloadFmt {
        pub choice2 : COrD ,
        pub len : u8 ,
    }

    pub type CaptureParamAndLocalXAPayloadFmtSpec = Named < Mapped < Sum < Varied < usize > , Varied < usize > > , FnSpecMapper < CaptureParamAndLocalXAPayloadInner , CaptureParamAndLocalXAPayloadSpec >> > ;

    # [doc = "specification constructor for `capture_param_and_local_x_a_payload`."]
    pub open spec fn capture_param_and_local_x_a_payload_fmt (choice2 : COrDSpec , len : u8) -> CaptureParamAndLocalXAPayloadFmtSpec {
        Named ("capture_param_and_local_x_a_payload" ,
        Mapped {
            inner : match choice2 {
                COrDSpec :: C => Sum :: Inl (Varied ((len as usize))) ,
                COrDSpec :: D => Sum :: Inr (Varied ((len as usize))) ,
            }
            ,
            mapper : (| parsed : CaptureParamAndLocalXAPayloadInner | -> CaptureParamAndLocalXAPayloadSpec {
                match parsed {
                    Sum :: Inl (v) => CaptureParamAndLocalXAPayloadSpec :: C (v) ,
                    Sum :: Inr (v) => CaptureParamAndLocalXAPayloadSpec :: D (v) ,
                }
            }
            ,
            | value : CaptureParamAndLocalXAPayloadSpec | -> CaptureParamAndLocalXAPayloadInner {
                match value {
                    CaptureParamAndLocalXAPayloadSpec :: C (v) => Sum :: Inl (v) ,
                    CaptureParamAndLocalXAPayloadSpec :: D (v) => Sum :: Inr (v) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_param_and_local_x_a`."]
    pub struct CaptureParamAndLocalXAFmt {
        pub choice2 : COrD ,
    }

    pub type CaptureParamAndLocalXAFmtSpec = Named < Mapped < Bind < U8 , spec_fn (u8) -> CaptureParamAndLocalXAPayloadFmt > , FnSpecMapper < CaptureParamAndLocalXAInner , CaptureParamAndLocalXASpec >> > ;

    # [doc = "specification constructor for `capture_param_and_local_x_a`."]
    pub open spec fn capture_param_and_local_x_a_fmt (choice2 : COrDSpec) -> CaptureParamAndLocalXAFmtSpec {
        Named ("capture_param_and_local_x_a" ,
        Mapped {
            inner : Bind (U8 ,
            | len : u8 | CaptureParamAndLocalXAPayloadFmt {
                choice2 ,
                len
            }
            ) ,
            mapper : (| parsed : CaptureParamAndLocalXAInner | -> CaptureParamAndLocalXASpec {
                let (len ,
                payload) = parsed ;
                CaptureParamAndLocalXASpec {
                    len ,
                    payload
                }
            }
            ,
            | value : CaptureParamAndLocalXASpec | -> CaptureParamAndLocalXAInner {
                let CaptureParamAndLocalXASpec {
                    len ,
                    payload
                }
                = value ;
                (len ,
                payload)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_param_and_local_x_b_y`."]
    pub struct CaptureParamAndLocalXBYFmt {
        pub tag : u8 ,
    }

    pub type CaptureParamAndLocalXBYFmtSpec = Named < Mapped < Sum < U8 , U16Le > , FnSpecMapper < CaptureParamAndLocalXBYInner , CaptureParamAndLocalXBYSpec >> > ;

    # [doc = "specification constructor for `capture_param_and_local_x_b_y`."]
    pub open spec fn capture_param_and_local_x_b_y_fmt (tag : u8) -> CaptureParamAndLocalXBYFmtSpec {
        Named ("capture_param_and_local_x_b_y" ,
        Mapped {
            inner : match tag {
                0 => Sum :: Inl (U8) ,
                _ => Sum :: Inr (U16Le) ,
            }
            ,
            mapper : (| parsed : CaptureParamAndLocalXBYInner | -> CaptureParamAndLocalXBYSpec {
                match parsed {
                    Sum :: Inl (v) => CaptureParamAndLocalXBYSpec :: Variant1 (v) ,
                    Sum :: Inr (v) => CaptureParamAndLocalXBYSpec :: Default (v) ,
                }
            }
            ,
            | value : CaptureParamAndLocalXBYSpec | -> CaptureParamAndLocalXBYInner {
                match value {
                    CaptureParamAndLocalXBYSpec :: Variant1 (v) => Sum :: Inl (v) ,
                    CaptureParamAndLocalXBYSpec :: Default (v) => Sum :: Inr (v) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_param_and_local_x_b`."]
    pub struct CaptureParamAndLocalXBFmt ;

    pub type CaptureParamAndLocalXBFmtSpec = Named < Mapped < Bind < U8 , spec_fn (u8) -> CaptureParamAndLocalXBYFmt > , FnSpecMapper < CaptureParamAndLocalXBInner , CaptureParamAndLocalXBSpec >> > ;

    # [doc = "specification constructor for `capture_param_and_local_x_b`."]
    pub open spec fn capture_param_and_local_x_b_fmt () -> CaptureParamAndLocalXBFmtSpec {
        Named ("capture_param_and_local_x_b" ,
        Mapped {
            inner : Bind (U8 ,
            | tag : u8 | CaptureParamAndLocalXBYFmt {
                tag
            }
            ) ,
            mapper : (| parsed : CaptureParamAndLocalXBInner | -> CaptureParamAndLocalXBSpec {
                let (tag ,
                y) = parsed ;
                CaptureParamAndLocalXBSpec {
                    tag ,
                    y
                }
            }
            ,
            | value : CaptureParamAndLocalXBSpec | -> CaptureParamAndLocalXBInner {
                let CaptureParamAndLocalXBSpec {
                    tag ,
                    y
                }
                = value ;
                (tag ,
                y)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_param_and_local_x`."]
    pub struct CaptureParamAndLocalXFmt {
        pub choice1 : AOrB ,
        pub choice2 : COrD ,
    }

    pub type CaptureParamAndLocalXFmtSpec = Named < Mapped < Sum < CaptureParamAndLocalXAFmt , CaptureParamAndLocalXBFmt > , FnSpecMapper < CaptureParamAndLocalXInner , CaptureParamAndLocalXSpec >> > ;

    # [doc = "specification constructor for `capture_param_and_local_x`."]
    pub open spec fn capture_param_and_local_x_fmt (choice1 : AOrBSpec , choice2 : COrDSpec) -> CaptureParamAndLocalXFmtSpec {
        Named ("capture_param_and_local_x" ,
        Mapped {
            inner : match choice1 {
                AOrBSpec :: A => Sum :: Inl (CaptureParamAndLocalXAFmt {
                    choice2
                }
                ) ,
                AOrBSpec :: B => Sum :: Inr (CaptureParamAndLocalXBFmt) ,
            }
            ,
            mapper : (| parsed : CaptureParamAndLocalXInner | -> CaptureParamAndLocalXSpec {
                match parsed {
                    Sum :: Inl (v) => CaptureParamAndLocalXSpec :: A (v) ,
                    Sum :: Inr (v) => CaptureParamAndLocalXSpec :: B (v) ,
                }
            }
            ,
            | value : CaptureParamAndLocalXSpec | -> CaptureParamAndLocalXInner {
                match value {
                    CaptureParamAndLocalXSpec :: A (v) => Sum :: Inl (v) ,
                    CaptureParamAndLocalXSpec :: B (v) => Sum :: Inr (v) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `nested_inner_choice_x_a`."]
    pub struct NestedInnerChoiceXAFmt {
        pub choice2 : COrD ,
    }

    pub type NestedInnerChoiceXAFmtSpec = Named < Mapped < Sum < U8 , U16Le > , FnSpecMapper < NestedInnerChoiceXAInner , NestedInnerChoiceXASpec >> > ;

    # [doc = "specification constructor for `nested_inner_choice_x_a`."]
    pub open spec fn nested_inner_choice_x_a_fmt (choice2 : COrDSpec) -> NestedInnerChoiceXAFmtSpec {
        Named ("nested_inner_choice_x_a" ,
        Mapped {
            inner : match choice2 {
                COrDSpec :: C => Sum :: Inl (U8) ,
                COrDSpec :: D => Sum :: Inr (U16Le) ,
            }
            ,
            mapper : (| parsed : NestedInnerChoiceXAInner | -> NestedInnerChoiceXASpec {
                match parsed {
                    Sum :: Inl (v) => NestedInnerChoiceXASpec :: C (v) ,
                    Sum :: Inr (v) => NestedInnerChoiceXASpec :: D (v) ,
                }
            }
            ,
            | value : NestedInnerChoiceXASpec | -> NestedInnerChoiceXAInner {
                match value {
                    NestedInnerChoiceXASpec :: C (v) => Sum :: Inl (v) ,
                    NestedInnerChoiceXASpec :: D (v) => Sum :: Inr (v) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_outer_and_local_payload_anon_inner_body_choice1`."]
    pub struct CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt ;

    pub type CaptureOuterAndLocalPayloadAnonInnerBodyChoice1FmtSpec = Named < Mapped < Bind < U8 , spec_fn (u8) -> Varied < usize > > , FnSpecMapper < CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner , CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec >> > ;

    # [doc = "specification constructor for `capture_outer_and_local_payload_anon_inner_body_choice1`."]
    pub open spec fn capture_outer_and_local_payload_anon_inner_body_choice1_fmt () -> CaptureOuterAndLocalPayloadAnonInnerBodyChoice1FmtSpec {
        Named ("capture_outer_and_local_payload_anon_inner_body_choice1" ,
        Mapped {
            inner : Bind (U8 ,
            | count : u8 | Varied ((count as usize))) ,
            mapper : (| parsed : CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner | -> CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec {
                let (count ,
                items) = parsed ;
                CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec {
                    count ,
                    items
                }
            }
            ,
            | value : CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec | -> CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner {
                let CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec {
                    count ,
                    items
                }
                = value ;
                (count ,
                items)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_outer_and_local_payload_anon_inner_body`."]
    pub struct CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
        pub frame_len : u8 ,
        pub tag : u8 ,
    }

    pub type CaptureOuterAndLocalPayloadAnonInnerBodyFmtSpec = Named < Mapped < Sum < Varied < usize > , CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt > , FnSpecMapper < CaptureOuterAndLocalPayloadAnonInnerBodyInner , CaptureOuterAndLocalPayloadAnonInnerBodySpec >> > ;

    # [doc = "specification constructor for `capture_outer_and_local_payload_anon_inner_body`."]
    pub open spec fn capture_outer_and_local_payload_anon_inner_body_fmt (frame_len : u8 , tag : u8) -> CaptureOuterAndLocalPayloadAnonInnerBodyFmtSpec {
        Named ("capture_outer_and_local_payload_anon_inner_body" ,
        Mapped {
            inner : match tag {
                0 => Sum :: Inl (Varied ((((frame_len as usize) - 1) as usize))) ,
                _ => Sum :: Inr (CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt) ,
            }
            ,
            mapper : (| parsed : CaptureOuterAndLocalPayloadAnonInnerBodyInner | -> CaptureOuterAndLocalPayloadAnonInnerBodySpec {
                match parsed {
                    Sum :: Inl (v) => CaptureOuterAndLocalPayloadAnonInnerBodySpec :: Variant1 (v) ,
                    Sum :: Inr (v) => CaptureOuterAndLocalPayloadAnonInnerBodySpec :: Default (v) ,
                }
            }
            ,
            | value : CaptureOuterAndLocalPayloadAnonInnerBodySpec | -> CaptureOuterAndLocalPayloadAnonInnerBodyInner {
                match value {
                    CaptureOuterAndLocalPayloadAnonInnerBodySpec :: Variant1 (v) => Sum :: Inl (v) ,
                    CaptureOuterAndLocalPayloadAnonInnerBodySpec :: Default (v) => Sum :: Inr (v) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_outer_and_local_payload`."]
    pub struct CaptureOuterAndLocalPayloadFmt {
        pub frame_len : u8 ,
    }

    pub type CaptureOuterAndLocalPayloadFmtSpec = Named < ExactLen < Bind < U8 , spec_fn (u8) -> CaptureOuterAndLocalPayloadAnonInnerBodyFmt > , usize > > ;

    # [doc = "specification constructor for `capture_outer_and_local_payload`."]
    pub open spec fn capture_outer_and_local_payload_fmt (frame_len : u8) -> CaptureOuterAndLocalPayloadFmtSpec {
        Named ("capture_outer_and_local_payload" ,
        ExactLen ((frame_len as usize) ,
        Bind (U8 ,
        | tag : u8 | CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            frame_len ,
            tag
        }
        )))
    }


    # [doc = "named format combinator for `capture_outer_and_local`."]
    pub struct CaptureOuterAndLocalFmt ;

    pub type CaptureOuterAndLocalFmtSpec = Named < Mapped < Bind < Refined < U8 , PredFnSpec < u8 >> , spec_fn (u8) -> CaptureOuterAndLocalPayloadFmt > , FnSpecMapper < CaptureOuterAndLocalInner , CaptureOuterAndLocalSpec >> > ;

    # [doc = "specification constructor for `capture_outer_and_local`."]
    pub open spec fn capture_outer_and_local_fmt () -> CaptureOuterAndLocalFmtSpec {
        Named ("capture_outer_and_local" ,
        Mapped {
            inner : Bind (Refined (U8 ,
            | x : u8 | x >= 1) ,
            | frame_len : u8 | CaptureOuterAndLocalPayloadFmt {
                frame_len
            }
            ) ,
            mapper : (| parsed : CaptureOuterAndLocalInner | -> CaptureOuterAndLocalSpec {
                let (frame_len ,
                payload) = parsed ;
                CaptureOuterAndLocalSpec {
                    frame_len ,
                    payload
                }
            }
            ,
            | value : CaptureOuterAndLocalSpec | -> CaptureOuterAndLocalInner {
                let CaptureOuterAndLocalSpec {
                    frame_len ,
                    payload
                }
                = value ;
                (frame_len ,
                payload)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `nested_inner_struct_anon_inner`."]
    pub struct NestedInnerStructAnonInnerFmt {
        pub len : u32 ,
    }

    pub type NestedInnerStructAnonInnerFmtSpec = Named < ExactLen < Pair < U8 , Tail > , usize > > ;

    # [doc = "specification constructor for `nested_inner_struct_anon_inner`."]
    pub open spec fn nested_inner_struct_anon_inner_fmt (len : u32) -> NestedInnerStructAnonInnerFmtSpec {
        Named ("nested_inner_struct_anon_inner" ,
        ExactLen ((len as usize) ,
        Pair (U8 ,
        Tail)))
    }


    # [doc = "named format combinator for `capture_local_in_anon_struct_wrapper_value_choice0`."]
    pub struct CaptureLocalInAnonStructWrapperValueChoice0Fmt ;

    pub type CaptureLocalInAnonStructWrapperValueChoice0FmtSpec = Named < Mapped < Bind < U8 , spec_fn (u8) -> Varied < usize > > , FnSpecMapper < CaptureLocalInAnonStructWrapperValueChoice0Inner , CaptureLocalInAnonStructWrapperValueChoice0Spec >> > ;

    # [doc = "specification constructor for `capture_local_in_anon_struct_wrapper_value_choice0`."]
    pub open spec fn capture_local_in_anon_struct_wrapper_value_choice0_fmt () -> CaptureLocalInAnonStructWrapperValueChoice0FmtSpec {
        Named ("capture_local_in_anon_struct_wrapper_value_choice0" ,
        Mapped {
            inner : Bind (U8 ,
            | len : u8 | Varied ((len as usize))) ,
            mapper : (| parsed : CaptureLocalInAnonStructWrapperValueChoice0Inner | -> CaptureLocalInAnonStructWrapperValueChoice0Spec {
                let (len ,
                bytes) = parsed ;
                CaptureLocalInAnonStructWrapperValueChoice0Spec {
                    len ,
                    bytes
                }
            }
            ,
            | value : CaptureLocalInAnonStructWrapperValueChoice0Spec | -> CaptureLocalInAnonStructWrapperValueChoice0Inner {
                let CaptureLocalInAnonStructWrapperValueChoice0Spec {
                    len ,
                    bytes
                }
                = value ;
                (len ,
                bytes)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_local_in_anon_struct_wrapper_value`."]
    pub struct CaptureLocalInAnonStructWrapperValueFmt {
        pub tag : u8 ,
    }

    pub type CaptureLocalInAnonStructWrapperValueFmtSpec = Named < Mapped < Sum < CaptureLocalInAnonStructWrapperValueChoice0Fmt , U16Le > , FnSpecMapper < CaptureLocalInAnonStructWrapperValueInner , CaptureLocalInAnonStructWrapperValueSpec >> > ;

    # [doc = "specification constructor for `capture_local_in_anon_struct_wrapper_value`."]
    pub open spec fn capture_local_in_anon_struct_wrapper_value_fmt (tag : u8) -> CaptureLocalInAnonStructWrapperValueFmtSpec {
        Named ("capture_local_in_anon_struct_wrapper_value" ,
        Mapped {
            inner : match tag {
                0 => Sum :: Inl (CaptureLocalInAnonStructWrapperValueChoice0Fmt) ,
                _ => Sum :: Inr (U16Le) ,
            }
            ,
            mapper : (| parsed : CaptureLocalInAnonStructWrapperValueInner | -> CaptureLocalInAnonStructWrapperValueSpec {
                match parsed {
                    Sum :: Inl (v) => CaptureLocalInAnonStructWrapperValueSpec :: Variant1 (v) ,
                    Sum :: Inr (v) => CaptureLocalInAnonStructWrapperValueSpec :: Default (v) ,
                }
            }
            ,
            | value : CaptureLocalInAnonStructWrapperValueSpec | -> CaptureLocalInAnonStructWrapperValueInner {
                match value {
                    CaptureLocalInAnonStructWrapperValueSpec :: Variant1 (v) => Sum :: Inl (v) ,
                    CaptureLocalInAnonStructWrapperValueSpec :: Default (v) => Sum :: Inr (v) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `nested_inner_choice_x`."]
    pub struct NestedInnerChoiceXFmt {
        pub choice1 : AOrB ,
        pub choice2 : COrD ,
    }

    pub type NestedInnerChoiceXFmtSpec = Named < Mapped < Sum < NestedInnerChoiceXAFmt , U32Le > , FnSpecMapper < NestedInnerChoiceXInner , NestedInnerChoiceXSpec >> > ;

    # [doc = "specification constructor for `nested_inner_choice_x`."]
    pub open spec fn nested_inner_choice_x_fmt (choice1 : AOrBSpec , choice2 : COrDSpec) -> NestedInnerChoiceXFmtSpec {
        Named ("nested_inner_choice_x" ,
        Mapped {
            inner : match choice1 {
                AOrBSpec :: A => Sum :: Inl (NestedInnerChoiceXAFmt {
                    choice2
                }
                ) ,
                AOrBSpec :: B => Sum :: Inr (U32Le) ,
            }
            ,
            mapper : (| parsed : NestedInnerChoiceXInner | -> NestedInnerChoiceXSpec {
                match parsed {
                    Sum :: Inl (v) => NestedInnerChoiceXSpec :: A (v) ,
                    Sum :: Inr (v) => NestedInnerChoiceXSpec :: B (v) ,
                }
            }
            ,
            | value : NestedInnerChoiceXSpec | -> NestedInnerChoiceXInner {
                match value {
                    NestedInnerChoiceXSpec :: A (v) => Sum :: Inl (v) ,
                    NestedInnerChoiceXSpec :: B (v) => Sum :: Inr (v) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `nested_inner_choice`."]
    pub struct NestedInnerChoiceFmt {
        pub choice1 : AOrB ,
        pub choice2 : COrD ,
    }

    pub type NestedInnerChoiceFmtSpec = Named < Mapped < NestedInnerChoiceXFmt , FnSpecMapper < NestedInnerChoiceInner , NestedInnerChoiceSpec >> > ;

    # [doc = "specification constructor for `nested_inner_choice`."]
    pub open spec fn nested_inner_choice_fmt (choice1 : AOrBSpec , choice2 : COrDSpec) -> NestedInnerChoiceFmtSpec {
        Named ("nested_inner_choice" ,
        Mapped {
            inner : NestedInnerChoiceXFmt {
                choice1 ,
                choice2
            }
            ,
            mapper : (| parsed : NestedInnerChoiceInner | -> NestedInnerChoiceSpec {
                let x = parsed ;
                NestedInnerChoiceSpec {
                    x
                }
            }
            ,
            | value : NestedInnerChoiceSpec | -> NestedInnerChoiceInner {
                let NestedInnerChoiceSpec {
                    x
                }
                = value ;
                x
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_param_and_local`."]
    pub struct CaptureParamAndLocalFmt {
        pub choice1 : AOrB ,
        pub choice2 : COrD ,
    }

    pub type CaptureParamAndLocalFmtSpec = Named < Mapped < CaptureParamAndLocalXFmt , FnSpecMapper < CaptureParamAndLocalInner , CaptureParamAndLocalSpec >> > ;

    # [doc = "specification constructor for `capture_param_and_local`."]
    pub open spec fn capture_param_and_local_fmt (choice1 : AOrBSpec , choice2 : COrDSpec) -> CaptureParamAndLocalFmtSpec {
        Named ("capture_param_and_local" ,
        Mapped {
            inner : CaptureParamAndLocalXFmt {
                choice1 ,
                choice2
            }
            ,
            mapper : (| parsed : CaptureParamAndLocalInner | -> CaptureParamAndLocalSpec {
                let x = parsed ;
                CaptureParamAndLocalSpec {
                    x
                }
            }
            ,
            | value : CaptureParamAndLocalSpec | -> CaptureParamAndLocalInner {
                let CaptureParamAndLocalSpec {
                    x
                }
                = value ;
                x
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `nested_inner_struct`."]
    pub struct NestedInnerStructFmt ;

    pub type NestedInnerStructFmtSpec = Named < Mapped < Bind < U32Le , spec_fn (u32) -> NestedInnerStructAnonInnerFmt > , FnSpecMapper < NestedInnerStructInner , NestedInnerStructSpec >> > ;

    # [doc = "specification constructor for `nested_inner_struct`."]
    pub open spec fn nested_inner_struct_fmt () -> NestedInnerStructFmtSpec {
        Named ("nested_inner_struct" ,
        Mapped {
            inner : Bind (U32Le ,
            | len : u32 | NestedInnerStructAnonInnerFmt {
                len
            }
            ) ,
            mapper : (| parsed : NestedInnerStructInner | -> NestedInnerStructSpec {
                let (len ,
                inner) = parsed ;
                NestedInnerStructSpec {
                    len ,
                    inner
                }
            }
            ,
            | value : NestedInnerStructSpec | -> NestedInnerStructInner {
                let NestedInnerStructSpec {
                    len ,
                    inner
                }
                = value ;
                (len ,
                inner)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `c_or_d`."]
    pub struct COrDFmt ;

    pub type COrDFmtSpec = Named < Mapped < Refined < U8 , PredFnSpec < u8 >> , FnSpecMapper < COrDInner , COrDSpec >> > ;

    # [doc = "specification constructor for `c_or_d`."]
    pub open spec fn c_or_d_fmt () -> COrDFmtSpec {
        Named ("c_or_d" ,
        Mapped {
            inner : Refined (U8 ,
            | x : u8 | x == 1 || x == 2) ,
            mapper : (| parsed : COrDInner | -> COrDSpec {
                match parsed {
                    1 => COrDSpec :: C ,
                    2 => COrDSpec :: D ,
                    _ => arbitrary () ,
                }
            }
            ,
            | value : COrDSpec | -> COrDInner {
                match value {
                    COrDSpec :: C => 1 ,
                    COrDSpec :: D => 2 ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_local_in_anon_struct_wrapper`."]
    pub struct CaptureLocalInAnonStructWrapperFmt ;

    pub type CaptureLocalInAnonStructWrapperFmtSpec = Named < Mapped < Bind < U8 , spec_fn (u8) -> CaptureLocalInAnonStructWrapperValueFmt > , FnSpecMapper < CaptureLocalInAnonStructWrapperInner , CaptureLocalInAnonStructWrapperSpec >> > ;

    # [doc = "specification constructor for `capture_local_in_anon_struct_wrapper`."]
    pub open spec fn capture_local_in_anon_struct_wrapper_fmt () -> CaptureLocalInAnonStructWrapperFmtSpec {
        Named ("capture_local_in_anon_struct_wrapper" ,
        Mapped {
            inner : Bind (U8 ,
            | tag : u8 | CaptureLocalInAnonStructWrapperValueFmt {
                tag
            }
            ) ,
            mapper : (| parsed : CaptureLocalInAnonStructWrapperInner | -> CaptureLocalInAnonStructWrapperSpec {
                let (tag ,
                value) = parsed ;
                CaptureLocalInAnonStructWrapperSpec {
                    tag ,
                    value
                }
            }
            ,
            | value : CaptureLocalInAnonStructWrapperSpec | -> CaptureLocalInAnonStructWrapperInner {
                let CaptureLocalInAnonStructWrapperSpec {
                    tag ,
                    value
                }
                = value ;
                (tag ,
                value)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `capture_local_in_anon_struct`."]
    pub struct CaptureLocalInAnonStructFmt ;

    pub type CaptureLocalInAnonStructFmtSpec = Named < Mapped < CaptureLocalInAnonStructWrapperFmt , FnSpecMapper < CaptureLocalInAnonStructInner , CaptureLocalInAnonStructSpec >> > ;

    # [doc = "specification constructor for `capture_local_in_anon_struct`."]
    pub open spec fn capture_local_in_anon_struct_fmt () -> CaptureLocalInAnonStructFmtSpec {
        Named ("capture_local_in_anon_struct" ,
        Mapped {
            inner : CaptureLocalInAnonStructWrapperFmt ,
            mapper : (| parsed : CaptureLocalInAnonStructInner | -> CaptureLocalInAnonStructSpec {
                let wrapper = parsed ;
                CaptureLocalInAnonStructSpec {
                    wrapper
                }
            }
            ,
            | value : CaptureLocalInAnonStructSpec | -> CaptureLocalInAnonStructInner {
                let CaptureLocalInAnonStructSpec {
                    wrapper
                }
                = value ;
                wrapper
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `a_or_b`."]
    pub struct AOrBFmt ;

    pub type AOrBFmtSpec = Named < Mapped < Refined < U8 , PredFnSpec < u8 >> , FnSpecMapper < AOrBInner , AOrBSpec >> > ;

    # [doc = "specification constructor for `a_or_b`."]
    pub open spec fn a_or_b_fmt () -> AOrBFmtSpec {
        Named ("a_or_b" ,
        Mapped {
            inner : Refined (U8 ,
            | x : u8 | x == 1 || x == 2) ,
            mapper : (| parsed : AOrBInner | -> AOrBSpec {
                match parsed {
                    1 => AOrBSpec :: A ,
                    2 => AOrBSpec :: B ,
                    _ => arbitrary () ,
                }
            }
            ,
            | value : AOrBSpec | -> AOrBInner {
                match value {
                    AOrBSpec :: A => 1 ,
                    AOrBSpec :: B => 2 ,
                }
            }
            )
        }
        )
    }

    // ============================================================
    // Derived Parser, Serializer, Length, and Consistency Specifications
    // ============================================================
    mod derived_specs {
        use super::*;

        impl SpecParser for CaptureParamAndLocalXAPayloadFmt {
            type PVal = CaptureParamAndLocalXAPayloadSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureParamAndLocalXAPayloadFmt {
            type Val = CaptureParamAndLocalXAPayloadSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureParamAndLocalXAPayloadFmt {
            type SValue = CaptureParamAndLocalXAPayloadSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureParamAndLocalXAPayloadFmt {
            type SVal = CaptureParamAndLocalXAPayloadSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureParamAndLocalXAPayloadFmt {
            type T = CaptureParamAndLocalXAPayloadSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for CaptureParamAndLocalXAFmt {
            type PVal = CaptureParamAndLocalXASpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureParamAndLocalXAFmt {
            type Val = CaptureParamAndLocalXASpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureParamAndLocalXAFmt {
            type SValue = CaptureParamAndLocalXASpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureParamAndLocalXAFmt {
            type SVal = CaptureParamAndLocalXASpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureParamAndLocalXAFmt {
            type T = CaptureParamAndLocalXASpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for CaptureParamAndLocalXBYFmt {
            type PVal = CaptureParamAndLocalXBYSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureParamAndLocalXBYFmt {
            type Val = CaptureParamAndLocalXBYSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureParamAndLocalXBYFmt {
            type SValue = CaptureParamAndLocalXBYSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureParamAndLocalXBYFmt {
            type SVal = CaptureParamAndLocalXBYSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureParamAndLocalXBYFmt {
            type T = CaptureParamAndLocalXBYSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for CaptureParamAndLocalXBFmt {
            type PVal = CaptureParamAndLocalXBSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_param_and_local_x_b_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureParamAndLocalXBFmt {
            type Val = CaptureParamAndLocalXBSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_param_and_local_x_b_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureParamAndLocalXBFmt {
            type SValue = CaptureParamAndLocalXBSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_param_and_local_x_b_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureParamAndLocalXBFmt {
            type SVal = CaptureParamAndLocalXBSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_param_and_local_x_b_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureParamAndLocalXBFmt {
            type T = CaptureParamAndLocalXBSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_param_and_local_x_b_fmt () . byte_len (v)
            }
        }

        impl SpecParser for CaptureParamAndLocalXFmt {
            type PVal = CaptureParamAndLocalXSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureParamAndLocalXFmt {
            type Val = CaptureParamAndLocalXSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureParamAndLocalXFmt {
            type SValue = CaptureParamAndLocalXSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureParamAndLocalXFmt {
            type SVal = CaptureParamAndLocalXSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureParamAndLocalXFmt {
            type T = CaptureParamAndLocalXSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for NestedInnerChoiceXAFmt {
            type PVal = NestedInnerChoiceXASpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for NestedInnerChoiceXAFmt {
            type Val = NestedInnerChoiceXASpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for NestedInnerChoiceXAFmt {
            type SValue = NestedInnerChoiceXASpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for NestedInnerChoiceXAFmt {
            type SVal = NestedInnerChoiceXASpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for NestedInnerChoiceXAFmt {
            type T = NestedInnerChoiceXASpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            type PVal = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_outer_and_local_payload_anon_inner_body_choice1_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            type Val = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_outer_and_local_payload_anon_inner_body_choice1_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            type SValue = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_outer_and_local_payload_anon_inner_body_choice1_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            type SVal = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_outer_and_local_payload_anon_inner_body_choice1_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            type T = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_outer_and_local_payload_anon_inner_body_choice1_fmt () . byte_len (v)
            }
        }

        impl SpecParser for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            type PVal = CaptureOuterAndLocalPayloadAnonInnerBodySpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            type Val = CaptureOuterAndLocalPayloadAnonInnerBodySpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            type SValue = CaptureOuterAndLocalPayloadAnonInnerBodySpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            type SVal = CaptureOuterAndLocalPayloadAnonInnerBodySpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            type T = CaptureOuterAndLocalPayloadAnonInnerBodySpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for CaptureOuterAndLocalPayloadFmt {
            type PVal = CaptureOuterAndLocalPayloadSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureOuterAndLocalPayloadFmt {
            type Val = CaptureOuterAndLocalPayloadSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureOuterAndLocalPayloadFmt {
            type SValue = CaptureOuterAndLocalPayloadSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureOuterAndLocalPayloadFmt {
            type SVal = CaptureOuterAndLocalPayloadSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureOuterAndLocalPayloadFmt {
            type T = CaptureOuterAndLocalPayloadSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for CaptureOuterAndLocalFmt {
            type PVal = CaptureOuterAndLocalSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_outer_and_local_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureOuterAndLocalFmt {
            type Val = CaptureOuterAndLocalSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_outer_and_local_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureOuterAndLocalFmt {
            type SValue = CaptureOuterAndLocalSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_outer_and_local_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureOuterAndLocalFmt {
            type SVal = CaptureOuterAndLocalSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_outer_and_local_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureOuterAndLocalFmt {
            type T = CaptureOuterAndLocalSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_outer_and_local_fmt () . byte_len (v)
            }
        }

        impl SpecParser for NestedInnerStructAnonInnerFmt {
            type PVal = NestedInnerStructAnonInnerSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for NestedInnerStructAnonInnerFmt {
            type Val = NestedInnerStructAnonInnerSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for NestedInnerStructAnonInnerFmt {
            type SValue = NestedInnerStructAnonInnerSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for NestedInnerStructAnonInnerFmt {
            type SVal = NestedInnerStructAnonInnerSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for NestedInnerStructAnonInnerFmt {
            type T = NestedInnerStructAnonInnerSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            type PVal = CaptureLocalInAnonStructWrapperValueChoice0Spec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_local_in_anon_struct_wrapper_value_choice0_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            type Val = CaptureLocalInAnonStructWrapperValueChoice0Spec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_local_in_anon_struct_wrapper_value_choice0_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            type SValue = CaptureLocalInAnonStructWrapperValueChoice0Spec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_local_in_anon_struct_wrapper_value_choice0_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            type SVal = CaptureLocalInAnonStructWrapperValueChoice0Spec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_local_in_anon_struct_wrapper_value_choice0_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            type T = CaptureLocalInAnonStructWrapperValueChoice0Spec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_local_in_anon_struct_wrapper_value_choice0_fmt () . byte_len (v)
            }
        }

        impl SpecParser for CaptureLocalInAnonStructWrapperValueFmt {
            type PVal = CaptureLocalInAnonStructWrapperValueSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureLocalInAnonStructWrapperValueFmt {
            type Val = CaptureLocalInAnonStructWrapperValueSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureLocalInAnonStructWrapperValueFmt {
            type SValue = CaptureLocalInAnonStructWrapperValueSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureLocalInAnonStructWrapperValueFmt {
            type SVal = CaptureLocalInAnonStructWrapperValueSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureLocalInAnonStructWrapperValueFmt {
            type T = CaptureLocalInAnonStructWrapperValueSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for NestedInnerChoiceXFmt {
            type PVal = NestedInnerChoiceXSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for NestedInnerChoiceXFmt {
            type Val = NestedInnerChoiceXSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for NestedInnerChoiceXFmt {
            type SValue = NestedInnerChoiceXSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for NestedInnerChoiceXFmt {
            type SVal = NestedInnerChoiceXSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for NestedInnerChoiceXFmt {
            type T = NestedInnerChoiceXSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for NestedInnerChoiceFmt {
            type PVal = NestedInnerChoiceSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for NestedInnerChoiceFmt {
            type Val = NestedInnerChoiceSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for NestedInnerChoiceFmt {
            type SValue = NestedInnerChoiceSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for NestedInnerChoiceFmt {
            type SVal = NestedInnerChoiceSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for NestedInnerChoiceFmt {
            type T = NestedInnerChoiceSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for CaptureParamAndLocalFmt {
            type PVal = CaptureParamAndLocalSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureParamAndLocalFmt {
            type Val = CaptureParamAndLocalSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureParamAndLocalFmt {
            type SValue = CaptureParamAndLocalSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureParamAndLocalFmt {
            type SVal = CaptureParamAndLocalSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureParamAndLocalFmt {
            type T = CaptureParamAndLocalSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for NestedInnerStructFmt {
            type PVal = NestedInnerStructSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                nested_inner_struct_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for NestedInnerStructFmt {
            type Val = NestedInnerStructSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                nested_inner_struct_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for NestedInnerStructFmt {
            type SValue = NestedInnerStructSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                nested_inner_struct_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for NestedInnerStructFmt {
            type SVal = NestedInnerStructSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                nested_inner_struct_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for NestedInnerStructFmt {
            type T = NestedInnerStructSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                nested_inner_struct_fmt () . byte_len (v)
            }
        }

        impl SpecParser for COrDFmt {
            type PVal = COrDSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                c_or_d_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for COrDFmt {
            type Val = COrDSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                c_or_d_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for COrDFmt {
            type SValue = COrDSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                c_or_d_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for COrDFmt {
            type SVal = COrDSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                c_or_d_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for COrDFmt {
            type T = COrDSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                c_or_d_fmt () . byte_len (v)
            }
        }

        impl SpecParser for CaptureLocalInAnonStructWrapperFmt {
            type PVal = CaptureLocalInAnonStructWrapperSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_local_in_anon_struct_wrapper_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureLocalInAnonStructWrapperFmt {
            type Val = CaptureLocalInAnonStructWrapperSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_local_in_anon_struct_wrapper_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureLocalInAnonStructWrapperFmt {
            type SValue = CaptureLocalInAnonStructWrapperSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_local_in_anon_struct_wrapper_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureLocalInAnonStructWrapperFmt {
            type SVal = CaptureLocalInAnonStructWrapperSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_local_in_anon_struct_wrapper_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureLocalInAnonStructWrapperFmt {
            type T = CaptureLocalInAnonStructWrapperSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_local_in_anon_struct_wrapper_fmt () . byte_len (v)
            }
        }

        impl SpecParser for CaptureLocalInAnonStructFmt {
            type PVal = CaptureLocalInAnonStructSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                capture_local_in_anon_struct_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for CaptureLocalInAnonStructFmt {
            type Val = CaptureLocalInAnonStructSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                capture_local_in_anon_struct_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for CaptureLocalInAnonStructFmt {
            type SValue = CaptureLocalInAnonStructSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                capture_local_in_anon_struct_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for CaptureLocalInAnonStructFmt {
            type SVal = CaptureLocalInAnonStructSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                capture_local_in_anon_struct_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for CaptureLocalInAnonStructFmt {
            type T = CaptureLocalInAnonStructSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                capture_local_in_anon_struct_fmt () . byte_len (v)
            }
        }

        impl SpecParser for AOrBFmt {
            type PVal = AOrBSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                a_or_b_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for AOrBFmt {
            type Val = AOrBSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                a_or_b_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for AOrBFmt {
            type SValue = AOrBSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                a_or_b_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for AOrBFmt {
            type SVal = AOrBSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                a_or_b_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for AOrBFmt {
            type T = AOrBSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                a_or_b_fmt () . byte_len (v)
            }
        }
    }

    // ============================================================
    // Proven Format Properties
    // ============================================================
    mod derived_proofs {
        use super::*;
        broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        impl SafeParser for CaptureParamAndLocalXAPayloadFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecParser > :: spec_parse) ;
                capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureParamAndLocalXAPayloadFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureParamAndLocalXAPayloadFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as Consistency > :: consistent) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureParamAndLocalXAPayloadFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureParamAndLocalXAPayloadFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureParamAndLocalXAPayloadFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as Consistency > :: consistent) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureParamAndLocalXAPayloadFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureParamAndLocalXAPayloadFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureParamAndLocalXAPayloadFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXAPayloadFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_a_payload_fmt (self . choice2 . deep_view () ,
                self . len . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureParamAndLocalXAFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecParser > :: spec_parse) ;
                capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureParamAndLocalXAFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureParamAndLocalXAFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXAFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXAFmt as Consistency > :: consistent) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureParamAndLocalXAFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXAFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureParamAndLocalXAFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXAFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureParamAndLocalXAFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureParamAndLocalXAFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXAFmt as Consistency > :: consistent) ;
                reveal (< CaptureParamAndLocalXAFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureParamAndLocalXAFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureParamAndLocalXAFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXAFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureParamAndLocalXAFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXAFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureParamAndLocalXBYFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecParser > :: spec_parse) ;
                capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureParamAndLocalXBYFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureParamAndLocalXBYFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXBYFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXBYFmt as Consistency > :: consistent) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureParamAndLocalXBYFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXBYFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureParamAndLocalXBYFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureParamAndLocalXBYFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureParamAndLocalXBYFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXBYFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXBYFmt as Consistency > :: consistent) ;
                reveal (< CaptureParamAndLocalXBYFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureParamAndLocalXBYFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureParamAndLocalXBYFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXBYFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureParamAndLocalXBYFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXBYFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXBYFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_b_y_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureParamAndLocalXBFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecParser > :: spec_parse) ;
                capture_param_and_local_x_b_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureParamAndLocalXBFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_param_and_local_x_b_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureParamAndLocalXBFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXBFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXBFmt as Consistency > :: consistent) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureParamAndLocalXBFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXBFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureParamAndLocalXBFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXBFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureParamAndLocalXBFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureParamAndLocalXBFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXBFmt as Consistency > :: consistent) ;
                reveal (< CaptureParamAndLocalXBFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureParamAndLocalXBFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureParamAndLocalXBFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXBFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureParamAndLocalXBFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXBFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_b_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureParamAndLocalXFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecParser > :: spec_parse) ;
                capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureParamAndLocalXFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureParamAndLocalXFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXFmt as Consistency > :: consistent) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureParamAndLocalXFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureParamAndLocalXFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureParamAndLocalXFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureParamAndLocalXFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXFmt as Consistency > :: consistent) ;
                reveal (< CaptureParamAndLocalXFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureParamAndLocalXFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureParamAndLocalXFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureParamAndLocalXFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalXFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for NestedInnerChoiceXAFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecParser > :: spec_parse) ;
                nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for NestedInnerChoiceXAFmt {
            open spec fn productive_inv (& self) -> bool {
                nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for NestedInnerChoiceXAFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceXAFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceXAFmt as Consistency > :: consistent) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for NestedInnerChoiceXAFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceXAFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for NestedInnerChoiceXAFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerChoiceXAFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< NestedInnerChoiceXAFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for NestedInnerChoiceXAFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceXAFmt as Consistency > :: consistent) ;
                reveal (< NestedInnerChoiceXAFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for NestedInnerChoiceXAFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for NestedInnerChoiceXAFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceXAFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for NestedInnerChoiceXAFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerChoiceXAFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceXAFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_choice_x_a_fmt (self . choice2 . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecParser > :: spec_parse) ;
                capture_outer_and_local_payload_anon_inner_body_choice1_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            open spec fn productive_inv (& self) -> bool {
                capture_outer_and_local_payload_anon_inner_body_choice1_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecParser > :: spec_parse) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as Consistency > :: consistent) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as Consistency > :: consistent) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecParser > :: spec_parse) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_choice1_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecParser > :: spec_parse) ;
                capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as Consistency > :: consistent) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as Consistency > :: consistent) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureOuterAndLocalPayloadAnonInnerBodyFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadAnonInnerBodyFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_outer_and_local_payload_anon_inner_body_fmt (self . frame_len . deep_view () ,
                self . tag . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureOuterAndLocalPayloadFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecParser > :: spec_parse) ;
                capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureOuterAndLocalPayloadFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureOuterAndLocalPayloadFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as Consistency > :: consistent) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureOuterAndLocalPayloadFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureOuterAndLocalPayloadFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureOuterAndLocalPayloadFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as Consistency > :: consistent) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureOuterAndLocalPayloadFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureOuterAndLocalPayloadFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureOuterAndLocalPayloadFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalPayloadFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_outer_and_local_payload_fmt (self . frame_len . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureOuterAndLocalFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecParser > :: spec_parse) ;
                capture_outer_and_local_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureOuterAndLocalFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_outer_and_local_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureOuterAndLocalFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalFmt as Consistency > :: consistent) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureOuterAndLocalFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureOuterAndLocalFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureOuterAndLocalFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureOuterAndLocalFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureOuterAndLocalFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureOuterAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalFmt as Consistency > :: consistent) ;
                reveal (< CaptureOuterAndLocalFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureOuterAndLocalFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureOuterAndLocalFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureOuterAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureOuterAndLocalFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureOuterAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureOuterAndLocalFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_outer_and_local_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for NestedInnerStructAnonInnerFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecParser > :: spec_parse) ;
                nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for NestedInnerStructAnonInnerFmt {
            open spec fn productive_inv (& self) -> bool {
                nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for NestedInnerStructAnonInnerFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerStructAnonInnerFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerStructAnonInnerFmt as Consistency > :: consistent) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for NestedInnerStructAnonInnerFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerStructAnonInnerFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for NestedInnerStructAnonInnerFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< NestedInnerStructAnonInnerFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for NestedInnerStructAnonInnerFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerStructAnonInnerFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerStructAnonInnerFmt as Consistency > :: consistent) ;
                reveal (< NestedInnerStructAnonInnerFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for NestedInnerStructAnonInnerFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for NestedInnerStructAnonInnerFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerStructAnonInnerFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for NestedInnerStructAnonInnerFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerStructAnonInnerFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerStructAnonInnerFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_struct_anon_inner_fmt (self . len . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser > :: spec_parse) ;
                capture_local_in_anon_struct_wrapper_value_choice0_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            open spec fn productive_inv (& self) -> bool {
                capture_local_in_anon_struct_wrapper_value_choice0_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser > :: spec_parse) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as Consistency > :: consistent) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as Consistency > :: consistent) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser > :: spec_parse) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_choice0_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureLocalInAnonStructWrapperValueFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecParser > :: spec_parse) ;
                capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureLocalInAnonStructWrapperValueFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureLocalInAnonStructWrapperValueFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as Consistency > :: consistent) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureLocalInAnonStructWrapperValueFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureLocalInAnonStructWrapperValueFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureLocalInAnonStructWrapperValueFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as Consistency > :: consistent) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureLocalInAnonStructWrapperValueFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureLocalInAnonStructWrapperValueFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureLocalInAnonStructWrapperValueFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperValueFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_local_in_anon_struct_wrapper_value_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for NestedInnerChoiceXFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecParser > :: spec_parse) ;
                nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for NestedInnerChoiceXFmt {
            open spec fn productive_inv (& self) -> bool {
                nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for NestedInnerChoiceXFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceXFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceXFmt as Consistency > :: consistent) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for NestedInnerChoiceXFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceXFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for NestedInnerChoiceXFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerChoiceXFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< NestedInnerChoiceXFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for NestedInnerChoiceXFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceXFmt as Consistency > :: consistent) ;
                reveal (< NestedInnerChoiceXFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for NestedInnerChoiceXFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for NestedInnerChoiceXFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceXFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for NestedInnerChoiceXFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerChoiceXFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceXFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_choice_x_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for NestedInnerChoiceFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecParser > :: spec_parse) ;
                nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for NestedInnerChoiceFmt {
            open spec fn productive_inv (& self) -> bool {
                nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for NestedInnerChoiceFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceFmt as Consistency > :: consistent) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for NestedInnerChoiceFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for NestedInnerChoiceFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerChoiceFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< NestedInnerChoiceFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for NestedInnerChoiceFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceFmt as Consistency > :: consistent) ;
                reveal (< NestedInnerChoiceFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for NestedInnerChoiceFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for NestedInnerChoiceFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for NestedInnerChoiceFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerChoiceFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_choice_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureParamAndLocalFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecParser > :: spec_parse) ;
                capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureParamAndLocalFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureParamAndLocalFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalFmt as Consistency > :: consistent) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureParamAndLocalFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureParamAndLocalFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureParamAndLocalFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureParamAndLocalFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureParamAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalFmt as Consistency > :: consistent) ;
                reveal (< CaptureParamAndLocalFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureParamAndLocalFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureParamAndLocalFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureParamAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureParamAndLocalFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureParamAndLocalFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureParamAndLocalFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_param_and_local_fmt (self . choice1 . deep_view () ,
                self . choice2 . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for NestedInnerStructFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerStructFmt as SpecParser > :: spec_parse) ;
                nested_inner_struct_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for NestedInnerStructFmt {
            open spec fn productive_inv (& self) -> bool {
                nested_inner_struct_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< NestedInnerStructFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_struct_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for NestedInnerStructFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerStructFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerStructFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_struct_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NestedInnerStructFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerStructFmt as Consistency > :: consistent) ;
                let fmt = nested_inner_struct_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for NestedInnerStructFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerStructFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< NestedInnerStructFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_struct_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for NestedInnerStructFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< NestedInnerStructFmt as SpecParser > :: spec_parse) ;
                reveal (< NestedInnerStructFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerStructFmt as Consistency > :: consistent) ;
                reveal (< NestedInnerStructFmt as SpecByteLen > :: byte_len) ;
                let fmt = nested_inner_struct_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for NestedInnerStructFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< NestedInnerStructFmt as SpecParser > :: spec_parse) ;
                let fmt = nested_inner_struct_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for NestedInnerStructFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< NestedInnerStructFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NestedInnerStructFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = nested_inner_struct_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for COrDFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< COrDFmt as SpecParser > :: spec_parse) ;
                c_or_d_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for COrDFmt {
            open spec fn productive_inv (& self) -> bool {
                c_or_d_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< COrDFmt as SpecParser > :: spec_parse) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for COrDFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< COrDFmt as SpecParser > :: spec_parse) ;
                reveal (< COrDFmt as SpecByteLen > :: byte_len) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< COrDFmt as SpecParser > :: spec_parse) ;
                reveal (< COrDFmt as Consistency > :: consistent) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for COrDFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< COrDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< COrDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< COrDFmt as SpecByteLen > :: byte_len) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for COrDFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< COrDFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< COrDFmt as SpecByteLen > :: byte_len) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for COrDFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< COrDFmt as SpecParser > :: spec_parse) ;
                reveal (< COrDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< COrDFmt as Consistency > :: consistent) ;
                reveal (< COrDFmt as SpecByteLen > :: byte_len) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for COrDFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< COrDFmt as SpecParser > :: spec_parse) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for COrDFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< COrDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< COrDFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for COrDFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< COrDFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< COrDFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = c_or_d_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureLocalInAnonStructWrapperFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecParser > :: spec_parse) ;
                capture_local_in_anon_struct_wrapper_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureLocalInAnonStructWrapperFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_local_in_anon_struct_wrapper_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureLocalInAnonStructWrapperFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as Consistency > :: consistent) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureLocalInAnonStructWrapperFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureLocalInAnonStructWrapperFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureLocalInAnonStructWrapperFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as Consistency > :: consistent) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureLocalInAnonStructWrapperFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureLocalInAnonStructWrapperFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureLocalInAnonStructWrapperFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructWrapperFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_local_in_anon_struct_wrapper_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for CaptureLocalInAnonStructFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecParser > :: spec_parse) ;
                capture_local_in_anon_struct_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for CaptureLocalInAnonStructFmt {
            open spec fn productive_inv (& self) -> bool {
                capture_local_in_anon_struct_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for CaptureLocalInAnonStructFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructFmt as Consistency > :: consistent) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for CaptureLocalInAnonStructFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for CaptureLocalInAnonStructFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< CaptureLocalInAnonStructFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< CaptureLocalInAnonStructFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for CaptureLocalInAnonStructFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecParser > :: spec_parse) ;
                reveal (< CaptureLocalInAnonStructFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructFmt as Consistency > :: consistent) ;
                reveal (< CaptureLocalInAnonStructFmt as SpecByteLen > :: byte_len) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for CaptureLocalInAnonStructFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecParser > :: spec_parse) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for CaptureLocalInAnonStructFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< CaptureLocalInAnonStructFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for CaptureLocalInAnonStructFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< CaptureLocalInAnonStructFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< CaptureLocalInAnonStructFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = capture_local_in_anon_struct_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for AOrBFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AOrBFmt as SpecParser > :: spec_parse) ;
                a_or_b_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for AOrBFmt {
            open spec fn productive_inv (& self) -> bool {
                a_or_b_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< AOrBFmt as SpecParser > :: spec_parse) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for AOrBFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AOrBFmt as SpecParser > :: spec_parse) ;
                reveal (< AOrBFmt as SpecByteLen > :: byte_len) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AOrBFmt as SpecParser > :: spec_parse) ;
                reveal (< AOrBFmt as Consistency > :: consistent) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for AOrBFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< AOrBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< AOrBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AOrBFmt as SpecByteLen > :: byte_len) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for AOrBFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< AOrBFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< AOrBFmt as SpecByteLen > :: byte_len) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for AOrBFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< AOrBFmt as SpecParser > :: spec_parse) ;
                reveal (< AOrBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AOrBFmt as Consistency > :: consistent) ;
                reveal (< AOrBFmt as SpecByteLen > :: byte_len) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for AOrBFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< AOrBFmt as SpecParser > :: spec_parse) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for AOrBFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< AOrBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AOrBFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for AOrBFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< AOrBFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AOrBFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = a_or_b_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }
    }

    // ============================================================
    // Executable Implementations
    // ============================================================
    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureParamAndLocalXAPayload


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureParamAndLocalXA


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureParamAndLocalXBY


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureParamAndLocalXB


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureParamAndLocalX


    // TODO(execs): emit Parser / Serializer / Prepare impls for NestedInnerChoiceXA


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureOuterAndLocalPayloadAnonInnerBody


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureOuterAndLocalPayload


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureOuterAndLocal


    // TODO(execs): emit Parser / Serializer / Prepare impls for NestedInnerStructAnonInner


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureLocalInAnonStructWrapperValueChoice0


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureLocalInAnonStructWrapperValue


    // TODO(execs): emit Parser / Serializer / Prepare impls for NestedInnerChoiceX


    // TODO(execs): emit Parser / Serializer / Prepare impls for NestedInnerChoice


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureParamAndLocal


    // TODO(execs): emit Parser / Serializer / Prepare impls for NestedInnerStruct


    // TODO(execs): emit Parser / Serializer / Prepare impls for COrD


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureLocalInAnonStructWrapper


    // TODO(execs): emit Parser / Serializer / Prepare impls for CaptureLocalInAnonStruct


    // TODO(execs): emit Parser / Serializer / Prepare impls for AOrB
}

