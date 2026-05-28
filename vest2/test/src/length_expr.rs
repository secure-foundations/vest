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
    # [doc = "data type for `header`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct Header {
        pub len : u16 ,
        pub flags : u8 ,
    }
    # [verifier :: ext_equal]
    pub struct HeaderSpec {
        pub len : u16 ,
        pub flags : u8 ,
    }
    pub type HeaderInner = (u16 , u8) ;
    impl DeepView for Header {
        type V = HeaderSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            HeaderSpec {
                len : self . len . deep_view () ,
                flags : self . flags . deep_view () ,
            }
        }
    }

    # [doc = "data type for `header_alias`."]
    pub type HeaderAlias = Header ;
    pub type HeaderAliasSpec = HeaderSpec ;


    # [doc = "data type for `divide`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct Divide < 'i > {
        pub chunks : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct DivideSpec {
        pub chunks : Seq < u8 > ,
    }
    pub type DivideInner = Seq < u8 > ;
    impl < 'i > DeepView for Divide < 'i > {
        type V = DivideSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            DivideSpec {
                chunks : self . chunks . deep_view () ,
            }
        }
    }

    # [doc = "data type for `fixed_choice`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum FixedChoice {
        Variant1 (u16) ,
        Default (u16) ,
    }
    # [verifier :: ext_equal]
    pub enum FixedChoiceSpec {
        Variant1 (u16) ,
        Default (u16) ,
    }
    pub type FixedChoiceInner = Sum < u16 , u16 > ;
    impl DeepView for FixedChoice {
        type V = FixedChoiceSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                FixedChoice :: Variant1 (v) => FixedChoiceSpec :: Variant1 (v . deep_view ()) ,
                FixedChoice :: Default (v) => FixedChoiceSpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `simple_sub`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct SimpleSub < 'i > {
        pub data : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct SimpleSubSpec {
        pub data : Seq < u8 > ,
    }
    pub type SimpleSubInner = Seq < u8 > ;
    impl < 'i > DeepView for SimpleSub < 'i > {
        type V = SimpleSubSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            SimpleSubSpec {
                data : self . data . deep_view () ,
            }
        }
    }

    # [doc = "data type for `alias_size`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct AliasSize < 'i > {
        pub bytes : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct AliasSizeSpec {
        pub bytes : Seq < u8 > ,
    }
    pub type AliasSizeInner = Seq < u8 > ;
    impl < 'i > DeepView for AliasSize < 'i > {
        type V = AliasSizeSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            AliasSizeSpec {
                bytes : self . bytes . deep_view () ,
            }
        }
    }

    # [doc = "data type for `multi_arith`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct MultiArith < 'i > {
        pub body : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct MultiArithSpec {
        pub body : Seq < u8 > ,
    }
    pub type MultiArithInner = Seq < u8 > ;
    impl < 'i > DeepView for MultiArith < 'i > {
        type V = MultiArithSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MultiArithSpec {
                body : self . body . deep_view () ,
            }
        }
    }

    # [doc = "data type for `size_arith`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct SizeArith < 'i > {
        pub bytes : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct SizeArithSpec {
        pub bytes : Seq < u8 > ,
    }
    pub type SizeArithInner = Seq < u8 > ;
    impl < 'i > DeepView for SizeArith < 'i > {
        type V = SizeArithSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            SizeArithSpec {
                bytes : self . bytes . deep_view () ,
            }
        }
    }

    # [doc = "data type for `payload_with_header`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct PayloadWithHeader < 'i > {
        pub data : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct PayloadWithHeaderSpec {
        pub data : Seq < u8 > ,
    }
    pub type PayloadWithHeaderInner = Seq < u8 > ;
    impl < 'i > DeepView for PayloadWithHeader < 'i > {
        type V = PayloadWithHeaderSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            PayloadWithHeaderSpec {
                data : self . data . deep_view () ,
            }
        }
    }

    # [doc = "data type for `mixed_const`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct MixedConst < 'i > {
        pub data : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct MixedConstSpec {
        pub data : Seq < u8 > ,
    }
    pub type MixedConstInner = Seq < u8 > ;
    impl < 'i > DeepView for MixedConst < 'i > {
        type V = MixedConstSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MixedConstSpec {
                data : self . data . deep_view () ,
            }
        }
    }

    # [doc = "data type for `choice_tag`."]
    pub type ChoiceTag < 'i > = & 'i [u8] ;
    pub type ChoiceTagSpec = Seq < u8 > ;


    # [doc = "data type for `named_size`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct NamedSize < 'i > {
        pub bytes : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct NamedSizeSpec {
        pub bytes : Seq < u8 > ,
    }
    pub type NamedSizeInner = Seq < u8 > ;
    impl < 'i > DeepView for NamedSize < 'i > {
        type V = NamedSizeSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            NamedSizeSpec {
                bytes : self . bytes . deep_view () ,
            }
        }
    }

    # [doc = "data type for `choice_format_size`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct ChoiceFormatSize < 'i > {
        pub bytes : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct ChoiceFormatSizeSpec {
        pub bytes : Seq < u8 > ,
    }
    pub type ChoiceFormatSizeInner = Seq < u8 > ;
    impl < 'i > DeepView for ChoiceFormatSize < 'i > {
        type V = ChoiceFormatSizeSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            ChoiceFormatSizeSpec {
                bytes : self . bytes . deep_view () ,
            }
        }
    }

    # [doc = "data type for `header_bytes`."]
    pub type HeaderBytes = Header ;
    pub type HeaderBytesSpec = HeaderSpec ;


    # [doc = "data type for `multiply`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct Multiply < 'i > {
        pub items : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct MultiplySpec {
        pub items : Seq < u8 > ,
    }
    pub type MultiplyInner = Seq < u8 > ;
    impl < 'i > DeepView for Multiply < 'i > {
        type V = MultiplySpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MultiplySpec {
                items : self . items . deep_view () ,
            }
        }
    }

    # [doc = "data type for `choice_arrays_folded_body`."]
    # [derive (Debug , PartialEq , Eq)]
    pub enum ChoiceArraysFoldedBody {
        Variant1 (u8) ,
        Variant2 (u16) ,
        Default (u16) ,
    }
    # [verifier :: ext_equal]
    pub enum ChoiceArraysFoldedBodySpec {
        Variant1 (u8) ,
        Variant2 (u16) ,
        Default (u16) ,
    }
    pub type ChoiceArraysFoldedBodyInner = Sum < u8 , Sum < u16 , u16 > > ;
    impl DeepView for ChoiceArraysFoldedBody {
        type V = ChoiceArraysFoldedBodySpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                ChoiceArraysFoldedBody :: Variant1 (v) => ChoiceArraysFoldedBodySpec :: Variant1 (v . deep_view ()) ,
                ChoiceArraysFoldedBody :: Variant2 (v) => ChoiceArraysFoldedBodySpec :: Variant2 (v . deep_view ()) ,
                ChoiceArraysFoldedBody :: Default (v) => ChoiceArraysFoldedBodySpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `choice_arrays_folded`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct ChoiceArraysFolded < 'i > {
        pub tag : ChoiceTag < 'i > ,
        pub body : ChoiceArraysFoldedBody ,
    }
    # [verifier :: ext_equal]
    pub struct ChoiceArraysFoldedSpec {
        pub tag : ChoiceTagSpec ,
        pub body : ChoiceArraysFoldedBodySpec ,
    }
    pub type ChoiceArraysFoldedInner = (ChoiceTagSpec , ChoiceArraysFoldedBodySpec) ;
    impl < 'i > DeepView for ChoiceArraysFolded < 'i > {
        type V = ChoiceArraysFoldedSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            ChoiceArraysFoldedSpec {
                tag : self . tag . deep_view () ,
                body : self . body . deep_view () ,
            }
        }
    }

    # [doc = "data type for `paren_expr`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct ParenExpr < 'i > {
        pub data : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct ParenExprSpec {
        pub data : Seq < u8 > ,
    }
    pub type ParenExprInner = Seq < u8 > ;
    impl < 'i > DeepView for ParenExpr < 'i > {
        type V = ParenExprSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            ParenExprSpec {
                data : self . data . deep_view () ,
            }
        }
    }

    # [doc = "data type for `reinterpret_size`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct ReinterpretSize < 'i > {
        pub bytes : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct ReinterpretSizeSpec {
        pub bytes : Seq < u8 > ,
    }
    pub type ReinterpretSizeInner = Seq < u8 > ;
    impl < 'i > DeepView for ReinterpretSize < 'i > {
        type V = ReinterpretSizeSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            ReinterpretSizeSpec {
                bytes : self . bytes . deep_view () ,
            }
        }
    }

    # [doc = "data type for `primitive_sizes`."]
    # [derive (Debug , PartialEq , Eq)]
    pub struct PrimitiveSizes < 'i > {
        pub byte : & 'i [u8] ,
        pub word : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct PrimitiveSizesSpec {
        pub byte : Seq < u8 > ,
        pub word : Seq < u8 > ,
    }
    pub type PrimitiveSizesInner = (Seq < u8 > , Seq < u8 >) ;
    impl < 'i > DeepView for PrimitiveSizes < 'i > {
        type V = PrimitiveSizesSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            PrimitiveSizesSpec {
                byte : self . byte . deep_view () ,
                word : self . word . deep_view () ,
            }
        }
    }

    // ============================================================
    // Format Specifications
    // ============================================================
    # [doc = "named format combinator for `header`."]
    pub struct HeaderFmt ;

    pub type HeaderFmtSpec = Named < Mapped < Bind < Refined < U16Le , PredFnSpec < u16 >> , spec_fn (u16) -> U8 > , FnSpecMapper < HeaderInner , HeaderSpec >> > ;

    # [doc = "specification constructor for `header`."]
    pub open spec fn header_fmt () -> HeaderFmtSpec {
        Named ("header" ,
        Mapped {
            inner : Bind (Refined (U16Le ,
            | x : u16 | x >= 3 && x <= 65535) ,
            | len : u16 | U8) ,
            mapper : (| parsed : HeaderInner | -> HeaderSpec {
                let (len ,
                flags) = parsed ;
                HeaderSpec {
                    len ,
                    flags
                }
            }
            ,
            | value : HeaderSpec | -> HeaderInner {
                let HeaderSpec {
                    len ,
                    flags
                }
                = value ;
                (len ,
                flags)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `header_alias`."]
    pub struct HeaderAliasFmt ;
    pub type HeaderAliasFmtSpec = HeaderFmtSpec ;
    # [doc = "specification constructor for `header_alias`."]
    pub open spec fn header_alias_fmt () -> HeaderAliasFmtSpec {
        header_fmt ()
    }

    # [doc = "named format combinator for `divide`."]
    pub struct DivideFmt {
        pub total : u32 ,
    }

    pub type DivideFmtSpec = Named < Mapped < Varied < usize > , FnSpecMapper < DivideInner , DivideSpec >> > ;

    # [doc = "specification constructor for `divide`."]
    pub open spec fn divide_fmt (total : u32) -> DivideFmtSpec {
        Named ("divide" ,
        Mapped {
            inner : Varied ((((total as usize) / 4) as usize)) ,
            mapper : (| parsed : DivideInner | -> DivideSpec {
                let chunks = parsed ;
                DivideSpec {
                    chunks
                }
            }
            ,
            | value : DivideSpec | -> DivideInner {
                let DivideSpec {
                    chunks
                }
                = value ;
                chunks
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `fixed_choice`."]
    pub struct FixedChoiceFmt {
        pub tag : u8 ,
    }

    pub type FixedChoiceFmtSpec = Named < Mapped < Sum < U16Le , U16Le > , FnSpecMapper < FixedChoiceInner , FixedChoiceSpec >> > ;

    # [doc = "specification constructor for `fixed_choice`."]
    pub open spec fn fixed_choice_fmt (tag : u8) -> FixedChoiceFmtSpec {
        Named ("fixed_choice" ,
        Mapped {
            inner : match tag {
                0 => Sum :: Inl (U16Le) ,
                _ => Sum :: Inr (U16Le) ,
            }
            ,
            mapper : (| parsed : FixedChoiceInner | -> FixedChoiceSpec {
                match parsed {
                    Sum :: Inl (v) => FixedChoiceSpec :: Variant1 (v) ,
                    Sum :: Inr (v) => FixedChoiceSpec :: Default (v) ,
                }
            }
            ,
            | value : FixedChoiceSpec | -> FixedChoiceInner {
                match value {
                    FixedChoiceSpec :: Variant1 (v) => Sum :: Inl (v) ,
                    FixedChoiceSpec :: Default (v) => Sum :: Inr (v) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `simple_sub`."]
    pub struct SimpleSubFmt {
        pub len : u16 ,
    }

    pub type SimpleSubFmtSpec = Named < Mapped < Varied < usize > , FnSpecMapper < SimpleSubInner , SimpleSubSpec >> > ;

    # [doc = "specification constructor for `simple_sub`."]
    pub open spec fn simple_sub_fmt (len : u16) -> SimpleSubFmtSpec {
        Named ("simple_sub" ,
        Mapped {
            inner : Varied ((((((len as usize) - 3) as usize) - 1) as usize)) ,
            mapper : (| parsed : SimpleSubInner | -> SimpleSubSpec {
                let data = parsed ;
                SimpleSubSpec {
                    data
                }
            }
            ,
            | value : SimpleSubSpec | -> SimpleSubInner {
                let SimpleSubSpec {
                    data
                }
                = value ;
                data
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `alias_size`."]
    pub struct AliasSizeFmt ;

    pub type AliasSizeFmtSpec = Named < Mapped < Fixed < 3 > , FnSpecMapper < AliasSizeInner , AliasSizeSpec >> > ;

    # [doc = "specification constructor for `alias_size`."]
    pub open spec fn alias_size_fmt () -> AliasSizeFmtSpec {
        Named ("alias_size" ,
        Mapped {
            inner : Fixed :: < 3 > ,
            mapper : (| parsed : AliasSizeInner | -> AliasSizeSpec {
                let bytes = parsed ;
                AliasSizeSpec {
                    bytes
                }
            }
            ,
            | value : AliasSizeSpec | -> AliasSizeInner {
                let AliasSizeSpec {
                    bytes
                }
                = value ;
                bytes
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `multi_arith`."]
    pub struct MultiArithFmt {
        pub total : u32 ,
        pub hdr_len : u8 ,
    }

    pub type MultiArithFmtSpec = Named < Mapped < Varied < usize > , FnSpecMapper < MultiArithInner , MultiArithSpec >> > ;

    # [doc = "specification constructor for `multi_arith`."]
    pub open spec fn multi_arith_fmt (total : u32 , hdr_len : u8) -> MultiArithFmtSpec {
        Named ("multi_arith" ,
        Mapped {
            inner : Varied ((((((total as usize) - (hdr_len as usize)) as usize) - 8) as usize)) ,
            mapper : (| parsed : MultiArithInner | -> MultiArithSpec {
                let body = parsed ;
                MultiArithSpec {
                    body
                }
            }
            ,
            | value : MultiArithSpec | -> MultiArithInner {
                let MultiArithSpec {
                    body
                }
                = value ;
                body
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `size_arith`."]
    pub struct SizeArithFmt ;

    pub type SizeArithFmtSpec = Named < Mapped < Fixed < 4 > , FnSpecMapper < SizeArithInner , SizeArithSpec >> > ;

    # [doc = "specification constructor for `size_arith`."]
    pub open spec fn size_arith_fmt () -> SizeArithFmtSpec {
        Named ("size_arith" ,
        Mapped {
            inner : Fixed :: < 4 > ,
            mapper : (| parsed : SizeArithInner | -> SizeArithSpec {
                let bytes = parsed ;
                SizeArithSpec {
                    bytes
                }
            }
            ,
            | value : SizeArithSpec | -> SizeArithInner {
                let SizeArithSpec {
                    bytes
                }
                = value ;
                bytes
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `payload_with_header`."]
    pub struct PayloadWithHeaderFmt {
        pub hdr : Header ,
    }

    pub type PayloadWithHeaderFmtSpec = Named < Mapped < Varied < usize > , FnSpecMapper < PayloadWithHeaderInner , PayloadWithHeaderSpec >> > ;

    # [doc = "specification constructor for `payload_with_header`."]
    pub open spec fn payload_with_header_fmt (hdr : HeaderSpec) -> PayloadWithHeaderFmtSpec {
        Named ("payload_with_header" ,
        Mapped {
            inner : Varied ((((hdr . len as usize) - 3) as usize)) ,
            mapper : (| parsed : PayloadWithHeaderInner | -> PayloadWithHeaderSpec {
                let data = parsed ;
                PayloadWithHeaderSpec {
                    data
                }
            }
            ,
            | value : PayloadWithHeaderSpec | -> PayloadWithHeaderInner {
                let PayloadWithHeaderSpec {
                    data
                }
                = value ;
                data
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `mixed_const`."]
    pub struct MixedConstFmt {
        pub len : u16 ,
    }

    pub type MixedConstFmtSpec = Named < Mapped < Varied < usize > , FnSpecMapper < MixedConstInner , MixedConstSpec >> > ;

    # [doc = "specification constructor for `mixed_const`."]
    pub open spec fn mixed_const_fmt (len : u16) -> MixedConstFmtSpec {
        Named ("mixed_const" ,
        Mapped {
            inner : Varied ((((((len as usize) - 4) as usize) + 2) as usize)) ,
            mapper : (| parsed : MixedConstInner | -> MixedConstSpec {
                let data = parsed ;
                MixedConstSpec {
                    data
                }
            }
            ,
            | value : MixedConstSpec | -> MixedConstInner {
                let MixedConstSpec {
                    data
                }
                = value ;
                data
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `choice_tag`."]
    pub struct ChoiceTagFmt ;

    pub type ChoiceTagFmtSpec = Named < Fixed < 2 > > ;

    # [doc = "specification constructor for `choice_tag`."]
    pub open spec fn choice_tag_fmt () -> ChoiceTagFmtSpec {
        Named ("choice_tag" ,
        Fixed :: < 2 >)
    }


    # [doc = "named format combinator for `named_size`."]
    pub struct NamedSizeFmt ;

    pub type NamedSizeFmtSpec = Named < Mapped < Fixed < 3 > , FnSpecMapper < NamedSizeInner , NamedSizeSpec >> > ;

    # [doc = "specification constructor for `named_size`."]
    pub open spec fn named_size_fmt () -> NamedSizeFmtSpec {
        Named ("named_size" ,
        Mapped {
            inner : Fixed :: < 3 > ,
            mapper : (| parsed : NamedSizeInner | -> NamedSizeSpec {
                let bytes = parsed ;
                NamedSizeSpec {
                    bytes
                }
            }
            ,
            | value : NamedSizeSpec | -> NamedSizeInner {
                let NamedSizeSpec {
                    bytes
                }
                = value ;
                bytes
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `choice_format_size`."]
    pub struct ChoiceFormatSizeFmt ;

    pub type ChoiceFormatSizeFmtSpec = Named < Mapped < Fixed < 2 > , FnSpecMapper < ChoiceFormatSizeInner , ChoiceFormatSizeSpec >> > ;

    # [doc = "specification constructor for `choice_format_size`."]
    pub open spec fn choice_format_size_fmt () -> ChoiceFormatSizeFmtSpec {
        Named ("choice_format_size" ,
        Mapped {
            inner : Fixed :: < 2 > ,
            mapper : (| parsed : ChoiceFormatSizeInner | -> ChoiceFormatSizeSpec {
                let bytes = parsed ;
                ChoiceFormatSizeSpec {
                    bytes
                }
            }
            ,
            | value : ChoiceFormatSizeSpec | -> ChoiceFormatSizeInner {
                let ChoiceFormatSizeSpec {
                    bytes
                }
                = value ;
                bytes
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `header_bytes`."]
    pub struct HeaderBytesFmt ;

    pub type HeaderBytesFmtSpec = Named < ExactLen < HeaderFmt , usize > > ;

    # [doc = "specification constructor for `header_bytes`."]
    pub open spec fn header_bytes_fmt () -> HeaderBytesFmtSpec {
        Named ("header_bytes" ,
        ExactLen (3 ,
        HeaderFmt))
    }


    # [doc = "named format combinator for `multiply`."]
    pub struct MultiplyFmt {
        pub count : u16 ,
        pub size : u8 ,
    }

    pub type MultiplyFmtSpec = Named < Mapped < Varied < usize > , FnSpecMapper < MultiplyInner , MultiplySpec >> > ;

    # [doc = "specification constructor for `multiply`."]
    pub open spec fn multiply_fmt (count : u16 , size : u8) -> MultiplyFmtSpec {
        Named ("multiply" ,
        Mapped {
            inner : Varied ((((count as usize) * (size as usize)) as usize)) ,
            mapper : (| parsed : MultiplyInner | -> MultiplySpec {
                let items = parsed ;
                MultiplySpec {
                    items
                }
            }
            ,
            | value : MultiplySpec | -> MultiplyInner {
                let MultiplySpec {
                    items
                }
                = value ;
                items
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `choice_arrays_folded_body`."]
    pub struct ChoiceArraysFoldedBodyFmt < 'i > {
        pub tag : ChoiceTag < 'i > ,
    }

    pub type ChoiceArraysFoldedBodyFmtSpec = Named < Mapped < Sum < U8 , Sum < U16Le , U16Le > > , FnSpecMapper < ChoiceArraysFoldedBodyInner , ChoiceArraysFoldedBodySpec >> > ;

    # [doc = "specification constructor for `choice_arrays_folded_body`."]
    pub open spec fn choice_arrays_folded_body_fmt (tag : ChoiceTagSpec) -> ChoiceArraysFoldedBodyFmtSpec {
        Named ("choice_arrays_folded_body" ,
        Mapped {
            inner : match tag {
                x if x == seq ! [0u8 ;
                2] => Sum :: Inl (U8) ,
                x if x == seq ! [1u8 ;
                2] => Sum :: Inr (Sum :: Inl (U16Le)) ,
                _ => Sum :: Inr (Sum :: Inr (U16Le)) ,
            }
            ,
            mapper : (| parsed : ChoiceArraysFoldedBodyInner | -> ChoiceArraysFoldedBodySpec {
                match parsed {
                    Sum :: Inl (v) => ChoiceArraysFoldedBodySpec :: Variant1 (v) ,
                    Sum :: Inr (Sum :: Inl (v)) => ChoiceArraysFoldedBodySpec :: Variant2 (v) ,
                    Sum :: Inr (Sum :: Inr (v)) => ChoiceArraysFoldedBodySpec :: Default (v) ,
                }
            }
            ,
            | value : ChoiceArraysFoldedBodySpec | -> ChoiceArraysFoldedBodyInner {
                match value {
                    ChoiceArraysFoldedBodySpec :: Variant1 (v) => Sum :: Inl (v) ,
                    ChoiceArraysFoldedBodySpec :: Variant2 (v) => Sum :: Inr (Sum :: Inl (v)) ,
                    ChoiceArraysFoldedBodySpec :: Default (v) => Sum :: Inr (Sum :: Inr (v)) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `choice_arrays_folded`."]
    pub struct ChoiceArraysFoldedFmt ;

    pub type ChoiceArraysFoldedFmtSpec = Named < Mapped < Bind < ChoiceTagFmt , spec_fn (ChoiceTagSpec) -> ChoiceArraysFoldedBodyFmtSpec > , FnSpecMapper < ChoiceArraysFoldedInner , ChoiceArraysFoldedSpec >> > ;

    # [doc = "specification constructor for `choice_arrays_folded`."]
    pub open spec fn choice_arrays_folded_fmt () -> ChoiceArraysFoldedFmtSpec {
        Named ("choice_arrays_folded" ,
        Mapped {
            inner : Bind (ChoiceTagFmt ,
            | tag : ChoiceTagSpec | choice_arrays_folded_body_fmt (tag)) ,
            mapper : (| parsed : ChoiceArraysFoldedInner | -> ChoiceArraysFoldedSpec {
                let (tag ,
                body) = parsed ;
                ChoiceArraysFoldedSpec {
                    tag ,
                    body
                }
            }
            ,
            | value : ChoiceArraysFoldedSpec | -> ChoiceArraysFoldedInner {
                let ChoiceArraysFoldedSpec {
                    tag ,
                    body
                }
                = value ;
                (tag ,
                body)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `paren_expr`."]
    pub struct ParenExprFmt {
        pub a : u16 ,
        pub b : u8 ,
        pub c : u8 ,
    }

    pub type ParenExprFmtSpec = Named < Mapped < Varied < usize > , FnSpecMapper < ParenExprInner , ParenExprSpec >> > ;

    # [doc = "specification constructor for `paren_expr`."]
    pub open spec fn paren_expr_fmt (a : u16 , b : u8 , c : u8) -> ParenExprFmtSpec {
        Named ("paren_expr" ,
        Mapped {
            inner : Varied ((((((a as usize) - (b as usize)) as usize) * (c as usize)) as usize)) ,
            mapper : (| parsed : ParenExprInner | -> ParenExprSpec {
                let data = parsed ;
                ParenExprSpec {
                    data
                }
            }
            ,
            | value : ParenExprSpec | -> ParenExprInner {
                let ParenExprSpec {
                    data
                }
                = value ;
                data
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `reinterpret_size`."]
    pub struct ReinterpretSizeFmt ;

    pub type ReinterpretSizeFmtSpec = Named < Mapped < Fixed < 3 > , FnSpecMapper < ReinterpretSizeInner , ReinterpretSizeSpec >> > ;

    # [doc = "specification constructor for `reinterpret_size`."]
    pub open spec fn reinterpret_size_fmt () -> ReinterpretSizeFmtSpec {
        Named ("reinterpret_size" ,
        Mapped {
            inner : Fixed :: < 3 > ,
            mapper : (| parsed : ReinterpretSizeInner | -> ReinterpretSizeSpec {
                let bytes = parsed ;
                ReinterpretSizeSpec {
                    bytes
                }
            }
            ,
            | value : ReinterpretSizeSpec | -> ReinterpretSizeInner {
                let ReinterpretSizeSpec {
                    bytes
                }
                = value ;
                bytes
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `primitive_sizes`."]
    pub struct PrimitiveSizesFmt ;

    pub type PrimitiveSizesFmtSpec = Named < Mapped < Pair < Fixed < 1 > , Fixed < 2 > > , FnSpecMapper < PrimitiveSizesInner , PrimitiveSizesSpec >> > ;

    # [doc = "specification constructor for `primitive_sizes`."]
    pub open spec fn primitive_sizes_fmt () -> PrimitiveSizesFmtSpec {
        Named ("primitive_sizes" ,
        Mapped {
            inner : Pair (Fixed :: < 1 > ,
            Fixed :: < 2 >) ,
            mapper : (| parsed : PrimitiveSizesInner | -> PrimitiveSizesSpec {
                let (byte ,
                word) = parsed ;
                PrimitiveSizesSpec {
                    byte ,
                    word
                }
            }
            ,
            | value : PrimitiveSizesSpec | -> PrimitiveSizesInner {
                let PrimitiveSizesSpec {
                    byte ,
                    word
                }
                = value ;
                (byte ,
                word)
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

        impl SpecParser for HeaderFmt {
            type PVal = HeaderSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                header_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for HeaderFmt {
            type Val = HeaderSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                header_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for HeaderFmt {
            type SValue = HeaderSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                header_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for HeaderFmt {
            type SVal = HeaderSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                header_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for HeaderFmt {
            type T = HeaderSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                header_fmt () . byte_len (v)
            }
        }

        impl SpecParser for HeaderAliasFmt {
            type PVal = HeaderAliasSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                header_alias_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for HeaderAliasFmt {
            type Val = HeaderAliasSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                header_alias_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for HeaderAliasFmt {
            type SValue = HeaderAliasSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                header_alias_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for HeaderAliasFmt {
            type SVal = HeaderAliasSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                header_alias_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for HeaderAliasFmt {
            type T = HeaderAliasSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                header_alias_fmt () . byte_len (v)
            }
        }

        impl SpecParser for DivideFmt {
            type PVal = DivideSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                divide_fmt (self . total . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for DivideFmt {
            type Val = DivideSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                divide_fmt (self . total . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for DivideFmt {
            type SValue = DivideSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                divide_fmt (self . total . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for DivideFmt {
            type SVal = DivideSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                divide_fmt (self . total . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for DivideFmt {
            type T = DivideSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                divide_fmt (self . total . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for FixedChoiceFmt {
            type PVal = FixedChoiceSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                fixed_choice_fmt (self . tag . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for FixedChoiceFmt {
            type Val = FixedChoiceSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                fixed_choice_fmt (self . tag . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for FixedChoiceFmt {
            type SValue = FixedChoiceSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                fixed_choice_fmt (self . tag . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for FixedChoiceFmt {
            type SVal = FixedChoiceSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                fixed_choice_fmt (self . tag . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for FixedChoiceFmt {
            type T = FixedChoiceSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                fixed_choice_fmt (self . tag . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for SimpleSubFmt {
            type PVal = SimpleSubSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                simple_sub_fmt (self . len . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for SimpleSubFmt {
            type Val = SimpleSubSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                simple_sub_fmt (self . len . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for SimpleSubFmt {
            type SValue = SimpleSubSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                simple_sub_fmt (self . len . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for SimpleSubFmt {
            type SVal = SimpleSubSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                simple_sub_fmt (self . len . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for SimpleSubFmt {
            type T = SimpleSubSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                simple_sub_fmt (self . len . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for AliasSizeFmt {
            type PVal = AliasSizeSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                alias_size_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for AliasSizeFmt {
            type Val = AliasSizeSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                alias_size_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for AliasSizeFmt {
            type SValue = AliasSizeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                alias_size_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for AliasSizeFmt {
            type SVal = AliasSizeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                alias_size_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for AliasSizeFmt {
            type T = AliasSizeSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                alias_size_fmt () . byte_len (v)
            }
        }

        impl SpecParser for MultiArithFmt {
            type PVal = MultiArithSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for MultiArithFmt {
            type Val = MultiArithSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for MultiArithFmt {
            type SValue = MultiArithSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MultiArithFmt {
            type SVal = MultiArithSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for MultiArithFmt {
            type T = MultiArithSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for SizeArithFmt {
            type PVal = SizeArithSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                size_arith_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for SizeArithFmt {
            type Val = SizeArithSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                size_arith_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for SizeArithFmt {
            type SValue = SizeArithSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                size_arith_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for SizeArithFmt {
            type SVal = SizeArithSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                size_arith_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for SizeArithFmt {
            type T = SizeArithSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                size_arith_fmt () . byte_len (v)
            }
        }

        impl SpecParser for PayloadWithHeaderFmt {
            type PVal = PayloadWithHeaderSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                payload_with_header_fmt (self . hdr . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for PayloadWithHeaderFmt {
            type Val = PayloadWithHeaderSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                payload_with_header_fmt (self . hdr . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for PayloadWithHeaderFmt {
            type SValue = PayloadWithHeaderSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                payload_with_header_fmt (self . hdr . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for PayloadWithHeaderFmt {
            type SVal = PayloadWithHeaderSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                payload_with_header_fmt (self . hdr . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for PayloadWithHeaderFmt {
            type T = PayloadWithHeaderSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                payload_with_header_fmt (self . hdr . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for MixedConstFmt {
            type PVal = MixedConstSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                mixed_const_fmt (self . len . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for MixedConstFmt {
            type Val = MixedConstSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                mixed_const_fmt (self . len . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for MixedConstFmt {
            type SValue = MixedConstSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                mixed_const_fmt (self . len . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MixedConstFmt {
            type SVal = MixedConstSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                mixed_const_fmt (self . len . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for MixedConstFmt {
            type T = MixedConstSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                mixed_const_fmt (self . len . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for ChoiceTagFmt {
            type PVal = ChoiceTagSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                choice_tag_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for ChoiceTagFmt {
            type Val = ChoiceTagSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                choice_tag_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for ChoiceTagFmt {
            type SValue = ChoiceTagSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                choice_tag_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for ChoiceTagFmt {
            type SVal = ChoiceTagSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                choice_tag_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for ChoiceTagFmt {
            type T = ChoiceTagSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                choice_tag_fmt () . byte_len (v)
            }
        }

        impl SpecParser for NamedSizeFmt {
            type PVal = NamedSizeSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                named_size_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for NamedSizeFmt {
            type Val = NamedSizeSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                named_size_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for NamedSizeFmt {
            type SValue = NamedSizeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                named_size_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for NamedSizeFmt {
            type SVal = NamedSizeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                named_size_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for NamedSizeFmt {
            type T = NamedSizeSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                named_size_fmt () . byte_len (v)
            }
        }

        impl SpecParser for ChoiceFormatSizeFmt {
            type PVal = ChoiceFormatSizeSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                choice_format_size_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for ChoiceFormatSizeFmt {
            type Val = ChoiceFormatSizeSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                choice_format_size_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for ChoiceFormatSizeFmt {
            type SValue = ChoiceFormatSizeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                choice_format_size_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for ChoiceFormatSizeFmt {
            type SVal = ChoiceFormatSizeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                choice_format_size_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for ChoiceFormatSizeFmt {
            type T = ChoiceFormatSizeSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                choice_format_size_fmt () . byte_len (v)
            }
        }

        impl SpecParser for HeaderBytesFmt {
            type PVal = HeaderBytesSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                header_bytes_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for HeaderBytesFmt {
            type Val = HeaderBytesSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                header_bytes_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for HeaderBytesFmt {
            type SValue = HeaderBytesSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                header_bytes_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for HeaderBytesFmt {
            type SVal = HeaderBytesSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                header_bytes_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for HeaderBytesFmt {
            type T = HeaderBytesSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                header_bytes_fmt () . byte_len (v)
            }
        }

        impl SpecParser for MultiplyFmt {
            type PVal = MultiplySpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for MultiplyFmt {
            type Val = MultiplySpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for MultiplyFmt {
            type SValue = MultiplySpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MultiplyFmt {
            type SVal = MultiplySpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for MultiplyFmt {
            type T = MultiplySpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) . byte_len (v)
            }
        }

        impl < 'i > SpecParser for ChoiceArraysFoldedBodyFmt < 'i > {
            type PVal = ChoiceArraysFoldedBodySpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                choice_arrays_folded_body_fmt (self . tag . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl < 'i > Consistency for ChoiceArraysFoldedBodyFmt < 'i > {
            type Val = ChoiceArraysFoldedBodySpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                choice_arrays_folded_body_fmt (self . tag . deep_view ()) . consistent (v)
            }
        }
        impl < 'i > SpecSerializerDps for ChoiceArraysFoldedBodyFmt < 'i > {
            type SValue = ChoiceArraysFoldedBodySpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                choice_arrays_folded_body_fmt (self . tag . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl < 'i > SpecSerializer for ChoiceArraysFoldedBodyFmt < 'i > {
            type SVal = ChoiceArraysFoldedBodySpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                choice_arrays_folded_body_fmt (self . tag . deep_view ()) . spec_serialize (v)
            }
        }
        impl < 'i > SpecByteLen for ChoiceArraysFoldedBodyFmt < 'i > {
            type T = ChoiceArraysFoldedBodySpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                choice_arrays_folded_body_fmt (self . tag . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for ChoiceArraysFoldedFmt {
            type PVal = ChoiceArraysFoldedSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                choice_arrays_folded_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for ChoiceArraysFoldedFmt {
            type Val = ChoiceArraysFoldedSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                choice_arrays_folded_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for ChoiceArraysFoldedFmt {
            type SValue = ChoiceArraysFoldedSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                choice_arrays_folded_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for ChoiceArraysFoldedFmt {
            type SVal = ChoiceArraysFoldedSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                choice_arrays_folded_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for ChoiceArraysFoldedFmt {
            type T = ChoiceArraysFoldedSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                choice_arrays_folded_fmt () . byte_len (v)
            }
        }

        impl SpecParser for ParenExprFmt {
            type PVal = ParenExprSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for ParenExprFmt {
            type Val = ParenExprSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for ParenExprFmt {
            type SValue = ParenExprSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for ParenExprFmt {
            type SVal = ParenExprSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for ParenExprFmt {
            type T = ParenExprSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for ReinterpretSizeFmt {
            type PVal = ReinterpretSizeSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                reinterpret_size_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for ReinterpretSizeFmt {
            type Val = ReinterpretSizeSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                reinterpret_size_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for ReinterpretSizeFmt {
            type SValue = ReinterpretSizeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                reinterpret_size_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for ReinterpretSizeFmt {
            type SVal = ReinterpretSizeSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                reinterpret_size_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for ReinterpretSizeFmt {
            type T = ReinterpretSizeSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                reinterpret_size_fmt () . byte_len (v)
            }
        }

        impl SpecParser for PrimitiveSizesFmt {
            type PVal = PrimitiveSizesSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                primitive_sizes_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for PrimitiveSizesFmt {
            type Val = PrimitiveSizesSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                primitive_sizes_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for PrimitiveSizesFmt {
            type SValue = PrimitiveSizesSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                primitive_sizes_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for PrimitiveSizesFmt {
            type SVal = PrimitiveSizesSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                primitive_sizes_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for PrimitiveSizesFmt {
            type T = PrimitiveSizesSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                primitive_sizes_fmt () . byte_len (v)
            }
        }
    }

    // ============================================================
    // Proven Format Properties
    // ============================================================
    mod derived_proofs {
        use super::*;
        broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        impl SafeParser for HeaderFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderFmt as SpecParser > :: spec_parse) ;
                header_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for HeaderFmt {
            open spec fn productive_inv (& self) -> bool {
                header_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< HeaderFmt as SpecParser > :: spec_parse) ;
                let fmt = header_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for HeaderFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderFmt as Consistency > :: consistent) ;
                let fmt = header_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for HeaderFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< HeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = header_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< HeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for HeaderFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< HeaderFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< HeaderFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for HeaderFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< HeaderFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderFmt as Consistency > :: consistent) ;
                reveal (< HeaderFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for HeaderFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< HeaderFmt as SpecParser > :: spec_parse) ;
                let fmt = header_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for HeaderFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< HeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = header_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for HeaderFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< HeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = header_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for HeaderAliasFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecParser > :: spec_parse) ;
                header_alias_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for HeaderAliasFmt {
            open spec fn productive_inv (& self) -> bool {
                header_alias_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecParser > :: spec_parse) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for HeaderAliasFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderAliasFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderAliasFmt as Consistency > :: consistent) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for HeaderAliasFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderAliasFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for HeaderAliasFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< HeaderAliasFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< HeaderAliasFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for HeaderAliasFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderAliasFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderAliasFmt as Consistency > :: consistent) ;
                reveal (< HeaderAliasFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for HeaderAliasFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecParser > :: spec_parse) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for HeaderAliasFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< HeaderAliasFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderAliasFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for HeaderAliasFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< HeaderAliasFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderAliasFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = header_alias_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for DivideFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< DivideFmt as SpecParser > :: spec_parse) ;
                divide_fmt (self . total . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for DivideFmt {
            open spec fn productive_inv (& self) -> bool {
                divide_fmt (self . total . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< DivideFmt as SpecParser > :: spec_parse) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for DivideFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< DivideFmt as SpecParser > :: spec_parse) ;
                reveal (< DivideFmt as SpecByteLen > :: byte_len) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< DivideFmt as SpecParser > :: spec_parse) ;
                reveal (< DivideFmt as Consistency > :: consistent) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for DivideFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< DivideFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< DivideFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< DivideFmt as SpecByteLen > :: byte_len) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for DivideFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< DivideFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< DivideFmt as SpecByteLen > :: byte_len) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for DivideFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< DivideFmt as SpecParser > :: spec_parse) ;
                reveal (< DivideFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< DivideFmt as Consistency > :: consistent) ;
                reveal (< DivideFmt as SpecByteLen > :: byte_len) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for DivideFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< DivideFmt as SpecParser > :: spec_parse) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for DivideFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< DivideFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< DivideFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for DivideFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< DivideFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< DivideFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = divide_fmt (self . total . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for FixedChoiceFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecParser > :: spec_parse) ;
                fixed_choice_fmt (self . tag . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for FixedChoiceFmt {
            open spec fn productive_inv (& self) -> bool {
                fixed_choice_fmt (self . tag . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecParser > :: spec_parse) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for FixedChoiceFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecParser > :: spec_parse) ;
                reveal (< FixedChoiceFmt as SpecByteLen > :: byte_len) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecParser > :: spec_parse) ;
                reveal (< FixedChoiceFmt as Consistency > :: consistent) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for FixedChoiceFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< FixedChoiceFmt as SpecByteLen > :: byte_len) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for FixedChoiceFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< FixedChoiceFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< FixedChoiceFmt as SpecByteLen > :: byte_len) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for FixedChoiceFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecParser > :: spec_parse) ;
                reveal (< FixedChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< FixedChoiceFmt as Consistency > :: consistent) ;
                reveal (< FixedChoiceFmt as SpecByteLen > :: byte_len) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for FixedChoiceFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecParser > :: spec_parse) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for FixedChoiceFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< FixedChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< FixedChoiceFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for FixedChoiceFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< FixedChoiceFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< FixedChoiceFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = fixed_choice_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for SimpleSubFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecParser > :: spec_parse) ;
                simple_sub_fmt (self . len . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for SimpleSubFmt {
            open spec fn productive_inv (& self) -> bool {
                simple_sub_fmt (self . len . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecParser > :: spec_parse) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for SimpleSubFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecParser > :: spec_parse) ;
                reveal (< SimpleSubFmt as SpecByteLen > :: byte_len) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecParser > :: spec_parse) ;
                reveal (< SimpleSubFmt as Consistency > :: consistent) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for SimpleSubFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< SimpleSubFmt as SpecByteLen > :: byte_len) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for SimpleSubFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< SimpleSubFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< SimpleSubFmt as SpecByteLen > :: byte_len) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for SimpleSubFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecParser > :: spec_parse) ;
                reveal (< SimpleSubFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< SimpleSubFmt as Consistency > :: consistent) ;
                reveal (< SimpleSubFmt as SpecByteLen > :: byte_len) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for SimpleSubFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecParser > :: spec_parse) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for SimpleSubFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< SimpleSubFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< SimpleSubFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for SimpleSubFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< SimpleSubFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< SimpleSubFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = simple_sub_fmt (self . len . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for AliasSizeFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecParser > :: spec_parse) ;
                alias_size_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for AliasSizeFmt {
            open spec fn productive_inv (& self) -> bool {
                alias_size_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecParser > :: spec_parse) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for AliasSizeFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< AliasSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< AliasSizeFmt as Consistency > :: consistent) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for AliasSizeFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AliasSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for AliasSizeFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< AliasSizeFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< AliasSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for AliasSizeFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< AliasSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AliasSizeFmt as Consistency > :: consistent) ;
                reveal (< AliasSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for AliasSizeFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecParser > :: spec_parse) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for AliasSizeFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< AliasSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AliasSizeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for AliasSizeFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< AliasSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AliasSizeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = alias_size_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MultiArithFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecParser > :: spec_parse) ;
                multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MultiArithFmt {
            open spec fn productive_inv (& self) -> bool {
                multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecParser > :: spec_parse) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MultiArithFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecParser > :: spec_parse) ;
                reveal (< MultiArithFmt as SpecByteLen > :: byte_len) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecParser > :: spec_parse) ;
                reveal (< MultiArithFmt as Consistency > :: consistent) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MultiArithFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MultiArithFmt as SpecByteLen > :: byte_len) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for MultiArithFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MultiArithFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MultiArithFmt as SpecByteLen > :: byte_len) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MultiArithFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecParser > :: spec_parse) ;
                reveal (< MultiArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MultiArithFmt as Consistency > :: consistent) ;
                reveal (< MultiArithFmt as SpecByteLen > :: byte_len) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MultiArithFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecParser > :: spec_parse) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for MultiArithFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< MultiArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MultiArithFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for MultiArithFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MultiArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MultiArithFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = multi_arith_fmt (self . total . deep_view () ,
                self . hdr_len . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for SizeArithFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecParser > :: spec_parse) ;
                size_arith_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for SizeArithFmt {
            open spec fn productive_inv (& self) -> bool {
                size_arith_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecParser > :: spec_parse) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for SizeArithFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecParser > :: spec_parse) ;
                reveal (< SizeArithFmt as SpecByteLen > :: byte_len) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecParser > :: spec_parse) ;
                reveal (< SizeArithFmt as Consistency > :: consistent) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for SizeArithFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< SizeArithFmt as SpecByteLen > :: byte_len) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for SizeArithFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< SizeArithFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< SizeArithFmt as SpecByteLen > :: byte_len) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for SizeArithFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecParser > :: spec_parse) ;
                reveal (< SizeArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< SizeArithFmt as Consistency > :: consistent) ;
                reveal (< SizeArithFmt as SpecByteLen > :: byte_len) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for SizeArithFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecParser > :: spec_parse) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for SizeArithFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< SizeArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< SizeArithFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for SizeArithFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< SizeArithFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< SizeArithFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = size_arith_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for PayloadWithHeaderFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecParser > :: spec_parse) ;
                payload_with_header_fmt (self . hdr . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for PayloadWithHeaderFmt {
            open spec fn productive_inv (& self) -> bool {
                payload_with_header_fmt (self . hdr . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecParser > :: spec_parse) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for PayloadWithHeaderFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecParser > :: spec_parse) ;
                reveal (< PayloadWithHeaderFmt as SpecByteLen > :: byte_len) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecParser > :: spec_parse) ;
                reveal (< PayloadWithHeaderFmt as Consistency > :: consistent) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for PayloadWithHeaderFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PayloadWithHeaderFmt as SpecByteLen > :: byte_len) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for PayloadWithHeaderFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< PayloadWithHeaderFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< PayloadWithHeaderFmt as SpecByteLen > :: byte_len) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for PayloadWithHeaderFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecParser > :: spec_parse) ;
                reveal (< PayloadWithHeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PayloadWithHeaderFmt as Consistency > :: consistent) ;
                reveal (< PayloadWithHeaderFmt as SpecByteLen > :: byte_len) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for PayloadWithHeaderFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecParser > :: spec_parse) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for PayloadWithHeaderFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< PayloadWithHeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PayloadWithHeaderFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for PayloadWithHeaderFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< PayloadWithHeaderFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PayloadWithHeaderFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = payload_with_header_fmt (self . hdr . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MixedConstFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecParser > :: spec_parse) ;
                mixed_const_fmt (self . len . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MixedConstFmt {
            open spec fn productive_inv (& self) -> bool {
                mixed_const_fmt (self . len . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecParser > :: spec_parse) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MixedConstFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecParser > :: spec_parse) ;
                reveal (< MixedConstFmt as SpecByteLen > :: byte_len) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecParser > :: spec_parse) ;
                reveal (< MixedConstFmt as Consistency > :: consistent) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MixedConstFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MixedConstFmt as SpecByteLen > :: byte_len) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for MixedConstFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MixedConstFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MixedConstFmt as SpecByteLen > :: byte_len) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MixedConstFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecParser > :: spec_parse) ;
                reveal (< MixedConstFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MixedConstFmt as Consistency > :: consistent) ;
                reveal (< MixedConstFmt as SpecByteLen > :: byte_len) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MixedConstFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecParser > :: spec_parse) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for MixedConstFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< MixedConstFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MixedConstFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for MixedConstFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MixedConstFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MixedConstFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = mixed_const_fmt (self . len . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for ChoiceTagFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecParser > :: spec_parse) ;
                choice_tag_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for ChoiceTagFmt {
            open spec fn productive_inv (& self) -> bool {
                choice_tag_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecParser > :: spec_parse) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for ChoiceTagFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceTagFmt as Consistency > :: consistent) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for ChoiceTagFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for ChoiceTagFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< ChoiceTagFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< ChoiceTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for ChoiceTagFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceTagFmt as Consistency > :: consistent) ;
                reveal (< ChoiceTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for ChoiceTagFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecParser > :: spec_parse) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for ChoiceTagFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceTagFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for ChoiceTagFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< ChoiceTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceTagFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = choice_tag_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for NamedSizeFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecParser > :: spec_parse) ;
                named_size_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for NamedSizeFmt {
            open spec fn productive_inv (& self) -> bool {
                named_size_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecParser > :: spec_parse) ;
                let fmt = named_size_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for NamedSizeFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< NamedSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = named_size_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< NamedSizeFmt as Consistency > :: consistent) ;
                let fmt = named_size_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for NamedSizeFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = named_size_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NamedSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = named_size_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for NamedSizeFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< NamedSizeFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< NamedSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = named_size_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for NamedSizeFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< NamedSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NamedSizeFmt as Consistency > :: consistent) ;
                reveal (< NamedSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = named_size_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for NamedSizeFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecParser > :: spec_parse) ;
                let fmt = named_size_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for NamedSizeFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< NamedSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NamedSizeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = named_size_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for NamedSizeFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< NamedSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< NamedSizeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = named_size_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for ChoiceFormatSizeFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecParser > :: spec_parse) ;
                choice_format_size_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for ChoiceFormatSizeFmt {
            open spec fn productive_inv (& self) -> bool {
                choice_format_size_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecParser > :: spec_parse) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for ChoiceFormatSizeFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceFormatSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceFormatSizeFmt as Consistency > :: consistent) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for ChoiceFormatSizeFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceFormatSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for ChoiceFormatSizeFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< ChoiceFormatSizeFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< ChoiceFormatSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for ChoiceFormatSizeFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceFormatSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceFormatSizeFmt as Consistency > :: consistent) ;
                reveal (< ChoiceFormatSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for ChoiceFormatSizeFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecParser > :: spec_parse) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for ChoiceFormatSizeFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceFormatSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceFormatSizeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for ChoiceFormatSizeFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< ChoiceFormatSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceFormatSizeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = choice_format_size_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for HeaderBytesFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecParser > :: spec_parse) ;
                header_bytes_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for HeaderBytesFmt {
            open spec fn productive_inv (& self) -> bool {
                header_bytes_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecParser > :: spec_parse) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for HeaderBytesFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderBytesFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderBytesFmt as Consistency > :: consistent) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for HeaderBytesFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderBytesFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for HeaderBytesFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< HeaderBytesFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< HeaderBytesFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for HeaderBytesFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecParser > :: spec_parse) ;
                reveal (< HeaderBytesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderBytesFmt as Consistency > :: consistent) ;
                reveal (< HeaderBytesFmt as SpecByteLen > :: byte_len) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for HeaderBytesFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecParser > :: spec_parse) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for HeaderBytesFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< HeaderBytesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderBytesFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for HeaderBytesFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< HeaderBytesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< HeaderBytesFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = header_bytes_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MultiplyFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecParser > :: spec_parse) ;
                multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MultiplyFmt {
            open spec fn productive_inv (& self) -> bool {
                multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecParser > :: spec_parse) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MultiplyFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecParser > :: spec_parse) ;
                reveal (< MultiplyFmt as SpecByteLen > :: byte_len) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecParser > :: spec_parse) ;
                reveal (< MultiplyFmt as Consistency > :: consistent) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MultiplyFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MultiplyFmt as SpecByteLen > :: byte_len) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for MultiplyFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MultiplyFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MultiplyFmt as SpecByteLen > :: byte_len) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MultiplyFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecParser > :: spec_parse) ;
                reveal (< MultiplyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MultiplyFmt as Consistency > :: consistent) ;
                reveal (< MultiplyFmt as SpecByteLen > :: byte_len) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MultiplyFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecParser > :: spec_parse) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for MultiplyFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< MultiplyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MultiplyFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for MultiplyFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MultiplyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MultiplyFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = multiply_fmt (self . count . deep_view () ,
                self . size . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl < 'i > SafeParser for ChoiceArraysFoldedBodyFmt < 'i > {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecParser > :: spec_parse) ;
                choice_arrays_folded_body_fmt (self . tag . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl < 'i > Productive for ChoiceArraysFoldedBodyFmt < 'i > {
            open spec fn productive_inv (& self) -> bool {
                choice_arrays_folded_body_fmt (self . tag . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecParser > :: spec_parse) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl < 'i > SoundParser for ChoiceArraysFoldedBodyFmt < 'i > {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceArraysFoldedBodyFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceArraysFoldedBodyFmt as Consistency > :: consistent) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl < 'i > NonTailFmt for ChoiceArraysFoldedBodyFmt < 'i > {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceArraysFoldedBodyFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl < 'i > GoodSerializer for ChoiceArraysFoldedBodyFmt < 'i > {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< ChoiceArraysFoldedBodyFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl < 'i > SPRoundTripDps for ChoiceArraysFoldedBodyFmt < 'i > {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceArraysFoldedBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceArraysFoldedBodyFmt as Consistency > :: consistent) ;
                reveal (< ChoiceArraysFoldedBodyFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl < 'i > NonMalleable for ChoiceArraysFoldedBodyFmt < 'i > {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecParser > :: spec_parse) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl < 'i > EquivSerializersGeneral for ChoiceArraysFoldedBodyFmt < 'i > {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceArraysFoldedBodyFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl < 'i > EquivSerializers for ChoiceArraysFoldedBodyFmt < 'i > {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< ChoiceArraysFoldedBodyFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceArraysFoldedBodyFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = choice_arrays_folded_body_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for ChoiceArraysFoldedFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecParser > :: spec_parse) ;
                choice_arrays_folded_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for ChoiceArraysFoldedFmt {
            open spec fn productive_inv (& self) -> bool {
                choice_arrays_folded_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecParser > :: spec_parse) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for ChoiceArraysFoldedFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceArraysFoldedFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceArraysFoldedFmt as Consistency > :: consistent) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for ChoiceArraysFoldedFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceArraysFoldedFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for ChoiceArraysFoldedFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< ChoiceArraysFoldedFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< ChoiceArraysFoldedFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for ChoiceArraysFoldedFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecParser > :: spec_parse) ;
                reveal (< ChoiceArraysFoldedFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceArraysFoldedFmt as Consistency > :: consistent) ;
                reveal (< ChoiceArraysFoldedFmt as SpecByteLen > :: byte_len) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for ChoiceArraysFoldedFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecParser > :: spec_parse) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for ChoiceArraysFoldedFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< ChoiceArraysFoldedFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceArraysFoldedFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for ChoiceArraysFoldedFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< ChoiceArraysFoldedFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ChoiceArraysFoldedFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = choice_arrays_folded_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for ParenExprFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecParser > :: spec_parse) ;
                paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for ParenExprFmt {
            open spec fn productive_inv (& self) -> bool {
                paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecParser > :: spec_parse) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for ParenExprFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecParser > :: spec_parse) ;
                reveal (< ParenExprFmt as SpecByteLen > :: byte_len) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecParser > :: spec_parse) ;
                reveal (< ParenExprFmt as Consistency > :: consistent) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for ParenExprFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ParenExprFmt as SpecByteLen > :: byte_len) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for ParenExprFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< ParenExprFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< ParenExprFmt as SpecByteLen > :: byte_len) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for ParenExprFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecParser > :: spec_parse) ;
                reveal (< ParenExprFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ParenExprFmt as Consistency > :: consistent) ;
                reveal (< ParenExprFmt as SpecByteLen > :: byte_len) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for ParenExprFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecParser > :: spec_parse) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for ParenExprFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< ParenExprFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ParenExprFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for ParenExprFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< ParenExprFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ParenExprFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = paren_expr_fmt (self . a . deep_view () ,
                self . b . deep_view () ,
                self . c . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for ReinterpretSizeFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecParser > :: spec_parse) ;
                reinterpret_size_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for ReinterpretSizeFmt {
            open spec fn productive_inv (& self) -> bool {
                reinterpret_size_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecParser > :: spec_parse) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for ReinterpretSizeFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< ReinterpretSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< ReinterpretSizeFmt as Consistency > :: consistent) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for ReinterpretSizeFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ReinterpretSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for ReinterpretSizeFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< ReinterpretSizeFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< ReinterpretSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for ReinterpretSizeFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecParser > :: spec_parse) ;
                reveal (< ReinterpretSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ReinterpretSizeFmt as Consistency > :: consistent) ;
                reveal (< ReinterpretSizeFmt as SpecByteLen > :: byte_len) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for ReinterpretSizeFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecParser > :: spec_parse) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for ReinterpretSizeFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< ReinterpretSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ReinterpretSizeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for ReinterpretSizeFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< ReinterpretSizeFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< ReinterpretSizeFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = reinterpret_size_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for PrimitiveSizesFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecParser > :: spec_parse) ;
                primitive_sizes_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for PrimitiveSizesFmt {
            open spec fn productive_inv (& self) -> bool {
                primitive_sizes_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecParser > :: spec_parse) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for PrimitiveSizesFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecParser > :: spec_parse) ;
                reveal (< PrimitiveSizesFmt as SpecByteLen > :: byte_len) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecParser > :: spec_parse) ;
                reveal (< PrimitiveSizesFmt as Consistency > :: consistent) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for PrimitiveSizesFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PrimitiveSizesFmt as SpecByteLen > :: byte_len) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for PrimitiveSizesFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< PrimitiveSizesFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< PrimitiveSizesFmt as SpecByteLen > :: byte_len) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for PrimitiveSizesFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecParser > :: spec_parse) ;
                reveal (< PrimitiveSizesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PrimitiveSizesFmt as Consistency > :: consistent) ;
                reveal (< PrimitiveSizesFmt as SpecByteLen > :: byte_len) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for PrimitiveSizesFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecParser > :: spec_parse) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for PrimitiveSizesFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< PrimitiveSizesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PrimitiveSizesFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for PrimitiveSizesFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< PrimitiveSizesFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PrimitiveSizesFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = primitive_sizes_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }
    }

    // ============================================================
    // Executable Implementations
    // ============================================================
    // TODO(execs): emit Parser / Serializer / Prepare impls for Header


    // TODO(execs): emit Parser / Serializer / Prepare impls for HeaderAlias


    // TODO(execs): emit Parser / Serializer / Prepare impls for Divide


    // TODO(execs): emit Parser / Serializer / Prepare impls for FixedChoice


    // TODO(execs): emit Parser / Serializer / Prepare impls for SimpleSub


    // TODO(execs): emit Parser / Serializer / Prepare impls for AliasSize


    // TODO(execs): emit Parser / Serializer / Prepare impls for MultiArith


    // TODO(execs): emit Parser / Serializer / Prepare impls for SizeArith


    // TODO(execs): emit Parser / Serializer / Prepare impls for PayloadWithHeader


    // TODO(execs): emit Parser / Serializer / Prepare impls for MixedConst


    // TODO(execs): emit Parser / Serializer / Prepare impls for ChoiceTag


    // TODO(execs): emit Parser / Serializer / Prepare impls for NamedSize


    // TODO(execs): emit Parser / Serializer / Prepare impls for ChoiceFormatSize


    // TODO(execs): emit Parser / Serializer / Prepare impls for HeaderBytes


    // TODO(execs): emit Parser / Serializer / Prepare impls for Multiply


    // TODO(execs): emit Parser / Serializer / Prepare impls for ChoiceArraysFoldedBody


    // TODO(execs): emit Parser / Serializer / Prepare impls for ChoiceArraysFolded


    // TODO(execs): emit Parser / Serializer / Prepare impls for ParenExpr


    // TODO(execs): emit Parser / Serializer / Prepare impls for ReinterpretSize


    // TODO(execs): emit Parser / Serializer / Prepare impls for PrimitiveSizes
}

