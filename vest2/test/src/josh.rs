# ! [allow (warnings)] use vest_lib2 :: combinators :: mapped :: spec :: * ;
use vest_lib2 :: combinators :: * ;
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
    # [doc = "data type for `tst_tag`."]
    # [repr (u8)]
    # [derive (Debug , PartialEq , Eq , Clone , Copy , Structural)]
    pub enum TstTag {
        C0 = 0 ,
        C1 = 1 ,
        C2 = 2 ,
        C3 = 3 ,
        C4 = 4 ,
        C5 = 5 ,
        C6 = 6 ,
        C7 = 7 ,
        C8 = 8 ,
        C9 = 9 ,
        C10 = 10 ,
        C11 = 11 ,
        C12 = 12 ,
        C13 = 13 ,
        C14 = 14 ,
        C15 = 15 ,
        C16 = 16 ,
        C17 = 17 ,
        C18 = 18 ,
        C19 = 19 ,
        C20 = 20 ,
        C21 = 21 ,
        C22 = 22 ,
        C23 = 23 ,
        C24 = 24 ,
        C25 = 25 ,
        C26 = 26 ,
        C27 = 27 ,
        C28 = 28 ,
        C29 = 29 ,
        C30 = 30 ,
        Unknown (u8) ,
    }
    pub type TstTagSpec = TstTag ;
    pub type TstTagInner = Sum < u8 , u8 > ;
    impl DeepView for TstTag {
        type V = TstTagSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match * self {
                TstTag :: C0 => TstTagSpec :: C0 ,
                TstTag :: C1 => TstTagSpec :: C1 ,
                TstTag :: C2 => TstTagSpec :: C2 ,
                TstTag :: C3 => TstTagSpec :: C3 ,
                TstTag :: C4 => TstTagSpec :: C4 ,
                TstTag :: C5 => TstTagSpec :: C5 ,
                TstTag :: C6 => TstTagSpec :: C6 ,
                TstTag :: C7 => TstTagSpec :: C7 ,
                TstTag :: C8 => TstTagSpec :: C8 ,
                TstTag :: C9 => TstTagSpec :: C9 ,
                TstTag :: C10 => TstTagSpec :: C10 ,
                TstTag :: C11 => TstTagSpec :: C11 ,
                TstTag :: C12 => TstTagSpec :: C12 ,
                TstTag :: C13 => TstTagSpec :: C13 ,
                TstTag :: C14 => TstTagSpec :: C14 ,
                TstTag :: C15 => TstTagSpec :: C15 ,
                TstTag :: C16 => TstTagSpec :: C16 ,
                TstTag :: C17 => TstTagSpec :: C17 ,
                TstTag :: C18 => TstTagSpec :: C18 ,
                TstTag :: C19 => TstTagSpec :: C19 ,
                TstTag :: C20 => TstTagSpec :: C20 ,
                TstTag :: C21 => TstTagSpec :: C21 ,
                TstTag :: C22 => TstTagSpec :: C22 ,
                TstTag :: C23 => TstTagSpec :: C23 ,
                TstTag :: C24 => TstTagSpec :: C24 ,
                TstTag :: C25 => TstTagSpec :: C25 ,
                TstTag :: C26 => TstTagSpec :: C26 ,
                TstTag :: C27 => TstTagSpec :: C27 ,
                TstTag :: C28 => TstTagSpec :: C28 ,
                TstTag :: C29 => TstTagSpec :: C29 ,
                TstTag :: C30 => TstTagSpec :: C30 ,
                TstTag :: Unknown (v) => TstTagSpec :: Unknown (v) ,
            }
        }
    }
    impl DeepEq for TstTag {
        fn deep_eq (& self ,
        other : & Self) -> bool {
            * self == * other
        }
    }
    impl SelfView for TstTag {
        proof fn self_view (& self) {
        }
        fn eq (& self ,
        other : & Self) -> bool {
            * self == * other
        }
    }

    # [doc = "data type for `mydata`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct Mydata < 'i > {
        pub foo : & 'i [u8] ,
        pub bar : & 'i [u8] ,
    }
    # [verifier :: ext_equal]
    pub struct MydataSpec {
        pub foo : Seq < u8 > ,
        pub bar : Seq < u8 > ,
    }
    pub type MydataInner = (Seq < u8 > , Seq < u8 >) ;
    impl < 'i > DeepView for Mydata < 'i > {
        type V = MydataSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MydataSpec {
                foo : self . foo . deep_view () ,
                bar : self . bar . deep_view () ,
            }
        }
    }

    # [doc = "data type for `tst_mydata`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub enum TstMydata < 'i > {
        C0 (Mydata < 'i >) ,
        C1 (Mydata < 'i >) ,
        C2 (Mydata < 'i >) ,
        C3 (Mydata < 'i >) ,
        C4 (Mydata < 'i >) ,
        C5 (Mydata < 'i >) ,
        C6 (Mydata < 'i >) ,
        C7 (Mydata < 'i >) ,
        C8 (Mydata < 'i >) ,
        C9 (Mydata < 'i >) ,
        C10 (Mydata < 'i >) ,
        C11 (Mydata < 'i >) ,
        C12 (Mydata < 'i >) ,
        C13 (Mydata < 'i >) ,
        C14 (Mydata < 'i >) ,
        C15 (Mydata < 'i >) ,
        C16 (Mydata < 'i >) ,
        C17 (Mydata < 'i >) ,
        C18 (Mydata < 'i >) ,
        C19 (Mydata < 'i >) ,
        C20 (Mydata < 'i >) ,
        C21 (Mydata < 'i >) ,
        C22 (Mydata < 'i >) ,
        C23 (Mydata < 'i >) ,
        C24 (Mydata < 'i >) ,
        C25 (Mydata < 'i >) ,
        C26 (Mydata < 'i >) ,
        C27 (Mydata < 'i >) ,
        C28 (Mydata < 'i >) ,
        C29 (Mydata < 'i >) ,
        C30 (Mydata < 'i >) ,
        Default (& 'i [u8]) ,
    }
    # [verifier :: ext_equal]
    pub enum TstMydataSpec {
        C0 (MydataSpec) ,
        C1 (MydataSpec) ,
        C2 (MydataSpec) ,
        C3 (MydataSpec) ,
        C4 (MydataSpec) ,
        C5 (MydataSpec) ,
        C6 (MydataSpec) ,
        C7 (MydataSpec) ,
        C8 (MydataSpec) ,
        C9 (MydataSpec) ,
        C10 (MydataSpec) ,
        C11 (MydataSpec) ,
        C12 (MydataSpec) ,
        C13 (MydataSpec) ,
        C14 (MydataSpec) ,
        C15 (MydataSpec) ,
        C16 (MydataSpec) ,
        C17 (MydataSpec) ,
        C18 (MydataSpec) ,
        C19 (MydataSpec) ,
        C20 (MydataSpec) ,
        C21 (MydataSpec) ,
        C22 (MydataSpec) ,
        C23 (MydataSpec) ,
        C24 (MydataSpec) ,
        C25 (MydataSpec) ,
        C26 (MydataSpec) ,
        C27 (MydataSpec) ,
        C28 (MydataSpec) ,
        C29 (MydataSpec) ,
        C30 (MydataSpec) ,
        Default (Seq < u8 >) ,
    }
    pub type TstMydataInner = Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Seq < u8 > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > ;
    impl < 'i > DeepView for TstMydata < 'i > {
        type V = TstMydataSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            match self {
                TstMydata :: C0 (v) => TstMydataSpec :: C0 (v . deep_view ()) ,
                TstMydata :: C1 (v) => TstMydataSpec :: C1 (v . deep_view ()) ,
                TstMydata :: C2 (v) => TstMydataSpec :: C2 (v . deep_view ()) ,
                TstMydata :: C3 (v) => TstMydataSpec :: C3 (v . deep_view ()) ,
                TstMydata :: C4 (v) => TstMydataSpec :: C4 (v . deep_view ()) ,
                TstMydata :: C5 (v) => TstMydataSpec :: C5 (v . deep_view ()) ,
                TstMydata :: C6 (v) => TstMydataSpec :: C6 (v . deep_view ()) ,
                TstMydata :: C7 (v) => TstMydataSpec :: C7 (v . deep_view ()) ,
                TstMydata :: C8 (v) => TstMydataSpec :: C8 (v . deep_view ()) ,
                TstMydata :: C9 (v) => TstMydataSpec :: C9 (v . deep_view ()) ,
                TstMydata :: C10 (v) => TstMydataSpec :: C10 (v . deep_view ()) ,
                TstMydata :: C11 (v) => TstMydataSpec :: C11 (v . deep_view ()) ,
                TstMydata :: C12 (v) => TstMydataSpec :: C12 (v . deep_view ()) ,
                TstMydata :: C13 (v) => TstMydataSpec :: C13 (v . deep_view ()) ,
                TstMydata :: C14 (v) => TstMydataSpec :: C14 (v . deep_view ()) ,
                TstMydata :: C15 (v) => TstMydataSpec :: C15 (v . deep_view ()) ,
                TstMydata :: C16 (v) => TstMydataSpec :: C16 (v . deep_view ()) ,
                TstMydata :: C17 (v) => TstMydataSpec :: C17 (v . deep_view ()) ,
                TstMydata :: C18 (v) => TstMydataSpec :: C18 (v . deep_view ()) ,
                TstMydata :: C19 (v) => TstMydataSpec :: C19 (v . deep_view ()) ,
                TstMydata :: C20 (v) => TstMydataSpec :: C20 (v . deep_view ()) ,
                TstMydata :: C21 (v) => TstMydataSpec :: C21 (v . deep_view ()) ,
                TstMydata :: C22 (v) => TstMydataSpec :: C22 (v . deep_view ()) ,
                TstMydata :: C23 (v) => TstMydataSpec :: C23 (v . deep_view ()) ,
                TstMydata :: C24 (v) => TstMydataSpec :: C24 (v . deep_view ()) ,
                TstMydata :: C25 (v) => TstMydataSpec :: C25 (v . deep_view ()) ,
                TstMydata :: C26 (v) => TstMydataSpec :: C26 (v . deep_view ()) ,
                TstMydata :: C27 (v) => TstMydataSpec :: C27 (v . deep_view ()) ,
                TstMydata :: C28 (v) => TstMydataSpec :: C28 (v . deep_view ()) ,
                TstMydata :: C29 (v) => TstMydataSpec :: C29 (v . deep_view ()) ,
                TstMydata :: C30 (v) => TstMydataSpec :: C30 (v . deep_view ()) ,
                TstMydata :: Default (v) => TstMydataSpec :: Default (v . deep_view ()) ,
            }
        }
    }

    # [doc = "data type for `tst`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct Tst < 'i > {
        pub tag : TstTag ,
        pub mydata : TstMydata < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct TstSpec {
        pub tag : TstTagSpec ,
        pub mydata : TstMydataSpec ,
    }
    pub type TstInner = (TstTagSpec , TstMydataSpec) ;
    impl < 'i > DeepView for Tst < 'i > {
        type V = TstSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            TstSpec {
                tag : self . tag . deep_view () ,
                mydata : self . mydata . deep_view () ,
            }
        }
    }

    # [doc = "data type for `pair_stress`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct PairStress {
        pub f1 : u8 ,
        pub f2 : u16 ,
        pub f3 : u32 ,
        pub f4 : u8 ,
        pub f5 : u8 ,
        pub f6 : u8 ,
        pub f7 : u8 ,
        pub f8 : u8 ,
        pub f9 : u8 ,
        pub f10 : u8 ,
        pub f11 : u8 ,
        pub f12 : u8 ,
        pub f13 : u8 ,
        pub f14 : u8 ,
        pub f15 : u8 ,
        pub f16 : u8 ,
        pub f17 : u8 ,
        pub f18 : u8 ,
    }
    # [verifier :: ext_equal]
    pub struct PairStressSpec {
        pub f1 : u8 ,
        pub f2 : u16 ,
        pub f3 : u32 ,
        pub f4 : u8 ,
        pub f5 : u8 ,
        pub f6 : u8 ,
        pub f7 : u8 ,
        pub f8 : u8 ,
        pub f9 : u8 ,
        pub f10 : u8 ,
        pub f11 : u8 ,
        pub f12 : u8 ,
        pub f13 : u8 ,
        pub f14 : u8 ,
        pub f15 : u8 ,
        pub f16 : u8 ,
        pub f17 : u8 ,
        pub f18 : u8 ,
    }
    pub type PairStressInner = (u8 , (u16 , (u32 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , (u8 , u8))))))))))))))))) ;
    impl DeepView for PairStress {
        type V = PairStressSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            PairStressSpec {
                f1 : self . f1 . deep_view () ,
                f2 : self . f2 . deep_view () ,
                f3 : self . f3 . deep_view () ,
                f4 : self . f4 . deep_view () ,
                f5 : self . f5 . deep_view () ,
                f6 : self . f6 . deep_view () ,
                f7 : self . f7 . deep_view () ,
                f8 : self . f8 . deep_view () ,
                f9 : self . f9 . deep_view () ,
                f10 : self . f10 . deep_view () ,
                f11 : self . f11 . deep_view () ,
                f12 : self . f12 . deep_view () ,
                f13 : self . f13 . deep_view () ,
                f14 : self . f14 . deep_view () ,
                f15 : self . f15 . deep_view () ,
                f16 : self . f16 . deep_view () ,
                f17 : self . f17 . deep_view () ,
                f18 : self . f18 . deep_view () ,
            }
        }
    }

    // ============================================================
    // Format Specifications
    // ============================================================
    # [doc = "named format combinator for `tst_tag`."]
    # [derive (Clone , Copy)]
    pub struct TstTagFmt ;

    pub type TstTagFmtSpec = Named < Mapped < Choice < Refined < U8 , PredFnSpec < u8 >> , Refined < U8 , PredFnSpec < u8 >> > , FnSpecMapper < TstTagInner , TstTagSpec >> > ;

    # [doc = "specification constructor for `tst_tag`."]
    pub open spec fn tst_tag_fmt () -> TstTagFmtSpec {
        Named ("tst_tag" ,
        Mapped {
            inner : Choice (Refined (U8 ,
            | x : u8 | x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 14 || x == 15 || x == 16 || x == 17 || x == 18 || x == 19 || x == 20 || x == 21 || x == 22 || x == 23 || x == 24 || x == 25 || x == 26 || x == 27 || x == 28 || x == 29 || x == 30) ,
            Refined (U8 ,
            | x : u8 | x != 0 && x != 1 && x != 2 && x != 3 && x != 4 && x != 5 && x != 6 && x != 7 && x != 8 && x != 9 && x != 10 && x != 11 && x != 12 && x != 13 && x != 14 && x != 15 && x != 16 && x != 17 && x != 18 && x != 19 && x != 20 && x != 21 && x != 22 && x != 23 && x != 24 && x != 25 && x != 26 && x != 27 && x != 28 && x != 29 && x != 30)) ,
            mapper : (| parsed : TstTagInner | -> TstTagSpec {
                match parsed {
                    Sum :: Inl (x) => match x {
                        0 => TstTagSpec :: C0 ,
                        1 => TstTagSpec :: C1 ,
                        2 => TstTagSpec :: C2 ,
                        3 => TstTagSpec :: C3 ,
                        4 => TstTagSpec :: C4 ,
                        5 => TstTagSpec :: C5 ,
                        6 => TstTagSpec :: C6 ,
                        7 => TstTagSpec :: C7 ,
                        8 => TstTagSpec :: C8 ,
                        9 => TstTagSpec :: C9 ,
                        10 => TstTagSpec :: C10 ,
                        11 => TstTagSpec :: C11 ,
                        12 => TstTagSpec :: C12 ,
                        13 => TstTagSpec :: C13 ,
                        14 => TstTagSpec :: C14 ,
                        15 => TstTagSpec :: C15 ,
                        16 => TstTagSpec :: C16 ,
                        17 => TstTagSpec :: C17 ,
                        18 => TstTagSpec :: C18 ,
                        19 => TstTagSpec :: C19 ,
                        20 => TstTagSpec :: C20 ,
                        21 => TstTagSpec :: C21 ,
                        22 => TstTagSpec :: C22 ,
                        23 => TstTagSpec :: C23 ,
                        24 => TstTagSpec :: C24 ,
                        25 => TstTagSpec :: C25 ,
                        26 => TstTagSpec :: C26 ,
                        27 => TstTagSpec :: C27 ,
                        28 => TstTagSpec :: C28 ,
                        29 => TstTagSpec :: C29 ,
                        30 => TstTagSpec :: C30 ,
                        _ => arbitrary () ,
                    }
                    ,
                    Sum :: Inr (x) => TstTagSpec :: Unknown (x) ,
                }
            }
            ,
            | value : TstTagSpec | -> TstTagInner {
                match value {
                    TstTagSpec :: C0 => Sum :: Inl (0) ,
                    TstTagSpec :: C1 => Sum :: Inl (1) ,
                    TstTagSpec :: C2 => Sum :: Inl (2) ,
                    TstTagSpec :: C3 => Sum :: Inl (3) ,
                    TstTagSpec :: C4 => Sum :: Inl (4) ,
                    TstTagSpec :: C5 => Sum :: Inl (5) ,
                    TstTagSpec :: C6 => Sum :: Inl (6) ,
                    TstTagSpec :: C7 => Sum :: Inl (7) ,
                    TstTagSpec :: C8 => Sum :: Inl (8) ,
                    TstTagSpec :: C9 => Sum :: Inl (9) ,
                    TstTagSpec :: C10 => Sum :: Inl (10) ,
                    TstTagSpec :: C11 => Sum :: Inl (11) ,
                    TstTagSpec :: C12 => Sum :: Inl (12) ,
                    TstTagSpec :: C13 => Sum :: Inl (13) ,
                    TstTagSpec :: C14 => Sum :: Inl (14) ,
                    TstTagSpec :: C15 => Sum :: Inl (15) ,
                    TstTagSpec :: C16 => Sum :: Inl (16) ,
                    TstTagSpec :: C17 => Sum :: Inl (17) ,
                    TstTagSpec :: C18 => Sum :: Inl (18) ,
                    TstTagSpec :: C19 => Sum :: Inl (19) ,
                    TstTagSpec :: C20 => Sum :: Inl (20) ,
                    TstTagSpec :: C21 => Sum :: Inl (21) ,
                    TstTagSpec :: C22 => Sum :: Inl (22) ,
                    TstTagSpec :: C23 => Sum :: Inl (23) ,
                    TstTagSpec :: C24 => Sum :: Inl (24) ,
                    TstTagSpec :: C25 => Sum :: Inl (25) ,
                    TstTagSpec :: C26 => Sum :: Inl (26) ,
                    TstTagSpec :: C27 => Sum :: Inl (27) ,
                    TstTagSpec :: C28 => Sum :: Inl (28) ,
                    TstTagSpec :: C29 => Sum :: Inl (29) ,
                    TstTagSpec :: C30 => Sum :: Inl (30) ,
                    TstTagSpec :: Unknown (x) => Sum :: Inr (x) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `mydata`."]
    # [derive (Clone , Copy)]
    pub struct MydataFmt ;

    pub type MydataFmtSpec = Named < Mapped < Pair < Fixed < 2 > , Fixed < 2 > > , FnSpecMapper < MydataInner , MydataSpec >> > ;

    # [doc = "specification constructor for `mydata`."]
    pub open spec fn mydata_fmt () -> MydataFmtSpec {
        Named ("mydata" ,
        Mapped {
            inner : Pair (Fixed :: < 2 > ,
            Fixed :: < 2 >) ,
            mapper : (| parsed : MydataInner | -> MydataSpec {
                let (foo ,
                bar) = parsed ;
                MydataSpec {
                    foo ,
                    bar
                }
            }
            ,
            | value : MydataSpec | -> MydataInner {
                let MydataSpec {
                    foo ,
                    bar
                }
                = value ;
                (foo ,
                bar)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `tst_mydata`."]
    # [derive (Clone , Copy)]
    pub struct TstMydataFmt {
        pub tag : TstTag ,
    }

    pub type TstMydataFmtSpec = Named < Mapped < Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Tail > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > , FnSpecMapper < TstMydataInner , TstMydataSpec >> > ;

    # [doc = "specification constructor for `tst_mydata`."]
    pub open spec fn tst_mydata_fmt (tag : TstTagSpec) -> TstMydataFmtSpec {
        Named ("tst_mydata" ,
        Mapped {
            inner : match tag {
                TstTagSpec :: C0 => Sum :: Inl (MydataFmt) ,
                TstTagSpec :: C1 => Sum :: Inr (Sum :: Inl (MydataFmt)) ,
                TstTagSpec :: C2 => Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))) ,
                TstTagSpec :: C3 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))) ,
                TstTagSpec :: C4 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))) ,
                TstTagSpec :: C5 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))) ,
                TstTagSpec :: C6 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))) ,
                TstTagSpec :: C7 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))) ,
                TstTagSpec :: C8 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))) ,
                TstTagSpec :: C9 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))) ,
                TstTagSpec :: C10 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))) ,
                TstTagSpec :: C11 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))) ,
                TstTagSpec :: C12 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))) ,
                TstTagSpec :: C13 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))) ,
                TstTagSpec :: C14 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))) ,
                TstTagSpec :: C15 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))))) ,
                TstTagSpec :: C16 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))))) ,
                TstTagSpec :: C17 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))))))) ,
                TstTagSpec :: C18 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))))))) ,
                TstTagSpec :: C19 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))))))))) ,
                TstTagSpec :: C20 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))))))))) ,
                TstTagSpec :: C21 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))))))))))) ,
                TstTagSpec :: C22 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))))))))))) ,
                TstTagSpec :: C23 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))))))))))))) ,
                TstTagSpec :: C24 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))))))))))))) ,
                TstTagSpec :: C25 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))))))))))))))) ,
                TstTagSpec :: C26 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))))))))))))))) ,
                TstTagSpec :: C27 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))))))))))))))))) ,
                TstTagSpec :: C28 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))))))))))))))))) ,
                TstTagSpec :: C29 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt)))))))))))))))))))))))))))))) ,
                TstTagSpec :: C30 => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (MydataFmt))))))))))))))))))))))))))))))) ,
                _ => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Tail))))))))))))))))))))))))))))))) ,
            }
            ,
            mapper : (| parsed : TstMydataInner | -> TstMydataSpec {
                match parsed {
                    Sum :: Inl (v) => TstMydataSpec :: C0 (v) ,
                    Sum :: Inr (Sum :: Inl (v)) => TstMydataSpec :: C1 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inl (v))) => TstMydataSpec :: C2 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))) => TstMydataSpec :: C3 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))) => TstMydataSpec :: C4 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))) => TstMydataSpec :: C5 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))) => TstMydataSpec :: C6 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))) => TstMydataSpec :: C7 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))) => TstMydataSpec :: C8 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))) => TstMydataSpec :: C9 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))) => TstMydataSpec :: C10 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))) => TstMydataSpec :: C11 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))) => TstMydataSpec :: C12 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))) => TstMydataSpec :: C13 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))) => TstMydataSpec :: C14 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))) => TstMydataSpec :: C15 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))) => TstMydataSpec :: C16 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))) => TstMydataSpec :: C17 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))) => TstMydataSpec :: C18 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))) => TstMydataSpec :: C19 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))) => TstMydataSpec :: C20 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))) => TstMydataSpec :: C21 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))) => TstMydataSpec :: C22 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))))) => TstMydataSpec :: C23 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))))) => TstMydataSpec :: C24 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))))))) => TstMydataSpec :: C25 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))))))) => TstMydataSpec :: C26 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))))))))) => TstMydataSpec :: C27 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))))))))) => TstMydataSpec :: C28 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))))))))))) => TstMydataSpec :: C29 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))))))))))) => TstMydataSpec :: C30 (v) ,
                    Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (v))))))))))))))))))))))))))))))) => TstMydataSpec :: Default (v) ,
                }
            }
            ,
            | value : TstMydataSpec | -> TstMydataInner {
                match value {
                    TstMydataSpec :: C0 (v) => Sum :: Inl (v) ,
                    TstMydataSpec :: C1 (v) => Sum :: Inr (Sum :: Inl (v)) ,
                    TstMydataSpec :: C2 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inl (v))) ,
                    TstMydataSpec :: C3 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))) ,
                    TstMydataSpec :: C4 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))) ,
                    TstMydataSpec :: C5 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))) ,
                    TstMydataSpec :: C6 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))) ,
                    TstMydataSpec :: C7 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))) ,
                    TstMydataSpec :: C8 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))) ,
                    TstMydataSpec :: C9 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))) ,
                    TstMydataSpec :: C10 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))) ,
                    TstMydataSpec :: C11 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))) ,
                    TstMydataSpec :: C12 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))) ,
                    TstMydataSpec :: C13 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))) ,
                    TstMydataSpec :: C14 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))) ,
                    TstMydataSpec :: C15 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))) ,
                    TstMydataSpec :: C16 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))) ,
                    TstMydataSpec :: C17 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))) ,
                    TstMydataSpec :: C18 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))) ,
                    TstMydataSpec :: C19 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))) ,
                    TstMydataSpec :: C20 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))) ,
                    TstMydataSpec :: C21 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))) ,
                    TstMydataSpec :: C22 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))) ,
                    TstMydataSpec :: C23 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))))) ,
                    TstMydataSpec :: C24 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))))) ,
                    TstMydataSpec :: C25 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))))))) ,
                    TstMydataSpec :: C26 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))))))) ,
                    TstMydataSpec :: C27 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))))))))) ,
                    TstMydataSpec :: C28 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))))))))) ,
                    TstMydataSpec :: C29 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v)))))))))))))))))))))))))))))) ,
                    TstMydataSpec :: C30 (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inl (v))))))))))))))))))))))))))))))) ,
                    TstMydataSpec :: Default (v) => Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (Sum :: Inr (v))))))))))))))))))))))))))))))) ,
                }
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `tst`."]
    # [derive (Clone , Copy)]
    pub struct TstFmt ;

    pub type TstFmtSpec = Named < Mapped < Bind < TstTagFmt , spec_fn (TstTagSpec) -> TstMydataFmt > , FnSpecMapper < TstInner , TstSpec >> > ;

    # [doc = "specification constructor for `tst`."]
    pub open spec fn tst_fmt () -> TstFmtSpec {
        Named ("tst" ,
        Mapped {
            inner : Bind (TstTagFmt ,
            | tag : TstTagSpec | TstMydataFmt {
                tag
            }
            ) ,
            mapper : (| parsed : TstInner | -> TstSpec {
                let (tag ,
                mydata) = parsed ;
                TstSpec {
                    tag ,
                    mydata
                }
            }
            ,
            | value : TstSpec | -> TstInner {
                let TstSpec {
                    tag ,
                    mydata
                }
                = value ;
                (tag ,
                mydata)
            }
            )
        }
        )
    }


    # [doc = "named format combinator for `pair_stress`."]
    # [derive (Clone , Copy)]
    pub struct PairStressFmt ;

    pub type PairStressFmtSpec = Named < Mapped < Pair < U8 , Pair < U16Le , Pair < U32Le , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , Pair < U8 , U8 > > > > > > > > > > > > > > > > > , FnSpecMapper < PairStressInner , PairStressSpec >> > ;

    # [doc = "specification constructor for `pair_stress`."]
    pub open spec fn pair_stress_fmt () -> PairStressFmtSpec {
        Named ("pair_stress" ,
        Mapped {
            inner : Pair (U8 ,
            Pair (U16Le ,
            Pair (U32Le ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            Pair (U8 ,
            U8))))))))))))))))) ,
            mapper : (| parsed : PairStressInner | -> PairStressSpec {
                let (f1 ,
                (f2 ,
                (f3 ,
                (f4 ,
                (f5 ,
                (f6 ,
                (f7 ,
                (f8 ,
                (f9 ,
                (f10 ,
                (f11 ,
                (f12 ,
                (f13 ,
                (f14 ,
                (f15 ,
                (f16 ,
                (f17 ,
                f18))))))))))))))))) = parsed ;
                PairStressSpec {
                    f1 ,
                    f2 ,
                    f3 ,
                    f4 ,
                    f5 ,
                    f6 ,
                    f7 ,
                    f8 ,
                    f9 ,
                    f10 ,
                    f11 ,
                    f12 ,
                    f13 ,
                    f14 ,
                    f15 ,
                    f16 ,
                    f17 ,
                    f18
                }
            }
            ,
            | value : PairStressSpec | -> PairStressInner {
                let PairStressSpec {
                    f1 ,
                    f2 ,
                    f3 ,
                    f4 ,
                    f5 ,
                    f6 ,
                    f7 ,
                    f8 ,
                    f9 ,
                    f10 ,
                    f11 ,
                    f12 ,
                    f13 ,
                    f14 ,
                    f15 ,
                    f16 ,
                    f17 ,
                    f18
                }
                = value ;
                (f1 ,
                (f2 ,
                (f3 ,
                (f4 ,
                (f5 ,
                (f6 ,
                (f7 ,
                (f8 ,
                (f9 ,
                (f10 ,
                (f11 ,
                (f12 ,
                (f13 ,
                (f14 ,
                (f15 ,
                (f16 ,
                (f17 ,
                f18)))))))))))))))))
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

        impl SpecParser for TstTagFmt {
            type PVal = TstTagSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                tst_tag_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for TstTagFmt {
            type Val = TstTagSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                tst_tag_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for TstTagFmt {
            type SValue = TstTagSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                tst_tag_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for TstTagFmt {
            type SVal = TstTagSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                tst_tag_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for TstTagFmt {
            type T = TstTagSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                tst_tag_fmt () . byte_len (v)
            }
        }

        impl SpecParser for MydataFmt {
            type PVal = MydataSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                mydata_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for MydataFmt {
            type Val = MydataSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                mydata_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for MydataFmt {
            type SValue = MydataSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                mydata_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MydataFmt {
            type SVal = MydataSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                mydata_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for MydataFmt {
            type T = MydataSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                mydata_fmt () . byte_len (v)
            }
        }

        impl SpecParser for TstMydataFmt {
            type PVal = TstMydataSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                tst_mydata_fmt (self . tag . deep_view ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for TstMydataFmt {
            type Val = TstMydataSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                tst_mydata_fmt (self . tag . deep_view ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for TstMydataFmt {
            type SValue = TstMydataSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                tst_mydata_fmt (self . tag . deep_view ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for TstMydataFmt {
            type SVal = TstMydataSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                tst_mydata_fmt (self . tag . deep_view ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for TstMydataFmt {
            type T = TstMydataSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                tst_mydata_fmt (self . tag . deep_view ()) . byte_len (v)
            }
        }

        impl SpecParser for TstFmt {
            type PVal = TstSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                tst_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for TstFmt {
            type Val = TstSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                tst_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for TstFmt {
            type SValue = TstSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                tst_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for TstFmt {
            type SVal = TstSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                tst_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for TstFmt {
            type T = TstSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                tst_fmt () . byte_len (v)
            }
        }

        impl SpecParser for PairStressFmt {
            type PVal = PairStressSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                pair_stress_fmt () . spec_parse (ibuf)
            }
        }
        impl Consistency for PairStressFmt {
            type Val = PairStressSpec ;
            # [verifier :: opaque] open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                pair_stress_fmt () . consistent (v)
            }
        }
        impl SpecSerializerDps for PairStressFmt {
            type SValue = PairStressSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                pair_stress_fmt () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for PairStressFmt {
            type SVal = PairStressSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                pair_stress_fmt () . spec_serialize (v)
            }
        }
        impl SpecByteLen for PairStressFmt {
            type T = PairStressSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                pair_stress_fmt () . byte_len (v)
            }
        }
    }

    // ============================================================
    // Proven Format Properties
    // ============================================================
    mod derived_proofs {
        use super::*;
        broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        impl SafeParser for TstTagFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                tst_tag_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for TstTagFmt {
            open spec fn productive_inv (& self) -> bool {
                tst_tag_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for TstTagFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                reveal (< TstTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                reveal (< TstTagFmt as Consistency > :: consistent) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for TstTagFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for TstTagFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< TstTagFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< TstTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for TstTagFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                reveal (< TstTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstTagFmt as Consistency > :: consistent) ;
                reveal (< TstTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for TstTagFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for TstTagFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstTagFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for TstTagFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< TstTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstTagFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = tst_tag_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MydataFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                mydata_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MydataFmt {
            open spec fn productive_inv (& self) -> bool {
                mydata_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                let fmt = mydata_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MydataFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                reveal (< MydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = mydata_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                reveal (< MydataFmt as Consistency > :: consistent) ;
                let fmt = mydata_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MydataFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = mydata_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = mydata_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for MydataFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MydataFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = mydata_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MydataFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                reveal (< MydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MydataFmt as Consistency > :: consistent) ;
                reveal (< MydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = mydata_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MydataFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                let fmt = mydata_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for MydataFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MydataFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = mydata_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for MydataFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MydataFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = mydata_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for TstMydataFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                tst_mydata_fmt (self . tag . deep_view ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for TstMydataFmt {
            open spec fn productive_inv (& self) -> bool {
                tst_mydata_fmt (self . tag . deep_view ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                let fmt = tst_mydata_fmt (self . tag . deep_view ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for TstMydataFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                reveal (< TstMydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_mydata_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                reveal (< TstMydataFmt as Consistency > :: consistent) ;
                let fmt = tst_mydata_fmt (self . tag . deep_view ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for TstMydataFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< TstMydataFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< TstMydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_mydata_fmt (self . tag . deep_view ()) ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for TstMydataFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                reveal (< TstMydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstMydataFmt as Consistency > :: consistent) ;
                reveal (< TstMydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_mydata_fmt (self . tag . deep_view ()) ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for TstMydataFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                let fmt = tst_mydata_fmt (self . tag . deep_view ()) ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for TstMydataFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< TstMydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstMydataFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = tst_mydata_fmt (self . tag . deep_view ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for TstFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                tst_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for TstFmt {
            open spec fn productive_inv (& self) -> bool {
                tst_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                let fmt = tst_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for TstFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                reveal (< TstFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                reveal (< TstFmt as Consistency > :: consistent) ;
                let fmt = tst_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for TstFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< TstFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< TstFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for TstFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                reveal (< TstFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstFmt as Consistency > :: consistent) ;
                reveal (< TstFmt as SpecByteLen > :: byte_len) ;
                let fmt = tst_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for TstFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                let fmt = tst_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for TstFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< TstFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = tst_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for PairStressFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PairStressFmt as SpecParser > :: spec_parse) ;
                pair_stress_fmt () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for PairStressFmt {
            open spec fn productive_inv (& self) -> bool {
                pair_stress_fmt () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< PairStressFmt as SpecParser > :: spec_parse) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for PairStressFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PairStressFmt as SpecParser > :: spec_parse) ;
                reveal (< PairStressFmt as SpecByteLen > :: byte_len) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< PairStressFmt as SpecParser > :: spec_parse) ;
                reveal (< PairStressFmt as Consistency > :: consistent) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for PairStressFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< PairStressFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< PairStressFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PairStressFmt as SpecByteLen > :: byte_len) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for PairStressFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< PairStressFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< PairStressFmt as SpecByteLen > :: byte_len) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for PairStressFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< PairStressFmt as SpecParser > :: spec_parse) ;
                reveal (< PairStressFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PairStressFmt as Consistency > :: consistent) ;
                reveal (< PairStressFmt as SpecByteLen > :: byte_len) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for PairStressFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< PairStressFmt as SpecParser > :: spec_parse) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for PairStressFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< PairStressFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PairStressFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for PairStressFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< PairStressFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< PairStressFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = pair_stress_fmt () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }
    }

    // ============================================================
    // Executable Implementations
    // ============================================================
    impl < 'i > Parser < & 'i [u8] > for TstTagFmt {
        type PT = TstTag ;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

            reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n , v) = U8 . parse (& rest) ? ;
            let enum_val = match v {
        0 => TstTag :: C0 ,
        1 => TstTag :: C1 ,
        2 => TstTag :: C2 ,
        3 => TstTag :: C3 ,
        4 => TstTag :: C4 ,
        5 => TstTag :: C5 ,
        6 => TstTag :: C6 ,
        7 => TstTag :: C7 ,
        8 => TstTag :: C8 ,
        9 => TstTag :: C9 ,
        10 => TstTag :: C10 ,
        11 => TstTag :: C11 ,
        12 => TstTag :: C12 ,
        13 => TstTag :: C13 ,
        14 => TstTag :: C14 ,
        15 => TstTag :: C15 ,
        16 => TstTag :: C16 ,
        17 => TstTag :: C17 ,
        18 => TstTag :: C18 ,
        19 => TstTag :: C19 ,
        20 => TstTag :: C20 ,
        21 => TstTag :: C21 ,
        22 => TstTag :: C22 ,
        23 => TstTag :: C23 ,
        24 => TstTag :: C24 ,
        25 => TstTag :: C25 ,
        26 => TstTag :: C26 ,
        27 => TstTag :: C27 ,
        28 => TstTag :: C28 ,
        29 => TstTag :: C29 ,
        30 => TstTag :: C30 ,
        x => TstTag :: Unknown (x) ,
    }
    ;
            assert (self . spec_parse (ibuf @) == Some ((n as int , enum_val . deep_view ()))) ;
            Ok((n, enum_val))
        }
    }



    impl < 'i > Parser < & 'i [u8] > for MydataFmt {
        type PT = Mydata < 'i > ;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

            reveal (< MydataFmt as SpecParser > :: spec_parse) ;
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1 , foo) = (Fixed :: < 2 >) . parse (& rest) ? ;
            let rest = rest.skip(n1);
            let (n2 , bar) = (Fixed :: < 2 >) . parse (& rest) ? ;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Mydata {
        foo ,
        bar
    }
    ;
            assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
            Ok((total_n, final_v))
        }
    }



    impl < 'i > Parser < & 'i [u8] > for TstMydataFmt {
        type PT = TstMydata < 'i > ;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

            reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n , v) = match self . tag {
        TstTag :: C0 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C0 (v))
        }
        ,
        TstTag :: C1 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C1 (v))
        }
        ,
        TstTag :: C2 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C2 (v))
        }
        ,
        TstTag :: C3 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C3 (v))
        }
        ,
        TstTag :: C4 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C4 (v))
        }
        ,
        TstTag :: C5 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C5 (v))
        }
        ,
        TstTag :: C6 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C6 (v))
        }
        ,
        TstTag :: C7 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C7 (v))
        }
        ,
        TstTag :: C8 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C8 (v))
        }
        ,
        TstTag :: C9 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C9 (v))
        }
        ,
        TstTag :: C10 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C10 (v))
        }
        ,
        TstTag :: C11 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C11 (v))
        }
        ,
        TstTag :: C12 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C12 (v))
        }
        ,
        TstTag :: C13 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C13 (v))
        }
        ,
        TstTag :: C14 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C14 (v))
        }
        ,
        TstTag :: C15 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C15 (v))
        }
        ,
        TstTag :: C16 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C16 (v))
        }
        ,
        TstTag :: C17 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C17 (v))
        }
        ,
        TstTag :: C18 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C18 (v))
        }
        ,
        TstTag :: C19 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C19 (v))
        }
        ,
        TstTag :: C20 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C20 (v))
        }
        ,
        TstTag :: C21 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C21 (v))
        }
        ,
        TstTag :: C22 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C22 (v))
        }
        ,
        TstTag :: C23 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C23 (v))
        }
        ,
        TstTag :: C24 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C24 (v))
        }
        ,
        TstTag :: C25 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C25 (v))
        }
        ,
        TstTag :: C26 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C26 (v))
        }
        ,
        TstTag :: C27 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C27 (v))
        }
        ,
        TstTag :: C28 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C28 (v))
        }
        ,
        TstTag :: C29 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C29 (v))
        }
        ,
        TstTag :: C30 => {
            let (n ,
            v) = (MydataFmt) . parse (& rest) ? ;
            (n ,
            TstMydata :: C30 (v))
        }
        ,
        _ => {
            let (n ,
            v) = (Tail) . parse (& rest) ? ;
            (n ,
            TstMydata :: Default (v))
        }
        ,
    }
    ;
            assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
            Ok((n, v))
        }
    }



    impl < 'i > Parser < & 'i [u8] > for TstFmt {
        type PT = Tst < 'i > ;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

            reveal (< TstFmt as SpecParser > :: spec_parse) ;
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1 , tag) = (TstTagFmt) . parse (& rest) ? ;
            let rest = rest.skip(n1);
            let (n2 , mydata) = (TstMydataFmt {
        tag : tag
    }
    ) . parse (& rest) ? ;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Tst {
        tag ,
        mydata
    }
    ;
            assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
            Ok((total_n, final_v))
        }
    }



    impl < 'i > Parser < & 'i [u8] > for PairStressFmt {
        type PT = PairStress ;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;

            reveal (< PairStressFmt as SpecParser > :: spec_parse) ;
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1 , f1) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n1);
            let (n2 , f2) = (U16Le) . parse (& rest) ? ;
            let rest = rest.skip(n2);
            let (n3 , f3) = (U32Le) . parse (& rest) ? ;
            let rest = rest.skip(n3);
            let (n4 , f4) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n4);
            let (n5 , f5) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n5);
            let (n6 , f6) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n6);
            let (n7 , f7) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n7);
            let (n8 , f8) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n8);
            let (n9 , f9) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n9);
            let (n10 , f10) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n10);
            let (n11 , f11) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n11);
            let (n12 , f12) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n12);
            let (n13 , f13) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n13);
            let (n14 , f14) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n14);
            let (n15 , f15) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n15);
            let (n16 , f16) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n16);
            let (n17 , f17) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n17);
            let (n18 , f18) = (U8) . parse (& rest) ? ;
            let rest = rest.skip(n18);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 + n11 + n12 + n13 + n14 + n15 + n16 + n17 + n18;
            let final_v = PairStress {
        f1 ,
        f2 ,
        f3 ,
        f4 ,
        f5 ,
        f6 ,
        f7 ,
        f8 ,
        f9 ,
        f10 ,
        f11 ,
        f12 ,
        f13 ,
        f14 ,
        f15 ,
        f16 ,
        f17 ,
        f18
    }
    ;
            assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
            Ok((total_n, final_v))
        }
    }

}

