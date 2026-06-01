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
        C31 = 31 ,
        C32 = 32 ,
        C33 = 33 ,
        C34 = 34 ,
        C35 = 35 ,
        Unknown (u8) ,
    }
    pub type TstTagSpec = TstTag ;
    pub type TstTagInner = Sum < u8 , u8 > ;
    impl DeepView for TstTag {
        type V = Self ;
        open spec fn deep_view (& self) -> Self :: V {
            * self
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
        C31 (Mydata < 'i >) ,
        C32 (Mydata < 'i >) ,
        C33 (Mydata < 'i >) ,
        C34 (Mydata < 'i >) ,
        C35 (Mydata < 'i >) ,
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
        C31 (MydataSpec) ,
        C32 (MydataSpec) ,
        C33 (MydataSpec) ,
        C34 (MydataSpec) ,
        C35 (MydataSpec) ,
        Default (Seq < u8 >) ,
    }
    pub type TstMydataInner = Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Sum < MydataSpec , Seq < u8 > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > ;
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
                TstMydata :: C31 (v) => TstMydataSpec :: C31 (v . deep_view ()) ,
                TstMydata :: C32 (v) => TstMydataSpec :: C32 (v . deep_view ()) ,
                TstMydata :: C33 (v) => TstMydataSpec :: C33 (v . deep_view ()) ,
                TstMydata :: C34 (v) => TstMydataSpec :: C34 (v . deep_view ()) ,
                TstMydata :: C35 (v) => TstMydataSpec :: C35 (v . deep_view ()) ,
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

    // ============================================================
    // Format Specifications
    // ============================================================
    # [doc = "named format combinator for `tst_tag`."]
    # [derive (Clone , Copy)]
    pub struct TstTagFmt ;

    pub type TstTagFmtSpec = Named < Mapped < Choice < Refined < U8 , PredFnSpec < u8 >> , Refined < U8 , PredFnSpec < u8 >> > , FnSpecMapper < TstTagInner , TstTagSpec >> > ;

    impl TstTagFmt {
        # [doc = "specification constructor for `tst_tag`."] pub open spec fn spec_inner () -> TstTagFmtSpec {
            Named ("tst_tag" ,
            Mapped {
                inner : Choice (Refined (U8 ,
                | x : u8 | x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 14 || x == 15 || x == 16 || x == 17 || x == 18 || x == 19 || x == 20 || x == 21 || x == 22 || x == 23 || x == 24 || x == 25 || x == 26 || x == 27 || x == 28 || x == 29 || x == 30 || x == 31 || x == 32 || x == 33 || x == 34 || x == 35) ,
                Refined (U8 ,
                | x : u8 | x != 0 && x != 1 && x != 2 && x != 3 && x != 4 && x != 5 && x != 6 && x != 7 && x != 8 && x != 9 && x != 10 && x != 11 && x != 12 && x != 13 && x != 14 && x != 15 && x != 16 && x != 17 && x != 18 && x != 19 && x != 20 && x != 21 && x != 22 && x != 23 && x != 24 && x != 25 && x != 26 && x != 27 && x != 28 && x != 29 && x != 30 && x != 31 && x != 32 && x != 33 && x != 34 && x != 35)) ,
                mapper : (| parsed : TstTagInner | -> TstTagSpec {
                    match parsed {
                        L (x) => match x {
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
                            31 => TstTagSpec :: C31 ,
                            32 => TstTagSpec :: C32 ,
                            33 => TstTagSpec :: C33 ,
                            34 => TstTagSpec :: C34 ,
                            35 => TstTagSpec :: C35 ,
                            _ => arbitrary () ,
                        }
                        ,
                        R (x) => TstTagSpec :: Unknown (x) ,
                    }
                }
                ,
                | value : TstTagSpec | -> TstTagInner {
                    match value {
                        TstTagSpec :: C0 => L (0) ,
                        TstTagSpec :: C1 => L (1) ,
                        TstTagSpec :: C2 => L (2) ,
                        TstTagSpec :: C3 => L (3) ,
                        TstTagSpec :: C4 => L (4) ,
                        TstTagSpec :: C5 => L (5) ,
                        TstTagSpec :: C6 => L (6) ,
                        TstTagSpec :: C7 => L (7) ,
                        TstTagSpec :: C8 => L (8) ,
                        TstTagSpec :: C9 => L (9) ,
                        TstTagSpec :: C10 => L (10) ,
                        TstTagSpec :: C11 => L (11) ,
                        TstTagSpec :: C12 => L (12) ,
                        TstTagSpec :: C13 => L (13) ,
                        TstTagSpec :: C14 => L (14) ,
                        TstTagSpec :: C15 => L (15) ,
                        TstTagSpec :: C16 => L (16) ,
                        TstTagSpec :: C17 => L (17) ,
                        TstTagSpec :: C18 => L (18) ,
                        TstTagSpec :: C19 => L (19) ,
                        TstTagSpec :: C20 => L (20) ,
                        TstTagSpec :: C21 => L (21) ,
                        TstTagSpec :: C22 => L (22) ,
                        TstTagSpec :: C23 => L (23) ,
                        TstTagSpec :: C24 => L (24) ,
                        TstTagSpec :: C25 => L (25) ,
                        TstTagSpec :: C26 => L (26) ,
                        TstTagSpec :: C27 => L (27) ,
                        TstTagSpec :: C28 => L (28) ,
                        TstTagSpec :: C29 => L (29) ,
                        TstTagSpec :: C30 => L (30) ,
                        TstTagSpec :: C31 => L (31) ,
                        TstTagSpec :: C32 => L (32) ,
                        TstTagSpec :: C33 => L (33) ,
                        TstTagSpec :: C34 => L (34) ,
                        TstTagSpec :: C35 => L (35) ,
                        TstTagSpec :: Unknown (x) => R (x) ,
                    }
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `mydata`."]
    # [derive (Clone , Copy)]
    pub struct MydataFmt ;

    pub type MydataFmtSpec = Named < Mapped < Pair < Fixed < 2 > , Fixed < 2 > > , FnSpecMapper < MydataInner , MydataSpec >> > ;

    impl MydataFmt {
        # [doc = "specification constructor for `mydata`."] pub open spec fn spec_inner () -> MydataFmtSpec {
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
    }


    # [doc = "named format combinator for `tst_mydata`."]
    # [derive (Clone , Copy)]
    pub struct TstMydataFmt {
        tag : TstTag ,
    }
    impl TstMydataFmt {
        # [verifier :: type_invariant] spec fn wf (& self) -> bool {
            TstTagFmt . consistent (self . tag . deep_view ())
        }
        pub closed spec fn tag_spec (& self) -> TstTagSpec {
            self . tag . deep_view ()
        }
        pub closed spec fn spec (tag : TstTag) -> Self {
            TstMydataFmt {
                tag
            }
        }
    }

    pub type TstMydataFmtSpec = Named < Mapped < Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Sum < MydataFmt , Tail > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > , FnSpecMapper < TstMydataInner , TstMydataSpec >> > ;

    impl TstMydataFmt {
        # [doc = "specification constructor for `tst_mydata`."] pub open spec fn spec_inner (tag : TstTagSpec) -> TstMydataFmtSpec {
            Named ("tst_mydata" ,
            Mapped {
                inner : match tag {
                    TstTagSpec :: C0 => L (MydataFmt) ,
                    TstTagSpec :: C1 => R (L (MydataFmt)) ,
                    TstTagSpec :: C2 => R (R (L (MydataFmt))) ,
                    TstTagSpec :: C3 => R (R (R (L (MydataFmt)))) ,
                    TstTagSpec :: C4 => R (R (R (R (L (MydataFmt))))) ,
                    TstTagSpec :: C5 => R (R (R (R (R (L (MydataFmt)))))) ,
                    TstTagSpec :: C6 => R (R (R (R (R (R (L (MydataFmt))))))) ,
                    TstTagSpec :: C7 => R (R (R (R (R (R (R (L (MydataFmt)))))))) ,
                    TstTagSpec :: C8 => R (R (R (R (R (R (R (R (L (MydataFmt))))))))) ,
                    TstTagSpec :: C9 => R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))) ,
                    TstTagSpec :: C10 => R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))) ,
                    TstTagSpec :: C11 => R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))) ,
                    TstTagSpec :: C12 => R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))) ,
                    TstTagSpec :: C13 => R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))) ,
                    TstTagSpec :: C14 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))) ,
                    TstTagSpec :: C15 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))) ,
                    TstTagSpec :: C16 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))) ,
                    TstTagSpec :: C17 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))) ,
                    TstTagSpec :: C18 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))) ,
                    TstTagSpec :: C19 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))) ,
                    TstTagSpec :: C20 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))))) ,
                    TstTagSpec :: C21 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))))) ,
                    TstTagSpec :: C22 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))))))) ,
                    TstTagSpec :: C23 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))))))) ,
                    TstTagSpec :: C24 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))))))))) ,
                    TstTagSpec :: C25 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))))))))) ,
                    TstTagSpec :: C26 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))))))))))) ,
                    TstTagSpec :: C27 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))))))))))) ,
                    TstTagSpec :: C28 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))))))))))))) ,
                    TstTagSpec :: C29 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))))))))))))) ,
                    TstTagSpec :: C30 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))))))))))))))) ,
                    TstTagSpec :: C31 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))))))))))))))) ,
                    TstTagSpec :: C32 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))))))))))))))))) ,
                    TstTagSpec :: C33 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))))))))))))))))) ,
                    TstTagSpec :: C34 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt))))))))))))))))))))))))))))))))))) ,
                    TstTagSpec :: C35 => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (MydataFmt)))))))))))))))))))))))))))))))))))) ,
                    _ => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (Tail)))))))))))))))))))))))))))))))))))) ,
                }
                ,
                mapper : (| parsed : TstMydataInner | -> TstMydataSpec {
                    match parsed {
                        L (v) => TstMydataSpec :: C0 (v) ,
                        R (L (v)) => TstMydataSpec :: C1 (v) ,
                        R (R (L (v))) => TstMydataSpec :: C2 (v) ,
                        R (R (R (L (v)))) => TstMydataSpec :: C3 (v) ,
                        R (R (R (R (L (v))))) => TstMydataSpec :: C4 (v) ,
                        R (R (R (R (R (L (v)))))) => TstMydataSpec :: C5 (v) ,
                        R (R (R (R (R (R (L (v))))))) => TstMydataSpec :: C6 (v) ,
                        R (R (R (R (R (R (R (L (v)))))))) => TstMydataSpec :: C7 (v) ,
                        R (R (R (R (R (R (R (R (L (v))))))))) => TstMydataSpec :: C8 (v) ,
                        R (R (R (R (R (R (R (R (R (L (v)))))))))) => TstMydataSpec :: C9 (v) ,
                        R (R (R (R (R (R (R (R (R (R (L (v))))))))))) => TstMydataSpec :: C10 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))) => TstMydataSpec :: C11 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))) => TstMydataSpec :: C12 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))) => TstMydataSpec :: C13 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))) => TstMydataSpec :: C14 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))) => TstMydataSpec :: C15 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))) => TstMydataSpec :: C16 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))) => TstMydataSpec :: C17 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))) => TstMydataSpec :: C18 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))) => TstMydataSpec :: C19 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))) => TstMydataSpec :: C20 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))) => TstMydataSpec :: C21 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))) => TstMydataSpec :: C22 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))) => TstMydataSpec :: C23 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))) => TstMydataSpec :: C24 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))) => TstMydataSpec :: C25 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))) => TstMydataSpec :: C26 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))) => TstMydataSpec :: C27 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))))) => TstMydataSpec :: C28 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))))) => TstMydataSpec :: C29 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))))))) => TstMydataSpec :: C30 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))))))) => TstMydataSpec :: C31 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))))))))) => TstMydataSpec :: C32 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))))))))) => TstMydataSpec :: C33 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))))))))))) => TstMydataSpec :: C34 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))))))))))) => TstMydataSpec :: C35 (v) ,
                        R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (v)))))))))))))))))))))))))))))))))))) => TstMydataSpec :: Default (v) ,
                    }
                }
                ,
                | value : TstMydataSpec | -> TstMydataInner {
                    match value {
                        TstMydataSpec :: C0 (v) => L (v) ,
                        TstMydataSpec :: C1 (v) => R (L (v)) ,
                        TstMydataSpec :: C2 (v) => R (R (L (v))) ,
                        TstMydataSpec :: C3 (v) => R (R (R (L (v)))) ,
                        TstMydataSpec :: C4 (v) => R (R (R (R (L (v))))) ,
                        TstMydataSpec :: C5 (v) => R (R (R (R (R (L (v)))))) ,
                        TstMydataSpec :: C6 (v) => R (R (R (R (R (R (L (v))))))) ,
                        TstMydataSpec :: C7 (v) => R (R (R (R (R (R (R (L (v)))))))) ,
                        TstMydataSpec :: C8 (v) => R (R (R (R (R (R (R (R (L (v))))))))) ,
                        TstMydataSpec :: C9 (v) => R (R (R (R (R (R (R (R (R (L (v)))))))))) ,
                        TstMydataSpec :: C10 (v) => R (R (R (R (R (R (R (R (R (R (L (v))))))))))) ,
                        TstMydataSpec :: C11 (v) => R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))) ,
                        TstMydataSpec :: C12 (v) => R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))) ,
                        TstMydataSpec :: C13 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))) ,
                        TstMydataSpec :: C14 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))) ,
                        TstMydataSpec :: C15 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))) ,
                        TstMydataSpec :: C16 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))) ,
                        TstMydataSpec :: C17 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))) ,
                        TstMydataSpec :: C18 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))) ,
                        TstMydataSpec :: C19 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))) ,
                        TstMydataSpec :: C20 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))) ,
                        TstMydataSpec :: C21 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))) ,
                        TstMydataSpec :: C22 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))) ,
                        TstMydataSpec :: C23 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))) ,
                        TstMydataSpec :: C24 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))) ,
                        TstMydataSpec :: C25 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))) ,
                        TstMydataSpec :: C26 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C27 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C28 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C29 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C30 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C31 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C32 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C33 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C34 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v))))))))))))))))))))))))))))))))))) ,
                        TstMydataSpec :: C35 (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (L (v)))))))))))))))))))))))))))))))))))) ,
                        TstMydataSpec :: Default (v) => R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (R (v)))))))))))))))))))))))))))))))))))) ,
                    }
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `tst`."]
    # [derive (Clone , Copy)]
    pub struct TstFmt ;

    pub type TstFmtSpec = Named < Mapped < Bind < TstTagFmt , spec_fn (TstTagSpec) -> TstMydataFmt > , FnSpecMapper < TstInner , TstSpec >> > ;

    impl TstFmt {
        # [doc = "specification constructor for `tst`."] pub open spec fn spec_inner () -> TstFmtSpec {
            Named ("tst" ,
            Mapped {
                inner : Bind (TstTagFmt ,
                | tag : TstTagSpec | TstMydataFmt :: spec (tag)) ,
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
                TstTagFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for TstTagFmt {
            type Val = TstTagSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                TstTagFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for TstTagFmt {
            type SValue = TstTagSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                TstTagFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for TstTagFmt {
            type SVal = TstTagSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                TstTagFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for TstTagFmt {
            type T = TstTagSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                TstTagFmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for MydataFmt {
            type PVal = MydataSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                MydataFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for MydataFmt {
            type Val = MydataSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                MydataFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for MydataFmt {
            type SValue = MydataSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                MydataFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MydataFmt {
            type SVal = MydataSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                MydataFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for MydataFmt {
            type T = MydataSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                MydataFmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for TstMydataFmt {
            type PVal = TstMydataSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                TstMydataFmt :: spec_inner (self . tag_spec ()) . spec_parse (ibuf)
            }
        }
        impl Consistency for TstMydataFmt {
            type Val = TstMydataSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                TstMydataFmt :: spec_inner (self . tag_spec ()) . consistent (v)
            }
        }
        impl SpecSerializerDps for TstMydataFmt {
            type SValue = TstMydataSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                TstMydataFmt :: spec_inner (self . tag_spec ()) . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for TstMydataFmt {
            type SVal = TstMydataSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                TstMydataFmt :: spec_inner (self . tag_spec ()) . spec_serialize (v)
            }
        }
        impl SpecByteLen for TstMydataFmt {
            type T = TstMydataSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                TstMydataFmt :: spec_inner (self . tag_spec ()) . byte_len (v)
            }
        }

        impl SpecParser for TstFmt {
            type PVal = TstSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                TstFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for TstFmt {
            type Val = TstSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                TstFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for TstFmt {
            type SValue = TstSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                TstFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for TstFmt {
            type SVal = TstSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                TstFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for TstFmt {
            type T = TstSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                TstFmt :: spec_inner () . byte_len (v)
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
                TstTagFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for TstTagFmt {
            open spec fn productive_inv (& self) -> bool {
                TstTagFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                let fmt = TstTagFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for TstTagFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                reveal (< TstTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = TstTagFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecParser > :: spec_parse) ;
                reveal (< TstTagFmt as Consistency > :: consistent) ;
                let fmt = TstTagFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for TstTagFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = TstTagFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< TstTagFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TstTagFmt as SpecByteLen > :: byte_len) ;
                let fmt = TstTagFmt :: spec_inner () ;
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
                let fmt = TstTagFmt :: spec_inner () ;
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
                let fmt = TstTagFmt :: spec_inner () ;
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
                let fmt = TstTagFmt :: spec_inner () ;
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
                let fmt = TstTagFmt :: spec_inner () ;
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
                let fmt = TstTagFmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MydataFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                MydataFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MydataFmt {
            open spec fn productive_inv (& self) -> bool {
                MydataFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                let fmt = MydataFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MydataFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                reveal (< MydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = MydataFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecParser > :: spec_parse) ;
                reveal (< MydataFmt as Consistency > :: consistent) ;
                let fmt = MydataFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MydataFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = MydataFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MydataFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = MydataFmt :: spec_inner () ;
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
                let fmt = MydataFmt :: spec_inner () ;
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
                let fmt = MydataFmt :: spec_inner () ;
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
                let fmt = MydataFmt :: spec_inner () ;
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
                let fmt = MydataFmt :: spec_inner () ;
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
                let fmt = MydataFmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for TstMydataFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                TstMydataFmt :: spec_inner (self . tag_spec ()) . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for TstMydataFmt {
            open spec fn productive_inv (& self) -> bool {
                TstMydataFmt :: spec_inner (self . tag_spec ()) . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                let fmt = TstMydataFmt :: spec_inner (self . tag_spec ()) ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for TstMydataFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                reveal (< TstMydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = TstMydataFmt :: spec_inner (self . tag_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                reveal (< TstMydataFmt as Consistency > :: consistent) ;
                let fmt = TstMydataFmt :: spec_inner (self . tag_spec ()) ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for TstMydataFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< TstMydataFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< TstMydataFmt as SpecByteLen > :: byte_len) ;
                let fmt = TstMydataFmt :: spec_inner (self . tag_spec ()) ;
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
                let fmt = TstMydataFmt :: spec_inner (self . tag_spec ()) ;
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
                let fmt = TstMydataFmt :: spec_inner (self . tag_spec ()) ;
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
                let fmt = TstMydataFmt :: spec_inner (self . tag_spec ()) ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for TstFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                TstFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for TstFmt {
            open spec fn productive_inv (& self) -> bool {
                TstFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                let fmt = TstFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for TstFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                reveal (< TstFmt as SpecByteLen > :: byte_len) ;
                let fmt = TstFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TstFmt as SpecParser > :: spec_parse) ;
                reveal (< TstFmt as Consistency > :: consistent) ;
                let fmt = TstFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for TstFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< TstFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< TstFmt as SpecByteLen > :: byte_len) ;
                let fmt = TstFmt :: spec_inner () ;
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
                let fmt = TstFmt :: spec_inner () ;
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
                let fmt = TstFmt :: spec_inner () ;
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
                let fmt = TstFmt :: spec_inner () ;
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

        impl < 'i > Parser < & 'i [u8] > for TstTagFmt {
            type PT = TstTag ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

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
            31 => TstTag :: C31 ,
            32 => TstTag :: C32 ,
            33 => TstTag :: C33 ,
            34 => TstTag :: C34 ,
            35 => TstTag :: C35 ,
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
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

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
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< TstMydataFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                proof {
                    use_type_invariant(self);
                }

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
            TstTag :: C31 => {
                let (n ,
                v) = (MydataFmt) . parse (& rest) ? ;
                (n ,
                TstMydata :: C31 (v))
            }
            ,
            TstTag :: C32 => {
                let (n ,
                v) = (MydataFmt) . parse (& rest) ? ;
                (n ,
                TstMydata :: C32 (v))
            }
            ,
            TstTag :: C33 => {
                let (n ,
                v) = (MydataFmt) . parse (& rest) ? ;
                (n ,
                TstMydata :: C33 (v))
            }
            ,
            TstTag :: C34 => {
                let (n ,
                v) = (MydataFmt) . parse (& rest) ? ;
                (n ,
                TstMydata :: C34 (v))
            }
            ,
            TstTag :: C35 => {
                let (n ,
                v) = (MydataFmt) . parse (& rest) ? ;
                (n ,
                TstMydata :: C35 (v))
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
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

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

    }
}

