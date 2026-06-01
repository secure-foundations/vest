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
    # [doc = "data type for `a`."]
    pub type A < 'i > = & 'i [u8] ;
    pub type ASpec = Seq < u8 > ;


    # [doc = "data type for `b`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct B < 'i > {
        pub x : & 'i [u8] ,
        pub y : A < 'i > ,
    }
    # [verifier :: ext_equal]
    pub struct BSpec {
        pub x : Seq < u8 > ,
        pub y : ASpec ,
    }
    pub type BInner = (Seq < u8 > , ASpec) ;
    impl < 'i > DeepView for B < 'i > {
        type V = BSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            BSpec {
                x : self . x . deep_view () ,
                y : self . y . deep_view () ,
            }
        }
    }

    # [doc = "data type for `msg`."]
    # [derive (Debug , PartialEq , Eq , Clone , Copy)]
    pub struct Msg {
        pub a : u8 ,
        pub b : [u8 ;
        2] ,
    }
    # [verifier :: ext_equal]
    pub struct MsgSpec {
        pub a : u8 ,
        pub b : Seq < u8 > ,
    }
    pub type MsgInner = (u8 , Seq < u8 >) ;
    impl DeepView for Msg {
        type V = MsgSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            MsgSpec {
                a : self . a . deep_view () ,
                b : self . b . deep_view () ,
            }
        }
    }

    # [doc = "data type for `tagged_mix`."]
    # [derive (Debug , PartialEq , Eq , Clone)]
    pub struct TaggedMix < 'i > {
        pub x : Option < & 'i [u8] > ,
        pub y : Vec < A < 'i > > ,
        pub z : Option < B < 'i > > ,
        pub w : Vec < Msg > ,
    }
    # [verifier :: ext_equal]
    pub struct TaggedMixSpec {
        pub x : Option < Seq < u8 > > ,
        pub y : Seq < ASpec > ,
        pub z : Option < BSpec > ,
        pub w : Seq < MsgSpec > ,
    }
    pub type TaggedMixInner = (Option < Seq < u8 > > , (Seq < ASpec > , (Option < BSpec > , Seq < MsgSpec >))) ;
    impl < 'i > DeepView for TaggedMix < 'i > {
        type V = TaggedMixSpec ;
        open spec fn deep_view (& self) -> Self :: V {
            TaggedMixSpec {
                x : self . x . deep_view () ,
                y : self . y . deep_view () ,
                z : self . z . deep_view () ,
                w : self . w . deep_view () ,
            }
        }
    }

    # [doc = "data type for `optmsg`."]
    pub type Optmsg = Option < Msg > ;
    pub type OptmsgSpec = Option < MsgSpec > ;

    // ============================================================
    // Format Specifications
    // ============================================================
    # [doc = "named format combinator for `a`."]
    # [derive (Clone , Copy)]
    pub struct AFmt ;

    pub type AFmtSpec = Named < PrefixTagged < U8 , PrefixTagged < U8 , SuffixTagged < Fixed < 10 > , U8 > > > > ;

    impl AFmt {
        # [doc = "specification constructor for `a`."] pub open spec fn spec_inner () -> AFmtSpec {
            Named ("a" ,
            PrefixTagged (U8 ,
            1 ,
            PrefixTagged (U8 ,
            2 ,
            SuffixTagged (Fixed :: < 10 > ,
            U8 ,
            3))))
        }
    }


    # [doc = "named format combinator for `b`."]
    # [derive (Clone , Copy)]
    pub struct BFmt ;

    pub type BFmtSpec = Named < Mapped < Pair < Fixed < 10 > , PrefixTagged < U16Le , SuffixTagged < AFmt , U8 > > > , FnSpecMapper < BInner , BSpec >> > ;

    impl BFmt {
        # [doc = "specification constructor for `b`."] pub open spec fn spec_inner () -> BFmtSpec {
            Named ("b" ,
            Mapped {
                inner : Pair (Fixed :: < 10 > ,
                PrefixTagged (U16Le ,
                65535 ,
                SuffixTagged (AFmt ,
                U8 ,
                1))) ,
                mapper : (| parsed : BInner | -> BSpec {
                    let (x ,
                    y) = parsed ;
                    BSpec {
                        x ,
                        y
                    }
                }
                ,
                | value : BSpec | -> BInner {
                    let BSpec {
                        x ,
                        y
                    }
                    = value ;
                    (x ,
                    y)
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `msg`."]
    # [derive (Clone , Copy)]
    pub struct MsgFmt ;

    pub type MsgFmtSpec = Named < Mapped < Pair < Const < U8 , u8 > , Const < Fixed < 2 > , [u8 ;
    2] > > , FnSpecMapper < MsgInner , MsgSpec >> > ;

    impl MsgFmt {
        # [doc = "specification constructor for `msg`."] pub open spec fn spec_inner () -> MsgFmtSpec {
            Named ("msg" ,
            Mapped {
                inner : Pair (Const (U8 ,
                1) ,
                Const (Fixed :: < 2 > ,
                [0x01u8 , 0x02u8])) ,
                mapper : (| parsed : MsgInner | -> MsgSpec {
                    let (a ,
                    b) = parsed ;
                    MsgSpec {
                        a ,
                        b
                    }
                }
                ,
                | value : MsgSpec | -> MsgInner {
                    let MsgSpec {
                        a ,
                        b
                    }
                    = value ;
                    (a ,
                    b)
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `tagged_mix`."]
    # [derive (Clone , Copy)]
    pub struct TaggedMixFmt ;

    pub type TaggedMixFmtSpec = Named < Mapped < Optional < PrefixTagged < U8 , Fixed < 1 > > , Repeat < PrefixTagged < U8 , AFmt > , Optional < PrefixTagged < U8 , BFmt > , RepeatTillEnd < PrefixTagged < U8 , MsgFmt > > > > > , FnSpecMapper < TaggedMixInner , TaggedMixSpec >> > ;

    impl TaggedMixFmt {
        # [doc = "specification constructor for `tagged_mix`."] pub open spec fn spec_inner () -> TaggedMixFmtSpec {
            Named ("tagged_mix" ,
            Mapped {
                inner : Optional (PrefixTagged (U8 ,
                10 ,
                Fixed :: < 1 >) ,
                Repeat (PrefixTagged (U8 ,
                11 ,
                AFmt) ,
                Optional (PrefixTagged (U8 ,
                12 ,
                BFmt) ,
                RepeatTillEnd (PrefixTagged (U8 ,
                13 ,
                MsgFmt))))) ,
                mapper : (| parsed : TaggedMixInner | -> TaggedMixSpec {
                    let (x ,
                    (y ,
                    (z ,
                    w))) = parsed ;
                    TaggedMixSpec {
                        x ,
                        y ,
                        z ,
                        w
                    }
                }
                ,
                | value : TaggedMixSpec | -> TaggedMixInner {
                    let TaggedMixSpec {
                        x ,
                        y ,
                        z ,
                        w
                    }
                    = value ;
                    (x ,
                    (y ,
                    (z ,
                    w)))
                }
                )
            }
            )
        }
    }


    # [doc = "named format combinator for `optmsg`."]
    # [derive (Clone , Copy)]
    pub struct OptmsgFmt ;

    pub type OptmsgFmtSpec = Named < OptionalEnd < MsgFmt > > ;

    impl OptmsgFmt {
        # [doc = "specification constructor for `optmsg`."] pub open spec fn spec_inner () -> OptmsgFmtSpec {
            Named ("optmsg" ,
            OptionalEnd (MsgFmt))
        }
    }

    // ============================================================
    // Derived Parser, Serializer, Length, and Consistency Specifications
    // ============================================================
    mod derived_specs {
        use super::*;

        impl SpecParser for AFmt {
            type PVal = ASpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                AFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for AFmt {
            type Val = ASpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                AFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for AFmt {
            type SValue = ASpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                AFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for AFmt {
            type SVal = ASpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                AFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for AFmt {
            type T = ASpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                AFmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for BFmt {
            type PVal = BSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                BFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for BFmt {
            type Val = BSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                BFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for BFmt {
            type SValue = BSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                BFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for BFmt {
            type SVal = BSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                BFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for BFmt {
            type T = BSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                BFmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for MsgFmt {
            type PVal = MsgSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                MsgFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for MsgFmt {
            type Val = MsgSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                MsgFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for MsgFmt {
            type SValue = MsgSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                MsgFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for MsgFmt {
            type SVal = MsgSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                MsgFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for MsgFmt {
            type T = MsgSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                MsgFmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for TaggedMixFmt {
            type PVal = TaggedMixSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                TaggedMixFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for TaggedMixFmt {
            type Val = TaggedMixSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                TaggedMixFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for TaggedMixFmt {
            type SValue = TaggedMixSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                TaggedMixFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for TaggedMixFmt {
            type SVal = TaggedMixSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                TaggedMixFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for TaggedMixFmt {
            type T = TaggedMixSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                TaggedMixFmt :: spec_inner () . byte_len (v)
            }
        }

        impl SpecParser for OptmsgFmt {
            type PVal = OptmsgSpec ;
            # [verifier :: opaque] open spec fn spec_parse (& self ,
            ibuf : Seq < u8 >) -> Option < (int ,
            Self :: PVal) > {
                OptmsgFmt :: spec_inner () . spec_parse (ibuf)
            }
        }
        impl Consistency for OptmsgFmt {
            type Val = OptmsgSpec ;
            open spec fn consistent (& self ,
            v : Self :: Val) -> bool {
                OptmsgFmt :: spec_inner () . consistent (v)
            }
        }
        impl SpecSerializerDps for OptmsgFmt {
            type SValue = OptmsgSpec ;
            # [verifier :: opaque] open spec fn spec_serialize_dps (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) -> Seq < u8 > {
                OptmsgFmt :: spec_inner () . spec_serialize_dps (v ,
                obuf)
            }
        }
        impl SpecSerializer for OptmsgFmt {
            type SVal = OptmsgSpec ;
            # [verifier :: opaque] open spec fn spec_serialize (& self ,
            v : Self :: SVal) -> Seq < u8 > {
                OptmsgFmt :: spec_inner () . spec_serialize (v)
            }
        }
        impl SpecByteLen for OptmsgFmt {
            type T = OptmsgSpec ;
            # [verifier :: opaque] open spec fn byte_len (& self ,
            v : Self :: T) -> nat {
                OptmsgFmt :: spec_inner () . byte_len (v)
            }
        }
    }

    // ============================================================
    // Proven Format Properties
    // ============================================================
    mod derived_proofs {
        use super::*;
        broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

        impl SafeParser for AFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AFmt as SpecParser > :: spec_parse) ;
                AFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for AFmt {
            open spec fn productive_inv (& self) -> bool {
                AFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< AFmt as SpecParser > :: spec_parse) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for AFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AFmt as SpecParser > :: spec_parse) ;
                reveal (< AFmt as SpecByteLen > :: byte_len) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< AFmt as SpecParser > :: spec_parse) ;
                reveal (< AFmt as Consistency > :: consistent) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for AFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< AFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< AFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AFmt as SpecByteLen > :: byte_len) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for AFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< AFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< AFmt as SpecByteLen > :: byte_len) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for AFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< AFmt as SpecParser > :: spec_parse) ;
                reveal (< AFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AFmt as Consistency > :: consistent) ;
                reveal (< AFmt as SpecByteLen > :: byte_len) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for AFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< AFmt as SpecParser > :: spec_parse) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for AFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< AFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for AFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< AFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< AFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = AFmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for BFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< BFmt as SpecParser > :: spec_parse) ;
                BFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for BFmt {
            open spec fn productive_inv (& self) -> bool {
                BFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< BFmt as SpecParser > :: spec_parse) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for BFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< BFmt as SpecParser > :: spec_parse) ;
                reveal (< BFmt as SpecByteLen > :: byte_len) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< BFmt as SpecParser > :: spec_parse) ;
                reveal (< BFmt as Consistency > :: consistent) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for BFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< BFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< BFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< BFmt as SpecByteLen > :: byte_len) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for BFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< BFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< BFmt as SpecByteLen > :: byte_len) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for BFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< BFmt as SpecParser > :: spec_parse) ;
                reveal (< BFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< BFmt as Consistency > :: consistent) ;
                reveal (< BFmt as SpecByteLen > :: byte_len) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for BFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< BFmt as SpecParser > :: spec_parse) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for BFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< BFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< BFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for BFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< BFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< BFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = BFmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for MsgFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgFmt as SpecParser > :: spec_parse) ;
                MsgFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for MsgFmt {
            open spec fn productive_inv (& self) -> bool {
                MsgFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< MsgFmt as SpecParser > :: spec_parse) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for MsgFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgFmt as SpecByteLen > :: byte_len) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< MsgFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgFmt as Consistency > :: consistent) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl NonTailFmt for MsgFmt {
            proof fn lemma_serialize_dps_prepend (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MsgFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_prepend (v ,
                obuf) ;
            }
            proof fn lemma_serialize_dps_len (& self ,
            v : Self :: SValue ,
            obuf : Seq < u8 >) {
                reveal (< MsgFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgFmt as SpecByteLen > :: byte_len) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . serialize_dps_inv ()) ;
                fmt . lemma_serialize_dps_len (v ,
                obuf) ;
            }
        }
        impl GoodSerializer for MsgFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< MsgFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< MsgFmt as SpecByteLen > :: byte_len) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for MsgFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< MsgFmt as SpecParser > :: spec_parse) ;
                reveal (< MsgFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgFmt as Consistency > :: consistent) ;
                reveal (< MsgFmt as SpecByteLen > :: byte_len) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for MsgFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< MsgFmt as SpecParser > :: spec_parse) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializersGeneral for MsgFmt {
            proof fn lemma_serialize_equiv (& self ,
            v : Self :: SVal ,
            obuf : Seq < u8 >) {
                reveal (< MsgFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . equiv_general_inv ()) ;
                fmt . lemma_serialize_equiv (v ,
                obuf) ;
            }
        }
        impl EquivSerializers for MsgFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< MsgFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< MsgFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = MsgFmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for TaggedMixFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TaggedMixFmt as SpecParser > :: spec_parse) ;
                TaggedMixFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for TaggedMixFmt {
            open spec fn productive_inv (& self) -> bool {
                TaggedMixFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< TaggedMixFmt as SpecParser > :: spec_parse) ;
                let fmt = TaggedMixFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for TaggedMixFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TaggedMixFmt as SpecParser > :: spec_parse) ;
                reveal (< TaggedMixFmt as SpecByteLen > :: byte_len) ;
                let fmt = TaggedMixFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< TaggedMixFmt as SpecParser > :: spec_parse) ;
                reveal (< TaggedMixFmt as Consistency > :: consistent) ;
                let fmt = TaggedMixFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for TaggedMixFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< TaggedMixFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< TaggedMixFmt as SpecByteLen > :: byte_len) ;
                let fmt = TaggedMixFmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for TaggedMixFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< TaggedMixFmt as SpecParser > :: spec_parse) ;
                reveal (< TaggedMixFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TaggedMixFmt as Consistency > :: consistent) ;
                reveal (< TaggedMixFmt as SpecByteLen > :: byte_len) ;
                let fmt = TaggedMixFmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for TaggedMixFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< TaggedMixFmt as SpecParser > :: spec_parse) ;
                let fmt = TaggedMixFmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for TaggedMixFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< TaggedMixFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< TaggedMixFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = TaggedMixFmt :: spec_inner () ;
                assert (fmt . equiv_inv ()) ;
                fmt . lemma_serialize_equiv_on_empty (v) ;
            }
        }

        impl SafeParser for OptmsgFmt {
            proof fn lemma_parse_safe (& self ,
            ibuf : Seq < u8 >) {
                reveal (< OptmsgFmt as SpecParser > :: spec_parse) ;
                OptmsgFmt :: spec_inner () . lemma_parse_safe (ibuf) ;
            }
        }
        impl Productive for OptmsgFmt {
            open spec fn productive_inv (& self) -> bool {
                OptmsgFmt :: spec_inner () . productive_inv ()
            }
            proof fn lemma_productive (& self ,
            s : Seq < u8 >) {
                reveal (< OptmsgFmt as SpecParser > :: spec_parse) ;
                let fmt = OptmsgFmt :: spec_inner () ;
                assert (fmt . productive_inv ()) ;
                fmt . lemma_productive (s) ;
            }
        }
        impl SoundParser for OptmsgFmt {
            proof fn lemma_parse_sound_consumption (& self ,
            ibuf : Seq < u8 >) {
                reveal (< OptmsgFmt as SpecParser > :: spec_parse) ;
                reveal (< OptmsgFmt as SpecByteLen > :: byte_len) ;
                let fmt = OptmsgFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_consumption (ibuf) ;
            }
            proof fn lemma_parse_sound_value (& self ,
            ibuf : Seq < u8 >) {
                reveal (< OptmsgFmt as SpecParser > :: spec_parse) ;
                reveal (< OptmsgFmt as Consistency > :: consistent) ;
                let fmt = OptmsgFmt :: spec_inner () ;
                assert (fmt . sound_inv ()) ;
                fmt . lemma_parse_sound_value (ibuf) ;
            }
        }
        impl GoodSerializer for OptmsgFmt {
            proof fn lemma_serialize_len (& self ,
            v : Self :: SVal) {
                reveal (< OptmsgFmt as SpecSerializer > :: spec_serialize) ;
                reveal (< OptmsgFmt as SpecByteLen > :: byte_len) ;
                let fmt = OptmsgFmt :: spec_inner () ;
                assert (fmt . serialize_inv ()) ;
                fmt . lemma_serialize_len (v) ;
            }
        }
        impl SPRoundTripDps for OptmsgFmt {
            proof fn theorem_serialize_dps_parse_roundtrip (& self ,
            v : Self :: T ,
            obuf : Seq < u8 >) {
                reveal (< OptmsgFmt as SpecParser > :: spec_parse) ;
                reveal (< OptmsgFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< OptmsgFmt as Consistency > :: consistent) ;
                reveal (< OptmsgFmt as SpecByteLen > :: byte_len) ;
                let fmt = OptmsgFmt :: spec_inner () ;
                assert (fmt . unambiguous ()) ;
                fmt . theorem_serialize_dps_parse_roundtrip (v ,
                obuf) ;
            }
        }
        impl NonMalleable for OptmsgFmt {
            proof fn lemma_parse_non_malleable (& self ,
            buf1 : Seq < u8 > ,
            buf2 : Seq < u8 >) {
                reveal (< OptmsgFmt as SpecParser > :: spec_parse) ;
                let fmt = OptmsgFmt :: spec_inner () ;
                assert (fmt . nonmal_inv ()) ;
                fmt . lemma_parse_non_malleable (buf1 ,
                buf2) ;
            }
        }
        impl EquivSerializers for OptmsgFmt {
            proof fn lemma_serialize_equiv_on_empty (& self ,
            v : Self :: SVal) {
                reveal (< OptmsgFmt as SpecSerializerDps > :: spec_serialize_dps) ;
                reveal (< OptmsgFmt as SpecSerializer > :: spec_serialize) ;
                let fmt = OptmsgFmt :: spec_inner () ;
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

        impl < 'i > Parser < & 'i [u8] > for AFmt {
            type PT = A < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< AFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n , v) = (PrefixTagged (U8 , 1 , PrefixTagged (U8 , 2 , SuffixTagged (Fixed :: < 10 > , U8 , 3)))) . parse (ibuf) ? ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for BFmt {
            type PT = B < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< BFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n1 , x) = (Fixed :: < 10 >) . parse (& rest) ? ;
                let rest = rest.skip(n1);
                let (n2 , y) = (PrefixTagged (U16Le , 65535 , SuffixTagged (AFmt , U8 , 1))) . parse (& rest) ? ;
                let rest = rest.skip(n2);
                let total_n = n1 + n2;
                let final_v = B {
            x ,
            y
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
                Ok((total_n, final_v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for MsgFmt {
            type PT = Msg ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< MsgFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n1 , a) = (Const (U8 , 1)) . parse (& rest) ? ;
                let rest = rest.skip(n1);
                let (n2 , b) = (Const (Fixed :: < 2 > , [0x01 , 0x02])) . parse (& rest) ? ;
                let rest = rest.skip(n2);
                let total_n = n1 + n2;
                let final_v = Msg {
            a ,
            b
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
                Ok((total_n, final_v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for TaggedMixFmt {
            type PT = TaggedMix < 'i > ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< TaggedMixFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n1 , x) = (Opt (PrefixTagged (U8 , 10 , Fixed :: < 1 >))) . parse (& rest) ? ;
                let rest = rest.skip(n1);
                let (n2 , y) = (Star (PrefixTagged (U8 , 11 , AFmt))) . parse (& rest) ? ;
                let rest = rest.skip(n2);
                let (n3 , z) = (Opt (PrefixTagged (U8 , 12 , BFmt))) . parse (& rest) ? ;
                let rest = rest.skip(n3);
                let (n4 , w) = (Star (PrefixTagged (U8 , 13 , MsgFmt))) . parse (& rest) ? ;
                let rest = rest.skip(n4);
                let _ = (Eof) . parse (& rest) ? ;
                let total_n = n1 + n2 + n3 + n4;
                let final_v = TaggedMix {
            x ,
            y ,
            z ,
            w
        }
        ;
                assert (self . spec_parse (ibuf @) == Some ((total_n as int , final_v . deep_view ()))) ;
                Ok((total_n, final_v))
            }
        }



        impl < 'i > Parser < & 'i [u8] > for OptmsgFmt {
            type PT = Optmsg ;

            fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
                broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

                reveal (< OptmsgFmt as SpecParser > :: spec_parse) ;
                let _ = ibuf.len();
                let rest = *ibuf;

                let (n , v) = (Opt (MsgFmt)) . parse (ibuf) ? ;
                let rest = ibuf . skip (n) ;
        let _ = (Eof) . parse (& rest) ? ;
                assert (self . spec_parse (ibuf @) == Some ((n as int , v . deep_view ()))) ;
                Ok((n, v))
            }
        }

    }
}

