{-# OPTIONS_GHC -Wall -Wdefault #-}

module M68k.ConvToRtlSpec where

import           CType
import           Data.Bits             ((.&.), (.>>.))
import           M68k.ConvToRtl
import           M68k.Parse
import           RTL.Stmt
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import           TestCommon
import           Text.Printf           (printf)

testEA2 :: Spec
testEA2 =
  let dx r t = dr t r
      ax r t = ar t r
      typeTest a b =
        forAll (elements itypes) $ \t -> (operand2Var a t) `shouldBe` (b t)
      ptypeTest a b =
        forAll (elements [int16, int32]) $ \t ->
          (operand2Var a t) `shouldBe` (b t)
      scTest = forAll (elements [0 .. 3])
      voidp = PTR VOID
      arp x t = ar (PTR t) x
      arvp x = arp x VOID
      ix = ExprVar . xr int32
      idx = ExprCast int32 . ExprVar . xr int16
      base2 = RtlMemoryI voidp . arvp
   in do describe "var" $ do
           let lv `memTest` rv =
                 regTest $ \r -> (Address $ lv r) `typeTest` (rv r)
               memTest0 lv rv = (Address lv) `typeTest` rv
               base2p = RtlMemoryC voidp
               base2g = RtlMemoryG voidp
           prop "Dn" $ regTest $ \r -> (DR r) `typeTest` (dx r)
           prop "An" $ regTest $ \r -> (AR r) `ptypeTest` (ax r)
           prop "(An)" $ memTest UnRefAR (\r -> RtlMemory . arp r)
           prop "(An+)" $
             memTest UnRefInc (\r -> RtlMemory . RtlIncDec True True . arp r)
           prop "(-An)" $
             memTest UnRefDec (\r -> RtlMemory . RtlIncDec False False . arp r)
           prop "(d16, An)" $
             let t1 d =
                   memTest
                     (Offset16 d . BaseAR)
                     (\r t -> RtlMemoryI t (arvp r) d)
              in immS16Test t1
           prop "(d16, PC)" $
             imm16Test $ \pc ->
               imm16Test $ \d ->
                 let lv = Address $ Offset16 d (BasePC pc)
                     rv t = RtlMemoryC t $ pc + d
                  in lv `typeTest` rv
           describe "(d8, An, Xn.W*scale)" $ do
             let lv ri sc w d rn = Offset8 d (BaseAR rn) w ri sc
                 rv ri sc w d rn t =
                   RtlMemoryD t (base2 rn d) sc $
                   (if w
                      then idx
                      else ix)
                     ri
                 doTest w =
                   rnTest $ \ri ->
                     scTest $ \sc ->
                       immS8Test $ \d -> (lv ri sc w d) `memTest` (rv ri sc w d)
             prop ".L" $ doTest False
             prop ".W" $ doTest True
           describe "(d8, PC, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS8Test $ \d ->
                     let lv pc = Offset8 d (BasePC pc) False ri sc
                         rv pc t = RtlMemoryD t (base2p $ pc + d) sc $ ix ri
                      in lv `memTest` rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS8Test $ \d ->
                     let lv pc = Offset8 d (BasePC pc) True ri sc
                         rv pc t = RtlMemoryD t (base2p $ pc + d) sc $ idx ri
                      in lv `memTest` rv
           describe "(bd, An, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv x = Indirect bd (BaseAR x) False (Just ri) sc
                         rv x t = RtlMemoryD t (base2 x bd) sc $ ix ri
                      in lv `memTest` rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv x = Indirect bd (BaseAR x) True (Just ri) sc
                         rv x t = RtlMemoryD t (base2 x bd) sc $ idx ri
                      in lv `memTest` rv
             prop "no-index" $
               immS32Test $ \bd ->
                 let lv x = Indirect bd (BaseAR x) False Nothing 0
                     rv x _ = base2 x bd
                  in lv `memTest` rv
           describe "(bd, 0, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv = Indirect bd BaseNone False (Just ri) sc
                         rv t = RtlMemoryD t (base2g bd) sc $ ix ri
                      in memTest0 lv rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \d ->
                     let lv x = Indirect d (BaseAR x) True (Just ri) sc
                         rv x t = RtlMemoryD t (base2 x d) sc $ idx ri
                      in lv `memTest` rv
             prop "no-index" $
               immS32Test $ \d ->
                 let lv x = Indirect d (BaseAR x) False Nothing 0
                     rv x _ = base2 x d
                  in lv `memTest` rv
           describe "(bd, PC, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv pc = Indirect bd (BasePC pc) False (Just ri) sc
                         rv pc t = RtlMemoryD t (base2p $ pc + bd) sc $ ix ri
                      in lv `memTest` rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv pc = Indirect bd (BasePC pc) True (Just ri) sc
                         rv pc t = RtlMemoryD t (base2p (pc + bd)) sc $ idx ri
                      in lv `memTest` rv
             prop "no-index" $
               immS32Test $ \bd ->
                 let lv pc = Indirect bd (BasePC pc) False Nothing 0
                     rv pc _ = base2p $ pc + bd
                  in lv `memTest` rv
           describe "([bd, An, Xn.W*scale], od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv x = PreIndex bd (BaseAR x) False (Just ri) sc od
                           rv1 x t = RtlMemoryD t (base2 x bd) sc $ ix ri
                           rv2 x t = RtlMemoryI t (rv1 x t) od
                        in lv `memTest` rv2
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv x = PreIndex bd (BaseAR x) True (Just ri) sc od
                           rv1 x t = RtlMemoryD t (base2 x bd) sc $ idx ri
                           rv2 x t = RtlMemoryI t (rv1 x t) od
                        in lv `memTest` rv2
             prop "no-index" $
               immS32Test $ \bd ->
                 immS32Test $ \od ->
                   let lv x = PreIndex bd (BaseAR x) False Nothing 0 od
                       rv1 x = base2 x bd
                       rv2 x t = RtlMemoryI t (rv1 x) od
                    in lv `memTest` rv2
           describe "([bd, 0, Xn.W*scale], od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv = PreIndex bd BaseNone False (Just ri) sc od
                           rv1 t = RtlMemoryD t (base2g bd) sc $ ix ri
                           rv2 t = RtlMemoryI t (rv1 t) od
                        in memTest0 lv rv2
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv = PreIndex bd BaseNone True (Just ri) sc od
                           rv1 t = RtlMemoryD t (base2g bd) sc $ idx ri
                           rv2 t = RtlMemoryI t (rv1 t) od
                        in memTest0 lv rv2
             prop "no-index" $
               immS32Test $ \bd ->
                 immS32Test $ \od ->
                   let lv = PreIndex bd BaseNone False Nothing 0 od
                       rv1 = base2g bd
                       rv2 t = RtlMemoryI t rv1 od
                    in memTest0 lv rv2
           describe "([bd, PC, Xn.W*scale], od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv pc = PreIndex bd (BasePC pc) False (Just ri) sc od
                           rv1 x t = RtlMemoryD t (base2p $ x + bd) sc $ ix ri
                           rv2 pc t = RtlMemoryI t (rv1 pc t) od
                        in lv `memTest` rv2
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv pc = PreIndex bd (BasePC pc) True (Just ri) sc od
                           rv1 pc t =
                             RtlMemoryD t (base2p $ pc + bd) sc $ idx ri
                           rv2 pc t = RtlMemoryI t (rv1 pc t) od
                        in lv `memTest` rv2
             prop "no-index" $
               immS32Test $ \bd ->
                 immS32Test $ \od ->
                   let lv pc = PreIndex bd (BasePC pc) False Nothing 0 od
                       rv1 pc = base2p $ pc + bd
                       rv2 pc t = RtlMemoryI t (rv1 pc) od
                    in lv `memTest` rv2
           describe "([bd, An], Xn.W*scale, od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv x = PostIndex bd (BaseAR x) False (Just ri) sc od
                           rv1 x t = RtlMemoryI t (base2 x bd) od
                           rv2 x t = RtlMemoryD t (rv1 x t) sc $ ix ri
                        in lv `memTest` rv2
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv x = PostIndex bd (BaseAR x) True (Just ri) sc od
                           rv1 x t = RtlMemoryI t (base2 x bd) od
                           rv2 x t = RtlMemoryD t (rv1 x t) sc $ idx ri
                        in lv `memTest` rv2
             prop "no-index" $
               immS32Test $ \bd ->
                 immS32Test $ \od ->
                   let lv x = PostIndex bd (BaseAR x) False Nothing 0 od
                       rv1 x = base2 x bd
                       rv2 x t = RtlMemoryI t (rv1 x) od
                    in lv `memTest` rv2
           describe "([bd, 0], Xn.W*scale, od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv = PostIndex bd BaseNone False (Just ri) sc od
                           rv1 t = RtlMemoryI t (base2g bd) od
                           rv2 t = RtlMemoryD t (rv1 t) sc $ ix ri
                        in memTest0 lv rv2
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv = PostIndex bd BaseNone True (Just ri) sc od
                           rv1 t = RtlMemoryI t (base2g bd) od
                           rv2 t = RtlMemoryD t (rv1 t) sc $ idx ri
                        in memTest0 lv rv2
             prop "no-index" $
               immS32Test $ \bd ->
                 immS32Test $ \od ->
                   let lv = PostIndex bd BaseNone False Nothing 0 od
                       rv1 = base2g bd
                       rv2 t = RtlMemoryI t rv1 od
                    in memTest0 lv rv2
           describe "([bd, PC], Xn.W*scale, od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv pc =
                             PostIndex bd (BasePC pc) False (Just ri) sc od
                           rv1 pc t = RtlMemoryI t (base2p $ pc + bd) od
                           rv2 pc t = RtlMemoryD t (rv1 pc t) sc $ ix ri
                        in lv `memTest` rv2
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                       let lv pc = PostIndex bd (BasePC pc) True (Just ri) sc od
                           rv1 pc t = RtlMemoryI t (base2p $ pc + bd) od
                           rv2 pc t = RtlMemoryD t (rv1 pc t) sc $ idx ri
                        in lv `memTest` rv2
             prop "no-index" $
               immS32Test $ \bd ->
                 immS32Test $ \od ->
                   let lv pc = PostIndex bd (BasePC pc) False Nothing 0 od
                       rv1 pc = base2p $ pc + bd
                       rv2 pc t = RtlMemoryI t (rv1 pc) od
                    in lv `memTest` rv2
           prop "(xxxx)" $ do
             imm32Test $ \imm -> memTest0 (ImmAddr imm) (\t -> RtlMemoryG t imm)
         describe "opcodes" $ do
           let cc_v = (RtlReg BOOL "V")
               cc_c = (RtlReg BOOL "C")
               cc_z = (RtlReg BOOL "Z")
               cc_n = (RtlReg BOOL "N")
               cc_x = (RtlReg BOOL "X")
               scc_i = (RtlReg uint8 "I")
               scc_m = (RtlReg BOOL "M")
               scc_S = (RtlReg BOOL "S")
               scc_t = (RtlReg uint8 "T")
               false = (ExprImm BOOL 0)
               true = (ExprImm BOOL 1)
               dn :: CType -> Int -> RtlVar
               dn t n = (RtlReg t $ printf "D%d" n)
           prop "ORI.B" $ do
             imm8Test $ \i ->
               toRtl (0, ORI BYTE (DR 1) i) `shouldBe`
               [ StmtAssignOr (dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint8 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint8 1) (ExprImm uint8 0)
               ]
           prop "ORI.B to CCR" $ do
             imm8Test $ \i ->
               toRtl (0, ORI BYTE CCR i) `shouldBe`
               [ StmtAssignOr cc_c $ ExprImm BOOL ((i .>>. 0) Data.Bits..&. 1)
               , StmtAssignOr cc_v $ ExprImm BOOL ((i .>>. 1) Data.Bits..&. 1)
               , StmtAssignOr cc_z $ ExprImm BOOL ((i .>>. 2) Data.Bits..&. 1)
               , StmtAssignOr cc_n $ ExprImm BOOL ((i .>>. 3) Data.Bits..&. 1)
               , StmtAssignOr cc_x $ ExprImm BOOL ((i .>>. 4) Data.Bits..&. 1)
               ]
           prop "ORI.W" $ do
             imm16Test $ \i ->
               toRtl (0, ORI WORD (DR 1) i) `shouldBe`
               [ StmtAssignOr (dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint16 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint16 1) (ExprImm uint16 0)
               ]
           prop "ORI.W to SR" $ do
             imm8Test $ \i ->
               toRtl (0, ORI WORD SR i) `shouldBe`
               [ StmtAssignOr cc_c $ ExprImm BOOL ((i .>>. 0) Data.Bits..&. 1)
               , StmtAssignOr cc_v $ ExprImm BOOL ((i .>>. 1) Data.Bits..&. 1)
               , StmtAssignOr cc_z $ ExprImm BOOL ((i .>>. 2) Data.Bits..&. 1)
               , StmtAssignOr cc_n $ ExprImm BOOL ((i .>>. 3) Data.Bits..&. 1)
               , StmtAssignOr cc_x $ ExprImm BOOL ((i .>>. 4) Data.Bits..&. 1)
               , StmtAssignOr scc_i $ ExprImm uint8 ((i .>>. 8) Data.Bits..&. 3)
               , StmtAssignOr scc_m $ ExprImm BOOL ((i .>>. 9) Data.Bits..&. 1)
               , StmtAssignOr scc_S $ ExprImm BOOL ((i .>>. 10) Data.Bits..&. 1)
               , StmtAssignOr scc_t $
                 ExprImm uint8 ((i .>>. 11) Data.Bits..&. 3)
               ]
           prop "ORI.L" $ do
             imm32Test $ \i ->
               toRtl (0, ORI LONG (DR 1) i) `shouldBe`
               [ StmtAssignOr (dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint32 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint32 1) (ExprImm uint32 0)
               ]
           prop "ANDI.B" $ do
             imm8Test $ \i ->
               toRtl (0, ANDI BYTE (DR 1) i) `shouldBe`
               [ StmtAssignAnd (dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint8 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint8 1) (ExprImm uint8 0)
               ]
           prop "ANDI.B to CCR" $ do
             imm8Test $ \i ->
               toRtl (0, ANDI BYTE CCR i) `shouldBe`
               [ StmtAssignAnd cc_c $ ExprImm BOOL ((i .>>. 0) Data.Bits..&. 1)
               , StmtAssignAnd cc_v $ ExprImm BOOL ((i .>>. 1) Data.Bits..&. 1)
               , StmtAssignAnd cc_z $ ExprImm BOOL ((i .>>. 2) Data.Bits..&. 1)
               , StmtAssignAnd cc_n $ ExprImm BOOL ((i .>>. 3) Data.Bits..&. 1)
               , StmtAssignAnd cc_x $ ExprImm BOOL ((i .>>. 4) Data.Bits..&. 1)
               ]
           prop "ANDI.W" $ do
             imm16Test $ \i ->
               toRtl (0, ANDI WORD (DR 1) i) `shouldBe`
               [ StmtAssignAnd (dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint16 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint16 1) (ExprImm uint16 0)
               ]
           prop "ANDI.W to SR" $ do
             imm8Test $ \i ->
               toRtl (0, ANDI WORD SR i) `shouldBe`
               [ StmtAssignAnd cc_c $ ExprImm BOOL ((i .>>. 0) Data.Bits..&. 1)
               , StmtAssignAnd cc_v $ ExprImm BOOL ((i .>>. 1) Data.Bits..&. 1)
               , StmtAssignAnd cc_z $ ExprImm BOOL ((i .>>. 2) Data.Bits..&. 1)
               , StmtAssignAnd cc_n $ ExprImm BOOL ((i .>>. 3) Data.Bits..&. 1)
               , StmtAssignAnd cc_x $ ExprImm BOOL ((i .>>. 4) Data.Bits..&. 1)
               , StmtAssignAnd scc_i $
                 ExprImm uint8 ((i .>>. 8) Data.Bits..&. 3)
               , StmtAssignAnd scc_m $
                 ExprImm BOOL ((i .>>. 12) Data.Bits..&. 1)
               , StmtAssignAnd scc_S $
                 ExprImm BOOL ((i .>>. 13) Data.Bits..&. 1)
               , StmtAssignAnd scc_t $
                 ExprImm uint8 ((i .>>. 14) Data.Bits..&. 3)
               ]
           prop "ANDI.L" $ do
             imm32Test $ \i ->
               toRtl (0, ANDI LONG (DR 1) i) `shouldBe`
               [ StmtAssignAnd (dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint32 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint32 1) (ExprImm uint32 0)
               ]
           prop "EORI.B" $ do
             imm8Test $ \i ->
               toRtl (0, EORI BYTE (DR 1) i) `shouldBe`
               [ StmtAssignXor (dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint8 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint8 1) (ExprImm uint8 0)
               ]
           prop "EORI.B to CCR" $ do
             imm8Test $ \i ->
               toRtl (0, EORI BYTE CCR i) `shouldBe`
               [ StmtAssignXor cc_c $ ExprImm BOOL ((i .>>. 0) Data.Bits..&. 1)
               , StmtAssignXor cc_v $ ExprImm BOOL ((i .>>. 1) Data.Bits..&. 1)
               , StmtAssignXor cc_z $ ExprImm BOOL ((i .>>. 2) Data.Bits..&. 1)
               , StmtAssignXor cc_n $ ExprImm BOOL ((i .>>. 3) Data.Bits..&. 1)
               , StmtAssignXor cc_x $ ExprImm BOOL ((i .>>. 4) Data.Bits..&. 1)
               ]
           prop "EORI.W" $ do
             imm16Test $ \i ->
               toRtl (0, EORI WORD (DR 1) i) `shouldBe`
               [ StmtAssignXor (dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint16 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint16 1) (ExprImm uint16 0)
               ]
           prop "EORI.W to SR" $ do
             imm8Test $ \i ->
               toRtl (0, EORI WORD SR i) `shouldBe`
               [ StmtAssignXor cc_c $ ExprImm BOOL ((i .>>. 0) Data.Bits..&. 1)
               , StmtAssignXor cc_v $ ExprImm BOOL ((i .>>. 1) Data.Bits..&. 1)
               , StmtAssignXor cc_z $ ExprImm BOOL ((i .>>. 2) Data.Bits..&. 1)
               , StmtAssignXor cc_n $ ExprImm BOOL ((i .>>. 3) Data.Bits..&. 1)
               , StmtAssignXor cc_x $ ExprImm BOOL ((i .>>. 4) Data.Bits..&. 1)
               , StmtAssignXor scc_i $
                 ExprImm uint8 ((i .>>. 8) Data.Bits..&. 3)
               , StmtAssignXor scc_m $
                 ExprImm BOOL ((i .>>. 12) Data.Bits..&. 1)
               , StmtAssignXor scc_S $
                 ExprImm BOOL ((i .>>. 13) Data.Bits..&. 1)
               , StmtAssignXor scc_t $
                 ExprImm uint8 ((i .>>. 14) Data.Bits..&. 3)
               ]
           prop "EORI.L" $ do
             imm32Test $ \i ->
               toRtl (0, EORI LONG (DR 1) i) `shouldBe`
               [ StmtAssignXor (dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_v false
               , StmtAssign cc_c false
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint32 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint32 1) (ExprImm uint32 0)
               ]
           prop "SUBI.B" $ do
             imm8Test $ \i ->
               toRtl (0, SUBI BYTE (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprSubV (ExprVar $ dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_c $
                 ExprSubC (ExprVar $ dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_x $ ExprVar $ cc_c
               , StmtAssignSub (dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint8 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint8 1) (ExprImm uint8 0)
               ]
           prop "SUBI.W" $ do
             imm16Test $ \i ->
               toRtl (0, SUBI WORD (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprSubV (ExprVar $ dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_c $
                 ExprSubC (ExprVar $ dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_x $ ExprVar $ cc_c
               , StmtAssignSub (dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint16 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint16 1) (ExprImm uint16 0)
               ]
           prop "SUBI.L" $ do
             imm32Test $ \i ->
               toRtl (0, SUBI LONG (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprSubV (ExprVar $ dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_c $
                 ExprSubC (ExprVar $ dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_x $ ExprVar $ cc_c
               , StmtAssignSub (dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint32 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint32 1) (ExprImm uint32 0)
               ]
           prop "ADDI.B" $ do
             imm8Test $ \i ->
               toRtl (0, ADDI BYTE (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprAddV (ExprVar $ dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_c $
                 ExprAddC (ExprVar $ dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_x $ ExprVar $ cc_c
               , StmtAssignAdd (dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint8 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint8 1) (ExprImm uint8 0)
               ]
           prop "ADDI.W" $ do
             imm16Test $ \i ->
               toRtl (0, ADDI WORD (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprAddV (ExprVar $ dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_c $
                 ExprAddC (ExprVar $ dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_x $ ExprVar $ cc_c
               , StmtAssignAdd (dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint16 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint16 1) (ExprImm uint16 0)
               ]
           prop "ADDI.L" $ do
             imm32Test $ \i ->
               toRtl (0, ADDI LONG (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprAddV (ExprVar $ dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_c $
                 ExprAddC (ExprVar $ dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_x $ ExprVar $ cc_c
               , StmtAssignAdd (dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_z $ ExprLNot $ ExprVar $ dn uint32 1
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint32 1) (ExprImm uint32 0)
               ]
           prop "CMPI.B" $ do
             imm8Test $ \i ->
               toRtl (0, CMPI BYTE (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprSubV (ExprVar $ dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_c $
                 ExprSubC (ExprVar $ dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_z $
                 ExprEq (ExprVar $ dn uint8 1) (ExprImm uint8 i)
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint8 1) (ExprImm uint8 i)
               ]
           prop "CMPI.W" $ do
             imm16Test $ \i ->
               toRtl (0, CMPI WORD (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprSubV (ExprVar $ dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_c $
                 ExprSubC (ExprVar $ dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_z $
                 ExprEq (ExprVar $ dn uint16 1) (ExprImm uint16 i)
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint16 1) (ExprImm uint16 i)
               ]
           prop "CMPI.L" $ do
             imm32Test $ \i ->
               toRtl (0, CMPI LONG (DR 1) i) `shouldBe`
               [ StmtAssign cc_v $
                 ExprSubV (ExprVar $ dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_c $
                 ExprSubC (ExprVar $ dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_z $
                 ExprEq (ExprVar $ dn uint32 1) (ExprImm uint32 i)
               , StmtAssign cc_n $
                 ExprLt (ExprVar $ dn uint32 1) (ExprImm uint32 i)
               ]
           describe "BTST.B" $ do
             prop "by Imm" $
               forAll (chooseInt (0, 7)) $ \sc ->
                 toRtl (0, BTST BYTE (Address $ UnRefAR 1) (BImm sc)) `shouldBe`
                 [ StmtAssign cc_z $
                   ExprBitTest
                     (ExprVar $ RtlMemory $ ar (PTR uint8) 1)
                     (ExprImm uint8 sc)
                 ]
             prop "by Reg" $
               forAll (chooseInt (0, 7)) $ \sc ->
                 toRtl (0, BTST BYTE (Address $ UnRefAR 1) (BReg sc)) `shouldBe`
                 [ StmtAssign cc_z $
                   ExprBitTest
                     (ExprVar $ RtlMemory $ ar (PTR uint8) 1)
                     (ExprVar $ dr uint32 sc)
                 ]
           describe "BTST.L" $ do
             prop "by Imm" $
               forAll (chooseInt (0, 7)) $ \sc ->
                 toRtl (0, BTST LONG (DR 1) (BImm sc)) `shouldBe`
                 [ StmtAssign cc_z $
                   ExprBitTest (ExprVar $ dr uint32 1) (ExprImm uint8 sc)
                 ]
             prop "by Reg" $
               forAll (chooseInt (0, 7)) $ \sc ->
                 toRtl (0, BTST LONG (DR 1) (BReg sc)) `shouldBe`
                 [ StmtAssign cc_z $
                   ExprBitTest (ExprVar $ dr uint32 1) (ExprVar $ dr uint32 sc)
                 ]
                 {-
         describe "addr" $ do
           let base r = ExprVar $ ar voidp r
               lv `memTest` rv =
                 regTest $ \r -> (operand2Addr (lv r) voidp) `shouldBe` rv r
               memTest0 lv rv = (operand2Addr lv voidp) `shouldBe` rv
               imm = ExprImm voidp
               immO = ExprImm int32
               (@+) a b = ExprOp voidp "+" [a, b]
           prop "(An)" $ memTest UnRefAR base
           prop "(An+)" $
             forAll (elements itypes) $ \t ->
               regTest $ \r ->
                 (operand2Addr (UnRefInc r) t) `shouldBe`
                 (ExprVar $ RtlIncDec True True $ arp r t)
           prop "(-An)" $
             forAll (elements itypes) $ \t ->
               regTest $ \r ->
                 (operand2Addr (UnRefDec r) t) `shouldBe`
                 (ExprVar $ RtlIncDec False False $ arp r t)
           prop "(d16, An)" $
             immS16Test $ \d ->
               memTest
                 (Offset16 d . BaseAR)
                 (\r -> ExprOp voidp "+" [base r, imm d])
           prop "(d16, PC)" $
             imm16Test $ \pc ->
               imm16Test $ \d ->
                 memTest0 (Offset16 d (BasePC pc)) (imm $ d + pc)
           describe "(d8, An, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS8Test $ \d ->
                     let lv r = Offset8 d (BaseAR r) False ri sc
                         rv r = (base r) @+ (imm d) @+ ix ri
                      in lv `memTest` rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS8Test $ \d ->
                     let lv r = Offset8 d (BaseAR r) True ri sc
                         rv r = (base r) @+ (imm d) @+ idx ri
                      in lv `memTest` rv
           describe "(d8, PC, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS8Test $ \d ->
                     let lv pc = Offset8 d (BasePC pc) False ri sc
                         rv pc = (imm $ pc + d) @+ ix ri
                      in lv `memTest` rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS8Test $ \d ->
                     let lv pc = Offset8 d (BasePC pc) True ri sc
                         rv pc = (imm $ pc + d) @+ idx ri
                      in lv `memTest` rv
           describe "(bd, An, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv x = Indirect bd (BaseAR x) False (Just ri) sc
                         rv x = (base x) @+ (immO bd) @+ ix ri
                      in lv `memTest` rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv x = Indirect bd (BaseAR x) True (Just ri) sc
                         rv x = (base x) @+ (immO bd) @+ idx ri
                      in lv `memTest` rv
             prop "no-index" $
               immS32Test $ \bd ->
                 let lv x = Indirect bd (BaseAR x) False Nothing 0
                     rv x = (base x) @+ (immO bd)
                  in lv `memTest` rv
           describe "(bd, 0, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv = Indirect bd BaseNone False (Just ri) sc
                         rv = (immO bd) @+ ix ri
                      in memTest0 lv rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv = Indirect bd BaseNone True (Just ri) sc
                         rv = (immO bd) @+ idx ri
                      in memTest0 lv rv
             prop "no-index" $
               immS32Test $ \bd ->
                 let lv = Indirect bd BaseNone False Nothing 0
                     rv = immO bd
                  in memTest0 lv rv
           describe "(bd, PC, Xn.W*scale)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv pc = Indirect bd (BasePC pc) False (Just ri) sc
                         rv pc = imm (bd + pc) @+ ix ri
                      in lv `memTest` rv
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     let lv pc = Indirect bd (BasePC pc) True (Just ri) sc
                         rv pc = imm (bd + pc) @+ idx ri
                      in lv `memTest` rv
             prop "no-index" $
               immS32Test $ \bd ->
                 let lv pc = Indirect bd (BasePC pc) False Nothing 0
                     rv pc = imm (bd + pc)
                  in lv `memTest` rv
           describe "([bd, An, Xn.W*scale], od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   immS32Test $ \bd ->
                     immS32Test $ \od ->
                   let lv x = PreIndex bd (BaseAR x) False (Just ri) sc od
                       rv1 x = RtlMemoryD (PTR VOID) (base2 x bd) sc $ ix ri
                       rv2 x = (ExprVar $ rv1 x) @+ immO od
                    in lv `memTest` rv2
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od x = PreIndex bd (BaseAR x) True (Just ri) sc od
                       rv1 d x t = RtlMemoryD t (base2 x d) sc $ idx ri
                       rv2 bd od x t = RtlMemoryI t (rv1 bd x t) od
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
             prop "no-index" $
               let lv bd od x = PreIndex bd (BaseAR x) False Nothing 0 od
                   rv1 bd x = base2 x bd
                   rv2 bd od x t = RtlMemoryI t (rv1 bd x) od
                in immS32Test $ \bd ->
                     immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
           describe "([bd, 0, Xn.W*scale], od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od = PreIndex bd BaseNone False (Just ri) sc od
                       rv1 d t =
                         RtlMemoryD t (base2g d) sc $ ix ri
                       rv2 bd od t = RtlMemoryI t (rv1 bd t) od
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest0 (lv bd od) (rv2 bd od)
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od = PreIndex bd BaseNone True (Just ri) sc od
                       rv1 bd t = RtlMemoryD t (base2g bd) sc $ idx ri
                       rv2 bd od t = RtlMemoryI t (rv1 bd t) od
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest0 (lv bd od) (rv2 bd od)
             prop "no-index" $
               let lv bd od = PreIndex bd BaseNone False Nothing 0 od
                   rv1 bd = base2g bd
                   rv2 bd od t = RtlMemoryI t (rv1 bd) od
                in immS32Test $ \bd ->
                     immS32Test $ \od -> memTest0 (lv bd od) (rv2 bd od)
           describe "([bd, PC, Xn.W*scale], od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od pc =
                         PreIndex bd (BasePC pc) False (Just ri) sc od
                       rv1 bd x t =
                         RtlMemoryD
                           t
                           (base2p $ x + bd)
                           sc
                           $ ix ri
                       rv2 bd od pc t = RtlMemoryI t (rv1 bd pc t) od
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od pc =
                         PreIndex bd (BasePC pc) True (Just ri) sc od
                       rv1 d pc t = RtlMemoryD t (base2p $ pc + d) sc $ idx ri
                       rv2 bd od pc t = RtlMemoryI t (rv1 bd pc t) od
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
             prop "no-index" $
               let lv bd od pc = PreIndex bd (BasePC pc) False Nothing 0 od
                   rv1 bd pc = base2p $ pc + bd
                   rv2 bd od pc t = RtlMemoryI t (rv1 bd pc) od
                in immS32Test $ \bd ->
                     immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
           describe "([bd, An], Xn.W*scale, od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od x =
                         PostIndex bd (BaseAR x) False (Just ri) sc od
                       rv1 bd od x t = RtlMemoryI t (base2 x bd) od
                       rv2 bd od x t =
                         RtlMemoryD t (rv1 bd od x t) sc $ ix ri
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od x = PostIndex bd (BaseAR x) True (Just ri) sc od
                       rv1 bd od x t = RtlMemoryI t (base2 x bd) od
                       rv2 bd od x t = RtlMemoryD t (rv1 bd od x t) sc $ idx ri
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
             prop "no-index" $
               let lv bd od x = PostIndex bd (BaseAR x) False Nothing 0 od
                   rv1 bd x = base2 x bd
                   rv2 bd od x t = RtlMemoryI t (rv1 bd x) od
                in immS32Test $ \bd ->
                     immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
           describe "([bd, 0], Xn.W*scale, od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od = PostIndex bd BaseNone False (Just ri) sc od
                       rv1 bd od t = RtlMemoryI t (base2g bd) od
                       rv2 bd od t =
                         RtlMemoryD t (rv1 bd od t) sc $ ix ri
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest0 (lv bd od) (rv2 bd od)
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od = PostIndex bd BaseNone True (Just ri) sc od
                       rv1 bd od t = RtlMemoryI t (base2g bd) od
                       rv2 bd od t = RtlMemoryD t (rv1 bd od t) sc $ idx ri
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest0 (lv bd od) (rv2 bd od)
             prop "no-index" $
               let lv bd od = PostIndex bd BaseNone False Nothing 0 od
                   rv1 bd = base2g bd
                   rv2 bd od t = RtlMemoryI t (rv1 bd) od
                in immS32Test $ \bd ->
                     immS32Test $ \od -> memTest0 (lv bd od) (rv2 bd od)
           describe "([bd, PC], Xn.W*scale, od)" $ do
             prop ".L" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od pc =
                         PostIndex bd (BasePC pc) False (Just ri) sc od
                       rv1 bd od pc t = RtlMemoryI t (base2p $ pc + bd) od
                       rv2 bd od pc t =
                         RtlMemoryD
                           t
                           (rv1 bd od pc t)
                           sc
                           $ ix ri
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
             prop ".W" $
               rnTest $ \ri ->
                 scTest $ \sc ->
                   let lv bd od pc =
                         PostIndex bd (BasePC pc) True (Just ri) sc od
                       rv1 bd od pc t = RtlMemoryI t (base2p $ pc + bd) od
                       rv2 bd od pc t =
                         RtlMemoryD t (rv1 bd od pc t) sc $ idx ri
                    in immS32Test $ \bd ->
                         immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
             prop "no-index" $
               let lv bd od pc = PostIndex bd (BasePC pc) False Nothing 0 od
                   rv1 bd pc = base2p $ pc + bd
                   rv2 bd od pc t = RtlMemoryI t (rv1 bd pc) od
                in immS32Test $ \bd ->
                     immS32Test $ \od -> memTest (lv bd od) (rv2 bd od)
           prop "(xxxx)" $ do
             imm32Test $ \imm -> memTest0 (ImmAddr imm) (\t -> RtlMemoryG t imm)
-}
