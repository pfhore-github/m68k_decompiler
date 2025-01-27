{-# OPTIONS_GHC -Wall -Wdefault #-}

module M68k.ConvToRtlSpec where

import           AST.CType
import           AST.Common
import           M68k.ConvToRtl (operand2Var, dr_v, ar_v, xr_v)
import           M68k.Parse
import           AST.Expr (deref) 
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import           TestCommon

dx :: Int -> CType -> Var
dx r t = dr t r

ax :: Int -> CType -> Var
ax r t = ar t r

cc2Type :: (Eq a, Num a) => a -> CType
cc2Type 0 = UINT8
cc2Type 1 = UINT16
cc2Type 2 = UINT32
cc2Type 3 = UINT64
cc2Type _ = undefined

testRtlEA :: Spec
testRtlEA =
  let typeTest a b =
        forAll (elements itypes) $ \t -> (operand2Var a t) `shouldBe` (b t)
      ptypeTest a b =
        forAll (elements [INT16, INT32]) $ \t ->
          (operand2Var a t) `shouldBe` (b t)
      scTest = forAll (elements [0 .. 3])
      voidp = PTR VOID
      arp x t = ar (PTR t) x
      arvp x = arp x VOID 
      arvpV x = ExprVar $ arp x VOID 
      ix = ExprVar . xr INT32
      idx = ExprCast INT32 . ExprVar . xr INT16
      base2 = RtlMemoryI voidp . arvpV
   in do describe "var" $ do
           let lv `memTest` rv =
                 regTest $ \r -> (Address $ lv r) `typeTest` (rv r)
               baseNoneX _ = BaseNone
               base2g _ = RtlMemoryG voidp
               base2p pc bd = RtlMemoryC voidp $ pc + bd
           prop "Dn" $ regTest $ \r -> (DR r) `typeTest` (dx r)
           prop "An" $ regTest $ \r -> (AR r) `ptypeTest` (ax r)
           prop "(An)" $ memTest UnRefAR (\r -> deref . arp r)
           prop "(An+)" $
             memTest UnRefInc (\r -> deref . RtlInc False . arp r)
           prop "(-An)" $
             memTest UnRefDec (\r -> deref . RtlDec True . arp r)
           prop "(d16, An)" $
             imm16Test $ \d ->
               memTest (Offset16 d . BaseAR) (\r t -> RtlMemoryI t (arvpV r) d)
           prop "(d16, PC)" $
             imm16Test $ \pc ->
               imm16Test $ \d ->
                 let lv = Address $ Offset16 d (BasePC pc)
                     rv t = RtlMemoryC t $ pc + d
                  in lv `typeTest` rv
           let doD8Test s base expected =
                 rnTest $ \ri ->
                   scTest $ \sc ->
                     immS8Test $ \d ->
                       let lv r = Offset8 d (base r) s ri sc
                           rv r t =
                             VarCast t $
                             RtlMemoryD (cc2Type sc) (ExprVar $ expected r d) $
                             (if s
                                then idx
                                else ix)
                               ri
                        in lv `memTest` rv
           describe "(d8, An, Xn.W*scale)" $ do
             prop ".L" $ doD8Test False BaseAR base2
             prop ".W" $ doD8Test True BaseAR base2
           describe "(d8, PC, Xn.W*scale)" $ do
             prop ".L" $ doD8Test False BasePC base2p
             prop ".W" $ doD8Test True BasePC base2p
           let doIndirectTest s base expected =
                 rnTest $ \ri ->
                   scTest $ \sc ->
                     immS32Test $ \bd ->
                       let lv x = Indirect bd (base x) s (Just ri) sc
                           rv x t =
                             VarCast t $
                             RtlMemoryD (cc2Type sc) (ExprVar $ expected x bd) $
                             (if s
                                then idx
                                else ix)
                               ri
                        in lv `memTest` rv
               doIndirectNoIndexTest base expected =
                 immS32Test $ \bd ->
                   let lv x = Indirect bd (base x) False Nothing 0
                       rv x t = VarCast t $ expected x bd
                    in lv `memTest` rv
           describe "(bd, An, Xn.W*scale)" $ do
             prop ".L" $ doIndirectTest False BaseAR base2
             prop ".W" $ doIndirectTest True BaseAR base2
             prop "no-index" $ doIndirectNoIndexTest BaseAR base2
           describe "(bd, 0, Xn.W*scale)" $ do
             prop ".L" $ doIndirectTest False baseNoneX base2g
             prop ".W" $ doIndirectTest True baseNoneX base2g
             prop "no-index" $ doIndirectNoIndexTest baseNoneX base2g
           describe "(bd, PC, Xn.W*scale)" $ do
             prop ".L" $ doIndirectTest False BasePC base2p
             prop ".W" $ doIndirectTest True BasePC base2p
             prop "no-index" $ doIndirectNoIndexTest BasePC base2p
           let doPreIndexTest s base expected =
                 rnTest $ \ri ->
                   scTest $ \sc ->
                     immS32Test $ \bd ->
                       immS32Test $ \od ->
                         let lv x = PreIndex bd (base x) s (Just ri) sc od
                             rv1 x =
                               VarCast (PTR VOID) $
                               RtlMemoryD (cc2Type sc) (ExprVar $ expected x bd) $
                               (if s
                                  then idx
                                  else ix)
                                 ri
                             rv2 x t = RtlMemoryI t (ExprVar $ rv1 x) od
                          in lv `memTest` rv2
               doPreIndexNoIndexTest base expected =
                 immS32Test $ \bd ->
                   immS32Test $ \od ->
                     let lv x = PreIndex bd (base x) False Nothing 0 od
                         rv1 x = VarCast (PTR VOID) $ expected x bd
                         rv2 x t = RtlMemoryI t (ExprVar $ rv1 x) od
                      in lv `memTest` rv2
           describe "([bd, An, Xn.W*scale], od)" $ do
             prop ".L" $ doPreIndexTest False BaseAR base2
             prop ".W" $ doPreIndexTest True BaseAR base2
             prop "no-index" $ doPreIndexNoIndexTest BaseAR base2
           describe "([bd, 0, Xn.W*scale], od)" $ do
             prop ".L" $ doPreIndexTest False baseNoneX base2g
             prop ".W" $ doPreIndexTest True baseNoneX base2g
             prop "no-index" $ doPreIndexNoIndexTest baseNoneX base2g
           describe "([bd, PC, Xn.W*scale], od)" $ do
             prop ".L" $ doPreIndexTest False BasePC base2p
             prop ".W" $ doPreIndexTest True BasePC base2p
             prop "no-index" $ doPreIndexNoIndexTest BasePC base2p
           let doPostIndexTest s base expected =
                 rnTest $ \ri ->
                   scTest $ \sc ->
                     immS32Test $ \bd ->
                       immS32Test $ \od ->
                         let lv x = PostIndex bd (base x) s (Just ri) sc od
                             rv1 x = RtlMemoryI (PTR VOID) (ExprVar $ expected x bd) od
                             rv2 x t =
                               VarCast t $
                               RtlMemoryD (cc2Type sc) (ExprVar $ rv1 x) $
                               (if s
                                  then idx
                                  else ix)
                                 ri
                          in lv `memTest` rv2
               doPostIndexNoIndexTest base expected =
                 immS32Test $ \bd ->
                   immS32Test $ \od ->
                     let lv x = PostIndex bd (base x) False Nothing 0 od
                         rv1 x = expected x bd
                         rv2 x t =
                           VarCast t $ RtlMemoryI (PTR VOID) (ExprVar $ rv1 x) od
                      in lv `memTest` rv2
           describe "([bd, An], Xn.W*scale, od)" $ do
             prop ".L" $ doPostIndexTest False BaseAR base2
             prop ".W" $ doPostIndexTest True BaseAR base2
             prop "no-index" $ doPostIndexNoIndexTest BaseAR base2
           describe "([bd, 0], Xn.W*scale, od)" $ do
             prop ".L" $ doPostIndexTest False baseNoneX base2g
             prop ".W" $ doPostIndexTest True baseNoneX base2g
             prop "no-index" $ doPostIndexNoIndexTest baseNoneX base2g
           describe "([bd, PC], Xn.W*scale, od)" $ do
             prop ".L" $ doPostIndexTest False BasePC base2p
             prop ".W" $ doPostIndexTest True BasePC base2p
             prop "no-index" $ doPostIndexNoIndexTest BasePC base2p
           prop "(xxxx)" $ do
             imm32Test $ \imm ->
               (Address $ ImmAddr imm) `typeTest` (\t -> RtlMemoryG t imm)
