module M68k.DecompileSpec where

import           CExpr
import           CStmt
import           CType
import           Data.Maybe
import qualified Data.Vector           as V
import qualified Data.Vector.Mutable   as MV
import qualified Data.Map.Strict     as M
import           M68k.Decompile
import           M68k.Env
import           M68k.Parse
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck       (chooseInt, forAll)
import           TestCommon
import           Text.Printf           (printf)
import           Util
import Control.Monad.State

updateDn :: Int -> Expr -> State MEnv ()
updateDn n v = do
  e <- get
  put e {v_dr = V.modify (\x -> MV.write x n $ Just v) (v_dr e)}

updateAn :: Int -> Expr -> State MEnv ()
updateAn n v = do
  e <- get
  put e {v_ar = V.modify (\x -> MV.write x n $ Just v) (v_ar e)}

updateCC :: Char -> Expr -> State MEnv ()
updateCC c v = do
  e <- get
  put e {v_cc = M.adjust (const v) c (v_cc e)}

testVar :: CType -> Expr
testVar t = addrOf $ GVar t "test"
envT :: CType -> Int -> MEnv
envT t n = execState ( do                 updateAn n $ testVar t) emptyEnv
testDecompileEA :: Spec
testApplyEaBase :: SpecWith ()
testApplyEaBase =
  let testF env base bd t expected = do
        let (ret, _) = runStateV (applyEaBase base bd t) env
        ret `shouldBe` addrOf expected
   in describe "applyEA" $ do
        it "SP" $
          testF (emptyEnv {v_sp = 100}) (BaseAR 7) 20 int32 (SVar int32 120)
        prop "AR" $ do
          let
          regXTest $ \n ->
            testF
              (envT (PTR int16) n)
              (BaseAR n)
              20
              int16
              (pMemberOf int16 (testVar (PTR int16)) 20)
        it "PC" $
          testF emptyEnv (BasePC 0x100) 0x20 int32 (GVar int32 "C_00120")
        it "zero" $ do testF emptyEnv BaseNone 0x20 int32 (GVar int32 "G_00020")

testDecompileEAAddr :: SpecWith ()
testDecompileEAAddr =
  describe "EA(addr)" $ do
    let testVar' = testVar (PTR VOID)
        envT' = envT (PTR VOID)
        ix = Const int32 2
    prop "(%An)" $
      regTest $ \n -> do
        let ea = operand2Addr (UnRefAR n) int16
            (ret, _) = runStateV ea $ envT int16 n
        ret `shouldBe` testVar int16
    prop "(%An)+" $
      regTest $ \n -> do
        let ea = operand2Addr (UnRefInc n) int16
            (ret, env') = runStateV ea $ envT int16 n
        ret `shouldBe` IncDec True True (anVar (PTR int16) n)
        let x = fromJust (v_ar env' V.! n)
        x `shouldBe` (testVar int16 $+# 1)
    prop "-(%An)" $
      regTest $ \n -> do
        let ea = operand2Addr (UnRefDec n) int16
            (ret, env') = runStateV ea $ envT int16 n
        ret `shouldBe` IncDec False False (anVar (PTR int16) n)
        let x = fromJust (v_ar env' V.! n)
        x `shouldBe` (testVar int16 $-# 1)
    describe "(d, %An)" $ do
      let runTest i base env expected = do
            let ea = operand2Addr (Offset16 i base) int16
                (ret, _) = runStateV ea env
            ret `shouldBe` expected
      prop "d" $
        imm16Test $ \i -> do
          let i' = toS16 i
          runTest i' (BaseAR 0) (envT' 0) $ addrOf (pMemberOf int16 testVar' i')
      prop "normal reg" $
        regXTest $ \rn -> do
          runTest 0x100 (BaseAR rn) (envT' rn) $
            addrOf (pMemberOf int16 testVar' 0x100)
      it "SP" $ do
        let env = emptyEnv {v_sp = 0x3000}
        runTest 0x100 (BaseAR 7) env $ addrOf $ SVar int16 0x3100
      it "PC" $
        runTest 0x100 (BasePC 0x4000) emptyEnv $ addrOf $ GVar int16 "C_04100"
    let envF n = execState ( updateDn n ix )
    describe "(d, %An, %Rn*i)" $ do
      prop "d" $
        forAll (chooseInt (0, 0x7F)) $ \d -> do
          let ea = operand2Addr (Offset8 d (BaseAR 1) False 0 0) int8
              env = envF 0 (envT (PTR VOID) 1)
              (ret, _) = runStateV ea env
          ret `shouldBe` addrOf (addrOf (pMemberOf int8 testVar' d) $@ ix)
      describe "base" $ do
        prop "normal base" $
          regXTest $ \an -> do
            let ea = operand2Addr (Offset8 0 (BaseAR an) False 1 0) int8
                (ret, _) = runStateV ea $ envF 1 (envT int8 an)
            ret `shouldBe` addrOf (testVar int8 $@ ix)
        it "SP" $ do
          let ea = operand2Addr (Offset8 0 (BaseAR 7) False 1 0) uint8
              env = envF 1 emptyEnv {v_sp = 0x1000}
              (ret, _) = runStateV ea env
          ret `shouldBe` addrOf (addrOf (SVar uint8 0x1000) $@ ix)
        it "PC" $ do
          let ea = operand2Addr (Offset8 0 (BasePC 0x2000) False 1 0) uint8
              env = envF 1 emptyEnv
              (ret, _) = runStateV ea env
          ret `shouldBe` addrOf (addrOf (GVar uint8 "C_02000") $@ ix)
      prop "Rn" $ do
        regTest $ \rn -> do
          let ea = operand2Addr (Offset8 0 (BaseAR 1) False rn 0) int8
              env = envF rn (envT int8 1)
              (ret, _) = runStateV ea env
          ret `shouldBe` addrOf (testVar int8 $@ ix)
      describe "Rn.size" $ do
        let doRnTest w val expected =
              let ea = operand2Addr (Offset8 0 (BaseAR 5) w 2 0) int8
                  env = execState (updateDn 2 val) (envT int8 5)
                  (ret, _) = runStateV ea env
               in ret `shouldBe` addrOf (testVar int8 $@ expected)
        it "W" $
          let j = Expr2 (Const uint16 0) (Const int16 0xFFFE)
              j' = Const int32 (-2)
           in doRnTest True j j'
        it "L" $
          let j = Const uint32 13000
           in doRnTest False j j
      describe "cc" $ do
        let doCCTest t cc ixx =
              let ea = operand2Addr (Offset8 0 (BaseAR 1) False 2 cc) t
                  env = envF 2 (envT t 1) 
                  (ret, _) = runStateV ea env
               in ret `shouldBe` addrOf (testVar t $@ ixx)
        describe "0" $ do
          it "int16" $ do doCCTest int16 0 $ ix $>># 1
          it "int32" $ do doCCTest int32 0 $ ix $>># 2
        describe "1" $ do
          it "int8" $ do doCCTest int8 1 $ ix $<<# 1
          it "int16" $ do doCCTest int16 1 ix
          it "int32" $ do doCCTest int32 1 $ ix $>># 1
        describe "2" $ do
          it "int8" $ do doCCTest int8 2 $ ix $<<# 2
          it "int16" $ do doCCTest int16 2 $ ix $<<# 1
          it "int32" $ do doCCTest int32 2 ix
        describe "3" $ do
          it "int8" $ do doCCTest int8 3 $ ix $<<# 3
          it "int16" $ do doCCTest int16 3 $ ix $<<# 2
          it "int32" $ do doCCTest int32 3 $ ix $<<# 1
    describe "(bd, %An, %Rn*i)" $ do
      prop "bd" $
        forAll (chooseInt (0, 0x7FFFFFFF)) $ \d -> do
          let ea = operand2Addr (Indirect d (BaseAR 0) False Nothing 0) int8
              env = envF 1 (envT' 0)
              (ret, _) = runStateV ea env
          ret `shouldBe` addrOf (pMemberOf int8 testVar' d)
      describe "base" $ do
        let doBaseTest base env resultVar =
              let ea = operand2Addr (Indirect 0 base False Nothing 0) int8
                  (ret, _) = runStateV ea env
               in ret `shouldBe` resultVar
        prop "An" $
          forAll (chooseInt (0, 6)) $ \an -> do
            doBaseTest (BaseAR an) (envT' an) (cast (PTR int8) testVar')
        it "SP" $ do
          doBaseTest (BaseAR 7) (emptyEnv {v_sp = 0x1000}) $
            addrOf $ SVar int8 0x1000
        it "PC" $ do
          doBaseTest (BasePC 0x2000) emptyEnv $ addrOf $ GVar int8 "C_02000"
        it "NoBase(0)" $ do
          doBaseTest BaseNone emptyEnv $ addrOf $ GVar int8 "G_00000"
        describe "Rn" $ do
          prop "n" $ do
            regTest $ \rn -> do
              let ea =
                    operand2Addr (Indirect 0 (BaseAR 1) False (Just rn) 0) int8
                  env = execState (do
                      updateAn 1 testVar' 
                      updateDn rn ix) emptyEnv
                  (ret, _) = runStateV ea env
              ret `shouldBe` addrOf (cast (PTR int8) testVar' $@ ix)
          describe "Rn.size" $ do
            let doRnTest w val expected =
                  let ea =
                        operand2Addr (Indirect 0 (BaseAR 5) w (Just 2) 0) int8
                      env = execState (do
                        updateAn 5 testVar' 
                        updateDn 2 val) emptyEnv
                      (ret, _) = runStateV ea env
                   in ret `shouldBe`
                      addrOf (cast (PTR int8) testVar' $@ expected)
            it "W" $
              let j = Expr2 (Const uint16 0) (Const int16 0xFFFE)
                  j' = Const int32 (-2)
               in doRnTest True j j'
            it "L" $
              let j = Const uint32 13000
               in doRnTest False j j
          describe "cc" $ do
            let doCCTest t cc ixx =
                  let ea =
                        operand2Addr (Indirect 0 (BaseAR 1) False (Just 2) cc) t
                      env = envF 2 (envT' 1)
                      (ret, _) = runStateV ea env
                   in ret `shouldBe` addrOf (cast (PTR t) testVar' $@ ixx)
            describe "0" $ do
              it "int16" $ do doCCTest int16 0 $ ix $>># 1
              it "int32" $ do doCCTest int32 0 $ ix $>># 2
            describe "1" $ do
              it "int8" $ do doCCTest int8 1 $ ix $<<# 1
              it "int16" $ do doCCTest int16 1 ix
              it "int32" $ do doCCTest int32 1 $ ix $>># 1
            describe "2" $ do
              it "int8" $ do doCCTest int8 2 $ ix $<<# 2
              it "int16" $ do doCCTest int16 2 $ ix $<<# 1
              it "int32" $ do doCCTest int32 2 ix
            describe "3" $ do
              it "int8" $ do doCCTest int8 3 $ ix $<<# 3
              it "int16" $ do doCCTest int16 3 $ ix $<<# 2
              it "int32" $ do doCCTest int32 3 $ ix $<<# 1
    let testVar2 = testVar (PTR (PTR VOID))
        envT2 = envT (PTR (PTR VOID))
    describe "([bd, *, %Rn*i], od)" $ do
      let testPre base env rn expectedBase =
            imm32Test $ \od ->
              imm32Test $ \bd -> do
                let ea =
                      operand2Addr (PreIndex bd base False (Just rn) 2 od) int8
                    (ret, _) = runStateV ea $ envF rn env
                ret `shouldBe`
                  addrOf (memberOf int8 (addrOf (expectedBase bd) $@ ix) od)
      prop "%An" $
        testPre (BaseAR 0) (envT2 0) 0 (pMemberOf (PTR VOID) testVar2)
      prop "SP" $
        testPre
          (BaseAR 7)
          (emptyEnv {v_sp = 0x1000})
          0
          (\bd -> SVar (PTR VOID) (0x1000 + bd))
      prop "PC" $
        testPre
          (BasePC 0x2000)
          emptyEnv
          0
          (\bd -> GVar (PTR VOID) (printf "C_%05X" (0x2000 + bd)))
      prop "NoBase(0)" $
        testPre BaseNone emptyEnv 0 (GVar (PTR VOID) . printf "G_%05X")
      describe "Rn" $ do
        prop "noIndex; ([bd, *], od)" $ do
          imm32Test $ \od ->
            imm32Test $ \bd -> do
              let ea =
                    operand2Addr
                      (PreIndex bd (BaseAR 0) False Nothing 2 od)
                      int8
                  (ret, _) = runStateV ea $ envF 1 (envT2 0)
              ret `shouldBe`
                addrOf (memberOf int8 (pMemberOf (PTR VOID) testVar2 bd) od)
        prop "n" $
          regTest $ \n ->
            testPre (BaseAR 1) (envT2 1) n (pMemberOf (PTR VOID) testVar2)
        describe "cc" $ do
          let doCCTest cc =
                let ea =
                      operand2Addr
                        (PreIndex 0 (BaseAR 1) False (Just 2) cc 0)
                        int32
                    env = envF 2 (envT' 1)
                    (ret, _) = runStateV ea env
                 in ret `shouldBe`
                    cast
                      (PTR int32)
                      (addrOf $ Index (PTR VOID) testVar' $ ix $<<# (cc - 2))
          it "=2" $ do doCCTest 2
          it "=3" $ do doCCTest 3
    describe "([bd, *], %Rn*i, od)" $ do
      let testPost base env rn expectedBase =
            imm32Test $ \od ->
              imm32Test $ \bd -> do
                let ea =
                      operand2Addr (PostIndex bd base False (Just rn) 0 od) int8
                    (ret, _) = runStateV ea $ envF rn env
                ret `shouldBe`
                  addrOf (addrOf (memberOf int8 (expectedBase bd) od) $@ ix)
      prop "%An" $
        testPost (BaseAR 0) (envT2 0) 0 (pMemberOf (PTR VOID) testVar2)
      prop "SP" $
        testPost (BaseAR 7) (emptyEnv {v_sp = 0x1000}) 0  (\bd -> SVar (PTR VOID) (0x1000 + bd))
      prop "PC" $
        testPost (BasePC 0x2000) emptyEnv 0 (\bd -> GVar (PTR VOID) (printf "C_%05X" (0x2000 + bd)))
      prop "NoBase(0)" $
         testPost BaseNone emptyEnv 0 (GVar (PTR VOID) . printf "G_%05X")
      describe "Rn" $ do
        prop "noIndex; ([bd, *], od)" $ do
          imm32Test $ \od ->
            imm32Test $ \bd -> do
              let ea =
                    operand2Addr
                      (PostIndex bd (BaseAR 0) False Nothing 2 od)
                      int8
                  (ret, _) = runStateV ea $ envF 1 (envT2 0)
              ret `shouldBe`
                addrOf (memberOf int8 (pMemberOf (PTR VOID) testVar2 bd) od)
        prop "n" $
          regTest $ \n ->
            testPost (BaseAR 1) (envT2 1) n (pMemberOf (PTR VOID) testVar2)
    it "(xxxx)" $ do
      let ea = operand2Addr (ImmAddr 0x2000) int8
          (ret, _) = runStateV ea emptyEnv
      ret `shouldBe` VarAddr (GVar int8 "G_02000")

testDecompileEA = do
  describe "EA" $ do
    it "#Imm" $ do
      let ea = operand2Value (ImmInt 2) uint32
      let (ret, _) = runStateV ea emptyEnv
      ret `shouldBe` Const uint32 2
    prop "%Dn" $ do
      forAll (chooseInt (0, 7)) $ \r -> do
        let ea = operand2Value (DR r) uint32
            env = execState (updateDn r (Const uint32 22)) emptyEnv 
            (ret, _) = runStateV ea env
        ret `shouldBe` Const uint32 22
    prop "%An" $ do
      forAll (chooseInt (0, 7)) $ \r -> do
        let ea = operand2Value (AR r) (PTR int32)
            env = execState (updateAn r (Const uint32 32)) emptyEnv 
            (ret, _) = runStateV ea env
        ret `shouldBe` Const (PTR int32) 32
    prop "(addr)" $
      regTest $ \n -> do
        let ea = operand2Value (Address (UnRefAR n)) int16
            (ret, _) = runStateV ea $ envT int16 n
        ret `shouldBe` VarValue (deref $ testVar int16)
  testDecompileEAAddr
  testApplyEaBase
--  testDecompile1