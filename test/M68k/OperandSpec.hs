module M68k.OperandSpec
  ( testOperand
  ) where

import           M68k.Operand
import           M68k.ParseSpec        (regRange, regRange2)
import           Test.Hspec            (Expectation, Spec, SpecWith, describe,
                                        it, shouldBe)
import           Test.Hspec.QuickCheck
import           Test.QuickCheck       (Property, chooseInt, conjoin, elements,
                                        forAll, property)
import           TestCommon
import           Text.Printf

anStr 7 = "%sp"
anStr 6 = "%fp"
anStr n = "%a" ++ show n

rnStr n
  | n < 8 = printf "%%d%d" n
  | otherwise = anStr (n - 8)

testOperand = do
  describe "showEa" $ do
    prop "Dn" $
      testFor regRange $ \x -> show (DReg $ DR x) `shouldBe` printf "%%d%d" x
    prop "An" $ testFor regRange $ \x -> show (AReg $ AR x) `shouldBe` anStr x
    prop "#xxx" $ imm32Test $ \i -> show (ImmInt i) `shouldBe` printf "#%d" i
    it "CCR" $ show CCR `shouldBe` "%ccr"
    it "SR" $ show SR `shouldBe` "%sr"
    prop "(An)" $
      testFor regRange $ \x ->
        show (UnRefAR $ AR x) `shouldBe` printf "(%s)" (anStr x)
    prop "(An)+" $
      testFor regRange $ \x ->
        show (UnRefInc $ AR x) `shouldBe` printf "(%s)+" (anStr x)
    prop "-(An)" $
      testFor regRange $ \x ->
        show (UnRefDec $ AR x) `shouldBe` printf "-(%s)" (anStr x)
    prop "(d16, An)" $
      testFor regRange $ \x ->
        immS16Test $ \i ->
          show (Offset16 i $ BaseAR $ AR x) `shouldBe`
          printf "(%d, %s)" i (anStr x)
    prop "(d16, PC)" $
      testFor regRange $ \x ->
        imm16Test $ \i ->
          show (Offset16 i $ BasePC 100) `shouldBe`
          printf "(0x%05x, %%pc)" (i + 100)
    describe "(d8, An.x, Ri*cc)" $ do
      prop "L" $
        testFor regRange $ \x ->
          immS8Test $ \d ->
            testFor regRange2 $ \r ->
              show (Offset8 d (BaseAR $ AR x) False (xr r) 0) `shouldBe`
              printf "(%d, %v, %v)" d (anStr x) (rnStr r)
      prop "W" $
        testFor regRange $ \x ->
          immS8Test $ \d ->
            testFor regRange2 $ \r ->
              show (Offset8 d (BaseAR $ AR x) True (xr r) 0) `shouldBe`
              printf "(%d, %v, %v.w)" d (anStr x) (rnStr r)
      prop "scaled" $
        testFor regRange $ \x ->
          immS8Test $ \d ->
            testFor regRange2 $ \r ->
              testFor [1 .. 3] $ \c ->
                show (Offset8 d (BaseAR $ AR x) False (xr r) c) `shouldBe`
                printf "(%d, %v, %v << %d)" d (anStr x) (rnStr r) c
    describe "(bd, An.x, Ri*cc)" $ do
      prop "L" $
        testFor regRange $ \x ->
          immS16Test $ \bd ->
            testFor regRange2 $ \r ->
              show (Indirect bd (BaseAR $ AR x) False (Just $ xr r) 0) `shouldBe`
              printf "(%d, %v, %v)" bd (anStr x) (rnStr r)
      prop "W" $
        testFor regRange $ \x ->
          immS16Test $ \bd ->
            testFor regRange2 $ \r ->
              show (Indirect bd (BaseAR $ AR x) True (Just $ xr r) 0) `shouldBe`
              printf "(%d, %v, %v.w)" bd (anStr x) (rnStr r)
      prop "scaled" $
        testFor regRange $ \x ->
          immS16Test $ \bd ->
            testFor regRange2 $ \r ->
              testFor [1 .. 3] $ \c ->
                show (Indirect bd (BaseAR $ AR x) False (Just $ xr r) c) `shouldBe`
                printf "(%d, %v, %v << %d)" bd (anStr x) (rnStr r) c
      prop "no-index" $
        testFor regRange $ \x ->
          immS16Test $ \bd ->
            testFor regRange2 $ \r ->
              show (Indirect bd (BaseAR $ AR x) False Nothing 0) `shouldBe`
              printf "(%d, %v)" bd (anStr x)
