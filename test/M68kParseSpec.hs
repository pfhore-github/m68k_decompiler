import M68k.Parse
import Test.Hspec
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Bits
main :: IO ()

main =
  let parseOps regT other olist regN =
        evalState ( runMaybeT $ parseEA regT regN other ) (100, olist)
      parseOpsX nextw base olist =
        evalState ( runMaybeT $ parseEaEx nextw base ) (100, olist)
      doTest values result expected =
        forM_ values ( do \x -> result x `shouldBe` expected x )
  in hspec $ do
    describe "parseEa" $ do
      it "DN" $
        doTest [0..7] (parseOps 0 nothingT []) (Just . DR)
      it "AN" $ do
        doTest [0..7] (parseOps 1 nothingT []) (Just . AR)
      it "(AN)" $ do
        doTest [0..7] (parseOps 2 nothingT []) (Just . Address . UnRefAR)
      it "(AN)+" $ do
        doTest [0..7] (parseOps 3 nothingT []) (Just . Address . UnRefInc)
      it "-(AN)" $ do
        doTest [0..7] (parseOps 4 nothingT []) (Just . Address . UnRefDec)
      it "(d, AN)" $ do
        doTest [0..7] (parseOps 5 nothingT [0x12, 0x34])
          (Just . Address . Offset16 0x1234 . BaseAR)
      it "extra-An" $ do
        doTest [0..7] (parseOps 6 nothingT [0x00, 0x23])
            (\x -> Just . Address $ Offset8 0x23 (BaseAR x) False 0 0)
      it "(imm16)" $ do
        parseOps 7  nothingT [0x12, 0x34] 0 `shouldBe` (Just . Address $ ImmAddr 0x1234)
      it "(imm32)" $ do
        parseOps 7  nothingT [0x12, 0x34, 0x56, 0x78] 1 `shouldBe` (Just . Address $ ImmAddr 0x12345678)
      it "(d, PC)" $ do
        parseOps 7 nothingT [0x12, 0x34] 2 `shouldBe`
          (Just . Address $ Offset16 0x1234 ( BasePC 100))
      it "extra-PC" $ do
        parseOps 7 nothingT [0x00, 0x23] 3 `shouldBe`
            (Just . Address $ Offset8 0x23 (BasePC 100) False 0 0)
      it "other" $ do
        parseOps 7 (do return $ ImmInt 4) [] 4 `shouldBe`
            Just (ImmInt 4)
      it "other-fail" $ do
        parseOps 7 nothingT [] 4 `shouldBe`
            Nothing
      it "fail" $ do
        parseOps 7 nothingT [] 5 `shouldBe`
            Nothing
    describe "parseEa" $ do
      describe "(d, An, Ri.w << c)" $ do
        it "An" $ do
          doTest [0..7] (\x -> parseOpsX 0x0023 (BaseAR x) [])
            (\x -> Just $ Offset8 0x23 (BaseAR x) False 0 0)
        it "Ri" $ do
          doTest [0..15] (\x -> parseOpsX (x `shiftL` 12 .|.  0x23) (BaseAR 0) [])
            (\x -> Just $ Offset8 0x23 (BaseAR 0) False (fromIntegral x) 0)
        it "w" $ do
          doTest [True, False] (\x -> parseOpsX ((if x then 0x800 else 0) .|. 0x23) (BaseAR 0) [])
            (\x -> Just $ Offset8 0x23 (BaseAR 0) x 0 0)
        it "cc" $ do
          doTest [0..3] (\x -> parseOpsX (x `shiftL` 9 .|. 0x23) (BaseAR 0) [])
            (Just . Offset8 0x23 (BaseAR 0) False 0 . fromIntegral)
      it "ILLEGAL#1(bdSize=0)" $ do
          parseOpsX 0x0100 (BaseAR 0) [] `shouldBe` Nothing
      describe "(bd, An, Ri.w << c)" $ do
        describe "bd" $ do
          it "zero" $ do
            parseOpsX 0x0110 (BaseAR 0) [] `shouldBe`
              Just (Indirect 0 (BaseAR 0) False (Just 0) 0)
          it "word" $ do
            parseOpsX 0x0120 (BaseAR 0) [0x12, 0x34] `shouldBe`
              Just (Indirect 0x1234 (BaseAR 0) False (Just 0) 0)
          it "long" $ do
            parseOpsX 0x0130 (BaseAR 0) [0x12, 0x34, 0x56, 0x78] `shouldBe`
              Just (Indirect 0x12345678 (BaseAR 0) False (Just 0) 0)
        it "An" $ do
          doTest [0..7] (\x -> parseOpsX 0x0110 (BaseAR x) [])
            (\x -> Just $ Indirect 0 (BaseAR x) False (Just 0) 0)
        it "Ri" $ do
          doTest [0..15] (\x -> parseOpsX (x `shiftL` 12 .|. 0x110) (BaseAR 0) [])
            (\x -> Just $ Indirect 0 (BaseAR 0) False (Just $ fromIntegral x) 0)
        it "w" $ do
          doTest [True, False] (\x -> parseOpsX ((if x then 0x800 else 0) .|. 0x110) (BaseAR 0) [])
            (\x -> Just $ Indirect 0 (BaseAR 0) x (Just 0) 0)
        it "cc" $ do
          doTest [0..3] (\x -> parseOpsX (x `shiftL` 9 .|. 0x110)  (BaseAR 0) [])
            (Just . Indirect 0 (BaseAR 0) False (Just 0) . fromIntegral)
        it "Base=0" $ do
          parseOpsX 0x0190 (BaseAR 0) [] `shouldBe`
            Just (Indirect 0 BaseNone False (Just 0) 0)
        it "NoIndex" $ do
          parseOpsX 0x0150 (BaseAR 0) [] `shouldBe`
            Just (Indirect 0 (BaseAR 0) False Nothing 0)
      describe "([bd, An, Ri.w << c], od)" $ do
        describe "od" $ do
          it "zero" $ do
            parseOpsX 0x0111 (BaseAR 0) [] `shouldBe`
              Just (PreIndex 0 (BaseAR 0) False (Just 0) 0 0)
          it "word" $ do
            parseOpsX 0x0112 (BaseAR 0) [0x12, 0x34] `shouldBe`
              Just (PreIndex 0 (BaseAR 0) False (Just 0) 0 0x1234)
          it "long" $ do
            parseOpsX 0x0113 (BaseAR 0) [0x12, 0x34, 0x56, 0x78] `shouldBe`
              Just (PreIndex 0 (BaseAR 0) False (Just 0) 0 0x12345678)
        describe "bd" $ do
          it "zero" $ do
            parseOpsX 0x0111 (BaseAR 0) [] `shouldBe`
              Just (PreIndex 0 (BaseAR 0) False (Just 0) 0 0)
          it "word" $ do
            parseOpsX 0x0121 (BaseAR 0) [0x12, 0x34] `shouldBe`
              Just (PreIndex 0x1234 (BaseAR 0) False (Just 0) 0 0)
          it "long" $ do
            parseOpsX 0x0131 (BaseAR 0) [0x12, 0x34, 0x56, 0x78] `shouldBe`
              Just (PreIndex 0x12345678 (BaseAR 0) False (Just 0) 0 0)
        it "An" $ do
          doTest [0..7] (\x -> parseOpsX 0x0111 (BaseAR x) [])
            (\x -> Just $ PreIndex 0 (BaseAR x) False (Just 0) 0 0)
        it "Ri" $ do
          doTest [0..15] (\x -> parseOpsX (x `shiftL` 12 .|. 0x111) (BaseAR 0) [])
            (\x -> Just $ PreIndex 0 (BaseAR 0) False (Just $ fromIntegral x) 0 0)
        it "w" $ do
          doTest [True, False] (\x -> parseOpsX ((if x then 0x800 else 0) .|.  0x111) (BaseAR 0) [])
            (\x -> Just $ PreIndex 0 (BaseAR 0) x (Just 0) 0 0)
        it "cc" $ do
          doTest [0..3] (\x -> parseOpsX (x `shiftL` 9 .|. 0x111) (BaseAR 0) [])
            (\x -> Just $ PreIndex 0 (BaseAR 0) False (Just 0) (fromIntegral x) 0)
        it "Base=0" $ do
          parseOpsX 0x0191 (BaseAR 0) [] `shouldBe`
            Just (PreIndex 0 BaseNone False (Just 0) 0 0)
        it "NoIndex" $ do
          parseOpsX 0x0151 (BaseAR 0) [] `shouldBe`
            Just (PreIndex 0 (BaseAR 0) False Nothing 0 0)
      describe "([bd, An], Ri.w << c, od)" $ do
        it "Invalid(odSize=0)" $ do
          parseOpsX 0x0114 (BaseAR 0) [] `shouldBe` Nothing
        describe "od" $ do
          it "zero" $ do
            parseOpsX 0x0115 (BaseAR 0) [] `shouldBe`
              Just (PostIndex 0 (BaseAR 0) False (Just 0) 0 0)
          it "word" $ do
            parseOpsX 0x0116 (BaseAR 0) [0x12, 0x34] `shouldBe`
              Just (PostIndex 0 (BaseAR 0) False (Just 0) 0 0x1234)
          it "long" $ do
            parseOpsX 0x0117 (BaseAR 0) [0x12, 0x34, 0x56, 0x78] `shouldBe`
              Just (PostIndex 0 (BaseAR 0) False (Just 0) 0 0x12345678)
        describe "bd" $ do
          it "zero" $ do
            parseOpsX 0x0115 (BaseAR 0) [] `shouldBe`
              Just (PostIndex 0 (BaseAR 0) False (Just 0) 0 0)
          it "word" $ do
            parseOpsX 0x0125 (BaseAR 0) [0x12, 0x34] `shouldBe`
              Just (PostIndex 0x1234 (BaseAR 0) False (Just 0) 0 0)
          it "long" $ do
            parseOpsX 0x0135 (BaseAR 0) [0x12, 0x34, 0x56, 0x78] `shouldBe`
              Just (PostIndex 0x12345678 (BaseAR 0) False (Just 0) 0 0)
        it "An" $ do
          doTest [0..7] (\x -> parseOpsX 0x0115 (BaseAR x) [])
            (\x -> Just $ PostIndex 0 (BaseAR x) False (Just 0) 0 0)
        it "Ri" $ do
          doTest [0..15] (\x -> parseOpsX ( x `shiftL` 12 .|. 0x0115) (BaseAR 0) [])
            (\x -> Just $ PostIndex 0 (BaseAR 0) False (Just $ fromIntegral x) 0 0)
        it "w" $ do
          doTest [True, False] (\x -> parseOpsX ((if x then 0x800 else 0) .|. 0x0115) (BaseAR 0) [])
            (\x -> Just $ PostIndex 0 (BaseAR 0) x (Just 0) 0 0)
        it "cc" $ do
          doTest [0..3] (\x -> parseOpsX (x `shiftL` 9 .|. 0x0115) (BaseAR 0) [])
            (\x -> Just $ PostIndex 0 (BaseAR 0) False (Just 0) (fromIntegral x) 0)
        it "Base=0" $ do
          parseOpsX 0x0195 (BaseAR 0) [] `shouldBe`
            Just (PostIndex 0 BaseNone False (Just 0) 0 0)
        it "NoIndex" $ do
          parseOpsX 0x0155 (BaseAR 0) [] `shouldBe`
            Just (PostIndex 0 (BaseAR 0) False Nothing 0 0)
      it "Invalid(BIT3=1)" $ do
        parseOpsX 0x0118 (BaseAR 0) [] `shouldBe` Nothing
