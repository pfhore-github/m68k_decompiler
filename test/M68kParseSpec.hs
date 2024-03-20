import M68k.Parse
import Test.Hspec
import Control.Monad.State
import Control.Monad.Trans.Maybe
import           Data.Word (Word8)
import Data.Bits
import Control.Monad
main :: IO ()

main =
  let parseOps regT other olist regN =
        evalState ( runMaybeT $ parseEA regT regN other ) (0, olist)
      doTest values result expected =
        forM_ values ( do \x -> (result x) `shouldBe` (expected x) )
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
          (\x -> Just . Address $ Offset16 0x1234 $ BaseAR x)
      describe "(d, An, Ri.w << c)" $ do
        it "An" $ do
          doTest [0..7] (parseOps 6 nothingT [0x00, 0x23])
            (\x -> Just . Address $ Offset8 0x23 (BaseAR x) False 0 0)
        it "Ri" $ do
          doTest [0..15] (\x -> parseOps 6 nothingT [x `shiftL` 4, 0x23] 0)
            (\x -> Just . Address $ Offset8 0x23 (BaseAR 0) False (fromIntegral x) 0)
        it "w" $ do
          doTest [True, False] (\x -> parseOps 6 nothingT [if x then 8 else 0, 0x23] 0)
            (\x -> Just . Address $ Offset8 0x23 (BaseAR 0) x 0 0)
        it "cc" $ do
          doTest [0..3] (\x -> parseOps 6 nothingT [x `shiftL` 1, 0x23] 0)
            (\x -> Just . Address $ Offset8 0x23 (BaseAR 0) False 0 $ fromIntegral x)
        it "ILLEGAL#1(bdSize=0)" $ do
          parseOps 6 nothingT [1, 0] 0 `shouldBe` Nothing
