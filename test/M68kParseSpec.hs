import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Bits
import           Data.Maybe
import           Data.Word
import           M68k.Parse
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck           (Property, Testable, chooseInt,
                                            conjoin, elements, forAll)
import           Util
import           UtilSpec

main :: IO ()
word2Byte :: Int -> [Int]
word2Byte v = [v `shiftR` 8, v .&. 0xff]

longToWord :: Int -> [Int]
longToWord c = [c `shiftR` 16, c .&. 0xffff]

intListToByteList :: [Int] -> [Word8]
intListToByteList x = map fromIntegral $ concatMap word2Byte x

testEA :: Spec
testEA = do
  let parseOps regT regN other olist =
        evalState
          (runMaybeT $ parseEA regT regN other)
          (100, intListToByteList olist)
      parseOpsX nextw base olist =
        evalState
          (runMaybeT $ parseEaEx nextw base)
          (100, intListToByteList olist)
  describe "parseEa" $ do
    prop "DN" $
      forAll (chooseInt (0, 7)) $ \x ->
        parseOps 0 x nothingT [] `shouldBe` Just (DR x)
    prop "AN" $
      forAll (chooseInt (0, 7)) $ \x ->
        parseOps 1 x nothingT [] `shouldBe` Just (AR x)
    prop "(AN)" $
      forAll (chooseInt (0, 7)) $ \x ->
        parseOps 2 x nothingT [] `shouldBe` (Just . Address $ UnRefAR x)
    prop "(AN)+" $
      forAll (chooseInt (0, 7)) $ \x ->
        parseOps 3 x nothingT [] `shouldBe` (Just . Address $ UnRefInc x)
    prop "-(AN)" $
      forAll (chooseInt (0, 7)) $ \x ->
        parseOps 4 x nothingT [] `shouldBe` (Just . Address $ UnRefDec x)
    prop "(d, AN)" $
      forAll (chooseInt (0, 7)) $ \x ->
        forAll (chooseInt (1, 65535)) $ \d ->
          parseOps 5 x nothingT [d] `shouldBe`
          (Just . Address $ Offset16 (toS16 d) $ BaseAR x)
    prop "extra-An" $
      forAll (chooseInt (0, 7)) $ \x ->
        forAll (chooseInt (1, 255)) $ \d ->
          parseOps 6 x nothingT [d] `shouldBe`
          (Just . Address $ Offset8 (toS8 d) (BaseAR x) False 0 0)
    prop "(imm16)" $
      forAll (chooseInt (1, 32767)) $ \x ->
        parseOps 7 0 nothingT [x] `shouldBe` (Just . Address $ ImmAddr x)
    prop "(imm32)" $
      forAll (chooseInt (1, 0x7FFFFFFF)) $ \x ->
        parseOps 7 1 nothingT (longToWord x) `shouldBe`
        (Just . Address $ ImmAddr x)
    prop "(d, PC)" $
      forAll (chooseInt (1, 32767)) $ \x ->
        parseOps 7 2 nothingT [x] `shouldBe`
        (Just . Address $ Offset16 x (BasePC 100))
    prop "extra-PC" $
      forAll (chooseInt (1, 127)) $ \x ->
        parseOps 7 3 nothingT [x] `shouldBe`
        (Just . Address $ Offset8 x (BasePC 100) False 0 0)
    prop "other" $ \d ->
      parseOps 7 4 (do return $ ImmInt d) [] `shouldBe` Just (ImmInt d)
    it "other-fail" $ do parseOps 7 4 nothingT [] `shouldBe` Nothing
    it "fail" $ do parseOps 7 5 nothingT [] `shouldBe` Nothing
  describe "parseEaEx" $ do
    let toExtWord x ri w cc =
          x .|. ri `shiftL` 12 .|.
          (if w
             then 0x800
             else 0) .|.
          cc `shiftL` 9
    prop "(d, An, Ri.w << c)" $
      forAll (chooseInt (1, 127)) $ \d ->
        forAll (chooseInt (0, 7)) $ \an ->
          forAll (chooseInt (0, 15)) $ \ri ->
            forAll (elements [False, True]) $ \w ->
              forAll (chooseInt (0, 3)) $ \cc ->
                parseOpsX (toExtWord d ri w cc) (BaseAR an) [] `shouldBe`
                Just (Offset8 d (BaseAR an) w ri cc)
    prop "ILLEGAL#1(bdSize=0)" $
      parseOpsX 0x0100 (BaseAR 0) [] `shouldBe` Nothing
    describe "(bd, An, Ri.w << c)" $ do
      describe "bd" $ do
        prop "zero" $
          forAll (chooseInt (0, 7)) $ \an ->
            forAll (chooseInt (0, 15)) $ \ri ->
              forAll (elements [False, True]) $ \w ->
                forAll (chooseInt (0, 3)) $ \cc ->
                  parseOpsX (toExtWord 0x0110 ri w cc) (BaseAR an) [] `shouldBe`
                  Just (Indirect 0 (BaseAR an) w (Just ri) cc)
        prop "word" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (0, 7)) $ \an ->
              forAll (chooseInt (0, 15)) $ \ri ->
                forAll (elements [False, True]) $ \w ->
                  forAll (chooseInt (0, 3)) $ \cc ->
                    parseOpsX (toExtWord 0x0120 ri w cc) (BaseAR an) [bd] `shouldBe`
                    Just (Indirect bd (BaseAR an) w (Just ri) cc)
        prop "long" $
          forAll (chooseInt (1, 0x7FFFFFFF)) $ \bd ->
            forAll (chooseInt (0, 7)) $ \an ->
              forAll (chooseInt (0, 15)) $ \ri ->
                forAll (elements [False, True]) $ \w ->
                  forAll (chooseInt (0, 3)) $ \cc ->
                    parseOpsX
                      (toExtWord 0x0130 ri w cc)
                      (BaseAR an)
                      (longToWord bd) `shouldBe`
                    Just (Indirect bd (BaseAR an) w (Just ri) cc)
      it "Base=0" $ do
        parseOpsX 0x0190 (BaseAR 0) [] `shouldBe`
          Just (Indirect 0 BaseNone False (Just 0) 0)
      it "NoIndex" $ do
        parseOpsX 0x0150 (BaseAR 0) [] `shouldBe`
          Just (Indirect 0 (BaseAR 0) False Nothing 0)
    describe "([bd, An, Ri.w << c], od)" $ do
      describe "od" $ do
        prop "zero" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (0, 7)) $ \an ->
              forAll (chooseInt (0, 15)) $ \ri ->
                forAll (elements [False, True]) $ \w ->
                  forAll (chooseInt (0, 3)) $ \cc ->
                    parseOpsX (toExtWord 0x0121 ri w cc) (BaseAR an) [bd] `shouldBe`
                    Just (PreIndex bd (BaseAR an) w (Just ri) cc 0)
        prop "word" $
          forAll (chooseInt (1, 32767)) $ \od ->
            forAll (chooseInt (1, 32767)) $ \bd ->
              forAll (chooseInt (0, 7)) $ \an ->
                forAll (chooseInt (0, 15)) $ \ri ->
                  forAll (elements [False, True]) $ \w ->
                    forAll (chooseInt (0, 3)) $ \cc ->
                      parseOpsX (toExtWord 0x0122 ri w cc) (BaseAR an) [bd, od] `shouldBe`
                      Just (PreIndex bd (BaseAR an) w (Just ri) cc od)
        prop "long" $
          forAll (chooseInt (1, 0x7FFFFFFF)) $ \od ->
            forAll (chooseInt (1, 32767)) $ \bd ->
              forAll (chooseInt (0, 7)) $ \an ->
                forAll (chooseInt (0, 15)) $ \ri ->
                  forAll (elements [False, True]) $ \w ->
                    forAll (chooseInt (0, 3)) $ \cc ->
                      parseOpsX
                        (toExtWord 0x0123 ri w cc)
                        (BaseAR an)
                        (bd : longToWord od) `shouldBe`
                      Just (PreIndex bd (BaseAR an) w (Just ri) cc od)
      describe "bd" $ do
        prop "zero" $
          forAll (chooseInt (0, 7)) $ \an ->
            forAll (chooseInt (0, 15)) $ \ri ->
              forAll (elements [False, True]) $ \w ->
                forAll (chooseInt (0, 3)) $ \cc ->
                  parseOpsX (toExtWord 0x0111 ri w cc) (BaseAR an) [] `shouldBe`
                  Just (PreIndex 0 (BaseAR an) w (Just ri) cc 0)
        prop "word" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (0, 7)) $ \an ->
              forAll (chooseInt (0, 15)) $ \ri ->
                forAll (elements [False, True]) $ \w ->
                  forAll (chooseInt (0, 3)) $ \cc ->
                    parseOpsX (toExtWord 0x0121 ri w cc) (BaseAR an) [bd] `shouldBe`
                    Just (PreIndex bd (BaseAR an) w (Just ri) cc 0)
        prop "long" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (0, 7)) $ \an ->
              forAll (chooseInt (0, 15)) $ \ri ->
                forAll (elements [False, True]) $ \w ->
                  forAll (chooseInt (0, 3)) $ \cc ->
                    parseOpsX
                      (toExtWord 0x0131 ri w cc)
                      (BaseAR an)
                      (longToWord bd) `shouldBe`
                    Just (PreIndex bd (BaseAR an) w (Just ri) cc 0)
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
        prop "zero" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (0, 7)) $ \an ->
              forAll (chooseInt (0, 15)) $ \ri ->
                forAll (elements [False, True]) $ \w ->
                  forAll (chooseInt (0, 3)) $ \cc ->
                    parseOpsX (toExtWord 0x0125 ri w cc) (BaseAR an) [bd] `shouldBe`
                    Just (PostIndex bd (BaseAR an) w (Just ri) cc 0)
        prop "word" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (1, 32767)) $ \od ->
              forAll (chooseInt (0, 7)) $ \an ->
                forAll (chooseInt (0, 15)) $ \ri ->
                  forAll (elements [False, True]) $ \w ->
                    forAll (chooseInt (0, 3)) $ \cc ->
                      parseOpsX (toExtWord 0x0126 ri w cc) (BaseAR an) [bd, od] `shouldBe`
                      Just (PostIndex bd (BaseAR an) w (Just ri) cc od)
        prop "long" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (1, 0x7FFFFFFF)) $ \od ->
              forAll (chooseInt (0, 7)) $ \an ->
                forAll (chooseInt (0, 15)) $ \ri ->
                  forAll (elements [False, True]) $ \w ->
                    forAll (chooseInt (0, 3)) $ \cc ->
                      parseOpsX
                        (toExtWord 0x0127 ri w cc)
                        (BaseAR an)
                        (bd : longToWord od) `shouldBe`
                      Just (PostIndex bd (BaseAR an) w (Just ri) cc od)
      describe "bd" $ do
        prop "zero" $
          forAll (chooseInt (0, 7)) $ \an ->
            forAll (chooseInt (0, 15)) $ \ri ->
              forAll (elements [False, True]) $ \w ->
                forAll (chooseInt (0, 3)) $ \cc ->
                  parseOpsX (toExtWord 0x0115 ri w cc) (BaseAR an) [] `shouldBe`
                  Just (PostIndex 0 (BaseAR an) w (Just ri) cc 0)
        prop "word" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (0, 7)) $ \an ->
              forAll (chooseInt (0, 15)) $ \ri ->
                forAll (elements [False, True]) $ \w ->
                  forAll (chooseInt (0, 3)) $ \cc ->
                    parseOpsX (toExtWord 0x0125 ri w cc) (BaseAR an) [bd] `shouldBe`
                    Just (PostIndex bd (BaseAR an) w (Just ri) cc 0)
        prop "long" $
          forAll (chooseInt (1, 32767)) $ \bd ->
            forAll (chooseInt (0, 7)) $ \an ->
              forAll (chooseInt (0, 15)) $ \ri ->
                forAll (elements [False, True]) $ \w ->
                  forAll (chooseInt (0, 3)) $ \cc ->
                    parseOpsX
                      (toExtWord 0x0135 ri w cc)
                      (BaseAR an)
                      (longToWord bd) `shouldBe`
                    Just (PostIndex bd (BaseAR an) w (Just ri) cc 0)
      it "Base=0" $ do
        parseOpsX 0x0195 (BaseAR 0) [] `shouldBe`
          Just (PostIndex 0 BaseNone False (Just 0) 0 0)
      it "NoIndex" $ do
        parseOpsX 0x0155 (BaseAR 0) [] `shouldBe`
          Just (PostIndex 0 (BaseAR 0) False Nothing 0 0)
    it "Invalid(BIT3=1)" $ do parseOpsX 0x0118 (BaseAR 0) [] `shouldBe` Nothing

data EaType
  = EaDN
  | EaAN
  | EaMem
  | EaPC
  | EaImm Int

runTest :: [Int] -> Op -> Expectation
runTest ops result =
  let xops = intListToByteList ops
   in parseOp 0 xops `shouldBe` (0, (result, length xops))

makeOp :: [Int] -> Int -> Int -> [Int]
makeOp ops x d = (head ops .|. x .|. d) : tail ops

checkOpWithEa :: [Int] -> (Operand -> Op) -> EaType -> Property
checkOpWithEa ops expected t = checkOpWithEa2 ops expected t []

checkOpWithEa2 :: [Int] -> (Operand -> Op) -> EaType -> [Int] -> Property
checkOpWithEa2 ops expected EaDN ex =
  forAll (chooseInt (0, 7)) $ \d ->
    runTest (makeOp ops 0o00 d ++ ex) (expected $ DR d)
checkOpWithEa2 ops expected EaAN ex =
  forAll (chooseInt (0, 7)) $ \d ->
    runTest (makeOp ops 0o10 d ++ ex) (expected $ AR d)
checkOpWithEa2 ops expected EaMem ex =
  forAll (chooseInt (1, 0x7fff)) $ \d ->
    forAll (chooseInt (0, 7)) $ \n ->
      runTest
        (makeOp ops 0o50 n ++ [d] ++ ex)
        (expected $ Address $ Offset16 d $ BaseAR n)
checkOpWithEa2 ops expected EaPC ex =
  forAll (chooseInt (1, 0x7fff)) $ \d ->
    runTest
      (makeOp ops 0o72 0 ++ [d] ++ ex)
      (expected $ Address $ Offset16 d $ BasePC $ 2 * length ops)
checkOpWithEa2 ops expected (EaImm 1) ex =
  forAll (chooseInt (0, 0xff)) $ \d ->
    runTest (makeOp ops 0o74 0 ++ [d] ++ ex) (expected $ ImmInt d)
checkOpWithEa2 ops expected (EaImm 2) ex =
  forAll (chooseInt (0, 0xffff)) $ \d ->
    runTest (makeOp ops 0o74 0 ++ [d] ++ ex) (expected $ ImmInt d)
checkOpWithEa2 ops expected (EaImm 4) ex =
  forAll (chooseInt (0, 0xffffffff)) $ \d ->
    runTest (makeOp ops 0o74 0 ++ longToWord d ++ ex) (expected $ ImmInt d)
checkOpWithEa2 _ _ _ _ = undefined

checkOpWithEaMem :: [Int] -> (MemOperand -> Op) -> EaType -> Property
checkOpWithEaMem ops expected EaMem =
  forAll (chooseInt (1, 0x7fff)) $ \d ->
    forAll (chooseInt (0, 7)) $ \r ->
      runTest (makeOp ops 0o50 r ++ [d]) (expected $ Offset16 d $ BaseAR r)
checkOpWithEaMem ops expected EaPC =
  forAll (chooseInt (1, 0x7fff)) $ \d ->
    runTest
      (makeOp ops 0o72 0 ++ [d])
      (expected $ Offset16 d $ BasePC $ 2 * length ops)
checkOpWithEaMem _ _ _ = undefined

main =
  hspec $ do
    testUtil
    testEA
    let testFor target op = conjoin $ map op target
        imm8Test :: (Testable a) => (Int -> a) -> Property
        imm8Test = forAll (chooseInt (0, 0xff))
        imm16Test :: (Testable a) => (Int -> a) -> Property
        imm16Test = forAll (chooseInt (0, 0xffff))
        imm32Test :: (Testable a) => (Int -> a) -> Property
        imm32Test = forAll (chooseInt (0, 0xffffffff))
        regTest :: (Testable a) => (Int -> a) -> Property
        regTest = forAll (chooseInt (0, 7))
        rnTest :: (Testable a) => (Int -> a) -> Property
        rnTest = forAll (chooseInt (0, 15))
        makeRegList v =
          mapMaybe
            (\x ->
               if testBit v x
                 then Just x
                 else Nothing)
            [0 .. 15]
    describe "decode" $ do
      prop "ORI.B" $
        imm8Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o000000, i] $ \x -> ORI BYTE x i
      prop "ORI.B #CCR" $
        imm8Test $ \i -> runTest [0o000074, i] (ORI BYTE CCR i)
      prop "ORI.W" $
        imm16Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o000100, i] $ \x -> ORI WORD x i
      prop "ORI.W #SR" $ imm16Test $ \i -> runTest [0o000174, i] (ORI WORD SR i)
      prop "ORI.L" $
        imm32Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa (0o000200 : longToWord i) $ \x -> ORI LONG x i
      prop "CMP2.B" $
        regTest $ \n ->
          testFor [EaMem] $
          checkOpWithEaMem [0o000300, n `shiftL` 12] $ \x -> CMP2 BYTE x n
      prop "CHK2.B" $
        regTest $ \n ->
          testFor [EaMem] $
          checkOpWithEaMem [0o000300, n `shiftL` 12 .|. 0x800] $ \x ->
            CHK2 BYTE x n
      prop "ANDI.B" $
        imm8Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o001000, i] $ \x -> ANDI BYTE x i
      prop "ANDI.B #CCR" $
        imm8Test $ \i -> runTest [0o001074, i] (ANDI BYTE CCR i)
      prop "ANDI.W" $
        imm16Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o001100, i] $ \x -> ANDI WORD x i
      prop "ANDI.W #SR" $
        imm16Test $ \i -> runTest [0o001174, i] (ANDI WORD SR i)
      prop "ANDI.L" $
        imm32Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa (0o001200 : longToWord i) $ \x -> ANDI LONG x i
      prop "CMP2.W" $
        regTest $ \n ->
          testFor [EaMem] $
          checkOpWithEaMem [0o001300, n `shiftL` 12] $ \x -> CMP2 WORD x n
      prop "CHK2.W" $
        regTest $ \n ->
          testFor [EaMem] $
          checkOpWithEaMem [0o001300, 0x800 .|. n `shiftL` 12] $ \x ->
            CHK2 WORD x n
      prop "SUBI.B" $
        imm8Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o002000, i] $ \x -> SUBI BYTE x i
      prop "SUBI.W" $
        imm16Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o002100, i] $ \x -> SUBI WORD x i
      prop "SUBI.L" $
        imm32Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa (0o002200 : longToWord i) $ \x -> SUBI LONG x i
      prop "CMP2.L" $
        regTest $ \n ->
          testFor [EaMem] $
          checkOpWithEaMem [0o002300, n `shiftL` 12] $ \x -> CMP2 LONG x n
      prop "CHK2.L" $
        regTest $ \n ->
          testFor [EaMem] $
          checkOpWithEaMem [0o002300, 0x800 .|. n `shiftL` 12] $ \x ->
            CHK2 LONG x n
      prop "ADDI.B" $
        imm8Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o003000, i] $ \x -> ADDI BYTE x i
      prop "ADDI.W" $
        imm16Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o003100, i] $ \x -> ADDI WORD x i
      prop "ADDI.L" $
        imm32Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa (0o003200 : longToWord i) $ \x -> ADDI LONG x i
      describe "BTST" $ do
        describe "byImm" $ do
          describe "LONG" $ do
            prop "imm=0(actually 8)" $
              testFor [EaDN] $
              checkOpWithEa [0o004000, 0] $ \x -> BTST LONG x $ BImm 8
            prop "imm!=0" $
              forAll (chooseInt (1, 31)) $ \i ->
                testFor [EaDN] $
                checkOpWithEa [0o004000, i] $ \x -> BTST LONG x $ BImm i
          describe "BYTE" $ do
            prop "imm=0(actually 8)" $
              testFor [EaMem, EaPC, EaImm 1] $
              checkOpWithEa [0o004000, 0] $ \x -> BTST BYTE x $ BImm 8
            prop "imm!=0" $
              forAll (chooseInt (1, 7)) $ \i ->
                testFor [EaMem, EaPC, EaImm 1] $
                checkOpWithEa [0o004000, i] $ \x -> BTST BYTE x $ BImm i
        describe "byReg" $ do
          prop "LONG" $ do
            regTest $ \n ->
              testFor [EaDN] $
              checkOpWithEa
                [0o000400 .|. shiftL n 9]
                (\x -> BTST LONG x $ BReg n)
          prop "BYTE" $ do
            regTest $ \n ->
              testFor [EaMem, EaPC, EaImm 1] $
              checkOpWithEa [0o000400 .|. shiftL n 9] $ \x ->
                BTST BYTE x $ BReg n
      describe "BCHG" $ do
        describe "byImm" $ do
          describe "LONG" $ do
            prop "imm=0(actually 8)" $
              testFor [EaDN] $
              checkOpWithEa [0o004100, 0] $ \x -> BCHG LONG x $ BImm 8
            prop "imm!=0" $
              forAll (chooseInt (1, 31)) $ \i ->
                testFor [EaDN] $
                checkOpWithEa [0o004100, i] $ \x -> BCHG LONG x $ BImm i
          describe "BYTE" $ do
            prop "imm=0(actually 8)" $
              testFor [EaMem] $
              checkOpWithEa [0o004100, 0] $ \x -> BCHG BYTE x $ BImm 8
            prop "imm!=0" $
              forAll (chooseInt (1, 7)) $ \i ->
                testFor [EaMem] $
                checkOpWithEa [0o004100, i] $ \x -> BCHG BYTE x $ BImm i
        describe "byReg" $ do
          prop "LONG" $ do
            regTest $ \n ->
              testFor [EaDN] $
              checkOpWithEa [0o000500 .|. shiftL n 9] $ \x ->
                BCHG LONG x $ BReg n
          prop "BYTE" $ do
            regTest $ \n ->
              testFor [EaMem] $
              checkOpWithEa [0o000500 .|. shiftL n 9] $ \x ->
                BCHG BYTE x $ BReg n
      describe "BCLR" $ do
        describe "byImm" $ do
          describe "LONG" $ do
            prop "imm=0(actually 8)" $
              testFor [EaDN] $
              checkOpWithEa [0o004200, 0] $ \x -> BCLR LONG x $ BImm 8
            prop "imm!=0" $
              forAll (chooseInt (1, 31)) $ \i ->
                testFor [EaDN] $
                checkOpWithEa [0o004200, i] $ \x -> BCLR LONG x $ BImm i
          describe "BYTE" $ do
            prop "imm=0(actually 8)" $
              testFor [EaMem] $
              checkOpWithEa [0o004200, 0] $ \x -> BCLR BYTE x $ BImm 8
            prop "imm!=0" $
              forAll (chooseInt (1, 7)) $ \i ->
                testFor [EaMem] $
                checkOpWithEa [0o004200, i] $ \x -> BCLR BYTE x $ BImm i
        describe "byReg" $ do
          prop "LONG" $ do
            regTest $ \n ->
              testFor [EaDN] $
              checkOpWithEa [0o000600 .|. shiftL n 9] $ \x ->
                BCLR LONG x $ BReg n
          prop "BYTE" $ do
            regTest $ \n ->
              testFor [EaMem] $
              checkOpWithEa [0o000600 .|. shiftL n 9] $ \x ->
                BCLR BYTE x $ BReg n
      describe "BSET" $ do
        describe "byImm" $ do
          describe "LONG" $ do
            prop "imm=0(actually 8)" $
              testFor [EaDN] $
              checkOpWithEa [0o004300, 0] $ \x -> BSET LONG x $ BImm 8
            prop "imm!=0" $
              forAll (chooseInt (1, 31)) $ \i ->
                testFor [EaDN] $
                checkOpWithEa [0o004300, i] $ \x -> BSET LONG x $ BImm i
          describe "BYTE" $ do
            prop "imm=0(actually 8)" $
              testFor [EaMem] $
              checkOpWithEa [0o004300, 0] $ \x -> BSET BYTE x $ BImm 8
            prop "imm!=0" $
              forAll (chooseInt (1, 7)) $ \i ->
                testFor [EaMem] $
                checkOpWithEa [0o004300, i] $ \x -> BSET BYTE x $ BImm i
        describe "byReg" $ do
          prop "LONG" $ do
            regTest $ \n ->
              testFor [EaDN] $
              checkOpWithEa [0o000700 .|. shiftL n 9] $ \x ->
                BSET LONG x $ BReg n
          prop "BYTE" $ do
            regTest $ \n ->
              testFor [EaMem] $
              checkOpWithEa [0o000700 .|. shiftL n 9] $ \x ->
                BSET BYTE x $ BReg n
      prop "EORI.B" $
        imm8Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o005000, i] $ \x -> EORI BYTE x i
      prop "EORI.B #CCR" $
        imm8Test $ \i -> runTest [0o005074, i] $ EORI BYTE CCR i
      prop "EORI.W" $
        imm16Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o005100, i] $ \x -> EORI WORD x i
      prop "EORI.W #SR" $
        imm16Test $ \i -> runTest [0o005174, i] $ EORI WORD SR i
      prop "EORI.L" $
        imm32Test $ \i ->
          testFor [EaDN, EaMem] $
          checkOpWithEa (0o005200 : longToWord i) $ \x -> EORI LONG x i
      prop "CAS.B" $
        regTest $ \u ->
          regTest $ \c ->
            testFor [EaMem] $
            checkOpWithEaMem [0o005300, shiftL u 6 .|. c] $ \x -> CAS BYTE c u x
      prop "SUBI.B" $
        imm8Test $ \i ->
          testFor [EaDN, EaMem, EaPC, EaImm 1] $
          checkOpWithEa [0o006000, i] $ \x -> CMPI BYTE x i
      prop "CMPI.W" $
        imm16Test $ \i ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o006100, i] $ \x -> CMPI WORD x i
      prop "CMPI.L" $
        imm32Test $ \i ->
          testFor [EaDN, EaMem, EaPC, EaImm 4] $
          checkOpWithEa (0o006200 : longToWord i) $ \x -> CMPI LONG x i
      prop "CAS.W" $
        regTest $ \u ->
          regTest $ \c ->
            testFor [EaMem] $
            checkOpWithEaMem [0o006300, shiftL u 6 .|. c] $ \x -> CAS WORD c u x
      prop "CAS2.W" $
        regTest $ \c1 ->
          regTest $ \c2 ->
            regTest $ \u1 ->
              regTest $ \u2 ->
                rnTest $ \r1 ->
                  rnTest $ \r2 ->
                    runTest
                      [ 0o006374
                      , c1 .|. shiftL u1 6 .|. shiftL r1 12
                      , c2 .|. shiftL u2 6 .|. shiftL r2 12
                      ]
                      (CAS2 WORD c1 c2 u1 u2 r1 r2)
      describe "MOVES.B" $ do
        prop "load" $
          rnTest $ \r ->
            testFor [EaMem] $
            checkOpWithEaMem [0o007000, r `shiftL` 12] $ \x ->
              MOVES BYTE False x r
        prop "store" $
          rnTest $ \r ->
            testFor [EaMem] $
            checkOpWithEaMem [0o007000, 0x0800 .|. r `shiftL` 12] $ \x ->
              MOVES BYTE True x r
      describe "MOVES.W" $ do
        prop "load" $
          rnTest $ \r ->
            testFor [EaMem] $
            checkOpWithEaMem [0o007100, r `shiftL` 12] $ \x ->
              MOVES WORD False x r
        prop "store" $
          rnTest $ \r ->
            testFor [EaMem] $
            checkOpWithEaMem [0o007100, 0x0800 .|. r `shiftL` 12] $ \x ->
              MOVES WORD True x r
      describe "MOVES.L" $ do
        prop "load" $
          rnTest $ \r ->
            testFor [EaMem] $
            checkOpWithEaMem [0o007200, r `shiftL` 12] $ \x ->
              MOVES LONG False x r
        prop "store" $
          rnTest $ \r ->
            testFor [EaMem] $
            checkOpWithEaMem [0o007200, 0x0800 .|. r `shiftL` 12] $ \x ->
              MOVES LONG True x r
      prop "CAS.L" $
        regTest $ \u ->
          regTest $ \c ->
            testFor [EaMem] $
            checkOpWithEaMem [0o007300, shiftL u 6 .|. c] $ \x -> CAS LONG c u x
      prop "CAS2.L" $
        regTest $ \c1 ->
          regTest $ \c2 ->
            regTest $ \u1 ->
              regTest $ \u2 ->
                rnTest $ \r1 ->
                  rnTest $ \r2 ->
                    runTest
                      [ 0o007374
                      , c1 .|. shiftL u1 6 .|. shiftL r1 12
                      , c2 .|. shiftL u2 6 .|. shiftL r2 12
                      ]
                      (CAS2 LONG c1 c2 u1 u2 r1 r2)
      describe "MOVE.B" $ do
        prop "toDn" $
          regTest $ \c ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o010000 .|. shiftL c 9] $ \x -> MOVE BYTE x (DR c)
        prop "toMem" $
          regTest $ \c ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o010200 .|. shiftL c 9] $ \x ->
              MOVE BYTE x (Address $ UnRefAR c)
        prop "toMemInc" $
          regTest $ \c ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o010300 .|. shiftL c 9] $ \x ->
              MOVE BYTE x (Address $ UnRefInc c)
        prop "toMemDec" $
          regTest $ \c ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o010400 .|. shiftL c 9] $ \x ->
              MOVE BYTE x (Address $ UnRefDec c)
        prop "toMemOffset16" $
          regTest $ \c ->
            imm16Test $ \d ->
              testFor [EaDN, EaMem, EaPC, EaImm 1] $ \z ->
                checkOpWithEa2
                  [0o010500 .|. shiftL c 9]
                  (\x -> MOVE BYTE x (Address $ Offset16 (toS16 d) (BaseAR c)))
                  z
                  [d]
        prop "toExt" $
          regTest $ \c ->
            imm8Test $ \d ->
              testFor [EaDN, EaMem, EaPC, EaImm 1] $ \z ->
                checkOpWithEa2
                  [0o010600 .|. shiftL c 9]
                  (\x ->
                     MOVE
                       BYTE
                       x
                       (Address $ Offset8 (toS8 d) (BaseAR c) False 0 0))
                  z
                  [d]
        prop "toAddrImm16" $
          imm16Test $ \d ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $ \z ->
              checkOpWithEa2
                [0o010700]
                (\x -> MOVE BYTE x (Address $ ImmAddr d))
                z
                [d]
        prop "toAddrImm32" $
          imm32Test $ \d ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $ \z ->
              checkOpWithEa2
                [0o011700]
                (\x -> MOVE BYTE x (Address $ ImmAddr d))
                z $
              longToWord d
      prop "MOVEA.L" $ do
        regTest $ \c ->
          testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
          checkOpWithEa [0o020100 .|. shiftL c 9] $ \x -> MOVEA LONG x c
      describe "MOVE.L" $ do
        prop "toDn" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o020000 .|. shiftL c 9] $ \x -> MOVE LONG x (DR c)
        prop "toMem" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o020200 .|. shiftL c 9] $ \x ->
              MOVE LONG x (Address $ UnRefAR c)
        prop "toMemInc" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o020300 .|. shiftL c 9] $ \x ->
              MOVE LONG x (Address $ UnRefInc c)
        prop "toMemDec" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o020400 .|. shiftL c 9] $ \x ->
              MOVE LONG x (Address $ UnRefDec c)
        prop "toMemOffset16" $
          regTest $ \c ->
            imm16Test $ \d ->
              testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $ \z ->
                checkOpWithEa2
                  [0o020500 .|. shiftL c 9]
                  (\x -> MOVE LONG x (Address $ Offset16 (toS16 d) (BaseAR c)))
                  z
                  [d]
        prop "toExt" $
          regTest $ \c ->
            imm8Test $ \d ->
              testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $ \z ->
                checkOpWithEa2
                  [0o020600 .|. shiftL c 9]
                  (\x ->
                     MOVE
                       LONG
                       x
                       (Address $ Offset8 (toS8 d) (BaseAR c) False 0 0))
                  z
                  [d]
        prop "toAddrImm16" $
          imm16Test $ \d ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $ \z ->
              checkOpWithEa2
                [0o020700]
                (\x -> MOVE LONG x (Address $ ImmAddr d))
                z
                [d]
        prop "toAddrImm32" $
          imm32Test $ \d ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $ \z ->
              checkOpWithEa2
                [0o021700]
                (\x -> MOVE LONG x (Address $ ImmAddr d))
                z $
              longToWord d
      prop "MOVEA.W" $ do
        regTest $ \c ->
          testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o030100 .|. shiftL c 9] $ \x -> MOVEA WORD x c
      describe "MOVE.W" $ do
        prop "toDn" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o030000 .|. shiftL c 9] $ \x -> MOVE WORD x (DR c)
        prop "toMem" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o030200 .|. shiftL c 9] $ \x ->
              MOVE WORD x (Address $ UnRefAR c)
        prop "toMemInc" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o030300 .|. shiftL c 9] $ \x ->
              MOVE WORD x (Address $ UnRefInc c)
        prop "toMemDec" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o030400 .|. shiftL c 9] $ \x ->
              MOVE WORD x (Address $ UnRefDec c)
        prop "toMemOffset16" $
          regTest $ \c ->
            imm16Test $ \d ->
              testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $ \z ->
                checkOpWithEa2
                  [0o030500 .|. shiftL c 9]
                  (\x -> MOVE WORD x (Address $ Offset16 (toS16 d) (BaseAR c)))
                  z
                  [d]
        prop "toExt" $
          regTest $ \c ->
            imm8Test $ \d ->
              testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $ \z ->
                checkOpWithEa2
                  [0o030600 .|. shiftL c 9]
                  (\x ->
                     MOVE
                       WORD
                       x
                       (Address $ Offset8 (toS8 d) (BaseAR c) False 0 0))
                  z
                  [d]
        prop "toAddrImm16" $
          imm16Test $ \d ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $ \z ->
              checkOpWithEa2
                [0o030700]
                (\x -> MOVE WORD x (Address $ ImmAddr d))
                z
                [d]
        prop "toAddrImm32" $
          imm32Test $ \d ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $ \z ->
              checkOpWithEa2
                [0o031700]
                (\x -> MOVE WORD x (Address $ ImmAddr d))
                z $
              longToWord d
      prop "NEGX.B" $
        testFor [EaDN, EaMem] $ checkOpWithEa [0o040000] $ NEGX BYTE
      prop "NEGX.W" $
        testFor [EaDN, EaMem] $ checkOpWithEa [0o040100] $ NEGX WORD
      prop "NEGX.L" $
        testFor [EaDN, EaMem] $ checkOpWithEa [0o040200] $ NEGX LONG
      prop "MOVE.W from SR" $
        testFor [EaDN, EaMem] $ checkOpWithEa [0o040300] $ MOVE WORD SR
      prop "CLR.B" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o041000] $ CLR BYTE
      prop "CLR.W" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o041100] $ CLR WORD
      prop "CLR.L" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o041200] $ CLR LONG
      prop "MOVE.W from CCR" $
        testFor [EaDN, EaMem] $ checkOpWithEa [0o041300] $ MOVE WORD CCR
      prop "NEG.B" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o042000] $ NEG BYTE
      prop "NEG.W" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o042100] $ NEG WORD
      prop "NEG.L" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o042200] $ NEG LONG
      prop "MOVE.W to CCR" $
        testFor [EaDN, EaMem, EaPC, EaImm 2] $
        checkOpWithEa [0o042300] $ \x -> MOVE WORD x CCR
      prop "NOT.B" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o043000] $ NOT BYTE
      prop "NOT.W" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o043100] $ NOT WORD
      prop "NOT.L" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o043200] $ NOT LONG
      prop "MOVE.W to SR" $
        testFor [EaDN, EaMem, EaPC, EaImm 2] $
        checkOpWithEa [0o043300] $ \x -> MOVE WORD x SR
      prop "NBCD" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o044000] $ NBCD BYTE
      prop "LINK.L" $
        regTest $ \c ->
          imm32Test $ \i -> runTest ((0o044010 .|. c) : longToWord i) $ LINK c i
      prop "SWAP" $ regTest $ \c -> runTest [0o044100 .|. c] $ SWAP c
      prop "BKPT" $ regTest $ \c -> runTest [0o044110 .|. c] $ BKPT c
      prop "PEA" $ testFor [EaMem, EaPC] $ checkOpWithEaMem [0o044100] PEA
      prop "EXT.W" $ regTest $ \c -> runTest [0o044200 .|. c] $ EXT WORD c
      describe "MOVEM.W" $ do
        describe "store" $ do
          prop "decr" $
            regTest $ \c ->
              imm16Test $ \i ->
                runTest [0o044240 .|. c, i] $
                MOVEM WORD True (UnRefDec c) $ makeRegList i
          prop "addr" $
            imm16Test $ \i ->
              testFor [EaMem] $
              checkOpWithEaMem [0o044200, i] $ \x ->
                MOVEM WORD True x $ makeRegList i
        describe "load" $ do
          prop "incr" $
            regTest $ \c ->
              imm16Test $ \i ->
                runTest [0o046230 .|. c, i] $
                MOVEM WORD False (UnRefInc c) $ makeRegList i
          prop "addr" $
            imm16Test $ \i ->
              testFor [EaMem] $
              checkOpWithEaMem [0o046200, i] $ \x ->
                MOVEM WORD False x $ makeRegList i
      prop "EXT.L" $ regTest $ \c -> runTest [0o044300 .|. c] $ EXT LONG c
      describe "MOVEM.L" $ do
        describe "store" $ do
          prop "decr" $
            regTest $ \c ->
              imm16Test $ \i ->
                runTest [0o044340 .|. c, i] $
                MOVEM LONG True (UnRefDec c) $ makeRegList i
          prop "addr" $
            imm16Test $ \i ->
              testFor [EaMem] $
              checkOpWithEaMem [0o044300, i] $ \x ->
                MOVEM LONG True x $ makeRegList i
        describe "load" $ do
          prop "incr" $
            regTest $ \c ->
              imm16Test $ \i ->
                runTest [0o046330 .|. c, i] $
                MOVEM LONG False (UnRefInc c) $ makeRegList i
          prop "addr" $
            imm16Test $ \i ->
              testFor [EaMem] $
              checkOpWithEaMem [0o046300, i] $ \x ->
                MOVEM LONG False x $ makeRegList i
      prop "TST.B" $
        testFor [EaDN, EaMem, EaPC, EaImm 1] $
        checkOpWithEa [0o045000] $ TST BYTE
      prop "TST.W" $
        testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
        checkOpWithEa [0o045100] $ TST WORD
      prop "TST.L" $
        testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
        checkOpWithEa [0o045200] $ TST LONG
      prop "TAS" $ testFor [EaDN, EaMem] $ checkOpWithEa [0o045300] $ TAS BYTE
