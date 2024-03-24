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

ccTest :: (Testable a) => (Int -> a) -> Property
ccTest = rnTest -- range is same as rnTest

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
    prop "DN" $ regTest $ \x -> parseOps 0 x nothingT [] `shouldBe` Just (DR x)
    prop "AN" $ regTest $ \x -> parseOps 1 x nothingT [] `shouldBe` Just (AR x)
    prop "(AN)" $
      regTest $ \x ->
        parseOps 2 x nothingT [] `shouldBe` (Just . Address $ UnRefAR x)
    prop "(AN)+" $
      regTest $ \x ->
        parseOps 3 x nothingT [] `shouldBe` (Just . Address $ UnRefInc x)
    prop "-(AN)" $
      regTest $ \x ->
        parseOps 4 x nothingT [] `shouldBe` (Just . Address $ UnRefDec x)
    prop "(d, AN)" $
      regTest $ \x ->
        imm16Test $ \d ->
          parseOps 5 x nothingT [d] `shouldBe`
          (Just . Address $ Offset16 (toS16 d) $ BaseAR x)
    prop "extra-An" $
      regTest $ \x ->
        imm8Test $ \d ->
          parseOps 6 x nothingT [d] `shouldBe`
          (Just . Address $ Offset8 (toS8 d) (BaseAR x) False 0 0)
    prop "(imm16)" $
      imm16Test $ \x ->
        parseOps 7 0 nothingT [x] `shouldBe` (Just . Address $ ImmAddr x)
    prop "(imm32)" $
      imm32Test $ \x ->
        parseOps 7 1 nothingT (longToWord x) `shouldBe`
        (Just . Address $ ImmAddr x)
    prop "(d, PC)" $
      imm16Test $ \x ->
        parseOps 7 2 nothingT [x] `shouldBe`
        (Just . Address $ Offset16 (toS16 x) (BasePC 100))
    prop "extra-PC" $
      forAll (chooseInt (0, 0x7F)) $ \x ->
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
    let textExtW f extw bdList =
          regTest $ \an ->
            rnTest $ \ri ->
              forAll (elements [False, True]) $ \w ->
                forAll (chooseInt (0, 3)) $ \cc ->
                  parseOpsX (toExtWord extw ri w cc) (BaseAR an) bdList `shouldBe`
                  Just (f (BaseAR an) w ri cc)
    prop "(d, An, Ri.w << c)" $
      forAll (chooseInt (1, 127)) $ \d -> textExtW (Offset8 d) d []
    prop "ILLEGAL#1(bdSize=0)" $
      parseOpsX 0x0100 (BaseAR 0) [] `shouldBe` Nothing
    describe "(bd, An, Ri.w << c)" $ do
      describe "bd" $ do
        let textExtBd bd = textExtW (\a w ri cc -> Indirect bd a w (Just ri) cc)
        prop "zero" $ textExtBd 0 0x0110 []
        prop "word" $ imm16Test $ \bd -> textExtBd (toS16 bd) 0x0120 [bd]
        prop "long" $
          imm32Test $ \bd -> textExtBd (toS32 bd) 0x0130 $ longToWord bd
      it "Base=0" $ do
        parseOpsX 0x0190 (BaseAR 0) [] `shouldBe`
          Just (Indirect 0 BaseNone False (Just 0) 0)
      it "NoIndex" $ do
        parseOpsX 0x0150 (BaseAR 0) [] `shouldBe`
          Just (Indirect 0 (BaseAR 0) False Nothing 0)
    let textExtBdOd f bd od = textExtW (\a w ri cc -> f bd a w (Just ri) cc od)
    describe "([bd, An, Ri.w << c], od)" $ do
      describe "od" $ do
        prop "zero" $
          imm16Test $ \bd -> textExtBdOd PreIndex (toS16 bd) 0 0x0121 [bd]
        prop "word" $
          imm16Test $ \od ->
            imm16Test $ \bd ->
              textExtBdOd PreIndex (toS16 bd) (toS16 od) 0x0122 [bd, od]
        prop "long" $
          imm32Test $ \od ->
            imm16Test $ \bd ->
              textExtBdOd
                PreIndex
                (toS16 bd)
                (toS32 od)
                0x0123
                (bd : longToWord od)
      describe "bd" $ do
        prop "zero" $ textExtBdOd PreIndex 0 0 0x0111 []
        prop "word" $
          imm16Test $ \bd -> textExtBdOd PreIndex (toS16 bd) 0 0x0121 [bd]
        prop "long" $
          imm32Test $ \bd ->
            textExtBdOd PreIndex (toS32 bd) 0 0x0131 $ longToWord bd
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
          imm16Test $ \bd -> textExtBdOd PostIndex (toS16 bd) 0 0x0125 [bd]
        prop "word" $
          imm16Test $ \od ->
            imm16Test $ \bd ->
              textExtBdOd PostIndex (toS16 bd) (toS16 od) 0x0126 [bd, od]
        prop "long" $
          imm32Test $ \od ->
            imm16Test $ \bd ->
              textExtBdOd
                PostIndex
                (toS16 bd)
                (toS32 od)
                0x0127
                (bd : longToWord od)
      describe "bd" $ do
        prop "zero" $ textExtBdOd PostIndex 0 0 0x0115 []
        prop "word" $
          imm16Test $ \bd -> textExtBdOd PostIndex (toS16 bd) 0 0x0125 [bd]
        prop "long" $
          imm32Test $ \bd ->
            textExtBdOd PostIndex (toS32 bd) 0 0x0135 $ longToWord bd
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
  regTest $ \d -> runTest (makeOp ops 0o00 d ++ ex) (expected $ DR d)
checkOpWithEa2 ops expected EaAN ex =
  regTest $ \d -> runTest (makeOp ops 0o10 d ++ ex) (expected $ AR d)
checkOpWithEa2 ops expected EaMem ex =
  imm16Test $ \d ->
    regTest $ \n ->
      runTest
        (makeOp ops 0o50 n ++ [d] ++ ex)
        (expected $ Address $ Offset16 (toS16 d) $ BaseAR n)
checkOpWithEa2 ops expected EaPC ex =
  imm16Test $ \d ->
    runTest
      (makeOp ops 0o72 0 ++ [d] ++ ex)
      (expected $ Address $ Offset16 (toS16 d) $ BasePC $ 2 * length ops)
checkOpWithEa2 ops expected (EaImm 1) ex =
  imm8Test $ \d ->
    runTest (makeOp ops 0o74 0 ++ [d] ++ ex) (expected $ ImmInt d)
checkOpWithEa2 ops expected (EaImm 2) ex =
  imm16Test $ \d ->
    runTest (makeOp ops 0o74 0 ++ [d] ++ ex) (expected $ ImmInt d)
checkOpWithEa2 ops expected (EaImm 4) ex =
  imm32Test $ \d ->
    runTest (makeOp ops 0o74 0 ++ longToWord d ++ ex) (expected $ ImmInt d)
checkOpWithEa2 _ _ _ _ = undefined

checkOpWithEaMem :: [Int] -> (MemOperand -> Op) -> EaType -> Property
checkOpWithEaMem ops expected EaMem =
  imm16Test $ \d ->
    regTest $ \r ->
      runTest
        (makeOp ops 0o50 r ++ [d])
        (expected $ Offset16 (toS16 d) $ BaseAR r)
checkOpWithEaMem ops expected EaPC =
  imm16Test $ \d ->
    runTest
      (makeOp ops 0o72 0 ++ [d])
      (expected $ Offset16 (toS16 d) $ BasePC $ 2 * length ops)
checkOpWithEaMem _ _ _ = undefined

main =
  hspec $ do
    testUtil
    testEA
    let testFor target op = conjoin $ map op target
        makeRegList v =
          mapMaybe
            (\x ->
               if testBit v x
                 then Just x
                 else Nothing)
            [0 .. 15]
        withDn op dn = op .|. (dn `shiftL` 9)
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
              checkOpWithEa [0o000400 `withDn` n] (\x -> BTST LONG x $ BReg n)
          prop "BYTE" $ do
            regTest $ \n ->
              testFor [EaMem, EaPC, EaImm 1] $
              checkOpWithEa [0o000400 `withDn` n] $ \x -> BTST BYTE x $ BReg n
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
              checkOpWithEa [0o000500 `withDn` n] $ \x -> BCHG LONG x $ BReg n
          prop "BYTE" $ do
            regTest $ \n ->
              testFor [EaMem] $
              checkOpWithEa [0o000500 `withDn` n] $ \x -> BCHG BYTE x $ BReg n
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
              checkOpWithEa [0o000600 `withDn` n] $ \x -> BCLR LONG x $ BReg n
          prop "BYTE" $ do
            regTest $ \n ->
              testFor [EaMem] $
              checkOpWithEa [0o000600 `withDn` n] $ \x -> BCLR BYTE x $ BReg n
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
              checkOpWithEa [0o000700 `withDn` n] $ \x -> BSET LONG x $ BReg n
          prop "BYTE" $ do
            regTest $ \n ->
              testFor [EaMem] $
              checkOpWithEa [0o000700 `withDn` n] $ \x -> BSET BYTE x $ BReg n
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
            checkOpWithEa [0o010000 `withDn` c] $ \x -> MOVE BYTE x (DR c)
        prop "toMem" $
          regTest $ \c ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o010200 `withDn` c] $ \x ->
              MOVE BYTE x (Address $ UnRefAR c)
        prop "toMemInc" $
          regTest $ \c ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o010300 `withDn` c] $ \x ->
              MOVE BYTE x (Address $ UnRefInc c)
        prop "toMemDec" $
          regTest $ \c ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o010400 `withDn` c] $ \x ->
              MOVE BYTE x (Address $ UnRefDec c)
        prop "toMemOffset16" $
          regTest $ \c ->
            imm16Test $ \d ->
              testFor [EaDN, EaMem, EaPC, EaImm 1] $ \z ->
                checkOpWithEa2
                  [0o010500 `withDn` c]
                  (\x -> MOVE BYTE x (Address $ Offset16 (toS16 d) (BaseAR c)))
                  z
                  [d]
        prop "toExt" $
          regTest $ \c ->
            imm8Test $ \d ->
              testFor [EaDN, EaMem, EaPC, EaImm 1] $ \z ->
                checkOpWithEa2
                  [0o010600 `withDn` c]
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
          checkOpWithEa [0o020100 `withDn` c] $ \x -> MOVEA LONG x c
      describe "MOVE.L" $ do
        prop "toDn" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o020000 `withDn` c] $ \x -> MOVE LONG x (DR c)
        prop "toMem" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o020200 `withDn` c] $ \x ->
              MOVE LONG x (Address $ UnRefAR c)
        prop "toMemInc" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o020300 `withDn` c] $ \x ->
              MOVE LONG x (Address $ UnRefInc c)
        prop "toMemDec" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o020400 `withDn` c] $ \x ->
              MOVE LONG x (Address $ UnRefDec c)
        prop "toMemOffset16" $
          regTest $ \c ->
            imm16Test $ \d ->
              testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $ \z ->
                checkOpWithEa2
                  [0o020500 `withDn` c]
                  (\x -> MOVE LONG x (Address $ Offset16 (toS16 d) (BaseAR c)))
                  z
                  [d]
        prop "toExt" $
          regTest $ \c ->
            imm8Test $ \d ->
              testFor [EaDN, EaAN, EaMem, EaPC, EaImm 4] $ \z ->
                checkOpWithEa2
                  [0o020600 `withDn` c]
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
          checkOpWithEa [0o030100 `withDn` c] $ \x -> MOVEA WORD x c
      describe "MOVE.W" $ do
        prop "toDn" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o030000 `withDn` c] $ \x -> MOVE WORD x (DR c)
        prop "toMem" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o030200 `withDn` c] $ \x ->
              MOVE WORD x (Address $ UnRefAR c)
        prop "toMemInc" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o030300 `withDn` c] $ \x ->
              MOVE WORD x (Address $ UnRefInc c)
        prop "toMemDec" $
          regTest $ \c ->
            testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o030400 `withDn` c] $ \x ->
              MOVE WORD x (Address $ UnRefDec c)
        prop "toMemOffset16" $
          regTest $ \c ->
            imm16Test $ \d ->
              testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $ \z ->
                checkOpWithEa2
                  [0o030500 `withDn` c]
                  (\x -> MOVE WORD x (Address $ Offset16 (toS16 d) (BaseAR c)))
                  z
                  [d]
        prop "toExt" $
          regTest $ \c ->
            imm8Test $ \d ->
              testFor [EaDN, EaAN, EaMem, EaPC, EaImm 2] $ \z ->
                checkOpWithEa2
                  [0o030600 `withDn` c]
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
      describe "MULU.L" $ do
        prop "no highword" $
          regTest $ \dl ->
            testFor [EaDN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o046000, dl `shiftL` 12] $ \x -> MULUL x dl
        prop "quad" $
          regTest $ \dl ->
            regTest $ \dh ->
              testFor [EaDN, EaMem, EaPC, EaImm 4] $
              checkOpWithEa [0o046000, 0x400 .|. dl `shiftL` 12 .|. dh] $ \x ->
                MULULL x dh dl
      describe "MULS.L" $ do
        prop "no highword" $
          regTest $ \dl ->
            testFor [EaDN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o046000, 0x800 .|. dl `shiftL` 12] $ \x ->
              MULSL x dl
        prop "quad" $
          regTest $ \dl ->
            regTest $ \dh ->
              testFor [EaDN, EaMem, EaPC, EaImm 4] $
              checkOpWithEa [0o046000, 0xC00 .|. dl `shiftL` 12 .|. dh] $ \x ->
                MULSLL x dh dl
      describe "DIVU.L" $ do
        prop "no highword" $
          regTest $ \dq ->
            regTest $ \dr ->
              testFor [EaDN, EaMem, EaPC, EaImm 4] $
              checkOpWithEa [0o046100, dq `shiftL` 12 .|. dr] $ \x ->
                DIVUL x dr dq
        prop "quad" $
          regTest $ \dq ->
            regTest $ \dr ->
              testFor [EaDN, EaMem, EaPC, EaImm 4] $
              checkOpWithEa [0o046100, 0x400 .|. dq `shiftL` 12 .|. dr] $ \x ->
                DIVULL x dr dq
      describe "DIVS.L" $ do
        prop "no highword" $
          regTest $ \dq ->
            regTest $ \dr ->
              testFor [EaDN, EaMem, EaPC, EaImm 4] $
              checkOpWithEa [0o046100, 0x800 .|. dq `shiftL` 12 .|. dr] $ \x ->
                DIVSL x dr dq
        prop "quad" $
          regTest $ \dq ->
            regTest $ \dr ->
              testFor [EaDN, EaMem, EaPC, EaImm 4] $
              checkOpWithEa [0o046100, 0xC00 .|. dq `shiftL` 12 .|. dr] $ \x ->
                DIVSLL x dr dq
      prop "TRAP" $
        forAll (chooseInt (0, 15)) $ \c -> runTest [0o047100 .|. c] $ TRAPn c
      prop "LINK.W" $
        regTest $ \an ->
          imm16Test $ \i -> runTest [0o047120 .|. an, i] $ LINK an i
      prop "UNLK" $ regTest $ \an -> runTest [0o047130 .|. an] $ UNLK an
      prop "MOVE to USP" $
        regTest $ \an ->
          runTest [0o047140 .|. an] $ MOVE LONG (AR an) (SpRG "USP")
      prop "MOVE from USP" $
        regTest $ \an ->
          runTest [0o047150 .|. an] $ MOVE LONG (SpRG "USP") (AR an)
      it "RESET" $ do runTest [0o047160] RESET
      it "NOP" $ do runTest [0o047161] NOP
      prop "STOP" $ imm16Test $ \i -> runTest [0o047162, i] $ STOP i
      it "RTE" $ do runTest [0o047163] RTE
      prop "RTD" $ imm16Test $ \i -> runTest [0o047164, i] $ RTD i
      it "RTS" $ do runTest [0o047165] RTS
      it "TRAPV" $ do runTest [0o047166] TRAPV
      it "RTR" $ do runTest [0o047167] RTR
      describe "MOVEC" $ do
        let doTest name code =
              describe name $ do
                prop "load" $
                  rnTest $ \rn ->
                    runTest [0o047172, rn `shiftL` 12 .|. code] $
                    MOVEC False rn name
                prop "store" $
                  rnTest $ \rn ->
                    runTest [0o047173, rn `shiftL` 12 .|. code] $
                    MOVEC True rn name
        doTest "SFC" 0
        doTest "DFC" 1
        doTest "CACR" 2
        doTest "TC" 3
        doTest "ITT0" 4
        doTest "ITT1" 5
        doTest "DTT0" 6
        doTest "DTT1" 7
        doTest "USP" 0x800
        doTest "VBR" 0x801
        doTest "MSP" 0x803
        doTest "ISP" 0x804
        doTest "MMUSR" 0x805
        doTest "URP" 0x806
        doTest "SRP" 0x807
      prop "JSR" $ testFor [EaMem, EaPC] $ checkOpWithEaMem [0o047200] JSR
      prop "JMP" $ testFor [EaMem, EaPC] $ checkOpWithEaMem [0o047300] JMP
      prop "CHK.L" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 4] $
          checkOpWithEa [0o040400 `withDn` dn] $ \x -> CHK LONG x dn
      prop "CHK.W" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o040600 `withDn` dn] $ \x -> CHK WORD x dn
      prop "EXTB" $ regTest $ \dn -> runTest [0o044700 .|. dn] $ EXTB dn
      prop "CHK.L" $
        regTest $ \an ->
          testFor [EaMem, EaPC] $
          checkOpWithEaMem [0o040700 `withDn` an] $ \x -> LEA x an
      describe "ADDQ.B" $ do
        prop "imm=0(actually 8)" $
          testFor [EaDN, EaMem] $ checkOpWithEa [0o050000] $ ADDQ BYTE 8
        prop "imm!=0" $
          forAll (chooseInt (1, 7)) $ \i ->
            testFor [EaDN, EaMem] $
            checkOpWithEa [0o050000 `withDn` i] $ ADDQ BYTE i
      describe "ADDQ.W" $ do
        prop "imm=0(actually 8)" $
          testFor [EaDN, EaAN, EaMem] $ checkOpWithEa [0o050100] $ ADDQ WORD 8
        prop "imm!=0" $
          forAll (chooseInt (1, 7)) $ \i ->
            testFor [EaDN, EaAN, EaMem] $
            checkOpWithEa [0o050100 `withDn` i] $ ADDQ WORD i
      describe "ADDQ.L" $ do
        prop "imm=0(actually 8)" $
          testFor [EaDN, EaAN, EaMem] $ checkOpWithEa [0o050200] $ ADDQ LONG 8
        prop "imm!=0" $
          forAll (chooseInt (1, 7)) $ \i ->
            testFor [EaDN, EaAN, EaMem] $
            checkOpWithEa [0o050200 `withDn` i] $ ADDQ LONG i
      describe "SUBQ.B" $ do
        prop "imm=0(actually 8)" $
          testFor [EaDN, EaMem] $ checkOpWithEa [0o050400] $ SUBQ BYTE 8
        prop "imm!=0" $
          forAll (chooseInt (1, 7)) $ \i ->
            testFor [EaDN, EaMem] $
            checkOpWithEa [0o050400 `withDn` i] $ SUBQ BYTE i
      describe "SUBQ.W" $ do
        prop "imm=0(actually 8)" $
          testFor [EaDN, EaAN, EaMem] $ checkOpWithEa [0o050500] $ SUBQ WORD 8
        prop "imm!=0" $
          forAll (chooseInt (1, 7)) $ \i ->
            testFor [EaDN, EaAN, EaMem] $
            checkOpWithEa [0o050500 `withDn` i] $ SUBQ WORD i
      describe "SUBQ.L" $ do
        prop "imm=0(actually 8)" $
          testFor [EaDN, EaAN, EaMem] $ checkOpWithEa [0o050600] $ SUBQ LONG 8
        prop "imm!=0" $
          forAll (chooseInt (1, 7)) $ \i ->
            testFor [EaDN, EaAN, EaMem] $
            checkOpWithEa [0o050600 `withDn` i] $ SUBQ LONG i
      prop "Scc" $
        ccTest $ \cc ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o050300 .|. cc `shiftL` 8] $ Scc cc
      prop "DBcc.W" $
        regTest $ \dn ->
          ccTest $ \cc ->
            imm16Test $ \d ->
              runTest [0o050310 .|. cc `shiftL` 8 .|. dn, d] $
              DBcc cc dn $ toS16 d + 2
      describe "Trapcc" $ do
        prop "W" $
          ccTest $ \cc ->
            imm16Test $ \t ->
              runTest [0o050372 .|. cc `shiftL` 8, t] $ TRAPcc cc $ Just t
        prop "L" $
          ccTest $ \cc ->
            imm32Test $ \t ->
              runTest ((0o050373 .|. cc `shiftL` 8) : longToWord t) $
              TRAPcc cc $ Just t
        prop "None" $
          ccTest $ \cc ->
            runTest [0o050374 .|. cc `shiftL` 8] $ TRAPcc cc Nothing
      describe "BRA" $ do
        prop "byte" $
          forAll (chooseInt (1, 0xFE)) $ \i ->
            runTest [0o060000 .|. i] $ BRA $ toS8 i + 2
        prop "word" $
          imm16Test $ \i -> runTest [0o060000, i] $ BRA $ toS16 i + 2
        prop "long" $
          imm32Test $ \i ->
            runTest (0o060377 : longToWord i) $ BRA $ toS32 i + 2
      describe "BSR" $ do
        prop "byte" $
          forAll (chooseInt (1, 0xFE)) $ \i ->
            runTest [0o060400 .|. i] $ BSR $ toS8 i + 2
        prop "word" $
          imm16Test $ \i -> runTest [0o060400, i] $ BSR $ toS16 i + 2
        prop "long" $
          imm32Test $ \i ->
            runTest (0o060777 : longToWord i) $ BSR $ toS32 i + 2
      describe "Bcc" $ do
        prop "byte" $
          forAll (chooseInt (2, 15)) $ \cc ->
            forAll (chooseInt (1, 0xFE)) $ \i ->
              runTest [0o060000 .|. cc `shiftL` 8 .|. i] $ Bcc cc $ toS8 i + 2
        prop "word" $
          forAll (chooseInt (2, 15)) $ \cc ->
            imm16Test $ \i ->
              runTest [0o060000 .|. cc `shiftL` 8, i] $ Bcc cc $ toS16 i + 2
        prop "long" $
          forAll (chooseInt (2, 15)) $ \cc ->
            imm32Test $ \i ->
              runTest ((0o060377 .|. cc `shiftL` 8) : longToWord i) $
              Bcc cc $ toS32 i + 2
      prop "MOVEQ" $
        regTest $ \dn ->
          imm8Test $ \i ->
            runTest [0o070000 `withDn` dn .|. i] $ MOVEQ (toS8 i) dn
      describe "OR.B" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o100000 `withDn` dn] $ \x -> OR BYTE x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o100400 `withDn` dn] $ OR_TO_MEM BYTE dn
      describe "OR.W" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o100100 `withDn` dn] $ \x -> OR WORD x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o100500 `withDn` dn] $ OR_TO_MEM WORD dn
      describe "OR.L" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o100200 `withDn` dn] $ \x -> OR LONG x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o100600 `withDn` dn] $ OR_TO_MEM LONG dn
      prop "DIVU.W" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o100300 `withDn` dn] $ \x -> DIVUW x dn
      describe "SBCD" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              runTest [0o100400 `withDn` dn .|. dm] $ SBCD_REG dn dm
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              runTest [0o100410 `withDn` an .|. am] $ SBCD_MEM an am
      describe "PACK" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              imm16Test $ \i ->
                runTest [0o100500 `withDn` dn .|. dm, i] $ PACK_REG dm dn i
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              imm16Test $ \i ->
                runTest [0o100510 `withDn` an .|. am, i] $ PACK_MEM am an i
      describe "UNPK" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              imm16Test $ \i ->
                runTest [0o100600 `withDn` dn .|. dm, i] $ UNPK_REG dm dn i
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              imm16Test $ \i ->
                runTest [0o100610 `withDn` an .|. am, i] $ UNPK_MEM am an i
      prop "DIVS.W" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o100700 `withDn` dn] $ \x -> DIVSW x dn
      describe "SUB.B" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o110000 `withDn` dn] $ \x -> SUB BYTE x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o110400 `withDn` dn] $ SUB_TO_MEM BYTE dn
      describe "SUB.W" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o110100 `withDn` dn] $ \x -> SUB WORD x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o110500 `withDn` dn] $ SUB_TO_MEM WORD dn
      describe "SUB.L" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o110200 `withDn` dn] $ \x -> SUB LONG x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o110600 `withDn` dn] $ SUB_TO_MEM LONG dn
      prop "SUBA.W" $
        regTest $ \an ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o110300 `withDn` an] $ \x -> SUBA WORD x an
      describe "SUBX.B" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              runTest [0o110400 `withDn` dn .|. dm] $ SUBX_REG BYTE dn dm
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              runTest [0o110410 `withDn` an .|. am] $ SUBX_MEM BYTE an am
      describe "SUBX.W" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              runTest [0o110500 `withDn` dn .|. dm] $ SUBX_REG WORD dn dm
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              runTest [0o110510 `withDn` an .|. am] $ SUBX_MEM WORD an am
      describe "SUBX.L" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              runTest [0o110600 `withDn` dn .|. dm] $ SUBX_REG LONG dn dm
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              runTest [0o110610 `withDn` an .|. am] $ SUBX_MEM LONG an am
      prop "SUBA.L" $
        regTest $ \an ->
          testFor [EaDN, EaMem, EaPC, EaImm 4] $
          checkOpWithEa [0o110700 `withDn` an] $ \x -> SUBA LONG x an
      prop "SYSCALL" $
        forAll (chooseInt (0, 0xFFF)) $ \c ->
          let cc = 0o120000 .|. c
           in runTest [cc] $ SYS cc
      prop "CMP.B" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 1] $
          checkOpWithEa [0o130000 `withDn` dn] $ \x -> CMP BYTE x dn
      prop "CMP.W" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o130100 `withDn` dn] $ \x -> CMP WORD x dn
      prop "CMP.L" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 4] $
          checkOpWithEa [0o130200 `withDn` dn] $ \x -> CMP LONG x dn
      prop "CMPA.W" $
        regTest $ \an ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o130300 `withDn` an] $ \x -> CMPA WORD x an
      prop "EOR.B" $
        regTest $ \dn ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o130400 `withDn` dn] $ EOR BYTE dn
      prop "EOR.W" $
        regTest $ \dn ->
          testFor [EaDN, EaMem] $
          checkOpWithEa [0o130500 `withDn` dn] $ EOR WORD dn
      prop "EOR.L" $
        regTest $ \dn ->
          testFor [EaMem] $ checkOpWithEa [0o130600 `withDn` dn] $ EOR LONG dn
      prop "CMPM.B" $
        regTest $ \an ->
          regTest $ \am ->
            runTest [0o130410 `withDn` an .|. am] $ CMPM BYTE am an
      prop "CMPM.W" $
        regTest $ \an ->
          regTest $ \am ->
            runTest [0o130510 `withDn` an .|. am] $ CMPM WORD am an
      prop "CMPM.L" $
        regTest $ \an ->
          regTest $ \am ->
            runTest [0o130610 `withDn` an .|. am] $ CMPM LONG am an
      prop "CMPA.L" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 4] $
          checkOpWithEa [0o130700 `withDn` dn] $ \x -> CMPA LONG x dn
      describe "AND.B" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o140000 `withDn` dn] $ \x -> AND BYTE x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o140400 `withDn` dn] $ AND_TO_MEM BYTE dn
      describe "AND.W" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o140100 `withDn` dn] $ \x -> AND WORD x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o140500 `withDn` dn] $ AND_TO_MEM WORD dn
      describe "AND.L" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o140200 `withDn` dn] $ \x -> AND LONG x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o140600 `withDn` dn] $ AND_TO_MEM LONG dn
      prop "MULU.W" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o140300 `withDn` dn] $ \x -> MULUW x dn
      describe "ABCD" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              runTest [0o140400 `withDn` dn .|. dm] $ ABCD_REG dm dn
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              runTest [0o140410 `withDn` an .|. am] $ ABCD_MEM am an
      describe "EXG" $ do
        prop "dm<>dn" $
          regTest $ \dn ->
            regTest $ \dm -> runTest [0o140500 `withDn` dn .|. dm] $ EXG_D dn dm
        prop "am<>an" $
          regTest $ \an ->
            regTest $ \am -> runTest [0o140510 `withDn` an .|. am] $ EXG_A an am
        prop "dm<>an" $
          regTest $ \dn ->
            regTest $ \am ->
              runTest [0o140610 `withDn` dn .|. am] $ EXG_DA dn am
      prop "MULS.W" $
        regTest $ \dn ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o140700 `withDn` dn] $ \x -> MULSW x dn
      describe "ADD.B" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 1] $
            checkOpWithEa [0o150000 `withDn` dn] $ \x -> ADD BYTE x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o150400 `withDn` dn] $ ADD_TO_MEM BYTE dn
      describe "ADD.W" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 2] $
            checkOpWithEa [0o150100 `withDn` dn] $ \x -> ADD WORD x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o150500 `withDn` dn] $ ADD_TO_MEM WORD dn
      describe "ADD.L" $ do
        prop "load" $
          regTest $ \dn ->
            testFor [EaDN, EaMem, EaPC, EaImm 4] $
            checkOpWithEa [0o150200 `withDn` dn] $ \x -> ADD LONG x dn
        prop "store" $
          regTest $ \dn ->
            testFor [EaMem] $
            checkOpWithEaMem [0o150600 `withDn` dn] $ ADD_TO_MEM LONG dn
      prop "ADDA.W" $
        regTest $ \an ->
          testFor [EaDN, EaMem, EaPC, EaImm 2] $
          checkOpWithEa [0o150300 `withDn` an] $ \x -> ADDA WORD x an
      describe "ADDX.B" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              runTest [0o150400 `withDn` dn .|. dm] $ ADDX_REG BYTE dm dn
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              runTest [0o150410 `withDn` an .|. am] $ ADDX_MEM BYTE am an
      describe "ADDX.W" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              runTest [0o150500 `withDn` dn .|. dm] $ ADDX_REG WORD dm dn
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              runTest [0o150510 `withDn` an .|. am] $ ADDX_MEM WORD am an
      describe "ADDX.L" $ do
        prop "register" $
          regTest $ \dn ->
            regTest $ \dm ->
              runTest [0o150600 `withDn` dn .|. dm] $ ADDX_REG LONG dm dn
        prop "memory" $
          regTest $ \an ->
            regTest $ \am ->
              runTest [0o150610 `withDn` an .|. am] $ ADDX_MEM LONG am an
      prop "ADDA.L" $
        regTest $ \an ->
          testFor [EaDN, EaMem, EaPC, EaImm 4] $
          checkOpWithEa [0o150700 `withDn` an] $ \x -> ADDA LONG x an
      describe "ASR.B" $ do
        prop "by imm(sc=0)" $
          regTest $ \dn -> runTest [0o160000 .|. dn] $ ASR BYTE False 8 dn
        prop "by imm" $
          regTest $ \dn ->
            forAll (chooseInt (1, 7)) $ \c ->
              runTest [0o160000 `withDn` c .|. dn] $ ASR BYTE False c dn
        prop "by reg" $
          regTest $ \dn ->
            forAll (chooseInt (0, 7)) $ \c ->
              runTest [0o160040 `withDn` c .|. dn] $ ASR BYTE True c dn
