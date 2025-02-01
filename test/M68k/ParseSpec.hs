module M68k.ParseSpec
  ( testEA
  , testDecode
  , regRange
  , regRange2
  ) where

import Data.List
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Bits
import           Data.Maybe
import           M68k.Common
import           M68k.Opcode
import           M68k.Operand
import           M68k.Parse
import           Test.Hspec                (Expectation, Spec, SpecWith,
                                            describe, it, shouldBe)
import           Test.Hspec.QuickCheck
import           Test.QuickCheck           (Property, chooseInt, conjoin,
                                            elements, forAll, property)
import           TestCommon
import           Util

regRange :: [Int]
regRange = [0 .. 7]

regRange2 :: [Int]
regRange2 = [0 .. 15]

ccRange :: [Int]
ccRange = regRange2

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
    let testEaForReg regT other result =
          testFor regRange $ \x ->
            parseOps regT x nothingT other `shouldBe` Just (result x)
    prop "DN" $ testEaForReg 0 [] $ DReg . DR
    prop "AN" $ testEaForReg 1 [] $ AReg . AR
    prop "(AN)" $ testEaForReg 2 [] $ Address . UnRefAR . AR
    prop "(AN)+" $ testEaForReg 3 [] $ Address . UnRefInc . AR
    prop "-(AN)" $ testEaForReg 4 [] $ Address . UnRefDec . AR
    prop "(d, AN)" $
      imm16Test $ \d ->
        testEaForReg 5 [d] $ Address . Offset16 (toS16 d) . BaseAR . AR
    prop "extra-An" $
      imm8Test $ \d ->
        testEaForReg 6 [d] $ \x ->
          Address $ Offset8 (toS8 d) (BaseAR $ AR x) False (xr 0) 0
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
        (Just . Address $ Offset8 x (BasePC 100) False (xr 0) 0)
    prop "other" $ \d ->
      parseOps 7 4 (do return $ ImmInt d) [] `shouldBe` Just (ImmInt d)
    it "other-fail" $ do parseOps 7 4 nothingT [] `shouldBe` Nothing
    it "fail" $ do parseOps 7 5 nothingT [] `shouldBe` Nothing
  describe "parseEaEx" $ do
    let toExtWord x ri w cc =
          bitExpand [(0, x), (12, ri), (11, bool2Bit w), (9, cc)]
    let textExtW f extw bdList =
          testFor regRange $ \an ->
            testFor regRange2 $ \ri ->
              forAll (elements [False, True]) $ \w ->
                forAll (chooseInt (0, 3)) $ \cc ->
                  parseOpsX (toExtWord extw ri w cc) (BaseAR $ AR an) bdList `shouldBe`
                  Just (f (BaseAR $ AR an) w (xr ri) cc)
    prop "(d, An, Ri.w << c)" $
      forAll (chooseInt (1, 127)) $ \d -> textExtW (Offset8 d) d []
    prop "ILLEGAL#1(bdSize=0)" $
      parseOpsX 0x0100 (BaseAR $ AR 0) [] `shouldBe` Nothing
    describe "(bd, An, Ri.w << c)" $ do
      describe "bd" $ do
        let textExtBd bd = textExtW (\a w ri cc -> Indirect bd a w (Just ri) cc)
        prop "zero" $ textExtBd 0 0x0110 []
        prop "word" $ imm16Test $ \bd -> textExtBd (toS16 bd) 0x0120 [bd]
        prop "long" $
          imm32Test $ \bd -> textExtBd (toS32 bd) 0x0130 $ longToWord bd
      it "Base=0" $ do
        parseOpsX 0x0190 (BaseAR $ AR 0) [] `shouldBe`
          Just (Indirect 0 BaseNone False (Just $ xr 0) 0)
      it "NoIndex" $ do
        parseOpsX 0x0150 (BaseAR $ AR 0) [] `shouldBe`
          Just (Indirect 0 (BaseAR $ AR 0) False Nothing 0)
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
        parseOpsX 0x0191 (BaseAR $ AR 0) [] `shouldBe`
          Just (PreIndex 0 BaseNone False (Just $ xr 0) 0 0)
      it "NoIndex" $ do
        parseOpsX 0x0151 (BaseAR $ AR 0) [] `shouldBe`
          Just (PreIndex 0 (BaseAR $ AR 0) False Nothing 0 0)
    describe "([bd, An], Ri.w << c, od)" $ do
      it "Invalid(odSize=0)" $ do
        parseOpsX 0x0114 (BaseAR $ AR 0) [] `shouldBe` Nothing
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
        parseOpsX 0x0195 (BaseAR $ AR 0) [] `shouldBe`
          Just (PostIndex 0 BaseNone False (Just $ xr 0) 0 0)
      it "NoIndex" $ do
        parseOpsX 0x0155 (BaseAR $ AR 0) [] `shouldBe`
          Just (PostIndex 0 (BaseAR $ AR 0) False Nothing 0 0)
    it "Invalid(BIT3=1)" $ do
      parseOpsX 0x0118 (BaseAR $ AR 0) [] `shouldBe` Nothing

data EaType
  = EaDN
  | EaAN
  | EaMem
  | EaPC
  | EaImm AType
  | EaExtra Operand

runTest :: [Int] -> Op -> Expectation
runTest ops result =
  let xops = intListToByteList ops
   in parseOp 0 xops `shouldBe` (0, result, length xops)

makeOp :: [Int] -> Int -> Int -> [Int]
makeOp ops x d = (head ops .|. x .|. d) : tail ops

checkOpWithEa :: [Int] -> (Operand -> Op) -> EaType -> Property
checkOpWithEa ops expected = checkOpWithEa2 ops expected []

checkOpWithEa2 :: [Int] -> (Operand -> Op) -> [Int] -> EaType -> Property
checkOpWithEa2 ops expected ex EaDN =
  testFor regRange $ \d ->
    runTest (makeOp ops 0o00 d ++ ex) (expected $ DReg $ DR d)
checkOpWithEa2 ops expected ex EaAN =
  testFor regRange $ \d ->
    runTest (makeOp ops 0o10 d ++ ex) (expected $ AReg $ AR d)
checkOpWithEa2 ops expected ex EaMem =
  imm16Test $ \d ->
    testFor regRange $ \n ->
      runTest
        (makeOp ops 0o50 n ++ [d] ++ ex)
        (expected $ Address $ Offset16 (toS16 d) $ BaseAR $ AR n)
checkOpWithEa2 ops expected ex EaPC =
  imm16Test $ \d ->
    runTest
      (makeOp ops 0o72 0 ++ [d] ++ ex)
      (expected $ Address $ Offset16 (toS16 d) $ BasePC $ 2 * length ops)
checkOpWithEa2 ops expected ex (EaImm BYTE) =
  imm8Test $ \d ->
    runTest (makeOp ops 0o74 0 ++ [d] ++ ex) (expected $ ImmInt d)
checkOpWithEa2 ops expected ex (EaImm WORD) =
  imm16Test $ \d ->
    runTest (makeOp ops 0o74 0 ++ [d] ++ ex) (expected $ ImmInt d)
checkOpWithEa2 ops expected ex (EaImm LONG) =
  imm32Test $ \d ->
    runTest (makeOp ops 0o74 0 ++ longToWord d ++ ex) (expected $ ImmInt d)
checkOpWithEa2 ops expected ex (EaExtra o) =
  property $ runTest (makeOp ops 0o74 0 ++ ex) (expected o)

checkOpWithEaMem :: [Int] -> (MemOperand -> Op) -> EaType -> Property
checkOpWithEaMem ops expected EaMem =
  imm16Test $ \d ->
    testFor regRange $ \r ->
      runTest
        (makeOp ops 0o50 r ++ [d])
        (expected $ Offset16 (toS16 d) $ BaseAR $ AR r)
checkOpWithEaMem ops expected EaPC =
  imm16Test $ \d ->
    runTest
      (makeOp ops 0o72 0 ++ [d])
      (expected $ Offset16 (toS16 d) $ BasePC $ 2 * length ops)
checkOpWithEaMem _ _ _ = undefined

bitExpand :: [(Int, Int)] -> Int
bitExpand ls =
  let bitExpandImpl z [] = z
      bitExpandImpl z ((pos, val):os) =
        bitExpandImpl (z .|. val `shiftL` pos) os
   in bitExpandImpl 0 ls

testDecode :: SpecWith ()
testDecode = do
  let testForX target op = conjoin $ map op target
      makeRegList v =
        mapMaybe
          (\x ->
             if testBit v x
               then Just $ xr x
               else Nothing)
          [0 .. 15]
      withDn op dn = bitExpand [(0, op), (9, dn)]
      immTest ::
           AType
        -> Int
        -> (AType -> Operand -> Int -> Op)
        -> [EaType]
        -> Property
      immTest BYTE op c e =
        imm8Test $ \i ->
          testForX ([EaDN, EaMem] ++ e) $
          checkOpWithEa [op, i] $ \x -> c BYTE x i
      immTest WORD op c e =
        imm16Test $ \i ->
          testForX ([EaDN, EaMem] ++ e) $
          checkOpWithEa [op, i] $ \x -> c WORD x i
      immTest LONG op c e =
        imm32Test $ \i ->
          testForX ([EaDN, EaMem] ++ e) $
          checkOpWithEa (op : longToWord i) $ \x -> c LONG x i
      atype2N BYTE = 0
      atype2N WORD = 1
      atype2N LONG = 2
  describe "decode" $ do
    describe "ORI" $ do
      prop "B" $ immTest BYTE 0o000000 ORI [EaExtra CCR]
      prop "W" $ immTest WORD 0o000100 ORI [EaExtra SR]
      prop "L" $ immTest LONG 0o000200 ORI []
    describe "ANDI" $ do
      prop "B" $ immTest BYTE 0o001000 ANDI [EaExtra CCR]
      prop "W" $ immTest WORD 0o001100 ANDI [EaExtra SR]
      prop "L" $ immTest LONG 0o001200 ANDI []
    describe "SUBI" $ do
      prop "B" $ immTest BYTE 0o002000 SUBI []
      prop "W" $ immTest WORD 0o002100 SUBI []
      prop "L" $ immTest LONG 0o002200 SUBI []
    describe "ADDI" $ do
      prop "B" $ immTest BYTE 0o003000 ADDI []
      prop "W" $ immTest WORD 0o003100 ADDI []
      prop "L" $ immTest LONG 0o003200 ADDI []
    describe "EORI" $ do
      prop "B" $ immTest BYTE 0o005000 EORI [EaExtra CCR]
      prop "W" $ immTest WORD 0o005100 EORI [EaExtra SR]
      prop "L" $ immTest LONG 0o005200 EORI []
    describe "CMPI" $ do
      prop "B" $ immTest BYTE 0o006000 CMPI [EaPC, EaImm BYTE]
      prop "W" $ immTest WORD 0o006100 CMPI [EaPC, EaImm WORD]
      prop "L" $ immTest LONG 0o006200 CMPI [EaPC, EaImm LONG]
    let doCmp2Chk2 opc at high =
          testFor regRange $ \n ->
            checkOpWithEaMem
              [opc, bitExpand [(12, n), (11, bool2Bit high)]]
              (\x ->
                 (if high
                    then CHK2
                    else CMP2)
                   at
                   x $
                 xr n)
              EaMem
    describe "CMP2" $ do
      prop "B" $ doCmp2Chk2 0o000300 BYTE False
      prop "W" $ doCmp2Chk2 0o001300 WORD False
      prop "L" $ doCmp2Chk2 0o002300 LONG False
    describe "CHK2" $ do
      prop "B" $ doCmp2Chk2 0o000300 BYTE True
      prop "W" $ doCmp2Chk2 0o001300 WORD True
      prop "L" $ doCmp2Chk2 0o002300 LONG True
    let bitTest op c isBTST = do
          let targetEx =
                if isBTST
                  then [EaPC, EaImm BYTE]
                  else []
              immOp = bitExpand [(0, 0o004000), (6, c)]
              regOp = bitExpand [(0, 0o000000), (6, c + 4)]
              realSc i =
                BImm
                  (if i == 0
                     then 8
                     else i)
          describe "byImm" $ do
            describe "LONG" $ do
              let testImm i =
                    testFor regRange $ \n ->
                      runTest [immOp .|. n, i] $
                      op LONG (DReg $ DR n) $ realSc i
              prop "imm=0(actually 8)" $ testImm 0
              prop "imm!=0" $ forAll (chooseInt (1, 31)) $ \i -> testImm i
            describe "BYTE" $ do
              let testImm i =
                    testForX (EaMem : targetEx) $
                    checkOpWithEa [immOp, i] $ \x -> op BYTE x $ realSc i
              prop "imm=0(actually 8)" $ testImm 0
              prop "imm!=0" $ forAll (chooseInt (1, 7)) $ \i -> testImm i
          describe "byReg" $ do
            prop "LONG" $ do
              testFor regRange $ \n ->
                testFor regRange $ \d ->
                  runTest [regOp .|. d `withDn` n] $
                  op LONG (DReg $ DR d) $ BReg $ DR n
            prop "BYTE" $ do
              testFor regRange $ \n ->
                testForX (EaMem : targetEx) $
                checkOpWithEa [regOp `withDn` n] $ \x -> op BYTE x $ BReg $ DR n
    describe "BTST" $ bitTest BTST 0 True
    describe "BCHG" $ bitTest BCHG 1 False
    describe "BCLR" $ bitTest BCLR 2 False
    describe "BSET" $ bitTest BSET 3 False
    describe "CAS" $ do
      let testCas t =
            testFor regRange $ \u ->
              testFor regRange $ \c ->
                checkOpWithEaMem
                  [ bitExpand [(0, 0o004300), (9, atype2N t + 1)]
                  , bitExpand [(0, c), (6, u)]
                  ]
                  (CAS t (DR c) (DR u))
                  EaMem
      prop "B" $ testCas BYTE
      prop "W" $ testCas WORD
      prop "L" $ testCas LONG
    describe "CAS2" $ do
      let doCas c t =
            testFor regRange $ \c1 ->
              testFor regRange $ \c2 ->
                testFor regRange $ \u1 ->
                  testFor regRange $ \u2 ->
                    testFor regRange $ \r1 ->
                      testFor regRange $ \r2 ->
                        runTest
                          [ c
                          , bitExpand [(0, c1), (6, u1), (12, r1)]
                          , bitExpand [(0, c2), (6, u2), (12, r2)]
                          ]
                          (CAS2
                             t
                             (DR c1)
                             (DR c2)
                             (DR u1)
                             (DR u2)
                             (xr r1)
                             (xr r2))
      prop "CAS2.W" $ doCas 0o006374 WORD
      prop "CAS2.L" $ doCas 0o007374 LONG
    describe "MOVES" $ do
      let doMoves opc t isStore =
            testFor regRange $ \r ->
              checkOpWithEaMem
                [opc, bitExpand [(11, bool2Bit isStore), (12, r)]]
                (\x -> MOVES t isStore x (xr r))
                EaMem
      describe "B" $ do
        prop "load" $ doMoves 0o007000 BYTE False
        prop "store" $ doMoves 0o007000 BYTE True
      describe "W" $ do
        prop "load" $ doMoves 0o007100 WORD False
        prop "store" $ doMoves 0o007100 WORD True
      describe "L" $ do
        prop "load" $ doMoves 0o007200 LONG False
        prop "store" $ doMoves 0o007200 LONG True
    describe "MOVE" $ do
      let moveTest t op1 dst op2 =
            testForX [EaDN, EaMem, EaPC, EaImm t] $
            checkOpWithEa2 [op1] (\x -> MOVE t x dst) op2
          doMoveTest t opc = do
            prop "toDn" $
              testFor regRange $ \c ->
                moveTest
                  t
                  (bitExpand [(6, 0), (9, c), (12, opc)])
                  (DReg $ DR c)
                  []
            prop "toMem" $
              testFor regRange $ \c ->
                moveTest
                  t
                  (bitExpand [(6, 2), (9, c), (12, opc)])
                  (Address $ UnRefAR $ AR c)
                  []
            prop "toMemInc" $
              testFor regRange $ \c ->
                moveTest
                  t
                  (bitExpand [(6, 3), (9, c), (12, opc)])
                  (Address $ UnRefInc $ AR c)
                  []
            prop "toMemDec" $
              testFor regRange $ \c ->
                moveTest
                  t
                  (bitExpand [(6, 4), (9, c), (12, opc)])
                  (Address $ UnRefDec $ AR c)
                  []
            prop "toMemOffset16" $
              testFor regRange $ \c ->
                imm16Test $ \d ->
                  moveTest
                    t
                    (bitExpand [(6, 5), (9, c), (12, opc)])
                    (Address $ Offset16 (toS16 d) (BaseAR $ AR c))
                    [d]
            prop "toExt" $
              testFor regRange $ \c ->
                imm8Test $ \d ->
                  moveTest
                    t
                    (bitExpand [(6, 6), (9, c), (12, opc)])
                    (Address $ Offset8 (toS8 d) (BaseAR $ AR c) False (xr 0) 0)
                    [d]
            prop "toAddrImm16" $
              imm16Test $ \d ->
                moveTest
                  t
                  (bitExpand [(6, 7), (9, 0), (12, opc)])
                  (Address $ ImmAddr d)
                  [d]
            prop "toAddrImm32" $
              imm32Test $ \d ->
                moveTest
                  t
                  (bitExpand [(6, 7), (9, 1), (12, opc)])
                  (Address $ ImmAddr d) $
                longToWord d
      describe "B" $ do doMoveTest BYTE 1
      describe "L" $ do doMoveTest LONG 2
      describe "W" $ do doMoveTest WORD 3
    describe "MOVEA" $ do
      let testMoveA t opc =
            testFor regRange $ \c ->
              testForX [EaDN, EaAN, EaMem, EaPC, EaImm t] $
              checkOpWithEa [bitExpand [(6, 1), (9, c), (12, opc)]] $ \x ->
                MOVEA t x $ AR c
      prop "L" $ testMoveA LONG 2
      prop "W" $ testMoveA WORD 3
    let testEa o opc t = testForX [EaDN, EaMem] $ checkOpWithEa [opc] $ o t
    describe "NEGX" $ do
      prop "B" $ testEa NEGX 0o040000 BYTE
      prop "W" $ testEa NEGX 0o040100 WORD
      prop "L" $ testEa NEGX 0o040200 LONG
    prop "MOVE from SR" $ testEa (`MOVE` SR) 0o040300 WORD
    describe "CLR" $ do
      prop "B" $ testEa CLR 0o041000 BYTE
      prop "W" $ testEa CLR 0o041100 WORD
      prop "L" $ testEa CLR 0o041200 LONG
    prop "MOVE from CCR" $ testEa (`MOVE` CCR) 0o041300 WORD
    describe "NEG" $ do
      prop "B" $ testEa NEG 0o042000 BYTE
      prop "W" $ testEa NEG 0o042100 WORD
      prop "L" $ testEa NEG 0o042200 LONG
    prop "MOVE to CCR" $
      testForX [EaDN, EaMem, EaPC, EaImm WORD] $
      checkOpWithEa [0o042300] $ \x -> MOVE WORD x CCR
    describe "NOT" $ do
      prop "B" $ testEa NOT 0o043000 BYTE
      prop "W" $ testEa NOT 0o043100 WORD
      prop "L" $ testEa NOT 0o043200 LONG
    prop "MOVE to SR" $
      testForX [EaDN, EaMem, EaPC, EaImm WORD] $
      checkOpWithEa [0o043300] $ \x -> MOVE WORD x SR
    prop "NBCD" $ testEa NBCD 0o044000 BYTE
    prop "LINK.L" $
      testFor regRange $ \c ->
        imm32Test $ \i ->
          runTest ((0o044010 .|. c) : longToWord i) $ LINK (AR c) i
    prop "SWAP" $
      testFor regRange $ \c -> runTest [0o044100 .|. c] $ SWAP (DR c)
    prop "BKPT" $ testFor regRange $ \c -> runTest [0o044110 .|. c] $ BKPT c
    prop "PEA" $ testForX [EaMem, EaPC] $ checkOpWithEaMem [0o044100] PEA
    describe "EXT" $ do
      prop "W" $
        testFor regRange $ \c -> runTest [0o044200 .|. c] $ EXT WORD $ DR c
      prop "L" $
        testFor regRange $ \c -> runTest [0o044300 .|. c] $ EXT LONG $ DR c
    describe "MOVEM" $ do
      let testMoveM opc t = do
            let baseOp = [(9, 0o044), (6, opc)]
            describe "store" $ do
              prop "decr" $
                testFor regRange $ \c ->
                  imm16Test $ \i ->
                    runTest [bitExpand (baseOp ++ [(0, c), (3, 4)]), i] $
                    MOVEM t True (UnRefDec $ AR c) $ makeRegList i
              prop "addr" $
                imm16Test $ \i ->
                  checkOpWithEaMem
                    [bitExpand baseOp, i]
                    (\x -> MOVEM t True x $ makeRegList i)
                    EaMem
            describe "load" $ do
              prop "incr" $
                testFor regRange $ \c ->
                  imm16Test $ \i ->
                    runTest [bitExpand (baseOp ++ [(10, 1), (0, c), (3, 3)]), i] $
                    MOVEM t False (UnRefInc $ AR c) $ makeRegList i
              prop "addr" $
                imm16Test $ \i ->
                  checkOpWithEaMem
                    [bitExpand ((10, 1) : baseOp), i]
                    (\x -> MOVEM t False x $ makeRegList i)
                    EaMem
      describe "W" $ testMoveM 2 WORD
      describe "L" $ testMoveM 3 LONG
    describe "TST" $ do
      let doTest t n =
            testForX ([EaDN, EaMem, EaPC, EaImm t] ++ ([EaAN | t /= BYTE])) $
            checkOpWithEa [bitExpand [(0, 0o045000), (6, n)]] $ TST t
      prop "B" $ doTest BYTE 0
      prop "W" $ doTest WORD 1
      prop "L" $ doTest LONG 2
    prop "TAS" $ testForX [EaDN, EaMem] $ checkOpWithEa [0o045300] $ TAS BYTE
    let doMulDivL o op1 op2 =
          testFor regRange $ \r ->
            testForX [EaDN, EaMem, EaPC, EaImm LONG] $
            checkOpWithEa [op1, bitExpand [(0, op2), (12, r)]] $ \x ->
              o x $ DR r
    describe "MULU.L" $ do
      prop "no highword" $ doMulDivL MULUL 0o046000 0
      prop "quad" $
        testFor regRange $ \dh ->
          doMulDivL (`MULULL` DR dh) 0o046000 (0x400 .|. dh)
    describe "MULS.L" $ do
      prop "no highword" $ doMulDivL MULSL 0o046000 0x800
      prop "quad" $
        testFor regRange $ \dh ->
          doMulDivL (`MULSLL` DR dh) 0o046000 (0xC00 .|. dh)
    describe "DIVU.L" $ do
      prop "no highword" $
        testFor regRange $ \r -> doMulDivL (`DIVUL` DR r) 0o046100 r
      prop "quad" $
        testFor regRange $ \r ->
          doMulDivL (`DIVULL` DR r) 0o046100 (0x400 .|. r)
    describe "DIVS.L" $ do
      prop "no highword" $
        testFor regRange $ \r -> doMulDivL (`DIVSL` DR r) 0o046100 (0x800 .|. r)
      prop "quad" $
        testFor regRange $ \r ->
          doMulDivL (`DIVSLL` DR r) 0o046100 (0xC00 .|. r)
    prop "TRAP" $
      forAll (chooseInt (0, 15)) $ \c -> runTest [0o047100 .|. c] $ TRAPn c
    prop "LINK.W" $
      testFor regRange $ \an ->
        imm16Test $ \i -> runTest [0o047120 .|. an, i] $ LINK (AR an) i
    prop "UNLK" $
      testFor regRange $ \an -> runTest [0o047130 .|. an] $ UNLK $ AR an
    prop "MOVE to USP" $
      testFor regRange $ \an ->
        runTest [0o047140 .|. an] $ MOVE LONG (AReg $ AR an) (SpRG "USP")
    prop "MOVE from USP" $
      testFor regRange $ \an ->
        runTest [0o047150 .|. an] $ MOVE LONG (SpRG "USP") (AReg $ AR an)
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
                testFor regRange $ \rn ->
                  runTest [0o047172, rn `shiftL` 12 .|. code] $
                  MOVEC False (xr rn) name
              prop "store" $
                testFor regRange $ \rn ->
                  runTest [0o047173, rn `shiftL` 12 .|. code] $
                  MOVEC True (xr rn) name
      doTest "sfc" 0
      doTest "dfc" 1
      doTest "cacr" 2
      doTest "tc" 3
      doTest "itt0" 4
      doTest "itt1" 5
      doTest "dtt0" 6
      doTest "dtt1" 7
      doTest "usp" 0x800
      doTest "vbr" 0x801
      doTest "msp" 0x803
      doTest "isp" 0x804
      doTest "mmusr" 0x805
      doTest "urp" 0x806
      doTest "srp" 0x807
    prop "JSR" $ testForX [EaMem, EaPC] $ checkOpWithEaMem [0o047200] JSR
    prop "JMP" $ testForX [EaMem, EaPC] $ checkOpWithEaMem [0o047300] JMP
    describe "CHK" $ do
      let testChk t opc =
            testFor regRange $ \dn ->
              testForX [EaDN, EaMem, EaPC, EaImm t] $
              checkOpWithEa [opc `withDn` dn] $ \x -> CHK t x $ DR dn
      prop "L" $ testChk LONG 0o040400
      prop "W" $ testChk WORD 0o040600
    prop "EXTB" $
      testFor regRange $ \dn -> runTest [0o044700 .|. dn] $ EXTB $ DR dn
    prop "LEA" $
      testFor regRange $ \an ->
        testForX [EaMem, EaPC] $
        checkOpWithEaMem [0o040700 `withDn` an] $ \x -> LEA x $ AR an
    let testAddSubQ op t opc = do
          let target = EaDN : EaMem : ([EaAN | t /= BYTE])
          prop "imm=0(actually 8)" $
            testForX target $ checkOpWithEa [opc] $ op t 8
          prop "imm!=0" $
            forAll (chooseInt (1, 7)) $ \i ->
              testForX target $ checkOpWithEa [opc `withDn` i] $ op t i
    describe "ADDQ" $ do
      describe "B" $ testAddSubQ ADDQ BYTE 0o050000
      describe "W" $ testAddSubQ ADDQ WORD 0o050100
      describe "L" $ testAddSubQ ADDQ LONG 0o050200
    describe "SUBQ" $ do
      describe "B" $ testAddSubQ SUBQ BYTE 0o050400
      describe "W" $ testAddSubQ SUBQ WORD 0o050500
      describe "L" $ testAddSubQ SUBQ LONG 0o050600
    prop "Scc" $
      testFor ccRange $ \cc ->
        testForX [EaDN, EaMem] $
        checkOpWithEa [bitExpand [(12, 5), (6, 3), (8, cc)]] $ Scc $ CC cc
    prop "DBcc.W" $
      testFor regRange $ \dn ->
        testFor ccRange $ \cc ->
          imm16Test $ \d ->
            runTest [bitExpand [(12, 5), (6, 3), (8, cc), (3, 1), (0, dn)], d] $
            DBcc (CC cc) (DR dn) $ toS16 d + 2
    describe "Trapcc" $ do
      prop "W" $
        testFor ccRange $ \cc ->
          imm16Test $ \t ->
            runTest [bitExpand [(0, 0o050372), (8, cc)], t] $
            TRAPcc (CC cc) $ Just t
      prop "L" $
        testFor ccRange $ \cc ->
          imm32Test $ \t ->
            runTest (bitExpand [(0, 0o050373), (8, cc)] : longToWord t) $
            TRAPcc (CC cc) $ Just t
      prop "None" $
        testFor ccRange $ \cc ->
          runTest [bitExpand [(0, 0o050374), (8, cc)]] $ TRAPcc (CC cc) Nothing
    let testBcc ccx op = do
          prop "byte" $
            forAll ccx $ \cc ->
              forAll (chooseInt (1, 0xFE)) $ \i ->
                runTest [bitExpand [(12, 6), (8, cc), (0, i)]] $
                op cc $ toS8 i + 2
          prop "word" $
            forAll ccx $ \cc ->
              imm16Test $ \i ->
                runTest [bitExpand [(12, 6), (8, cc), (0, 0)], i] $
                op cc $ toS16 i + 2
          prop "long" $
            forAll ccx $ \cc ->
              imm32Test $ \i ->
                runTest (bitExpand [(12, 6), (8, cc), (0, 0xff)] : longToWord i) $
                op cc $ toS32 i + 2
    describe "BRA" $ testBcc (return 0) $ \_ i -> BRA i
    describe "BSR" $ testBcc (return 1) $ \_ i -> BSR i
    describe "Bcc" $ testBcc (chooseInt (2, 15)) $ Bcc . CC
    prop "MOVEQ" $
      testFor regRange $ \dn ->
        imm8Test $ \i ->
          runTest [0o070000 `withDn` dn .|. i] $ MOVEQ (toS8 i) (DR dn)
    let testRegMemR op t opc canAN f =
          testFor regRange $ \dn ->
            testForX (EaDN : EaMem : EaPC : EaImm t : ([EaAN | canAN])) $
            checkOpWithEa [opc `withDn` dn] $ \x -> op t x (f dn)
    let testRegMemW op t opc f =
          testFor regRange $ \dn ->
            checkOpWithEaMem [opc `withDn` dn] (op t $ f dn) EaMem
    describe "OR" $ do
      describe "B" $ do
        prop "load" $ testRegMemR OR BYTE 0o100000 False DR
        prop "store" $ testRegMemW OR_TO_MEM BYTE 0o100400 DR
      describe "W" $ do
        prop "load" $ testRegMemR OR WORD 0o100100 False DR
        prop "store" $ testRegMemW OR_TO_MEM WORD 0o100500 DR
      describe "L" $ do
        prop "load" $ testRegMemR OR LONG 0o100200 False DR
        prop "store" $ testRegMemW OR_TO_MEM LONG 0o100600 DR
    prop "DIVU.W" $ testRegMemR (\_ x dn -> DIVUW x dn) WORD 0o100300 False DR
    let testXY opc op rev f =
          testFor regRange $ \n ->
            testFor regRange $ \m ->
              runTest [opc `withDn` n .|. m] $
              if rev
                then op (f n) (f m)
                else op (f m) (f n)
    let testXYi opc op f =
          testFor regRange $ \n ->
            testFor regRange $ \m ->
              imm16Test $ \i ->
                runTest [opc `withDn` n .|. m, i] $ op (f m) (f n) i
    describe "SBCD" $ do
      prop "register" $ testXY 0o100400 SBCD_REG True DR
      prop "memory" $ testXY 0o0100410 SBCD_MEM True AR
    describe "PACK" $ do
      prop "register" $ testXYi 0o100500 PACK_REG DR
      prop "memory" $ testXYi 0o100510 PACK_MEM AR
    describe "UNPK" $ do
      prop "register" $ testXYi 0o100600 UNPK_REG DR
      prop "memory" $ testXYi 0o100610 UNPK_MEM AR
    prop "DIVS.W" $ testRegMemR (\_ x dn -> DIVSW x dn) WORD 0o100700 False DR
    describe "SUB" $ do
      describe "B" $ do
        prop "load" $ testRegMemR SUB BYTE 0o110000 False DR
        prop "store" $ testRegMemW SUB_TO_MEM BYTE 0o110400 DR
      describe "W" $ do
        prop "load" $ testRegMemR SUB WORD 0o110100 True DR
        prop "store" $ testRegMemW SUB_TO_MEM WORD 0o110500 DR
      describe "L" $ do
        prop "load" $ testRegMemR SUB LONG 0o110200 True DR
        prop "store" $ testRegMemW SUB_TO_MEM LONG 0o110600 DR
    describe "SUBA" $ do
      prop "W" $ testRegMemR SUBA WORD 0o110300 True AR
      prop "L" $ testRegMemR SUBA LONG 0o110700 True AR
    describe "SUBX" $ do
      describe "B" $ do
        prop "register" $ testXY 0o110400 (SUBX_REG BYTE) True DR
        prop "memory" $ testXY 0o0110410 (SUBX_MEM BYTE) True AR
      describe "W" $ do
        prop "register" $ testXY 0o110500 (SUBX_REG WORD) True DR
        prop "memory" $ testXY 0o0110510 (SUBX_MEM WORD) True AR
      describe "L" $ do
        prop "register" $ testXY 0o110600 (SUBX_REG LONG) True DR
        prop "memory" $ testXY 0o0110610 (SUBX_MEM LONG) True AR
    prop "SYSCALL" $
      forAll (chooseInt (0, 0xFFF)) $ \c ->
        let cc = 0o120000 .|. c
         in runTest [cc] $ SYS cc
    describe "CMP" $ do
      prop "B" $ testRegMemR CMP BYTE 0o130000 False DR
      prop "W" $ testRegMemR CMP WORD 0o130100 True DR
      prop "L" $ testRegMemR CMP LONG 0o130200 True DR
    describe "CMPA" $ do
      prop "W" $ testRegMemR CMPA WORD 0o130300 True AR
      prop "L" $ testRegMemR CMPA LONG 0o130700 True AR
    describe "EOR" $ do
      let testEOR t opc =
            testFor regRange $ \dn ->
              testForX [EaDN, EaMem] $
              checkOpWithEa [opc `withDn` dn] $ \x -> EOR t (DR dn) x
      prop "B" $ testEOR BYTE 0o130400
      prop "W" $ testEOR WORD 0o130500
      prop "L" $ testEOR LONG 0o130600
    describe "CMPM" $ do
      prop "B" $ testXY 0o130410 (CMPM BYTE) False AR
      prop "W" $ testXY 0o130510 (CMPM WORD) False AR
      prop "L" $ testXY 0o130610 (CMPM LONG) False AR
    describe "AND" $ do
      describe "B" $ do
        prop "load" $ testRegMemR AND BYTE 0o140000 False DR
        prop "store" $ testRegMemW AND_TO_MEM BYTE 0o140400 DR
      describe "W" $ do
        prop "load" $ testRegMemR AND WORD 0o140100 False DR
        prop "store" $ testRegMemW AND_TO_MEM WORD 0o140500 DR
      describe "L" $ do
        prop "load" $ testRegMemR AND LONG 0o140200 False DR
        prop "store" $ testRegMemW AND_TO_MEM LONG 0o140600 DR
    prop "MULU.W" $ testRegMemR (\_ x dn -> MULUW x dn) WORD 0o140300 False DR
    describe "ABCD" $ do
      prop "register" $ testXY 0o140400 ABCD_REG False DR
      prop "memory" $ testXY 0o140410 ABCD_MEM False AR
    describe "EXG" $ do
      prop "dm<>dn" $ testXY 0o140500 EXG_D True DR
      prop "am<>an" $ testXY 0o140510 EXG_A True AR
      prop "dm<>an" $
        testFor regRange $ \n ->
          testFor regRange $ \m ->
            runTest [0o140610 `withDn` n .|. m] $ EXG_DA (DR n) (AR m)
    prop "MULS.W" $ testRegMemR (\_ x dn -> MULSW x dn) WORD 0o140700 False DR
    describe "ADD" $ do
      describe "B" $ do
        prop "load" $ testRegMemR ADD BYTE 0o150000 False DR
        prop "store" $ testRegMemW ADD_TO_MEM BYTE 0o150400 DR
      describe "W" $ do
        prop "load" $ testRegMemR ADD WORD 0o150100 True DR
        prop "store" $ testRegMemW ADD_TO_MEM WORD 0o150500 DR
      describe "L" $ do
        prop "load" $ testRegMemR ADD LONG 0o150200 True DR
        prop "store" $ testRegMemW ADD_TO_MEM LONG 0o150600 DR
    describe "ADDA" $ do
      prop "W" $ testRegMemR ADDA WORD 0o150300 True AR
      prop "L" $ testRegMemR ADDA LONG 0o150700 True AR
    describe "ADDX" $ do
      describe "B" $ do
        prop "register" $ testXY 0o150400 (ADDX_REG BYTE) False DR
        prop "memory" $ testXY 0o0150410 (ADDX_MEM BYTE) False AR
      describe "W" $ do
        prop "register" $ testXY 0o150500 (ADDX_REG WORD) False DR
        prop "memory" $ testXY 0o0150510 (ADDX_MEM WORD) False AR
      describe "L" $ do
        prop "register" $ testXY 0o150600 (ADDX_REG LONG) False DR
        prop "memory" $ testXY 0o0150610 (ADDX_MEM LONG) False AR
    let testShift op t opc = do
          prop "by imm(sc=0)" $
            testFor regRange $ \dn ->
              runTest [opc .|. dn] $ op t (BImm 8) (DR dn)
          prop "by imm" $
            testFor regRange $ \dn ->
              forAll (chooseInt (1, 7)) $ \c ->
                runTest [opc `withDn` c .|. dn] $ op t (BImm c) (DR dn)
          prop "by reg" $
            testFor regRange $ \dn ->
              forAll (chooseInt (0, 7)) $ \c ->
                runTest [opc `withDn` c .|. 0o40 .|. dn] $
                op t (BReg $ DR c) $ DR dn
    describe "ASR" $ do
      describe "B" $ testShift ASR BYTE 0o160000
      describe "W" $ testShift ASR WORD 0o160100
      describe "L" $ testShift ASR LONG 0o160200
      prop "EA" $ checkOpWithEaMem [0o160300] ASR_EA EaMem
    describe "LSR" $ do
      describe "B" $ testShift LSR BYTE 0o160010
      describe "W" $ testShift LSR WORD 0o160110
      describe "L" $ testShift LSR LONG 0o160210
      prop "EA" $ checkOpWithEaMem [0o161300] LSR_EA EaMem
    describe "ROXR" $ do
      describe "B" $ testShift ROXR BYTE 0o160020
      describe "W" $ testShift ROXR WORD 0o160120
      describe "L" $ testShift ROXR LONG 0o160220
      prop "EA" $ checkOpWithEaMem [0o162300] ROXR_EA EaMem
    describe "ROR" $ do
      describe "B" $ testShift ROR BYTE 0o160030
      describe "W" $ testShift ROR WORD 0o160130
      describe "L" $ testShift ROR LONG 0o160230
      prop "EA" $ checkOpWithEaMem [0o163300] ROR_EA EaMem
    describe "ASL" $ do
      describe "B" $ testShift ASL BYTE 0o160400
      describe "W" $ testShift ASL WORD 0o160500
      describe "L" $ testShift ASL LONG 0o160600
      prop "EA" $ checkOpWithEaMem [0o160700] ASL_EA EaMem
    describe "LSL" $ do
      describe "B" $ testShift LSL BYTE 0o160410
      describe "W" $ testShift LSL WORD 0o160510
      describe "L" $ testShift LSL LONG 0o160610
      prop "EA" $ checkOpWithEaMem [0o161700] LSL_EA EaMem
    describe "ROXL" $ do
      describe "B" $ testShift ROXL BYTE 0o160420
      describe "W" $ testShift ROXL WORD 0o160520
      describe "L" $ testShift ROXL LONG 0o160620
      prop "EA" $ checkOpWithEaMem [0o162700] ROXL_EA EaMem
    describe "ROL" $ do
      describe "B" $ testShift ROL BYTE 0o160430
      describe "W" $ testShift ROL WORD 0o160530
      describe "L" $ testShift ROL LONG 0o160630
      prop "EA" $ checkOpWithEaMem [0o163700] ROL_EA EaMem
    let testBf1 op opc isBFTST = do
          let target = EaDN : EaMem : ([EaPC | isBFTST])
          forAll (elements [True, False]) $ \off_d ->
            forAll (elements [True, False]) $ \len_d ->
              forAll (chooseInt (0, 31)) $ \off ->
                forAll (chooseInt (0, 31)) $ \len ->
                  testForX target $
                  checkOpWithEa
                    [ opc
                    , bitExpand
                        [ (0, len)
                        , (5, bool2Bit len_d)
                        , (6, off)
                        , (11, bool2Bit off_d)
                        ]
                    ] $ \x ->
                    op
                      x
                      ((if off_d
                          then BReg . DR
                          else BImm)
                         off)
                      (if len_d
                         then BReg $ DR len
                         else BImm
                                (if len == 0
                                   then 32
                                   else len))
    prop "BFTST" $ testBf1 BFTST 0o164300 True
    prop "BFCHG" $ testBf1 BFCHG 0o165300 False
    prop "BFCLR" $ testBf1 BFCLR 0o166300 False
    prop "BFSET" $ testBf1 BFSET 0o167300 False
    let testBf2 op opc = do
          let target = [EaDN, EaMem, EaPC]
          forAll (elements [True, False]) $ \off_d ->
            forAll (elements [True, False]) $ \len_d ->
              forAll (chooseInt (0, 31)) $ \off ->
                forAll (chooseInt (0, 31)) $ \len ->
                  testFor regRange $ \dn ->
                    testForX target $
                    checkOpWithEa
                      [ opc
                      , bitExpand
                          [ (0, len)
                          , (5, bool2Bit len_d)
                          , (6, off)
                          , (11, bool2Bit off_d)
                          , (12, dn)
                          ]
                      ] $ \x ->
                      op
                        x
                        ((if off_d
                            then BReg . DR
                            else BImm)
                           off)
                        (if len_d
                           then BReg $ DR len
                           else BImm
                                  (if len == 0
                                     then 32
                                     else len)) $
                      DR dn
    prop "BFEXTU" $ testBf2 BFEXTU 0o164700
    prop "BFEXTS" $ testBf2 BFEXTS 0o165700
    prop "BFFFO" $ testBf2 BFFFO 0o166700
    prop "BFINS" $
      forAll (elements [True, False]) $ \off_d ->
        forAll (elements [True, False]) $ \len_d ->
          forAll (chooseInt (0, 31)) $ \off ->
            forAll (chooseInt (0, 31)) $ \len ->
              testFor regRange $ \dn ->
                testForX [EaDN, EaMem] $
                checkOpWithEa
                  [ 0o167700
                  , bitExpand
                      [ (0, len)
                      , (5, bool2Bit len_d)
                      , (6, off)
                      , (11, bool2Bit off_d)
                      , (12, dn)
                      ]
                  ] $ \x ->
                  BFINS
                    (DR dn)
                    x
                    ((if off_d
                        then BReg . DR
                        else BImm)
                       off)
                    (if len_d
                       then BReg $ DR len
                       else BImm
                              (if len == 0
                                 then 32
                                 else len))
