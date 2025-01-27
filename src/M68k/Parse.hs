{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE BinaryLiterals     #-}
{-# LANGUAGE StandaloneDeriving #-}

module M68k.Parse where

import           Control.Monad             (mzero)
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Bits                 (Bits (shiftL, shiftR, testBit, (.&.), (.|.)))
import           Data.Maybe
import           Data.Word
import           GHC.Float                 (castWord32ToFloat,
                                            castWord64ToDouble)
import           M68k.Common
import           M68k.LongDouble
import           M68k.Opcode
import           M68k.Operand
import           Util                      (between, getBit, toS16, toS32, toS8)

getRn :: Int -> Operand
getRn d =
  if d > 7
    then AReg $ AR (d - 8)
    else DReg $ DR d

nothingT :: MaybeT (State (Int, [Word8])) a
nothingT = mzero

toAFType :: Int -> AFType
toAFType n =
  case n of
    0 -> FInt LONG
    1 -> FSINGLE
    2 -> FEXT
    3 -> FPACKED
    4 -> FInt WORD
    5 -> FDOUBLE
    6 -> FInt BYTE
    7 -> FPACKED
    _ -> undefined

getPC :: State (Int, [Word8]) Int
getPC = state (\(s, p) -> (s, (s, p)))

next8 :: MaybeT (State (Int, [Word8])) Int
next8 = do
  (s, x) <- get
  if null x
    then MaybeT $ do return Nothing
    else do
      put (s + 1, drop 1 x)
      return (fromIntegral $ head x :: Int)

next16 =
  let
   in do high <- next8
         low <- next8
         return $ high `shiftL` 8 .|. low

next32 = do
  high <- next16
  low <- next16
  return $ high `shiftL` 16 .|. low

nextX t =
  if t == LONG
    then next32
    else next16

parseEaEx :: Int -> AddrBase -> MaybeT (State (Int, [Word8])) MemOperand
parseEaEx nw base
  | not (testBit nw 8) = do
    return $ Offset8 (toS8 (getBit nw 0 0xff)) base ext index cc
  | testBit nw 3 = nothingT
  | od_i == 0 && isPost = nothingT
  | otherwise = do
    bd <-
      case getBit nw 4 3 of
        1 -> return 0
        2 -> toS16 <$> next16
        3 -> toS32 <$> next32
        _ -> nothingT
    od <-
      case od_i of
        2 -> toS16 <$> next16
        3 -> toS32 <$> next32
        _ -> return 0
    return $
      if od_i == 0
        then Indirect bd base_p ext index_p cc
        else (if isPost
                then PostIndex
                else PreIndex)
               bd
               base_p
               ext
               index_p
               cc
               od
  where
    index = xr $ getBit nw 12 15
    ext = testBit nw 11
    cc = getBit nw 9 3
    od_i = getBit nw 0 3
    isPost = testBit nw 2
    index_p =
      if testBit nw 6
        then Nothing
        else Just index
    base_p =
      if testBit nw 7
        then BaseNone
        else base

isSpecialEA regT regN = regT == 7 && regN == 4

dr = DReg . DR

ar = AReg . AR

parseEA ::
     Int
  -> Int
  -> MaybeT (State (Int, [Word8])) Operand
  -> MaybeT (State (Int, [Word8])) Operand
parseEA 0 regN _ = do
  return $ dr regN
parseEA 1 regN _ = do
  return $ ar regN
parseEA 7 4 other = other
parseEA n r _ = do
  mem <- parseEAMem n r
  return $ Address mem

parseEAMem :: Int -> Int -> MaybeT (State (Int, [Word8])) MemOperand
parseEAMem 2 regN = do
  return $ UnRefAR $ AR regN
parseEAMem 3 regN = do
  return $ UnRefInc $ AR regN
parseEAMem 4 regN = do
  return $ UnRefDec $ AR regN
parseEAMem 5 regN = do
  nw <- next16
  return $ Offset16 (toS16 nw) $ BaseAR $ AR regN
parseEAMem 6 regN = do
  nw <- next16
  parseEaEx nw (BaseAR $ AR regN)
parseEAMem 7 0 = do
  ImmAddr <$> next16
parseEAMem 7 1 = do
  ImmAddr <$> next32
parseEAMem 7 2 = do
  pc <- lift getPC
  imm <- next16
  return $ Offset16 (toS16 imm) $ BasePC pc
parseEAMem 7 3 = do
  pc <- lift getPC
  nw <- next16
  parseEaEx nw (BasePC pc)
parseEAMem _ _ = MaybeT $ do return Nothing

nextOpX :: AType -> MaybeT (State (Int, [Word8])) Int
nextOpX BYTE = next16
nextOpX WORD = next16
nextOpX LONG = next32

parseOpMoves :: AType -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOpMoves t regT regN = do
  nw <- next16
  let rn = xr $ getBit nw 12 15
  ea <- parseEAMem regT regN
  return $ MOVES t (testBit nw 11) ea rn

parseOpCmp2 :: AType -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOpCmp2 t regT regN = do
  nw <- next16
  ea <- parseEAMem regT regN
  let op =
        (if testBit nw 11
           then CHK2
           else CMP2)
  let rn = xr $ getBit nw 12 15
  return $ op t ea rn

parseBitTestCommon ::
     Int
  -> Int
  -> (AType -> Operand -> t -> b)
  -> t
  -> MaybeT (State (Int, [Word8])) b
parseBitTestCommon regT regN op_c pos = do
  let t =
        if regT == 0
          then LONG
          else BYTE
  op <- parseEA regT regN (ImmInt <$> next16)
  return $ op_c t op pos

parseBitTest ::
     Int
  -> Int
  -> (AType -> Operand -> BopSc -> b)
  -> MaybeT (State (Int, [Word8])) b
parseBitTest regT regN op_c = do
  x <- next16
  parseBitTestCommon regT regN op_c $
    BImm
      (if x == 0
         then 8
         else x)

parseBitTest2 ::
     Int
  -> Int
  -> (AType -> Operand -> BopSc -> b)
  -> Int
  -> MaybeT (State (Int, [Word8])) b
parseBitTest2 regT regN op_c dn =
  parseBitTestCommon regT regN op_c (BReg $ DR dn)

parseMoveP :: AType -> Int -> Int -> Bool -> MaybeT (State (Int, [Word8])) Op
parseMoveP t dn regN toMem = do
  imm <- next16
  return $ MOVEP t toMem (AR regN) imm (DR dn)

parseCas t regT regN = do
  nw <- next16
  let dc = DR $ getBit nw 0 7
      du = DR $ getBit nw 6 7
   in if isSpecialEA regT regN
        then do
          extw <- next16
          let rn1 = xr $ getBit nw 12 15
              dc2 = DR $ getBit extw 0 7
              du2 = DR $ getBit extw 6 7
              rn2 = xr $ getBit extw 12 15
          return $ CAS2 t dc dc2 du du2 rn1 rn2
        else do
          ea <- parseEAMem regT regN
          return $ CAS t dc du ea

doOp2 f t dstM immM = do
  o <- immM
  dst <- dstM
  return $ f t dst o

toBitOp :: (Eq a, Num a) => a -> AType -> Operand -> BopSc -> Op
toBitOp 0 = BTST
toBitOp 1 = BCHG
toBitOp 2 = BCLR
toBitOp 3 = BSET
toBitOp _ = undefined

parseOp0 :: Int -> Int -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp0 dni opi regT regN
  | opi < 3 = do
    let t = toEnum opi
        bitOp = toBitOp opi
        ea = parseEA regT regN nothingT
        dst =
          parseEA
            regT
            regN
            (case opi of
               0 -> return CCR
               1 -> return SR
               _ -> nothingT)
        src = parseEA regT regN (ImmInt <$> nextX t)
     in case dni of
          0 -> doOp2 ORI t dst $ nextX t
          1 -> doOp2 ANDI t dst $ nextX t
          2 -> doOp2 SUBI t ea $ nextX t
          3 -> doOp2 ADDI t ea $ nextX t
          4 -> parseBitTest regT regN bitOp
          5 -> doOp2 EORI t dst $ nextX t
          6 -> doOp2 CMPI t src $ nextX t
          7 -> parseOpMoves t regT regN
          _ -> nothingT
  | opi == 3 = do
    case dni of
      3 -> return ILLEGAL
      4 -> parseBitTest regT regN BSET
      _
        | dni < 3 -> parseOpCmp2 (toEnum dni) regT regN
        | otherwise -> parseCas (toEnum $ dni - 5) regT regN
  | otherwise = do
    if regT == 1
      then parseMoveP
             (if even opi
                then WORD
                else LONG)
             dni
             regN
             (opi < 6)
      else parseBitTest2 regT regN (toBitOp $ opi - 4) dni

parseOpMove ::
     AType -> Int -> Int -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOpMove t dstT dstN srcT srcN = do
  srcEA <-
    parseEA
      srcT
      srcN
      (ImmInt <$>
       (if t == LONG
          then next32
          else next16))
  dstEA <- parseEA dstT dstN nothingT
  return $
    if dstT == 1
      then MOVEA t srcEA $ AR dstN
      else MOVE t srcEA dstEA

parseOpV1 ::
     t
  -> (t -> Operand -> b)
  -> MaybeT (State (Int, [Word8])) Operand
  -> Int
  -> Int
  -> MaybeT (State (Int, [Word8])) b
parseOpV1 t opc e regT regN = opc t <$> parseEA regT regN e

movecName :: (Eq a, Num a) => a -> String
movecName x
  | x == 0 = "sfc"
  | x == 1 = "dfc"
  | x == 2 = "cacr"
  | x == 3 = "tc"
  | x == 4 = "itt0"
  | x == 5 = "itt1"
  | x == 6 = "dtt0"
  | x == 7 = "dtt1"
  | x == 0x800 = "usp"
  | x == 0x801 = "vbr"
  | x == 0x803 = "msp"
  | x == 0x804 = "isp"
  | x == 0x805 = "mmusr"
  | x == 0x806 = "urp"
  | x == 0x807 = "srp"
  | otherwise = "???"

parseOp40 ::
     (Eq a, Num a) => a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp40 0 = parseOpV1 BYTE NEGX nothingT
parseOp40 1 = parseOpV1 BYTE CLR nothingT
parseOp40 2 = parseOpV1 BYTE NEG nothingT
parseOp40 3 = parseOpV1 BYTE NOT nothingT
parseOp40 4 =
  \regT regN ->
    (if regT == 1
       then LINK (AR regN) <$> next32
       else parseOpV1 BYTE NBCD nothingT regT regN)
parseOp40 5 = parseOpV1 BYTE TST $ ImmInt <$> next16
parseOp40 6 = parseMul
parseOp40 _ = undefined

parseOp41 ::
     (Eq a, Num a) => a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp41 0 = parseOpV1 WORD NEGX nothingT
parseOp41 1 = parseOpV1 WORD CLR nothingT
parseOp41 2 = parseOpV1 WORD NEG nothingT
parseOp41 3 = parseOpV1 WORD NOT nothingT
parseOp41 4 =
  \regT regN ->
    (case regT of
       0 -> return $ SWAP (DR regN)
       1 -> return $ BKPT regN
       _ -> PEA <$> parseEAMem regT regN)
parseOp41 5 = parseOpV1 WORD TST $ ImmInt <$> next16
parseOp41 6 = parseDiv
parseOp41 7 = parse0471
parseOp41 _ = undefined

parseMul :: Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseMul regT regN = do
  nw <- next16
  let qw = testBit nw 10
      sg = testBit nw 11
      dl = DR $ getBit nw 12 7
      dh = DR $ getBit nw 0 7
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $
    if qw
      then (if sg
              then MULSLL
              else MULULL)
             ea
             dh
             dl
      else (if sg
              then MULSL
              else MULUL)
             ea
             dl

parseDiv :: Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseDiv regT regN = do
  nw <- next16
  let qw = testBit nw 10
      sg = testBit nw 11
      dq = DR $ getBit nw 12 7
      dr_i = DR $ getBit nw 0 7
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $
    (if qw
       then if sg
              then DIVSLL
              else DIVULL
       else if sg
              then DIVSL
              else DIVUL)
      ea
      dr_i
      dq

parse0471 :: (Eq a, Num a) => a -> Int -> MaybeT (State (Int, [Word8])) Op
parse0471 0 regN = do
  return $ TRAPn regN
parse0471 1 regN = do
  return $ TRAPn $ 8 + regN
parse0471 2 regN = LINK (AR regN) <$> next16
parse0471 3 regN = do
  return $ UNLK $ AR regN
parse0471 4 regN = do
  return $ MOVE LONG (AReg $ AR regN) (SpRG "USP")
parse0471 5 regN = do
  return $ MOVE LONG (SpRG "USP") (AReg $ AR regN)
parse0471 6 0 = do
  return RESET
parse0471 6 1 = do
  return NOP
parse0471 6 2 = do
  STOP <$> next16
parse0471 6 3 = do
  return RTE
parse0471 6 4 = do
  RTD <$> next16
parse0471 6 5 = do
  return RTS
parse0471 6 6 = do
  return TRAPV
parse0471 6 7 = do
  return RTR
parse0471 7 regN = do
  nw <- next16
  let rn = xr $ getBit nw 12 15
      cc = getBit nw 0 0xFFF
  return $
    case regN of
      2 -> MOVEC False rn $ movecName cc
      3 -> MOVEC True rn $ movecName cc
      _ -> ILLEGAL
parse0471 _ _ = undefined

parseOp42 ::
     (Eq a, Num a) => a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp42 0 = parseOpV1 LONG NEGX nothingT
parseOp42 1 = parseOpV1 LONG CLR nothingT
parseOp42 2 = parseOpV1 LONG NEG nothingT
parseOp42 3 = parseOpV1 LONG NOT nothingT
parseOp42 4 =
  \regT regN ->
    (if regT == 0
       then return $ EXT WORD $ DR regN
       else do
         imm <- next16
         ea <- parseEAMem regT regN
         return $ MOVEM WORD True ea [xr x | x <- [0 .. 15], testBit imm x])
parseOp42 5 = parseOpV1 LONG TST $ ImmInt <$> next32
parseOp42 6 =
  \regT regN ->
    (do imm <- next16
        ea <- parseEAMem regT regN
        return $ MOVEM WORD False ea [xr x | x <- [0 .. 15], testBit imm x])
parseOp42 7 =
  \regT regN ->
    (do ea <- parseEAMem regT regN
        return $ JSR ea)
parseOp42 _ = undefined

parseOp43 ::
     (Eq a, Num a) => a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp43 4 0 regN = return $ EXT LONG $ DR regN
parseOp43 4 regT regN = do
  imm <- next16
  ea <- parseEAMem regT regN
  return $ MOVEM LONG True ea [xr x | x <- [0 .. 15], testBit imm x]
parseOp43 5 regT regN = parseOpV1 BYTE TAS nothingT regT regN
parseOp43 6 regT regN = do
  imm <- next16
  ea <- parseEAMem regT regN
  return $ MOVEM LONG False ea [xr x | x <- [0 .. 15], testBit imm x]
parseOp43 7 regT regN = do
  ea <- parseEAMem regT regN
  return $ JMP ea
parseOp43 dni regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  case dni of
    0 -> return $ MOVE WORD SR ea
    1 -> return $ MOVE WORD CCR ea
    2 -> return $ MOVE WORD ea CCR
    3 -> return $ MOVE WORD ea SR
    _ -> undefined

parseChk :: AType -> Int -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseChk t dni regT regN = do
  ea <- parseEA regT regN $ ImmInt <$> nextX t
  return $ CHK t ea $ DR dni

parseOp4 ::
     (Eq a, Num a) => Int -> a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp4 dni 0 = do
  parseOp40 dni
parseOp4 dni 1 = do
  parseOp41 dni
parseOp4 dni 2 = do
  parseOp42 dni
parseOp4 dni 3 = do
  parseOp43 dni
parseOp4 dni 4 = do
  parseChk LONG dni
parseOp4 _ 5 = \_ _ -> do return ILLEGAL
parseOp4 dni 6 = do
  parseChk WORD dni
parseOp4 dni 7 =
  \regT regN -> do
    if regT == 0 && dni == 4
      then return $ EXTB $ DR regN
      else do
        ea <- parseEAMem regT regN
        return $ LEA ea $ AR dni
parseOp4 _ _ = undefined

parseOp5 dni opi regT regN
  | opi == 3 || opi == 7 =
    let cc =
          CC $
          dni * 2 +
          (if opi == 3
             then 0
             else 1)
        ea = parseEA regT regN nothingT
     in case regT of
          7 ->
            case regN of
              2 -> TRAPcc cc . Just <$> next16
              3 -> TRAPcc cc . Just <$> next32
              4 -> return $ TRAPcc cc Nothing
              _ -> Scc cc <$> ea
          1 -> do
            pc <- lift getPC
            imm <- next16
            let target = pc + toS16 imm
            return $ DBcc cc (DR regN) target
          _ -> Scc cc <$> ea
  | opi < 3 = ADDQ (toEnum opi) immi <$> parseEA regT regN nothingT
  | otherwise = SUBQ (toEnum $ opi - 4) immi <$> parseEA regT regN nothingT
  where
    immi =
      if dni == 0
        then 8
        else dni

parseOp6 op = do
  let cc = getBit op 8 15
      immX = toS8 $ getBit op 0 0xff
  pc <- lift getPC
  imm <-
    do case immX of
         0  -> toS16 <$> next16
         -1 -> toS32 <$> next32
         _  -> return immX
  let target = imm + pc
  return $
    case cc of
      0 -> BRA target
      1 -> BSR target
      _ -> Bcc (CC cc) target

parseOp8 dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ DIVUW ea $ DR dn
parseOp8 dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ DIVSW ea $ DR dn
parseOp8 dn 4 0 regN = do
  return $ SBCD_REG (DR dn) (DR regN)
parseOp8 dn 4 1 regN = do
  return $ SBCD_MEM (AR dn) (AR regN)
parseOp8 dn 5 0 regN = PACK_REG (DR regN) (DR dn) <$> next16
parseOp8 dn 5 1 regN = PACK_MEM (AR regN) (AR dn) <$> next16
parseOp8 dn 6 0 regN = UNPK_REG (DR regN) (DR dn) <$> next16
parseOp8 dn 6 1 regN = UNPK_MEM (AR regN) (AR dn) <$> next16
parseOp8 dn n regT regN
  | n < 3 = do
    ea <- parseEA regT regN (ImmInt <$> nextX (toEnum n))
    return $ OR (toEnum n) ea (DR dn)
  | otherwise = do
    ea <- parseEAMem regT regN
    return $ OR_TO_MEM (toEnum $ n - 4) (DR dn) ea

parseOp9 dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ SUBA WORD ea (AR dn)
parseOp9 dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $ SUBA LONG ea (AR dn)
parseOp9 dn n regT regN
  | n < 3 = do
    ea <- parseEA regT regN (ImmInt <$> nextX (toEnum n))
    return $ SUB (toEnum n) ea (DR dn)
  | regT == 0 = do return $ SUBX_REG (toEnum $ n - 4) (DR dn) (DR regN)
  | regT == 1 = do return $ SUBX_MEM (toEnum $ n - 4) (AR dn) (AR regN)
  | otherwise = do
    ea <- parseEAMem regT regN
    return $ SUB_TO_MEM (toEnum $ n - 4) (DR dn) ea

parseOpB dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ CMPA WORD ea (AR dn)
parseOpB dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $ CMPA LONG ea (AR dn)
parseOpB dn n regT regN
  | n < 3 = do
    ea <- parseEA regT regN (ImmInt <$> nextX (toEnum n))
    return $ CMP (toEnum n) ea (DR dn)
  | otherwise = do
    if regT == 1
      then return $ CMPM (toEnum $ n - 4) (AR regN) (AR dn)
      else do
        ea <- parseEA regT regN nothingT
        return $ EOR (toEnum $ n - 4) (DR dn) ea

parseOpC dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ MULUW ea (DR dn)
parseOpC dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ MULSW ea (DR dn)
parseOpC dn 4 0 regN = do
  return $ ABCD_REG (DR regN) (DR dn)
parseOpC dn 4 1 regN = do
  return $ ABCD_MEM (AR regN) (AR dn)
parseOpC dn 5 0 regN = do
  return $ EXG_D (DR dn) (DR regN)
parseOpC dn 5 1 regN = do
  return $ EXG_A (AR dn) (AR regN)
parseOpC _ 6 0 _ = do
  return ILLEGAL
parseOpC dn 6 1 regN = do
  return $ EXG_DA (DR dn) (AR regN)
parseOpC dn n regT regN
  | n < 3 = do
    ea <- parseEA regT regN (ImmInt <$> nextX (toEnum n))
    return $ AND (toEnum n) ea (DR dn)
  | otherwise = do
    ea <- parseEAMem regT regN
    return $ AND_TO_MEM (toEnum $ n - 4) (DR dn) ea

parseOpD dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ ADDA WORD ea (AR dn)
parseOpD dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $ ADDA LONG ea (AR dn)
parseOpD dn n regT regN
  | n < 3 = do
    ea <- parseEA regT regN (ImmInt <$> nextX (toEnum n))
    return $ ADD (toEnum n) ea (DR dn)
  | regT == 0 = do return $ ADDX_REG (toEnum $ n - 4) (DR regN) (DR dn)
  | regT == 1 = do return $ ADDX_MEM (toEnum $ n - 4) (AR regN) (AR dn)
  | otherwise = do
    ea <- parseEAMem regT regN
    return $ ADD_TO_MEM (toEnum $ n - 4) (DR dn) ea

parseShift dir t regT dn regN
  | regT == 0 || regT == 4 = do
    return $
      (if dir
         then ASR
         else ASL)
        t
        sc
        (DR regN)
  | regT == 1 || regT == 5 = do
    return $
      (if dir
         then LSR
         else LSL)
        t
        sc
        (DR regN)
  | regT == 2 || regT == 6 = do
    return $
      (if dir
         then ROXR
         else ROXL)
        t
        sc
        (DR regN)
  | otherwise = do
    return $
      (if dir
         then ROR
         else ROL)
        t
        sc
        (DR regN)
  where
    isReg = testBit regT 2
    sc =
      if isReg
        then BReg $ DR dn
        else if dn == 0
               then BImm 8
               else BImm dn

parseOpE 0 3 regT regN = ASR_EA <$> parseEAMem regT regN
parseOpE 1 3 regT regN = LSR_EA <$> parseEAMem regT regN
parseOpE 2 3 regT regN = ROXR_EA <$> parseEAMem regT regN
parseOpE 3 3 regT regN = ROR_EA <$> parseEAMem regT regN
parseOpE 0 7 regT regN = ASL_EA <$> parseEAMem regT regN
parseOpE 1 7 regT regN = LSL_EA <$> parseEAMem regT regN
parseOpE 2 7 regT regN = ROXL_EA <$> parseEAMem regT regN
parseOpE 3 7 regT regN = ROL_EA <$> parseEAMem regT regN
parseOpE dn 3 regT regN = do
  nw <- next16
  ea <- parseEA regT regN nothingT
  let off_i = getBit nw 6 31
      width_i = getBit nw 0 31
      off =
        if testBit nw 11
          then BReg $ DR off_i
          else BImm off_i
      width =
        if testBit nw 5
          then BReg $ DR width_i
          else BImm
                 (if width_i == 0
                    then 32
                    else width_i)
  return $
    (case dn of
       4 -> BFTST
       5 -> BFCHG
       6 -> BFCLR
       7 -> BFSET
       _ -> undefined)
      ea
      off
      width
parseOpE dn 7 regT regN = do
  nw <- next16
  ea <- parseEA regT regN nothingT
  let off_i = getBit nw 6 31
      width_i = getBit nw 0 31
      off =
        if testBit nw 11
          then BReg $ DR off_i
          else BImm off_i
      width =
        if testBit nw 5
          then BReg $ DR width_i
          else BImm
                 (if width_i == 0
                    then 32
                    else width_i)
      dm = DR $ getBit nw 12 7
  return $
    case dn of
      4 -> BFEXTU ea off width dm
      5 -> BFEXTS ea off width dm
      6 -> BFFFO ea off width dm
      7 -> BFINS dm ea off width
      _ -> undefined
parseOpE dn opi regT regN =
  parseShift (opi < 4) (toEnum $ opi `mod` 4) regT dn regN

next64 = do
  high <- next32
  low <- next32
  return $ high `shiftL` 32 .|. low

parseOpFPULoad rm regT regN fpm fpn opc = do
  let readFpuEA at@(FInt t) = do
        ea <- parseEA regT regN (ImmInt <$> nextX t)
        return (at, FpuOperandInt ea)
      readFpuEA x =
        if isSpecialEA regT regN
          then do
            v <-
              case x of
                FSINGLE -> do
                  imm <- next32
                  return . fromSingle . castWord32ToFloat $ fromIntegral imm
                FDOUBLE -> do
                  imm <- next64
                  return . fromDouble . castWord64ToDouble $ fromIntegral imm
                FEXT -> do
                  imm1 <- next32
                  frac <- next64
                  let e = imm1 `shiftR` 16
                  return . fromExtWord e $ fromIntegral frac
                FPACKED -> do
                  imm1 <- next32
                  frac <- next64
                  let e = imm1 `shiftR` 16
                  return . fromPacked e $ fromIntegral frac
            return (x, FpuImm v)
          else do
            ea <- parseEAMem regT regN
            return (x, FpuOperandFlt ea)
  (t, src) <-
    if rm
      then return (FEXT, FpuRn $ FPR fpm)
      else readFpuEA $ toAFType fpm
  return
    (if between opc 48 55
       then FSINCOS t src (FPR $ opc .&. 7) $ FPR fpn
       else if opc == 58
              then FTST t src
              else maybe
                     ILLEGAL
                     (\x -> FOp x t src $ FPR fpn)
                     (case opc of
                        0b0000000 -> Just "fmove"
                        0b0000001 -> Just "fint"
                        0b0000010 -> Just "fsinh"
                        0b0000011 -> Just "fintz"
                        0b0000100 -> Just "fsqrt"
                        0b0000110 -> Just "flognp1"
                        0b0001000 -> Just "fetoxm1"
                        0b0001001 -> Just "ftanh"
                        0b0001010 -> Just "fatan"
                        0b0001100 -> Just "fasin"
                        0b0001101 -> Just "fatanh"
                        0b0001110 -> Just "fsin"
                        0b0001111 -> Just "ftan"
                        0b0010000 -> Just "fetox"
                        0b0010001 -> Just "ftwotox"
                        0b0010010 -> Just "ftentox"
                        0b0010100 -> Just "flogn"
                        0b0010101 -> Just "flog10"
                        0b0010110 -> Just "flog2"
                        0b0011000 -> Just "fabs"
                        0b0011001 -> Just "fcosh"
                        0b0011010 -> Just "fneg"
                        0b0011100 -> Just "facos"
                        0b0011101 -> Just "fcos"
                        0b0011110 -> Just "fgetexp"
                        0b0011111 -> Just "fgetman"
                        0b0100000 -> Just "fdiv"
                        0b0100001 -> Just "fmod"
                        0b0100010 -> Just "fadd"
                        0b0100011 -> Just "fmul"
                        0b0100100 -> Just "fsgldiv"
                        0b0100101 -> Just "frem"
                        0b0100110 -> Just "fscale"
                        0b0100111 -> Just "fsglmul"
                        0b0101000 -> Just "fsum"
                        0b0111000 -> Just "fcmp"
                        0b1000000 -> Just "fsmove"
                        0b1000001 -> Just "fssqrt"
                        0b1000100 -> Just "fdmove"
                        0b1000101 -> Just "fdsqrt"
                        0b1011000 -> Just "fsabs"
                        0b1011010 -> Just "fsneg"
                        0b1011100 -> Just "fdabs"
                        0b1011110 -> Just "fdneg"
                        0b1100000 -> Just "fsdiv"
                        0b1100010 -> Just "fsadd"
                        0b1100011 -> Just "fsmul"
                        0b1100100 -> Just "fddiv"
                        0b1100110 -> Just "fdadd"
                        0b1100111 -> Just "fdmul"
                        0b1101000 -> Just "fssub"
                        0b1101100 -> Just "fdsub"
                        _         -> Nothing))

parseOpFPUStore regT regN 0 fpn _ = do
  ea <- parseEA regT regN nothingT
  return $ FMOVEStore (FInt LONG) (FPR fpn) (FpuOperandInt ea)
parseOpFPUStore regT regN 1 fpn _ = do
  ea <- parseEAMem regT regN
  return $ FMOVEStore FSINGLE (FPR fpn) (FpuOperandFlt ea)
parseOpFPUStore regT regN 2 fpn _ = do
  ea <- parseEAMem regT regN
  return $ FMOVEStore FEXT (FPR fpn) (FpuOperandFlt ea)
parseOpFPUStore regT regN 3 fpn k = do
  ea <- parseEAMem regT regN
  return $ FMOVEStoreP (FPR fpn) (FpuOperandFlt ea) $ BImm k
parseOpFPUStore regT regN 4 fpn _ = do
  ea <- parseEA regT regN nothingT
  return $ FMOVEStore (FInt WORD) (FPR fpn) (FpuOperandInt ea)
parseOpFPUStore regT regN 5 fpn _ = do
  ea <- parseEAMem regT regN
  return $ FMOVEStore FDOUBLE (FPR fpn) (FpuOperandFlt ea)
parseOpFPUStore regT regN 6 fpn _ = do
  ea <- parseEA regT regN nothingT
  return $ FMOVEStore (FInt BYTE) (FPR fpn) (FpuOperandInt ea)
parseOpFPUStore regT regN 7 fpn k = do
  ea <- parseEAMem regT regN
  return $ FMOVEStoreP (FPR fpn) (FpuOperandFlt ea) $ BReg $ DR k
parseOpFPUStore _ _ _ _ _ = nothingT

parseOpF10_0 regT regN fpm fpn opc
  | fpm /= 7 = parseOpFPULoad False regT regN fpm fpn opc
  | otherwise = nothingT

parseOpF10_2 _ _ 7 fpn opc = do
  return $ FMOVECR opc $ FPR fpn
parseOpF10_2 regT regN fpm fpn opc = parseOpFPULoad False regT regN fpm fpn opc

parseOpF10_3 ::
     (Eq a, Num a)
  => Int
  -> Int
  -> a
  -> Int
  -> Int
  -> MaybeT (State (Int, [Word8])) Op
parseOpF10_3 = parseOpFPUStore

parseOpF10_4_5 regT regN nw bit13 = do
  let cr = (["CR" | testBit nw 12])
      sr = (["SR" | testBit nw 11])
      ir = (["IR" | testBit nw 10])
  ea <- parseEAMem regT regN
  return $ FMOVECC bit13 (cr ++ sr ++ ir) ea

parseOpF10_6 regT regN nw = do
  ea <- parseEAMem regT regN
  if testBit nw 12
    then if testBit nw 11
           then let dn = getBit nw 4 7
                 in return $ FMOVEM_DYNAMIC False ea $ DR dn
           else let bits = getBit nw 0 0xff
                 in return $
                    FMOVEM_STATIC
                      False
                      ea
                      [FPR n | n <- [0 .. 7], testBit bits (7 - n)]
    else return ILLEGAL

parseOpF10_7 4 regN nw
  | testBit nw 12 = return ILLEGAL
  | otherwise = do
    ea <- parseEAMem 4 regN
    if testBit nw 11
      then let dn = getBit nw 4 7
            in return $ FMOVEM_DYNAMIC True ea $ DR dn
      else let bits = getBit nw 0 0xff
            in return $
               FMOVEM_STATIC True ea [FPR n | n <- reverse [0 .. 7], testBit bits n]
parseOpF10_7 regT regN nw
  | testBit nw 12 = do
    ea <- parseEAMem regT regN
    if testBit nw 11
      then let dn = getBit nw 4 7
            in return $ FMOVEM_DYNAMIC True ea $ DR dn
      else let bits = getBit nw 0 0xff
            in return $
               FMOVEM_STATIC False ea [FPR n | n <- [0 .. 7], testBit bits (7 - n)]
  | otherwise = return ILLEGAL

parseOpF10 regT regN = do
  nw <- next16
  let fpm = getBit nw 10 7
      fpn = getBit nw 7 7
      opc = getBit nw 0 0x7F
  case getBit nw 13 7 of
    0 -> parseOpF10_0 regT regN fpm fpn opc
    2 -> parseOpF10_2 regT regN fpm fpn opc
    3 -> parseOpFPUStore regT regN fpm fpn opc
    4 -> parseOpF10_4_5 regT regN nw False
    5 -> parseOpF10_4_5 regT regN nw True
    6 -> parseOpF10_6 regT regN nw
    7 -> parseOpF10_7 regT regN nw
    _ -> nothingT

parseOpF11 1 regN = do
  nw <- next16
  pc <- lift getPC
  disp <- next16
  return $ FDBcc (FCC $ getBit nw 0 0x3F) (DR regN) (disp + pc)
parseOpF11 7 2 = do
  nw <- next16
  FTRAPcc (FCC $ getBit nw 0 0x3F) <$> next16
parseOpF11 7 3 = do
  nw <- next16
  FTRAPcc (FCC $ getBit nw 0 0x3F) <$> next32
parseOpF11 7 4 = do
  nw <- next16
  return $ FTRAPcc (FCC $ getBit nw 0 0x3F) 0
parseOpF11 regT regN = do
  nw <- next16
  ea <- parseEA regT regN nothingT
  return $ FScc (FCC $ getBit nw 0 0x3F) ea

parseOpF12 0 = do
  return FNOP
parseOpF12 cc = do
  pc <- lift getPC
  offset <- next16
  return $ FBcc (FCC cc) (pc + offset)

parseOpF13 cc = do
  pc <- lift getPC
  offset <- next32
  return $ FBcc (FCC cc) (pc + offset)

parseOpF14 regT regN = do
  ea <- parseEAMem regT regN
  return $ FSAVE ea

parseOpF15 regT regN = do
  ea <- parseEAMem regT regN
  return $ FRESTORE ea

parseOpF2x 0 _ _ = return ILLEGAL
parseOpF2x 4 0 an = return $ PFLUSHN (AR an)
parseOpF2x 4 1 an = return $ PFLUSH (AR an)
parseOpF2x 4 2 _ = return PFLUSHAN
parseOpF2x 4 3 _ = return PFLUSHA
parseOpF2x 5 1 an = return $ PTESTW (AR an)
parseOpF2x 5 5 an = return $ PTESTW (AR an)
parseOpF2x c t an
  | t == 1 = return $ CINVL (target c) (AR an)
  | t == 2 = return $ CINVP (target c) (AR an)
  | t == 3 = return $ CINVA (target c)
  | t == 5 = return $ CPUSHL (target c) (AR an)
  | t == 6 = return $ CPUSHP (target c) (AR an)
  | t == 7 = return $ CPUSHA (target c)
  | otherwise = return ILLEGAL
  where
    target 1 = "DC"
    target 2 = "IC"
    target 3 = "BC"
    target _ = ""

parseOpF3x 0 ay = do
  MOVE16 True True (AR ay) <$> next32
parseOpF3x 1 ay = do
  MOVE16 False True (AR ay) <$> next32
parseOpF3x 2 ay = do
  MOVE16 True False (AR ay) <$> next32
parseOpF3x 3 ay = do
  MOVE16 False False (AR ay) <$> next32
parseOpF3x 4 ax = do
  nw <- next16
  let ay = AR $ getBit nw 12 7
  return $ MOVE16IncInc (AR ax) ay
parseOpF3x _ _ = return ILLEGAL

parseOpMain op
  | h == 0 = parseOp0 dn opi regT regN
  | h == 1 = parseOpMove BYTE opi dn regT regN
  | h == 2 = parseOpMove LONG opi dn regT regN
  | h == 3 = parseOpMove WORD opi dn regT regN
  | h == 4 = parseOp4 dn opi regT regN
  | h == 5 = parseOp5 dn opi regT regN
  | h == 6 = parseOp6 op
  | h == 7 =
    let imm = toS8 $ getBit op 0 0xff
     in return $ MOVEQ imm (DR dn)
  | h == 8 = parseOp8 dn opi regT regN
  | h == 9 = parseOp9 dn opi regT regN
  | h == 10 = return $ SYS op
  | h == 11 = parseOpB dn opi regT regN
  | h == 12 = parseOpC dn opi regT regN
  | h == 13 = parseOpD dn opi regT regN
  | h == 14 = parseOpE dn opi regT regN
  | h == 15 && dn == 1 && opi == 0 = parseOpF10 regT regN
  | h == 15 && dn == 1 && opi == 1 = parseOpF11 regT regN
  | h == 15 && dn == 1 && opi == 2 = parseOpF12 $ getBit op 0 0x1F
  | h == 15 && dn == 1 && opi == 3 = parseOpF13 $ getBit op 0 0x1F
  | h == 15 && dn == 1 && opi == 4 = parseOpF14 regT regN
  | h == 15 && dn == 1 && opi == 5 = parseOpF15 regT regN
  | h == 15 && dn == 2 = parseOpF2x opi regT regN
  | h == 15 && dn == 3 && opi == 0 = parseOpF3x regT regN
  | otherwise = return ILLEGAL
  where
    h = getBit op 12 15
    dn = getBit op 9 7
    opi = getBit op 6 7
    regT = getBit op 3 7
    regN = getBit op 0 7

parseOp :: Int -> [Word8] -> (Int, Op, Int)
parseOp pc opsv =
  let (o, (next, _)) =
        runState
          (runMaybeT $ do
             op <- next16
             parseOpMain op)
          (pc, drop pc opsv)
   in (pc, fromMaybe ILLEGAL o, next)
