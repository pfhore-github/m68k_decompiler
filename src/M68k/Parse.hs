{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE BinaryLiterals #-}
module M68k.Parse where

import           Control.Monad.State
import           Data.Bits           (Bits (shiftL, shiftR, testBit, (.&.), (.|.)))
import           Data.Maybe
import           Data.Word
import Text.Printf
import Control.Monad.Trans.Maybe
import GHC.Float (castWord32ToFloat, castWord64ToDouble)
import M68k.LongDouble
import Util

data AType
  = BYTE
  | WORD
  | LONG
  deriving (Eq)
instance Show AType where
  show BYTE = "B"
  show WORD = "W"
  show LONG = "L"

instance PrintfArg AType where
  formatArg x = formatString (show x)

data AddrBase
  = BaseAR Int
  | BasePC Int -- value is actually (PCBase + addr)
  | BaseNone
  deriving (Eq)

data Operand
  = DR Int
  | AR Int
  | Address MemOperand
  | ImmInt Int
  | CCR
  | SR
  | SpRG [Char]
  deriving (Eq)

instance Show Operand where
  show (DR n) = printf "%%D%d" n
  show (AR n) = printf "%%A%d" n
  show (ImmInt x) = printf "#%d" x
  show CCR = "%CCR"
  show SR = "%SR"
  show (SpRG s) = printf "%%%s" s
  show (Address x) = show x

instance PrintfArg Operand where
  formatArg x = formatArg (show x)

data MemOperand
  = UnRefAR Int
  | UnRefInc Int
  | UnRefDec Int
  | Offset16 Int AddrBase
  | Offset8 Int AddrBase Bool Int Int
  | Indirect Int AddrBase Bool (Maybe Int) Int
  | PreIndex Int AddrBase Bool (Maybe Int) Int Int
  | PostIndex Int AddrBase Bool (Maybe Int) Int Int
  | ImmAddr Int
  deriving (Eq)

base2Str :: Int -> AddrBase -> String
base2Str d (BasePC pc) = printf "0x%05X, %%PC" (d + pc)
base2Str d BaseNone = printf "0x%05X" d
base2Str d (BaseAR n) = printf "%d, %%A%d" d n

rn2Str :: Int -> String
rn2Str n
  | n < 8 = printf "%%D%d" n
  | otherwise = printf "%%A%d" (n-8)

toScale :: Int -> Bool -> Int -> String
toScale rn w = printf "%s%s << %d" (rn2Str rn) (if w then ".W" else "")

indexStr :: Bool -> Maybe Int -> Bool -> Int -> String
indexStr _ Nothing _ _ = ""
indexStr True (Just rn) w cc = ", " ++ toScale rn w cc
indexStr False (Just rn) w cc = toScale rn w cc ++ ", "

instance Show MemOperand where
  show (UnRefAR a) = printf "(%%A%d)" a
  show (UnRefInc a) = printf "(%%A%d)+" a
  show (UnRefDec a) = printf "-(%%A%d)" a
  show (Offset16 a base) = printf "(%s)" ( base2Str a base)
  show (Offset8 bd base w rn cc) =
    printf "(%s, %s)" (base2Str bd base) $ toScale rn w cc
  show (Indirect bd base w rnp cc) =
    printf "(%s%s)" (base2Str bd base) (indexStr True rnp w cc)
  show (PreIndex bd base w rnp cc od) =
    printf "([%s%s], %d)" (base2Str bd base) (indexStr True rnp w cc) od
  show (PostIndex bd base w rnp cc od) =
    printf "([%s], %s%d)" (base2Str bd base) (indexStr False rnp w cc) od
  show (ImmAddr x) = printf "0x%05X" x

instance PrintfArg MemOperand where
  formatArg x = formatArg (show x)


getRn :: Int -> Operand
getRn d =
  if d > 7
    then AR (d - 8)
    else DR d

data BopSc
  = BImm Int
  | BReg Int
  deriving (Eq)
instance Show BopSc where
  show (BImm n) = printf "#%d" n
  show (BReg n) = printf "%%D%d" n

instance PrintfArg BopSc where
  formatArg x = formatString (show x)

data AFType = FInt AType | FSINGLE | FDOUBLE | FEXT | FPACKED
  deriving (Show, Eq)

instance PrintfArg AFType where
  formatArg x = formatString (
    case x of
      FInt t ->  printf "%v" t
      FSINGLE -> "S"
      FDOUBLE -> "D"
      FEXT -> "X"
      FPACKED -> "P"
     )

nothingT :: MaybeT (State (Int, [Word8])) a
nothingT = mzero

toAFType :: Int -> AFType
toAFType n = case n of
  0 -> FInt LONG
  1 -> FSINGLE
  2 -> FEXT
  3 -> FPACKED
  4 -> FInt WORD
  5 -> FDOUBLE
  6 -> FInt BYTE
  7 -> FPACKED
  _ -> undefined

data FpuOperand =
  FpuRn Int |
  FpuOperandInt Operand |
  FpuOperandFlt MemOperand |
  FpuImm LongDouble
  deriving (Eq)

instance Show FpuOperand where
  show (FpuRn n) = printf "%%FP%d" n
  show (FpuOperandInt t) = show t
  show (FpuOperandFlt t) = show t
  show (FpuImm d) = show d
instance PrintfArg FpuOperand where
  formatArg x = formatArg (show x)

data Op
  = ILLEGAL
  | ORI AType Operand Int
  | ANDI AType Operand Int
  | SUBI AType Operand Int
  | ADDI AType Operand Int
  | EORI AType Operand Int
  | CMPI AType Operand Int
  | BTST AType Operand BopSc
  | BCHG AType Operand BopSc
  | BCLR AType Operand BopSc
  | BSET AType Operand BopSc
  | CMP2 AType MemOperand Int
  | CHK2 AType MemOperand Int
  | CAS AType Int Int MemOperand
  | CAS2 AType Int Int Int Int Int Int
  | MOVES AType Bool MemOperand Int
  | MOVEP AType Bool Int Int Int
  | MOVE AType Operand Operand
  | MOVEA AType Operand Int
  | NEGX AType Operand
  | CLR AType Operand
  | NEG AType Operand
  | NOT AType Operand
  | TST AType Operand
  | NBCD AType Operand
  | TAS AType Operand
  | MULUL Operand Int
  | MULSL Operand Int
  | MULULL Operand Int Int
  | MULSLL Operand Int Int
  | DIVUL Operand Int Int
  | DIVSL Operand Int Int
  | DIVULL Operand Int Int
  | DIVSLL Operand Int Int
  | SWAP Int
  | TRAPn Int
  | LINK Int Int
  | UNLK Int
  | RESET
  | NOP
  | STOP Int
  | RTE
  | RTD Int
  | RTS
  | TRAPV
  | RTR
  | BKPT Int
  | PEA MemOperand
  | EXT AType Int
  | EXTB Int
  | MOVEM AType Bool MemOperand [Int]
  | JSR MemOperand
  | JMP MemOperand
  | CHK AType Operand Int
  | LEA MemOperand Int
  | MOVEC Bool Int String
  | ADDQ AType Int Operand
  | SUBQ AType Int Operand
  | TRAPcc Int (Maybe Int)
  | Scc Int Operand
  | DBcc Int Int Int
  | BRA Int
  | BSR Int
  | Bcc Int Int
  | MOVEQ Int Int
  | OR AType Operand Int
  | OR_TO_MEM AType Int MemOperand
  | DIVUW Operand Int
  | SBCD_REG Int Int
  | SBCD_MEM Int Int
  | PACK_REG Int Int Int
  | PACK_MEM Int Int Int
  | UNPK_REG Int Int Int
  | UNPK_MEM Int Int Int
  | DIVSW Operand Int
  | SUB AType Operand Int
  | SUB_TO_MEM AType Int MemOperand
  | SUBA AType Operand Int
  | SUBX_REG AType Int Int
  | SUBX_MEM AType Int Int
  | CMP AType Operand Int
  | CMPA AType Operand Int
  | CMPM AType Int Int
  | EOR AType Int Operand
  | AND AType Operand Int
  | AND_TO_MEM AType Int MemOperand
  | MULUW Operand Int
  | ABCD_REG Int Int
  | ABCD_MEM Int Int
  | EXG_D Int Int
  | EXG_A Int Int
  | EXG_DA Int Int
  | MULSW Operand Int
  | SYS Int
  | ADD AType Operand Int
  | ADD_TO_MEM AType Int MemOperand
  | ADDA AType Operand Int
  | ADDX_REG AType Int Int
  | ADDX_MEM AType Int Int
  | ASR AType Bool Int Int
  | ASL AType Bool Int Int
  | LSR AType Bool Int Int
  | LSL AType Bool Int Int
  | ROXR AType Bool Int Int
  | ROXL AType Bool Int Int
  | ROR AType Bool Int Int
  | ROL AType Bool Int Int
  | ASR_EA MemOperand
  | ASL_EA MemOperand
  | LSR_EA MemOperand
  | LSL_EA MemOperand
  | ROXR_EA MemOperand
  | ROXL_EA MemOperand
  | ROR_EA MemOperand
  | ROL_EA MemOperand
  | BFTST Operand BopSc BopSc
  | BFCHG Operand BopSc BopSc
  | BFCLR Operand BopSc BopSc
  | BFSET Operand BopSc BopSc
  | BFEXTU Operand BopSc BopSc Int
  | BFEXTS Operand BopSc BopSc Int
  | BFFFO Operand BopSc BopSc Int
  | BFINS Int Operand BopSc BopSc
  | FOp String AFType FpuOperand Int
  | FSINCOS AFType FpuOperand Int Int
  | FTST AFType FpuOperand
  | FMOVECR Int Int
  | FMOVEStore AFType Int FpuOperand
  | FMOVEP Int FpuOperand Bool Int
  | FMOVECC Bool [String] MemOperand
  | FMOVEMS Bool MemOperand [Int]
  | FMOVEMD Bool MemOperand Int
  | FScc Int Operand
  | FDBcc Int Int Int
  | FTRAPcc Int Int
  | FNOP
  | FBcc Int Int
  | FSAVE MemOperand
  | FRESTORE MemOperand
  | CINVL String Int
  | CINVP String Int
  | CINVA String
  | CPUSHL String Int
  | CPUSHP String Int
  | CPUSHA String
  | PFLUSHN Int
  | PFLUSH Int
  | PFLUSHAN
  | PFLUSHA
  | PTESTW Int
  | PTESTR Int
  | MOVE16 Bool Bool Int Int
  | MOVE16IncInc Int Int
  deriving (Show, Eq)

getPC :: State (Int, [Word8]) Int
getPC = state (\(s, p) -> (s, (s, p)))

next8 :: MaybeT (State (Int, [Word8])) Int
next8 = do
  (s, x) <- get
  if null x
    then
      MaybeT $ do return Nothing
    else do
      put (s+1, tail x)
      return (fromIntegral $ head x :: Int)

next16 =
  let
  in do
      high <- next8
      low <- next8
      return $ high `shiftL` 8 .|. low

next32 = do
  high <- next16
  low <- next16
  return $ high `shiftL` 16 .|. low

nextX t = if t == LONG then next32 else next16

parseEaEx :: Int -> AddrBase -> MaybeT (State (Int, [Word8])) MemOperand
parseEaEx nw base
  | not ( testBit nw 8) = do return $ Offset8 (toS8 (getBit nw 0 0xff)) base ext index cc
  | testBit nw 3 = nothingT
  | getBit nw 6 3 == 3 = nothingT
  | od_i == 0 && isPost = nothingT
  | otherwise = do
      bd <-
        case getBit nw 4 3 of
          1 -> return 0
          2 -> next16
          3 -> next32
          _ -> nothingT
      od <-
        case od_i of
          2 -> next16
          3 -> next32
          _ -> return 0
      return $ if od_i == 0
        then Indirect bd base_p ext index_p cc
        else (if isPost
               then PostIndex
               else PreIndex )
             bd base_p ext index_p cc od
        where index = getBit nw 12 15
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


parseEA :: Int -> Int -> MaybeT (State (Int, [Word8])) Operand
  -> MaybeT (State (Int, [Word8])) Operand
parseEA 0 regN _ = do
  return $ DR regN
parseEA 1 regN _ = do
  return $ AR regN
parseEA 7 4 other = other
parseEA n r _ = do
  mem <- parseEAMem n r
  return $ Address mem


parseEAMem :: Int -> Int -> MaybeT (State (Int, [Word8])) MemOperand
parseEAMem 2 regN = do
  return $ UnRefAR regN
parseEAMem 3 regN = do
  return $ UnRefInc regN
parseEAMem 4 regN = do
  return $ UnRefDec regN
parseEAMem 5 regN = do
  nw <- next16
  return $ Offset16 (toS16 nw) $ BaseAR regN
parseEAMem 6 regN = do
  nw <- next16
  parseEaEx nw (BaseAR regN)
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
  let rn = getBit nw 12 15
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
  let rn = getBit nw 12 15
  return $ op t ea rn

parseBitTestCommon :: Int -> Int -> (AType -> Operand -> t -> b) -> t -> MaybeT (State (Int, [Word8])) b
parseBitTestCommon regT regN op_c pos = do
  let t =
        if regT == 0
          then LONG
          else BYTE
  op <- parseEA regT regN (ImmInt <$> next16 )
  return $ op_c t op pos

parseBitTest :: Int -> Int -> (AType -> Operand -> BopSc -> b) -> MaybeT (State (Int, [Word8])) b
parseBitTest regT regN op_c = do
  x <- next16
  parseBitTestCommon regT regN op_c $ BImm (if x == 0 then 8 else x)

parseBitTest2 :: Int -> Int -> (AType -> Operand -> BopSc -> b) -> Int -> MaybeT (State (Int, [Word8])) b
parseBitTest2 regT regN op_c dn = parseBitTestCommon regT regN op_c (BReg dn)

parseMoveP :: AType -> Int -> Int -> Bool -> MaybeT (State (Int, [Word8])) Op
parseMoveP t dn regN toMem = do
  imm <- next16
  return $ MOVEP t toMem regN imm dn

parseCas t regT regN = do
  nw <- next16
  let dc = getBit nw 0 7
      du = getBit nw 6 7
   in if isSpecialEA regT regN
        then do
          extw <- next16
          let rn1 = getBit nw 12 15
              dc2 = getBit extw 0 7
              du2 = getBit extw 6 7
              rn2 = getBit extw 12 15
          return $ CAS2 t dc dc2 du du2 rn1 rn2
        else do
          ea <- parseEAMem regT regN
          return $ CAS t dc du ea

doOp2 f t dstM immM = do
  o <- immM
  dst <- dstM
  return $ f t dst o

toAType :: (Eq a, Num a) => a -> AType
toAType 0 = BYTE
toAType 1 = WORD
toAType 2 = LONG
toAType _ = undefined

toBitOp :: (Eq a, Num a) => a -> AType -> Operand -> BopSc -> Op
toBitOp 0 = BTST
toBitOp 1 = BCHG
toBitOp 2 = BCLR
toBitOp 3 = BSET
toBitOp _ = undefined

parseOp0 :: Int -> Int -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp0 dni opi regT regN
  | opi < 3 = do
    let t = toAType opi
        bitOp = toBitOp opi
        ea = parseEA regT regN nothingT
        dst = parseEA regT regN (case opi of
                                   0 -> return CCR
                                   1 -> return SR
                                   _ -> nothingT
                                )
              
        src = parseEA regT regN ( ImmInt <$> nextX t )
     in case dni of
          0 -> doOp2 ORI t dst $ nextX t
          1 -> doOp2 ANDI t dst $ nextX t
          2 -> doOp2 SUBI t ea $ nextX t
          3 -> doOp2 ADDI t ea  $ nextX t
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
        | dni < 3 -> parseOpCmp2 (toAType dni) regT regN
        | otherwise -> parseCas (toAType $ dni - 5) regT regN
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

parseOpMove :: AType -> Int -> Int -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOpMove t dstT dstN srcT srcN = do
  srcEA <- parseEA srcT srcN ( ImmInt <$> ( if t == LONG then next32 else next16 ) )
  dstEA <- parseEA dstT dstN nothingT
  return $
    if dstT == 1
      then MOVEA t srcEA dstN
      else MOVE t srcEA dstEA

parseOpV1 :: t -> (t -> Operand -> b) -> MaybeT (State (Int, [Word8])) Operand -> Int -> Int -> MaybeT (State (Int, [Word8])) b
parseOpV1 t opc e regT regN = opc t <$> parseEA regT regN e

movecName :: (Eq a, Num a) => a -> String
movecName x
  | x == 0 = "SFC"
  | x == 1 = "DFC"
  | x == 2 = "CACR"
  | x == 3 = "TC"
  | x == 4 = "ITT0"
  | x == 5 = "ITT1"
  | x == 6 = "DTT0"
  | x == 7 = "DTT1"
  | x == 0x800 = "USP"
  | x == 0x801 = "VBR"
  | x == 0x803 = "MSP"
  | x == 0x804 = "ISP"
  | x == 0x805 = "MMUSR"
  | x == 0x806 = "URP"
  | x == 0x807 = "SRP"
  | otherwise = "???"

parseOp40 :: (Eq a, Num a) => a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp40 0 = parseOpV1 BYTE NEGX nothingT
parseOp40 1 = parseOpV1 BYTE CLR nothingT
parseOp40 2 = parseOpV1 BYTE NEG nothingT
parseOp40 3 = parseOpV1 BYTE NOT nothingT
parseOp40 4 =
  \regT regN ->
    (if regT == 1
       then LINK regN <$> next32
       else parseOpV1 BYTE NBCD nothingT regT regN)
parseOp40 5 = parseOpV1 BYTE TST $ ImmInt <$> next16
parseOp40 6 = parseMul
parseOp40 _ = undefined

parseOp41 :: (Eq a, Num a) => a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp41 0 = parseOpV1 WORD NEGX nothingT
parseOp41 1 = parseOpV1 WORD CLR nothingT
parseOp41 2 = parseOpV1 WORD NEG nothingT
parseOp41 3 = parseOpV1 WORD NOT nothingT
parseOp41 4 =
  \regT regN ->
    (case regT of
       0 -> return $ SWAP regN
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
      dl = getBit nw 12 7
      dh = getBit nw 0 7
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
      dq = getBit nw 12 7
      dr = getBit nw 0 7
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
      dr
      dq

parse0471 :: (Eq a, Num a) => a -> Int -> MaybeT (State (Int, [Word8])) Op
parse0471 0 regN = do
  return $ TRAPn regN
parse0471 1 regN = do
  return $ TRAPn $ 8 + regN
parse0471 2 regN = LINK regN <$> next16
parse0471 3 regN = do
  return $ UNLK regN
parse0471 4 regN = do
  return $ MOVE LONG (AR regN) (SpRG "USR")
parse0471 5 regN = do
  return $ MOVE LONG (SpRG "USR") (AR regN)
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
  let rn = getBit nw 12 15
      cc = getBit nw 0 0xFFF
  return $
    case regN of
      2 -> MOVEC False rn $ movecName cc
      3 -> MOVEC True rn  $ movecName cc
      _ -> ILLEGAL
parse0471 _ _ = undefined

parseOp42 :: (Eq a, Num a) => a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp42 0 = parseOpV1 LONG NEGX nothingT
parseOp42 1 = parseOpV1 LONG CLR nothingT
parseOp42 2 = parseOpV1 LONG NEG nothingT
parseOp42 3 = parseOpV1 LONG NOT nothingT
parseOp42 4 =
  \regT regN ->
    (if regT == 0
       then return $ EXT WORD regN
       else do
         imm <- next16
         ea <- parseEAMem regT regN
         return $ MOVEM WORD True ea [x | x <- [0 .. 15], testBit imm x])
parseOp42 5 = parseOpV1 LONG TST $ ImmInt <$> next32
parseOp42 6 =
  \regT regN ->
    (do imm <- next16
        ea <- parseEAMem regT regN
        return $ MOVEM WORD False ea [x | x <- [0 .. 15], testBit imm x])
parseOp42 7 =
  \regT regN ->
    (do ea <- parseEAMem regT regN
        return $ JSR ea)
parseOp42 _ = undefined

parseOp43 :: (Eq a, Num a) => a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOp43 4 0 regN = return $ EXT LONG regN
parseOp43 4 regT regN= do
          imm <- next16
          ea <- parseEAMem regT regN
          return $ MOVEM LONG True ea [x | x <- [0 .. 15], testBit imm x]

parseOp43 5 regT regN = parseOpV1 BYTE TAS nothingT regT regN

parseOp43 6 regT regN = do
  imm <- next16
  ea <- parseEAMem regT regN
  return $ MOVEM LONG False ea [x | x <- [0 .. 15], testBit imm x]

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
  ea <- parseEA regT regN nothingT
  return $ CHK t ea dni

parseOp4 :: (Eq a, Num a) => Int -> a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
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
      then return $ EXTB regN
      else do
        ea <- parseEAMem regT regN
        return $ LEA ea dni
parseOp4 _ _ = undefined

parseOp5 dni opi regT regN
  | opi == 3 || opi == 7 =
    let cc =
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
            return $ DBcc cc regN target
          _ -> Scc cc <$> ea
  | opi < 3 = ADDQ (toAType opi) immi <$> parseEA regT regN nothingT
  | otherwise = SUBQ (toAType $ opi - 4) immi <$> parseEA regT regN nothingT
  where immi = if dni == 0 then 8 else dni

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
      _ -> Bcc cc target

parseOp8 dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $ DIVUW ea dn
parseOp8 dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $ DIVUW ea dn
parseOp8 dn 4 0 regN = do
  return $ SBCD_REG dn regN
parseOp8 dn 4 1 regN = do
  return $ SBCD_MEM dn regN
parseOp8 dn 5 0 regN = PACK_REG regN dn <$> next16
parseOp8 dn 5 1 regN = PACK_MEM regN dn <$> next16
parseOp8 dn 6 0 regN = UNPK_REG regN dn <$> next16
parseOp8 dn 6 1 regN = UNPK_MEM regN dn <$> next16
parseOp8 dn n regT regN
  | n < 3 = do
      ea <- parseEA regT regN (ImmInt <$> nextX (toAType n))
      return $ OR (toAType n) ea dn
  | otherwise = do
      ea <- parseEAMem regT regN
      return $ OR_TO_MEM (toAType n) dn ea

parseOp9 dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ SUBA WORD ea dn
parseOp9 dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $ SUBA LONG ea dn
parseOp9 dn n 0 regN = do
  return $ SUBX_REG (toAType $ n - 4) dn regN
parseOp9 dn n 1 regN = do
  return $ SUBX_MEM (toAType $ n - 4) dn regN
parseOp9 dn n regT regN
  | n < 3 = do
      ea <- parseEA regT regN (ImmInt <$> nextX (toAType n))
      return $ SUB (toAType n) ea dn
  | otherwise = do
      ea <- parseEAMem regT regN
      return $ SUB_TO_MEM (toAType $ n - 4) dn ea

parseOpB dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ CMPA WORD ea dn
parseOpB dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $ CMPA LONG ea dn
parseOpB dn n regT regN
  | n < 3 = do
    ea <- parseEA regT regN  (ImmInt <$> nextX (toAType n))
    return $ CMP (toAType n) ea dn
  | otherwise = do
    if regT == 1
      then return $ CMPM (toAType $ n - 4) regN dn
      else do
        ea <- parseEA regT regN nothingT
        return $ EOR (toAType $ n - 4) dn ea

parseOpC dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ MULUW ea dn
parseOpC dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ MULSW ea dn
parseOpC dn 4 0 regN = do
  return $ ABCD_REG regN dn
parseOpC dn 4 1 regN = do
  return $ ABCD_MEM regN dn
parseOpC dn 5 0 regN = do
  return $ EXG_D dn regN
parseOpC dn 5 1 regN = do
  return $ EXG_A dn regN
parseOpC _ 6 0 _ = do
  return ILLEGAL
parseOpC dn 6 1 regN = do
  return $ EXG_DA dn regN
parseOpC dn n regT regN
  | n < 3 = do
    ea <- parseEA regT regN (ImmInt <$> nextX (toAType n))
    return $ AND (toAType n) ea dn
  | otherwise = do
    ea <- parseEAMem regT regN
    return $ AND_TO_MEM (toAType $ n - 4) dn ea

parseOpD dn 3 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next16)
  return $ ADDA WORD ea dn
parseOpD dn 7 regT regN = do
  ea <- parseEA regT regN (ImmInt <$> next32)
  return $ ADDA LONG ea dn
parseOpD dn n 0 regN
  | n >= 4 = do return $ ADDX_REG (toAType $ n - 4) regN dn
parseOpD dn n 1 regN
  | n >= 4 = do return $ ADDX_MEM (toAType $ n - 4) regN dn
parseOpD dn n regT regN
  | n < 3 = do
      ea <- parseEA regT regN (ImmInt <$> nextX (toAType n))
      return $ ADD (toAType n) ea dn
  | otherwise = do
      ea <- parseEAMem regT regN
      return $ ADD_TO_MEM (toAType $ n - 4) dn ea

parseShift dir t regT dn regN
  | regT == 0 || regT == 4 = do
    return $
      (if dir
         then ASR
         else ASL)
        t
        (testBit regT 2)
        dn
        regN
  | regT == 1 || regT == 5 = do
    return $
      (if dir
         then LSR
         else LSL)
        t
        (testBit regT 2)
        dn
        regN
  | regT == 2 || regT == 6 = do
    return $
      (if dir
         then ROXR
         else ROXL)
        t
        (testBit regT 2)
        dn
        regN
  | otherwise = do
    return $
      (if dir
         then ROR
         else ROL)
        t
        (testBit regT 2)
        dn
        regN

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
          then BReg off_i
          else BImm off_i
      width =
        if testBit nw 5
          then BReg width_i
          else BImm width_i
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
          then BReg off_i
          else BImm off_i
      width =
        if testBit nw 5
          then BReg width_i
          else BImm width_i
      dm = getBit nw 12 7
  return $
    case dn of
      4 -> BFEXTU ea off width dm
      5 -> BFEXTS ea off width dm
      6 -> BFFFO ea off width dm
      7 -> BFINS dm ea off width
      _ -> undefined
parseOpE dn opi regT regN =
  parseShift (opi < 4) (toAType $ opi `mod` 4) regT dn regN

next64 = do
  high <- next32
  low <- next32
  return $ high `shiftL` 32 .|. low

parseOpFPULoad rm regT regN fpm fpn opc = do
  let readFpuEA at@(FInt t) = do
        ea <- parseEA regT regN (ImmInt <$> nextX t)
        return (at, FpuOperandInt ea)
      readFpuEA x =
        if isSpecialEA regT regN then
         do
           v <- case x of
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
  (t, src) <- if rm then
                return (FEXT, FpuRn fpm)
              else
                readFpuEA $ toAFType fpm
  return (
    if between opc 48 55 then
      FSINCOS t src (opc .&. 7) fpn
    else if opc == 58 then
      FTST t src
    else maybe ILLEGAL (\x -> FOp x t src fpn)
         ( case opc of
             0b0000000 -> Just "FMOVE"
             0b0000001 -> Just "FINT"
             0b0000010 -> Just "FSINH"
             0b0000011 -> Just "FINTZ"
             0b0000100 -> Just "FSQRT"
             0b0000110 -> Just "FLOGNP1"
             0b0001000 -> Just "FETOXM1"
             0b0001001 -> Just "FTANH"
             0b0001010 -> Just "FATAN"
             0b0001100 -> Just "FASIN"
             0b0001101 -> Just "FATANH"
             0b0001110 -> Just "FSIN"
             0b0001111 -> Just "FTAN"
             0b0010000 -> Just "FETOX"
             0b0010001 -> Just "FTWOTOX"
             0b0010010 -> Just "FTENTOX"
             0b0010100 -> Just "FLOGN"
             0b0010101 -> Just "FLOG10"
             0b0010110 -> Just "FLOG2"
             0b0011000 -> Just "FABS"
             0b0011001 -> Just "FCOSH"
             0b0011010 -> Just "FNEG"
             0b0011100 -> Just "FACOS"
             0b0011101 -> Just "FCOS"
             0b0011110 -> Just "FGETEXP"
             0b0011111 -> Just "FGETMAN"
             0b0100000 -> Just "FDIV"
             0b0100001 -> Just "FMOD"
             0b0100010 -> Just "FADD"
             0b0100011 -> Just "FMUL"
             0b0100100 -> Just "FSGLDIV"
             0b0100101 -> Just "FREM"
             0b0100110 -> Just "FSCALE"
             0b0100111 -> Just "FSGLMUL"
             0b0101000 -> Just "FSUB"
             0b0111000 -> Just "FCMP"
             0b1000000 -> Just "FSMOVE"
             0b1000001 -> Just "FSSQRT"
             0b1000100 -> Just "FDMOVE"
             0b1000101 -> Just "FDSQRT"
             0b1011000 -> Just "FSABS"
             0b1011010 -> Just "FSNEG"
             0b1011100 -> Just "FDABS"
             0b1011110 -> Just "FDNEG"
             0b1100000 -> Just "FSDIV"
             0b1100010 -> Just "FSADD"
             0b1100011 -> Just "FSMUL"
             0b1100100 -> Just "FDDIV"
             0b1100110 -> Just "FDADD"
             0b1100111 -> Just "FDMUL"
             0b1101000 -> Just "FSSUB"
             0b1101100 -> Just "FDSUB"
             _ -> Nothing
         )
    )

parseOpFPUStore regT regN 0 fpn _ = do
  ea <- parseEA regT regN nothingT
  return $ FMOVEStore (FInt LONG) fpn (FpuOperandInt ea)
parseOpFPUStore regT regN 1 fpn _ = do
  ea <- parseEAMem regT regN
  return $ FMOVEStore FSINGLE fpn (FpuOperandFlt ea)
parseOpFPUStore regT regN 2 fpn _ = do
  ea <- parseEAMem regT regN
  return $ FMOVEStore FEXT fpn (FpuOperandFlt ea)
parseOpFPUStore regT regN 3 fpn k = do
  ea <- parseEAMem regT regN
  return $ FMOVEP fpn (FpuOperandFlt ea) False k
parseOpFPUStore regT regN 4 fpn _ = do
  ea <- parseEA regT regN nothingT
  return $ FMOVEStore (FInt WORD) fpn (FpuOperandInt ea)
parseOpFPUStore regT regN 5 fpn _ = do
  ea <- parseEAMem regT regN
  return $ FMOVEStore FDOUBLE fpn (FpuOperandFlt ea)
parseOpFPUStore regT regN 6 fpn _ = do
  ea <- parseEA regT regN nothingT
  return $ FMOVEStore (FInt BYTE) fpn (FpuOperandInt ea)
parseOpFPUStore regT regN 7 fpn k = do
  ea <- parseEAMem regT regN
  return $ FMOVEP fpn (FpuOperandFlt ea) True k
parseOpFPUStore _ _ _ _ _ = nothingT

parseOpF10_0 regT regN fpm fpn opc
  | fpm /= 7 = parseOpFPULoad False regT regN fpm fpn opc
  | otherwise = nothingT
parseOpF10_2 _ _ 7 fpn opc = do return $ FMOVECR opc fpn
parseOpF10_2 regT regN fpm fpn opc = parseOpFPULoad False regT regN fpm fpn opc

parseOpF10_3 :: (Eq a, Num a) => Int -> Int -> a -> Int -> Int -> MaybeT (State (Int, [Word8])) Op
parseOpF10_3 = parseOpFPUStore

parseOpF10_4_5 regT regN nw bit13 = do
  let cr = (["CR" | testBit nw 12])
      sr = (["SR" | testBit nw 11])
      ir = (["IR" | testBit nw 10])
  ea <- parseEAMem regT regN
  return $ FMOVECC bit13 (cr ++ sr ++ ir) ea

parseOpF10_6 regT regN nw = do
  ea <- parseEAMem regT regN
  if testBit nw 12 then
    if testBit nw 11 then
      let dn = getBit nw 4 7
      in return $ FMOVEMD False ea dn
    else
      let bits = getBit nw 0 0xff
      in return $ FMOVEMS False ea [n | n <- [0..7], testBit bits (7-n)]
  else
    return ILLEGAL

parseOpF10_7 4 regN nw
  | testBit nw 12 = return ILLEGAL
  | otherwise = do
      ea <- parseEAMem 4 regN
      if testBit nw 11
        then let dn = getBit nw 4 7
             in return $ FMOVEMD True ea dn
        else let bits = getBit nw 0 0xff
             in return $ FMOVEMS True ea
                [n | n <- reverse [0..7], testBit bits n]
parseOpF10_7 regT regN nw
  | testBit nw 12 = do
      ea <- parseEAMem regT regN
      if testBit nw 11
        then let dn = getBit nw 4 7
             in return $ FMOVEMD True ea dn
        else let bits = getBit nw 0 0xff
             in return $ FMOVEMS False ea
                [n | n <- [0..7], testBit bits (7-n)]
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
  return $ FDBcc (getBit nw 0 0x3F) regN (disp + pc)

parseOpF11 7 2 = do
  nw <- next16
  FTRAPcc  (getBit nw 0 0x3F) <$> next16

parseOpF11 7 3 = do
  nw <- next16
  FTRAPcc  (getBit nw 0 0x3F) <$> next32

parseOpF11 7 4 = do
  nw <- next16
  return $ FTRAPcc  (getBit nw 0 0x3F) 0

parseOpF11 regT regN = do
  nw <- next16
  ea <- parseEA regT regN nothingT
  return $ FScc (getBit nw 0 0x3F) ea

parseOpF12 0 = do return FNOP
parseOpF12 cc = do
  pc <- lift getPC
  offset <- next16
  return $ FBcc cc (pc+offset)

parseOpF13 cc = do
  pc <- lift getPC
  offset <- next32
  return $ FBcc cc (pc+offset)

parseOpF14 regT regN = do
  ea <- parseEAMem regT regN
  return $ FSAVE ea

parseOpF15 regT regN = do
  ea <- parseEAMem regT regN
  return $ FRESTORE ea


parseOpF2x 0 _ _ = return ILLEGAL
parseOpF2x 4 0 an = return $ PFLUSHN an
parseOpF2x 4 1 an = return $ PFLUSH an
parseOpF2x 4 2 _ = return PFLUSHAN
parseOpF2x 4 3 _ = return PFLUSHA
parseOpF2x 5 1 an = return $ PTESTW an
parseOpF2x 5 5 an = return $ PTESTW an
parseOpF2x c t an
  | t == 1 = return $ CINVL (target c) an
  | t == 2 = return $ CINVP (target c) an
  | t == 3 = return $ CINVA (target c)
  | t == 5 = return $ CPUSHL (target c) an
  | t == 6 = return $ CPUSHP (target c) an
  | t == 7 = return $ CPUSHA (target c)
  | otherwise = return ILLEGAL
  where
    target 1 = "DC"
    target 2 = "IC"
    target 3 = "BC"
    target _ = ""

parseOpF3x 0 ay = do
  MOVE16 True True ay <$> next32
parseOpF3x 1 ay = do
  MOVE16 False True ay <$> next32
parseOpF3x 2 ay = do
  MOVE16 True False ay <$> next32
parseOpF3x 3 ay = do
  MOVE16 False False ay <$> next32
parseOpF3x 4 ax = do
  nw <- next16
  let ay = getBit nw 12 7
  return $ MOVE16IncInc ax ay
parseOpF3x _ _ = return ILLEGAL

parseOpMain op
  | h == 0 = parseOp0 dn opi regT regN
  | h == 1 = parseOpMove BYTE opi dn regT regN
  | h == 2 = parseOpMove LONG opi dn regT regN
  | h == 3 = parseOpMove WORD opi dn regT regN
  | h == 4 = parseOp4 dn opi regT regN
  | h == 5 = parseOp5 dn opi regT regN
  | h == 6 = parseOp6 op
  | h == 7 = let imm = toS8 $ getBit op 0 0xff
             in return $ MOVEQ imm dn
  | h == 8  = parseOp8 dn opi regT regN
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

parseOp :: Int -> [Word8] -> (Int, (Op, Int))
parseOp pc opsv =
  let (o, (next, _)) =
        runState ( runMaybeT $ do
                     op <- next16
                     parseOpMain op
                 ) (pc, drop pc opsv)
   in (pc, (fromMaybe ILLEGAL o, next))


getLabels [] = []
getLabels ((_, op):ss) =
  (case op of
    LEA (Offset16 s (BasePC n)) _ -> [s+n]
    LEA (Offset8 s (BasePC n) _ _ _) _ -> [s+n]
    LEA (Indirect s (BasePC n) _ _ _) _ -> [s+n]
    LEA (PreIndex s (BasePC n) _ _ _ _) _ -> [s+n]
    LEA (PostIndex s (BasePC n) _ _ _ _) _ -> [s+n]
    DBcc _ _ x -> [x]
    Bcc _ x -> [x]
    BRA x -> [x]
    JMP (Offset16 s (BasePC n)) -> [s+n]
    JMP (Offset8 s (BasePC n) _ _ _) -> [s+n]
    JMP (Indirect s (BasePC n) _ _ _) -> [s+n]
    JMP (PreIndex s (BasePC n) _ _ _ _) -> [s+n]
    JMP (PostIndex s (BasePC n) _ _ _ _) -> [s+n]
    FDBcc _ _ x -> [x]
    FBcc _ x -> [x]
    _ -> []
  ) ++ getLabels ss
