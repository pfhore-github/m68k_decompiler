{-# LANGUAGE InstanceSigs #-}
module M68k.Operand where

import           M68k.LongDouble
import           Text.Printf
import M68k.Common (AType, AFType)

class Reg a where
  reg_num :: a -> Int

newtype DR =
  DR Int
  deriving (Eq)

newtype AR =
  AR Int
  deriving (Eq)

newtype FPR =
  FPR Int
  deriving (Eq)

newtype CC =
  CC Int
  deriving (Eq)

newtype FCC =
  FCC Int
  deriving (Eq)

instance Show DR where
  show (DR n) = "%d" ++ show n

instance PrintfArg DR where
  formatArg = formatArg . show

instance Reg DR where
  reg_num (DR n) = n

instance Show AR where
  show (AR 7) = "%sp"
  show (AR 6) = "%fp"
  show (AR n) = "%a" ++ show n

instance PrintfArg AR where
  formatArg = formatArg . show

instance Reg AR where
  reg_num (AR n) = n + 8

instance Show FPR where
  show (FPR n) = "%fp" ++ show n

instance PrintfArg FPR where
  formatArg = formatArg . show

instance Reg FPR where
  reg_num (FPR n) = n

data XR
  = XR_D Int
  | XR_A Int
  deriving (Eq)

xr :: Int -> XR
xr n
  | n < 8 = XR_D n
  | otherwise = XR_A $ n - 8

instance Reg XR where
  reg_num (XR_D n) = n
  reg_num (XR_A n) = n + 8

instance Show XR where
  show (XR_D n) = show (DR n)
  show (XR_A n) = show (AR n)

instance PrintfArg XR where
  formatArg = formatArg . show

instance Show CC where
  show (CC 0)  = "t"
  show (CC 1)  = "f"
  show (CC 2)  = "hi"
  show (CC 3)  = "ls"
  show (CC 4)  = "cc"
  show (CC 5)  = "cs"
  show (CC 6)  = "ne"
  show (CC 7)  = "eq"
  show (CC 8)  = "vc"
  show (CC 9)  = "vs"
  show (CC 10) = "pl"
  show (CC 11) = "mi"
  show (CC 12) = "ge"
  show (CC 13) = "lt"
  show (CC 14) = "gt"
  show (CC 15) = "le"
  show (CC _)  = ""

instance PrintfArg CC where
  formatArg = formatArg . show

instance Show FCC where
  show (FCC 0)  = "f"
  show (FCC 1)  = "eq"
  show (FCC 2)  = "ogt"
  show (FCC 3)  = "oge"
  show (FCC 4)  = "olt"
  show (FCC 5)  = "ole"
  show (FCC 6)  = "ogl"
  show (FCC 7)  = "or"
  show (FCC 8)  = "un"
  show (FCC 9)  = "ueq"
  show (FCC 10) = "ugt"
  show (FCC 11) = "uge"
  show (FCC 12) = "ult"
  show (FCC 13) = "ule"
  show (FCC 14) = "ne"
  show (FCC 15) = "t"
  show (FCC 16) = "sf"
  show (FCC 17) = "seq"
  show (FCC 18) = "gt"
  show (FCC 19) = "ge"
  show (FCC 20) = "lt"
  show (FCC 21) = "le"
  show (FCC 22) = "gl"
  show (FCC 23) = "gle"
  show (FCC 24) = "ngle"
  show (FCC 25) = "ngl"
  show (FCC 26) = "nle"
  show (FCC 27) = "nlt"
  show (FCC 28) = "nge"
  show (FCC 29) = "ngt"
  show (FCC 30) = "sne"
  show (FCC 31) = "st"
  show (FCC _)  = ""

instance PrintfArg FCC where
  formatArg = formatArg . show

data AddrBase
  = BaseAR AR
  | BasePC Int -- value is actually (PCBase + addr)
  | BaseNone
  deriving (Eq)

data Operand
  = DReg DR
  | AReg AR
  | Address MemOperand
  | ImmInt Int
  | CCR
  | SR
  | SpRG [Char]
  deriving (Eq)

instance Show Operand where
  show (DReg dr)   = show dr
  show (AReg ar)   = show ar
  show (ImmInt x)  = printf "#%d" x
  show CCR         = "%ccr"
  show SR          = "%sr"
  show (SpRG s)    = "%" ++ s
  show (Address x) = show x

instance PrintfArg Operand where
  formatArg = formatArg . show

data MemOperand
  = UnRefAR AR
  | UnRefInc AR
  | UnRefDec AR
  | Offset16 Int AddrBase
  | Offset8 Int AddrBase Bool XR Int
  | Indirect Int AddrBase Bool (Maybe XR) Int
  | PreIndex Int AddrBase Bool (Maybe XR) Int Int
  | PostIndex Int AddrBase Bool (Maybe XR) Int Int
  | ImmAddr Int
  deriving (Eq)

toScale :: XR -> Bool -> Int -> String
toScale idx w d
  | d == 0 = printf "%v%s" idx ex
  | otherwise = printf "%v%s << %d" idx ex d
  where
    ex =
      if w
        then ".w"
        else ""

indexStr :: Bool -> Maybe XR -> Bool -> Int -> String
indexStr _ Nothing _ _        = ""
indexStr True (Just rn) w cc  = printf ", %s" $ toScale rn w cc
indexStr False (Just rn) w cc = printf "%s, " $ toScale rn w cc

base2Str :: Int -> AddrBase -> String
base2Str d (BasePC pc) = printf "0x%05x" (d + pc) ++ ", %pc"
base2Str d BaseNone    = printf "0x%05x" d
base2Str d (BaseAR ar) = printf "%d, %v" d ar

instance Show MemOperand where
  show (UnRefAR ar) = printf "(%v)" ar
  show (UnRefInc ar) = printf "(%v)+" ar
  show (UnRefDec ar) = printf "-(%v)" ar
  show (Offset16 a base) = printf "(%s)" $ base2Str a base
  show (Offset8 bd base w rn cc) =
    printf "(%s, %s)" (base2Str bd base) $ toScale rn w cc
  show (Indirect bd base w rnp cc) =
    printf "(%s%s)" (base2Str bd base) (indexStr True rnp w cc)
  show (PreIndex bd base w rnp cc od) =
    printf "([%s%s], %d)" (base2Str bd base) (indexStr True rnp w cc) od
  show (PostIndex bd base w rnp cc od) =
    printf "([%s], %s%d)" (base2Str bd base) (indexStr False rnp w cc) od
  show (ImmAddr x) = printf "0x%05x" x

instance PrintfArg MemOperand where
  formatArg = formatArg . show

data FpuOperand
  = FpuRn FPR
  | FpuOperandInt AType Operand
  | FpuOperandFlt AFType MemOperand
  | FpuImm AFType LongDouble
  deriving (Eq)

instance Show FpuOperand where
  show :: FpuOperand -> String
  show (FpuRn n)         = printf "%%fp%d" n
  show (FpuOperandInt _ t) = show t
  show (FpuOperandFlt _ t) = show t
  show (FpuImm _ d)        = show d

typeOfO :: FpuOperand -> String
typeOfO (FpuRn _)         = "x"
typeOfO (FpuOperandInt t _) = show t
typeOfO (FpuOperandFlt t _) = show t
typeOfO (FpuImm t _)        = show t
 

instance PrintfArg FpuOperand where
  formatArg = formatArg . show
