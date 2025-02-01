module M68k.LongDouble(LongDouble, fromSingle, fromDouble, fromExtWord, fromPacked, isNAN) where

import qualified Data.Number.MPFR as M
import Data.Ratio
import GHC.Float ( float2Double )
import Data.Bits
import Data.Char
import Util
-- 80bit number
newtype LongDouble = LongDouble M.MPFR

fromSingle :: Float -> LongDouble
fromSingle s = LongDouble $ M.fromDouble M.Near 64 $ float2Double s
fromDouble :: Double -> LongDouble
fromDouble d = LongDouble $ M.fromDouble M.Near 64 d

fromExtWord :: Int -> Integer -> LongDouble
fromExtWord e f = LongDouble $ M.compose M.Near 64 (f, e+63)
fromPacked :: Int -> Int -> LongDouble
fromPacked e f
  | se && yy == 3 && expF == 0xFFF && f == 0 = LongDouble $ M.setInf 64 (if sm then -1 else 1)
  | se && yy == 3 && expF == 0xFFF && f /= 0 = LongDouble $ M.setNaN 64
  | f == 0 && sm = LongDouble $ M.neg M.Near 64 M.zero
  | f == 0 && not sm = LongDouble M.zero
  | otherwise =
    let sg s = (if s then '-' else '+')
        getD x n = (x `shiftR` (4*n)) .&. 0xF
        fracS = int2Str f $ reverse [0..15]
        expS = int2Str e $ reverse [0..3]
        int2Str x = map (intToDigit . getD x)
    in LongDouble $ M.stringToMPFR M.Near 64 10
       ((sg sm:intToDigit (e .&. 0xF):'.':fracS) ++ ('e':sg se:expS))
  where sm = testBit e 31
        se = testBit e 30
        yy = getBit e 28 3
        expF = getBit e 16 0xFFF

instance Show LongDouble where
  show (LongDouble x) = M.toString 30 x

liftLD :: Num t => (M.RoundMode -> t -> M.MPFR -> M.MPFR) -> LongDouble -> LongDouble
liftLD o (LongDouble x) = LongDouble (o M.Near 64 x)
liftLD2 :: Num t => (M.RoundMode -> t -> M.MPFR -> M.MPFR -> M.MPFR) -> LongDouble -> LongDouble -> LongDouble
liftLD2 o (LongDouble x) (LongDouble y) = LongDouble (o M.Near 64 x y)

instance Eq LongDouble where
  (LongDouble x) == (LongDouble y) = x == y

instance Ord LongDouble where
  compare (LongDouble x) (LongDouble y) = compare x y

instance Num LongDouble where
  (+) = liftLD2 M.add
  (-) = liftLD2 M.sub
  (*) = liftLD2 M.mul
  negate = liftLD M.neg
  abs = liftLD M.absD
  signum (LongDouble x) = case M.sgn x of
    Nothing -> LongDouble x
    Just x' -> LongDouble $ M.fromInt M.Near 64 x'
  fromInteger x = LongDouble $ M.fromIntegerA M.Near 64 x

instance Fractional LongDouble where
  (LongDouble x) / (LongDouble y) = LongDouble (M.div M.Near 64 x y)
  fromRational x = ((fromInteger $ numerator x) :: LongDouble) /
                   ((fromInteger $ denominator x) :: LongDouble)

isNAN :: M.MPFR -> Bool
isNAN = M.isNaN
instance Floating LongDouble where
  pi = LongDouble $ M.pi M.Near 64
  exp = liftLD M.exp
  log = liftLD M.log
  sqrt = liftLD M.sqrt
  (**) = liftLD2 M.pow
  sin = liftLD M.sin
  cos = liftLD M.cos
  tan = liftLD M.tan
  asin = liftLD M.asin
  acos = liftLD M.acos
  atan = liftLD M.atan
  sinh = liftLD M.sinh
  cosh = liftLD M.cosh
  tanh = liftLD M.tanh
  asinh = liftLD M.asinh
  acosh = liftLD M.acosh
  atanh = liftLD M.atanh

