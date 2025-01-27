module Util where
import Data.Bits

between :: Ord a => a -> a -> a -> Bool
between a b x = (a <= x) && (x <= b)
betweenX :: Ord a => a -> a -> a -> Bool
betweenX a b x = (a < x) && (x < b)

data SplitCase = SplitCont | SplitBefore | SplitBoth
  
splitBlock :: (a -> SplitCase) -> [a] -> [[a]]
splitBlock f s =
  let splitBlockImpl [] c l = l ++ [c]
      splitBlockImpl (x:y) [] l =
        case f x of
          SplitCont -> splitBlockImpl y [x] l
          SplitBefore -> splitBlockImpl y [x] l
          SplitBoth -> splitBlockImpl y [] (l ++ [[x]])

      splitBlockImpl (x:y) c l =
        case f x of
          SplitCont -> splitBlockImpl y (c ++ [x]) l
          SplitBefore -> splitBlockImpl y [x] ( l ++ [c] )
          SplitBoth -> splitBlockImpl y [] (l ++ [c]  ++ [[x]])

  in splitBlockImpl s [] []

toS8 :: Int -> Int
toS8 v =
  if v >= 0x80
    then v - 0x100
    else v

toS16 :: Int -> Int
toS16 v =
  if v >= 0x8000
    then v - 0x10000
    else v

toS32 :: Int -> Int
toS32 v =
  if v >= 0x80000000
    then v - 0x100000000
    else v

getBit :: Int -> Int -> Int -> Int
getBit v pos mask
  | pos > 0 = shiftR v pos .&. mask
  | pos == 0 = v .&. mask
  | otherwise = undefined

bool2Bit :: Num a => Bool -> a
bool2Bit True = 1
bool2Bit False = 0
