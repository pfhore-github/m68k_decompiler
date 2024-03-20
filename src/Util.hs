module Util where
import Data.Bits
between :: Ord a => a -> a -> a -> Bool
between a b x = (a <= x) && (x <= b)
betweenX :: Ord a => a -> a -> a -> Bool
betweenX a b x = (a < x) && (x < b)

data SplitCase = SplitCont | SplitBefore | SplitBoth
splitBlockImpl :: (a->SplitCase) -> [a] -> [a] -> [[a]] -> [[a]]
splitBlockImpl _ [] c l = l ++ [c]
splitBlockImpl f (x:y) [] l =
  case f x of
    SplitCont -> splitBlockImpl f y [x] l
    SplitBefore -> splitBlockImpl f y [x] l
    SplitBoth -> splitBlockImpl f y [] (l ++ [[x]])

splitBlockImpl f (x:y) c l =
  case f x of
    SplitCont -> splitBlockImpl f y (c ++ [x]) l
    SplitBefore -> splitBlockImpl f y [x] ( l ++ [c] )
    SplitBoth -> splitBlockImpl f y [] (l ++ [c]  ++ [[x]])
  
splitBlock :: (a -> SplitCase) -> [a] -> [[a]]
splitBlock f s = splitBlockImpl f s [] []

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
  | otherwise = 0
