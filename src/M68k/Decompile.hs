{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module M68k.Decompile where
import           M68k.Opcode

partition :: [a] -> (a -> Int) -> [[a]]
partition  = 
  partitionImpl [] 
  where
    partitionImpl :: [a] -> [a] -> (a -> Int) -> [[a]]
    partitionImpl current [] _ = [current]
    partitionImpl current (i:o) f
      | f i == 0 && not (null current) = current : partitionImpl [i] o f
      | f i == 0 && null current = partitionImpl [i] o f
      | f i == 1 && not (null current) = (current++ [i]) : partitionImpl [] o f
      | f i == 1 && null current = [i] : partitionImpl [] o f
      | otherwise = partitionImpl (current ++ [i]) o f

groupOps :: [(Int, Op, Int)] -> [Int] -> [[(Int, Op, Int)]]
groupOps ops labels =
  partition ops ( \(pc, op, _) -> 
    if  pc `elem` labels then 0
    else (
      case op of
        (Bcc _ _) -> 1
        DBcc {} -> 1
        (TRAPcc _ _) -> 1
        (BSR _) -> 1
        (BRA _) -> 1
        (SYS _) -> 1
        (JMP _) -> 1
        (JSR _) -> 1
        _ -> 2
    ) )
