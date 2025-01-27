{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module M68k.Decompile where
import           M68k.Opcode
{-
-- decompile 1st phase
import           CExpr
import           CType
import           Control.Monad (when)
import           Data.Bits
import qualified Data.Map            as M
import           Env
import           M68k.Env
import           MonadOp
import           Text.Printf
import qualified Control.Monad.Operational as O

-}

partition :: [a] -> (a -> Int) -> [[a]]
partition lists func = 
  partitionImpl [] lists func
  where
    partitionImpl :: [a] -> [a] -> (a -> Int) -> [[a]]
    partitionImpl current [] _ = [current]
    partitionImpl current (i:o) f
      | (f i) == 0 && (length current) /= 0 = [current] ++ partitionImpl [i] o f
      | (f i) == 0 && (length current) == 0 = partitionImpl [i] o f
      | (f i) == 1 && (length current) /= 0 = [current++ [i]] ++ partitionImpl [] o f
      | (f i) == 1 && (length current) == 0 = [[i]] ++ partitionImpl [] o f
      | otherwise = partitionImpl (current ++ [i]) o f

groupOps :: [(Int, Op, Int)] -> [Int] -> [[(Int, Op, Int)]]
groupOps ops labels =
  partition ops ( \(pc, op, _) -> 
    if elem pc labels then 0
    else (
      case op of
        (Bcc _ _) -> 1
        (DBcc  _ _ _) -> 1
        (TRAPcc _ _) -> 1
        (BSR _) -> 1
        (BRA _) -> 1
        (SYS _) -> 1
        (JMP _) -> 1
        (JSR _) -> 1
        _ -> 2
    ) )
