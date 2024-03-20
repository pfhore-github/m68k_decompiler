import M68k.Parse as P
import CExpr as C
import qualified Data.ByteString as B
import System.Environment (getArgs)
import Data.Binary.Get ()
import Data.Word
import System.IO
import Numeric
import Data.Bits
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import M68k.Env

main :: IO ()
main = do
  args <- getArgs
  contents <- B.readFile "../../quadra950.ROM"
  let start = fst $ head $ readHex ( head args )
  let end = fst $ head $ readHex ( args !! 1 )
  let list = B.unpack contents
  let ops = [(`parseOp` list) y | y <- [start .. end], even y]
--  let (stmts,vars) = decompile start end emptyEnv $ M.fromList ops
--  let merged = mergeStmt stmts
  print $ getJumpTargets ops

getJumpTargets :: [(Int, (Op, Int))] -> S.Set Int
getJumpTargets c =
  S.fromList $ mapMaybe (\(_, (op, _)) ->
           case op of
             P.BRA v -> Just v
             P.Bcc _ v -> Just v
             P.DBcc _ _ v -> Just v
             P.JMP s ->
               case s of
                 Offset16 s2 ( BasePC n)-> Just (n + s2)
                 _ -> Nothing
             _ -> Nothing
      ) c
