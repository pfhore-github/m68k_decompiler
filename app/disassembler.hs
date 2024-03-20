import M68k.Disassemble
import M68k.Parse as P
import qualified Data.ByteString as B
import System.Environment (getArgs)
import Data.Binary.Get ()
import Data.Word
import System.IO
import Numeric
import Data.Bits

disasm from to ops 
  | from < to =
    let (pc, (o, next)) = parseOp from ops
    in (pc, o) : disasm next to ops
  | otherwise = []

main = do
  args <- getArgs
  contents <- B.readFile "../../quadra950.ROM"
  let start = fst $ head $ readHex ( head args )
  let end = ( fst $ head $ readHex ( args !! 1 ) )
  let list = B.unpack contents
  let ops = disasm start end list
  putStr $ showOp ops

