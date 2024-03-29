import           Test.Hspec
import M68k.DecompileSpec
import UtilSpec
import M68k.ParseSpec
-- import CExprSpec

main :: IO ()
main =
  hspec $ do
    testUtil
--    testCExpr
    testEA
    testDecode
    testDecompileEA
  
