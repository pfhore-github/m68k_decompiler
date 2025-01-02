import           M68k.ConvToRtlSpec
import           M68k.ParseSpec
import           Test.Hspec
import           UtilSpec

-- import CExprSpec
main :: IO ()
main =
  hspec $ do
    testUtil
--    testCExpr
    testEA
    testDecode
    testEA2
--    testDecompileEA
