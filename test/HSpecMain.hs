import           M68k.ConvToAstSpec ()
import           M68k.ParseSpec
import           Test.Hspec
import           UtilSpec
import M68k.OperandSpec
-- import CExprSpec
main :: IO ()
main =
  hspec $ do
    testUtil
    testEA
    testDecode
    testOperand
--    testRtlEA
