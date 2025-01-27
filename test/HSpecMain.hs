import           M68k.ConvToRtlSpec (testRtlEA)
import           M68k.ParseSpec
import           Test.Hspec
import           UtilSpec

-- import CExprSpec
main :: IO ()
main =
  hspec $ do
    testUtil
    testEA
    testDecode
    testRtlEA
