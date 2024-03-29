module TestCommon where

import           Data.Word
import           Test.QuickCheck           (Property, Testable, chooseInt,
                                            forAll)
import           Data.Bits




word2Byte :: Int -> [Int]
word2Byte v = [v `shiftR` 8, v .&. 0xff]

longToWord :: Int -> [Int]
longToWord c = [c `shiftR` 16, c .&. 0xffff]

intListToByteList :: [Int] -> [Word8]
intListToByteList x = map fromIntegral $ concatMap word2Byte x
immXTest :: (Testable a) => Int -> (Int -> a) -> Property
immXTest limit = forAll (chooseInt (0, limit))
imm8Test :: (Testable a) => (Int -> a) -> Property
imm8Test = immXTest 0xFF

imm16Test :: (Testable a) => (Int -> a) -> Property
imm16Test = immXTest 0xFFFF
imm32Test :: (Testable a) => (Int -> a) -> Property
imm32Test = immXTest 0xFFFFFFFF

regTest :: (Testable a) => (Int -> a) -> Property
regTest = forAll (chooseInt (0, 7))

regXTest :: (Testable a) => (Int -> a) -> Property
regXTest = forAll (chooseInt (0, 6))

rnTest :: (Testable a) => (Int -> a) -> Property
rnTest = forAll (chooseInt (0, 15))

ccTest :: (Testable a) => (Int -> a) -> Property
ccTest = rnTest -- range is same as rnTest

