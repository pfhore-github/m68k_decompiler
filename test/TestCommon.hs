module TestCommon where

import           Data.Word
import           Test.QuickCheck           (Gen, Property, Testable, chooseInt,
                                            forAll, elements)
import           Data.Bits
import AST.CType

import M68k.Operand

word2Byte :: Int -> [Int]
word2Byte v = [v `shiftR` 8, v .&. 0xff]

longToWord :: Int -> [Int]
longToWord c = [c `shiftR` 16, c .&. 0xffff]

intListToByteList :: [Int] -> [Word8]
intListToByteList x = map fromIntegral $ concatMap word2Byte x

itypes :: [CType]
itypes = [INT8, INT16, INT32, UINT8, UINT16, UINT32]


immXTest :: (Testable a) => Int -> (Int -> a) -> Property
immXTest limit = forAll $ chooseInt (0, limit)
imm8Test :: (Testable a) => (Int -> a) -> Property
imm8Test = immXTest 0xFF

immS8Test :: (Testable a) => (Int -> a) -> Property
immS8Test = forAll $ chooseInt (-128, 127)

imm16Test :: (Testable a) => (Int -> a) -> Property
imm16Test = immXTest 0xFFFF

immS16Test :: (Testable a) => (Int -> a) -> Property
immS16Test = forAll $ chooseInt (-32768, 32767)

imm32Test :: (Testable a) => (Int -> a) -> Property
imm32Test = immXTest 0xFFFFFFFF

immS32Test :: (Testable a) => (Int -> a) -> Property
immS32Test = forAll $ chooseInt (-2147483648, 2147483647)

iregs :: Gen Integer
iregs = elements [0..7]

testFor :: (Testable a) => [Int] -> (Int -> a) -> Property
testFor range f = forAll (elements range) $ \d -> f d

