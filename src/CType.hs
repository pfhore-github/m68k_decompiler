module CType where

import Text.Printf ( formatString, PrintfArg(formatArg) )

data CType =
  VOID 
  | BOOL
  | BCD
  | PTR CType
  | INT Bool Int
  deriving (Eq)

int8 :: CType
int8 = INT True 1
int16 :: CType
int16 = INT True 2
int32 :: CType
int32 = INT True 4
int64 :: CType
int64 = INT True 8
uint8 :: CType
uint8 = INT False 1
uint16 :: CType
uint16 = INT False 2
uint32 :: CType
uint32 = INT False 4
uint64 :: CType
uint64 = INT False 8

instance Show CType where
  show (PTR t) = show t ++ "*"
  show VOID = "void"
  show BOOL = "bool"
  show BCD = "bcd"
  show (INT True 1) = "signed char"
  show (INT True 2) = "short"
  show (INT True 4) = "int"
  show (INT True 8) = "long long"
  show (INT False 1) = "unsigned char"
  show (INT False 2) = "unsigned short"
  show (INT False 4) = "unsigned int"
  show (INT False 8) = "unsigned long long"
  show _ = "void"

sizeOf :: CType -> Int
sizeOf BOOL = 1
sizeOf BCD = 1
sizeOf (PTR _) = 4
sizeOf (INT _ n) = n
sizeOf VOID = 0

shiftSizeOf :: CType -> Int
shiftSizeOf x
  | sizeOf x == 1 = 0
  | sizeOf x == 2 = 1
  | sizeOf x == 4 = 2
  | sizeOf x == 8 = 3
  | otherwise = undefined

sizeOfS :: CType -> Int
sizeOfS t = max (sizeOf t) 2

toSigned :: CType -> CType
toSigned (INT _ y) = INT True y
toSigned _ = undefined

toUnsigned :: CType -> CType
toUnsigned (INT _ y) = INT False y
toUnsigned _ = undefined

instance PrintfArg CType where
  formatArg x = formatString (show x)

