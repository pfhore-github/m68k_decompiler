module AST.CType where

import Text.Printf ( formatString, PrintfArg(formatArg) )

data CType =
  VOID 
  | BOOL
  | BCD
  | PTR CType
  | INT8
  | UINT8
  | INT16
  | UINT16
  | INT32
  | UINT32
  | INT64
  | UINT64
  | FLT
  | DBL
  | EXT
  | FLT_BCD
  deriving (Eq)


instance Show CType where
  show (PTR t) = show t ++ "*"
  show VOID = "void"
  show BOOL = "bool"
  show BCD = "bcd"
  show INT8 = "char"
  show INT16 = "short"
  show INT32 = "int"
  show INT64 = "long long"
  show UINT8 = "unsigned char"
  show UINT16 = "unsigned short"
  show UINT32 = "unsigned int"
  show UINT64 = "unsigned long long"
  show FLT = "float"
  show DBL = "double"
  show EXT = "long double"
  show FLT_BCD = "float bcd"

joinType :: CType -> CType
joinType INT8 = INT16
joinType INT16 = INT32
joinType INT32 = INT64
joinType UINT8 = UINT16
joinType UINT16 = UINT32
joinType UINT32 = UINT64
joinType _ = undefined

sizeOf :: CType -> Int
sizeOf BOOL = 1
sizeOf BCD = 1
sizeOf (PTR _) = 4
sizeOf INT8 = 1
sizeOf UINT8 = 1
sizeOf INT16 = 2
sizeOf UINT16 = 2
sizeOf INT32 = 4
sizeOf UINT32 = 4
sizeOf INT64 = 8
sizeOf UINT64 = 8
sizeOf FLT = 4
sizeOf DBL = 8
sizeOf EXT = 12
sizeOf FLT_BCD = 12
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

isInteger :: CType -> Bool
isInteger c = isSignedType c || isUnsignedType c

isSignedType :: CType -> Bool
isSignedType INT8 = True
isSignedType INT16 = True
isSignedType INT32 = True
isSignedType INT64 = True
isSignedType UINT8 = False
isSignedType UINT16 = False
isSignedType UINT32 = False
isSignedType UINT64 = False
isSignedType _ = False

isUnsignedType :: CType -> Bool
isUnsignedType INT8 = False
isUnsignedType INT16 = False
isUnsignedType INT32 = False
isUnsignedType INT64 = False
isUnsignedType UINT8 = True
isUnsignedType UINT16 = True
isUnsignedType UINT32 = True
isUnsignedType UINT64 = True
isUnsignedType _ = undefined

toSigned :: CType -> CType
toSigned INT8 = INT8
toSigned INT16 = INT16
toSigned INT32 = INT32
toSigned INT64 = INT64
toSigned UINT8 = INT8
toSigned UINT16 = INT16
toSigned UINT32 = INT32
toSigned UINT64 = INT64
toSigned t = t

toUnsigned :: CType -> CType
toUnsigned INT8 = UINT8
toUnsigned INT16 = UINT16
toUnsigned INT32 = UINT32
toUnsigned INT64 = UINT64
toUnsigned UINT8 = UINT8
toUnsigned UINT16 = UINT16
toUnsigned UINT32 = UINT32
toUnsigned UINT64 = UINT64
toUnsigned t = t

instance PrintfArg CType where
  formatArg x = formatString (show x)

toUnsignedValue :: Bool -> Integer -> Integer
toUnsignedValue False v = v
toUnsignedValue True v = if v < 0 then (0x100000000 + v) else v

toSignedValue :: Bool -> Integer -> Integer
toSignedValue False v = v
toSignedValue True v = if v > 0x7FFFFFFF then (0x100000000 - v) else v

typePromote :: CType -> CType -> CType
typePromote a b = 
  if (isInteger a) && (isInteger b) then
    let aIsSigned = isSignedType a
        bIsSigned = isSignedType b
    in if (aIsSigned && bIsSigned) then
          INT32
       else 
          UINT32
  else
      EXT 
