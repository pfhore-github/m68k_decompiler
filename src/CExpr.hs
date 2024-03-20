{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE ExistentialQuantification #-}

module CExpr where

import           CType
import           Data.Bits
import           Text.Printf

data Expr
  = Const CType Int
  | Arg CType String -- dummy
  | VarValue Var -- var(value)
  | VarAddr Var -- &var
  | Cast CType Expr -- (type)v
  | Op1 String Expr -- !v/~v/-v etc
  | IncDec Bool Bool Var -- isPost, isInc, var; var++/++var
  | Op2 Expr String Expr -- v1 op v2
  | CondExpr Expr Expr Expr -- c ? v1 : v2
  | Expr2 Expr Expr

typeOf :: Expr -> CType
typeOf (Const t _) = t
typeOf (Arg t _) = t
typeOf (VarValue v) = typeofV v
typeOf (VarAddr v) = PTR (typeofV v)
typeOf (Cast t _) = t
typeOf (Op1 c x)
  | c == "!" = BOOL
  | otherwise = typeOf x
typeOf (IncDec _ _ v) = typeofV v
typeOf (Op2 x op _)
  | op == "&&" ||
      op == "||" ||
      op == ">" ||
      op == ">=" ||
      op == "<" || op == "<=" || op == "==" || op == "!=" || op == "/V" = BOOL
  | otherwise = typeOf x
typeOf (CondExpr _ t _) = typeOf t
typeOf (Expr2 h _) =
  let t1 = typeOf h
   in case t1 of
        INT x n -> INT x (n * 2)
        _       -> undefined

data Var
  = EnvVar CType String -- reg var
  | GVar CType Int -- Low Global
  | CVar CType Int -- PC realative
  | TVar CType Int -- temporaly for C
  | SPVar CType String -- Special Register(cannot merge)
  | SVar CType Int -- Stack variable
  | Deref Expr -- * var
  | Member CType Var Int -- var.member
  | PMember CType Expr Int -- ptr->member
  | BitField CType Var Int Int -- var.member_m (bit field)
  | BitFieldX CType Var Expr Expr -- (non-supported)
  | Index CType Expr Expr -- var[index]

typeofV :: Var -> CType
typeofV (EnvVar t _) = t
typeofV (GVar t _) = t
typeofV (CVar t _) = t
typeofV (TVar t _) = t
typeofV (SPVar t _) = t
typeofV (SVar t _) = t
typeofV (Deref e) =
  case typeOf e of
    PTR n -> n
    _     -> undefined
typeofV (Member t _ _) = t
typeofV (PMember t _ _) = t
typeofV (BitField t _ _ _) = t
typeofV (BitFieldX t _ _ _) = t
typeofV (Index t _ _) = t

typeSuffix :: CType -> String
typeSuffix t =
  case t of
    INT _ 1 -> "B"
    INT _ 2 -> "W"
    INT _ 4 -> "L"
    _       -> ""

priority :: String -> Integer
priority "*"  = 3
priority "/"  = 3
priority "%"  = 3
priority "+"  = 4
priority "-"  = 4
priority "<<" = 5
priority ">>" = 5
priority "<"  = 6
priority "<=" = 6
priority ">"  = 6
priority ">=" = 6
priority "==" = 7
priority "!=" = 7
priority "&"  = 8
priority "^"  = 9
priority "|"  = 10
priority "&&" = 11
priority "||" = 12
priority _    = 99

cast :: CType -> Expr -> Expr
cast t y
  | typeOf y == t = y
cast BOOL v = v $!= Const (typeOf v) 0
cast BCD v = Op1 "toBCD" v
cast tt@(PTR _) v =
  let t' = typeOf v
   in Cast tt $
      case t' of
        PTR _ -> v
        _     -> Cast int32 v
cast tt@(INT _ n) (Expr2 a b) =
  let n' = sizeOf $ typeOf a
   in if n' >= n
        then cast tt b
        else cast tt $ (cast tt a $<<# (8 * n)) $| cast tt b
cast tt@(INT _ _) v =
  let t' = typeOf v
   in Cast tt $
      case t' of
        PTR _ -> Cast int32 v
        _     -> v
cast t v = Cast t v

lNot :: Expr -> Expr
lNot (Const _ 0)    = Const BOOL 1
lNot (Const _ _)    = Const BOOL 0
lNot (Op2 a "&&" b) = lNot b $|| lNot a
lNot (Op2 a "||" b) = lNot b $&& lNot a
lNot (Op2 a "<=" b) = a $> b
lNot (Op2 a "<" b)  = a $>= b
lNot (Op2 a ">=" b) = a $< b
lNot (Op2 a ">" b)  = a $<= b
lNot (Op2 a "==" b) = a $!= b
lNot (Op2 a "!=" b) = a $== b
lNot t              = Op1 "!" $ cast BOOL t

neg :: Expr -> Expr
neg (Const t x) = Const t (-x)
neg x           = Op1 "-" x

bNot :: Expr -> Expr
bNot (Const t x) = Const t $ complement x
bNot x           = Op1 "~" x

op1 :: String -> Expr -> Expr
op1 "~" = bNot
op1 "!" = lNot . cast BOOL
op1 "-" = neg
op1 c   = Op1 c

immT :: Expr
immT = Const BOOL 1

immF :: Expr
immF = Const BOOL 0

immNA :: Expr
immNA = Const BOOL (-1)

cmpOp :: String -> Expr -> Expr -> Expr
cmpOp c (Const _ x) (Const _ y) =
  Const
    BOOL
    (if (case c of
           ">"  -> (>)
           ">=" -> (>=)
           "<"  -> (<)
           "<=" -> (<=)
           "==" -> (==)
           "!=" -> (/=)
           _    -> \_ _ -> False)
          x
          y
       then 1
       else 0)
cmpOp c x y = Op2 x c (cast (typeOf x) y)

infix 2 $==

infix 2 $!=

infix 3 $>

infix 3 $>=

infix 3 $<

infix 3 $<=

($>) :: Expr -> Expr -> Expr
($>) = cmpOp ">"

($>=) :: Expr -> Expr -> Expr
($>=) = cmpOp ">="

($<) :: Expr -> Expr -> Expr
($<) = cmpOp "<"

($<=) :: Expr -> Expr -> Expr
($<=) = cmpOp "<="

($==) :: Expr -> Expr -> Expr
($==) = cmpOp "=="

($!=) :: Expr -> Expr -> Expr
($!=) = cmpOp "!="

($@#) :: Expr -> Int -> Var
($@#) x n = x $@ Const int32 n

($@) :: Expr -> Expr -> Var
($@) x = Index (typeOf x) x

($||) :: Expr -> Expr -> Expr
($||) (Const BOOL 0) _ = immT
($||) (Const BOOL 1) y = y
($||) x y              = Op2 (cast BOOL x) "||" (cast BOOL y)

($&&) :: Expr -> Expr -> Expr
($&&) (Const BOOL 0) y = y
($&&) (Const BOOL 1) _ = immF
($&&) x y              = Op2 (cast BOOL x) "&&" (cast BOOL y)

condExpr :: Expr -> Expr -> Expr -> Expr
condExpr (Const BOOL 0) _ y = y
condExpr (Const BOOL 1) x _ = x
condExpr c x y              = CondExpr c x y

($&#) :: Expr -> Int -> Expr
($&#) x y = x $& Const uint32 y

($|#) :: Expr -> Int -> Expr
($|#) x y = x $| Const uint32 y

($^#) :: Expr -> Int -> Expr
($^#) x y = x $^ Const uint32 y

bitOp :: String -> Expr -> Expr -> Expr
bitOp op (Expr2 h1 l1) (Expr2 h2 l2) = Expr2 (bitOp op h1 h2) (bitOp op l1 l2)
bitOp op x@(Expr2 h1 _) y =
  let tt@(INT _ n) = typeOf h1
      y' = Expr2 (cast tt (y $>> Const int8 (8 * n))) (cast tt y)
   in bitOp op x y'
bitOp op x y@(Expr2 h1 _) =
  let tt@(INT _ n) = typeOf h1
      x' = Expr2 (cast tt (x $>> Const int8 (8 * n))) (cast tt x)
   in bitOp op x' y
bitOp "&" (Const t x) (Const _ y) = Const t (x .&. y)
bitOp "|" (Const t x) (Const _ y) = Const t (x .|. y)
bitOp "^" (Const t x) (Const _ y) = Const t (x .^. y)
bitOp c x y = Op2 x c (cast (typeOf x) y)

($&) :: Expr -> Expr -> Expr
($&) = bitOp "&"

($|) :: Expr -> Expr -> Expr
($|) = bitOp "|"

($^) :: Expr -> Expr -> Expr
($^) = bitOp "^"

($<<) :: Expr -> Expr -> Expr
($<<) (Const t1 x) (Const _ y) = Const t1 $ x `shiftL` y
($<<) x y                      = Op2 x "<<" (cast uint8 y)

($>>) :: Expr -> Expr -> Expr
($>>) (Const t1 x) (Const _ y) = Const t1 $ x `shiftR` y
($>>) x y                      = Op2 x ">>" y

arithOp :: String -> Expr -> Expr -> Expr
arithOp "+" (Const t1 x) (Const _ y) = Const t1 $ x + y
arithOp "-" (Const t1 x) (Const _ y) = Const t1 $ x - y
arithOp "*" (Const t1 x) (Const _ y) = Const t1 $ x * y
arithOp "/" (Const t1 x) (Const _ y) = Const t1 $ x `div` y
arithOp "%" (Const t1 x) (Const _ y) = Const t1 $ x `mod` y
arithOp c xx yy                      = Op2 xx c yy

subV :: Expr -> Expr -> Expr
subV = arithOp "subV"

($<<#) :: Expr -> Int -> Expr
($<<#) x y = x $<< Const uint8 y

($>>#) :: Expr -> Int -> Expr
($>>#) x y = x $>> Const uint8 y

(#$<<) :: Int -> Expr -> Expr
(#$<<) x y = Const uint32 x $<< y

(#$>>) :: Int -> Expr -> Expr
(#$>>) x y = Const uint32 x $>> y

($+) :: Expr -> Expr -> Expr
($+) = arithOp "+"

($-) :: Expr -> Expr -> Expr
($-) = arithOp "+"

($+#) :: Expr -> Int -> Expr
($+#) x y = x $+ Const (typeOf x) y

($-#) :: Expr -> Int -> Expr
($-#) x y = x $- Const (typeOf x) y

-- multiply/div
($*) :: Expr -> Expr -> Expr
($*) x = Op2 x "*"

($**) :: Expr -> Expr -> (Expr, Expr)
($**) x y = (Op2 x "*H" y, x $* y)

($/) :: Expr -> Expr -> Expr
($/) x = Op2 x "/"

($%) :: Expr -> Expr -> Expr
($%) x = Op2 x "%"

-- Quad div overflow
($/!) :: Expr -> Expr -> Expr
($/!) x = Op2 x "/V"

op2 :: String -> Expr -> Expr -> Expr
op2 "==" x y = x $== y
op2 "!=" x y = x $!= y
op2 ">" x y  = x $> y
op2 ">=" x y = x $>= y
op2 "<" x y  = x $< y
op2 "<=" x y = x $<= y
op2 "*" x y  = x $* y
op2 "/" x y  = x $/ y
op2 "%" x y  = x $% y
op2 "+" x y  = x $+ y
op2 "-" x y  = x $- y
op2 "&" x y  = x $& y
op2 "|" x y  = x $| y
op2 "^" x y  = x $^ y
op2 ">>" x y = x $>> y
op2 "<<" x y = x $<< y
op2 op x y   = Op2 x op y

deref :: Expr -> Var -- *expr
deref (VarAddr var) = var
deref (Op2 a "+" (Op2 b "<<" (Const _ c))) =
  let (PTR t) = typeOf a
   in case b of
        Const _ n -> PMember t a $ n `shiftL` c
        _ ->
          let sizec = shiftSizeOf t
              indexN =
                if sizec > c
                  then b $>># (sizec - c)
                  else b $<<# (c - sizec)
           in Index t a indexN
deref (Op2 a "+" b) =
  let (PTR t) = typeOf a
   in case b of
        Const _ n -> PMember t a n
        _         -> Index t a (b $<<# shiftSizeOf t)
deref x =
  case typeOf x of
    PTR _ -> Deref x
    _     -> undefined

instance Show Expr where
  show (Arg _ v) = v
  show (VarValue v) = show v
  show (VarAddr v) = printf "&%s" $ show v
  show (Const t v) =
    case t of
      INT True n -> printf "0x%0*X" (n * 2) v
      PTR _ -> printf "0x%08X" v
      BOOL ->
        if v == 1
          then "true"
          else "false"
      _ -> printf "%d" v
  show (Cast t v) = printf "(%v)(%s)" t $ show v
  show (IncDec True c (Deref v)) =
    printf
      "(*%s)%s"
      (show v)
      (if c
         then "++"
         else "--")
  show (IncDec True c v) =
    printf
      "%s%s"
      (show v)
      (if c
         then "++"
         else "--")
  show (IncDec False c v) =
    printf
      "%s%s"
      (if c
         then "++"
         else "--")
      (show v)
  show (Op1 op v) = printf "%s %s" op (show v)
  show (Op2 v1 o1 v2) =
    let v1s =
          case v1 of
            (Op2 _ o2 _)
              | priority o2 < priority o1 -> printf "(%s)" (show v1)
            _ -> show v1
        v2s =
          case v2 of
            (Op2 _ o2 _)
              | priority o2 < priority o1 -> printf "(%s)" (show v2)
            _ -> show v2
     in printf "%s %s %s" v1s o1 v2s
  show (CondExpr c v1 v2) = printf "%s ? %s : %s" (show c) (show v1) (show v2)
  show (Expr2 v1 v2) = printf "(%s, %s)" (show v1) (show v2)

instance Show Var where
  show (EnvVar _ s) = s
  show (GVar _ v) = printf "_G_%05x" v
  show (TVar _ v) = printf "_t_%d" v
  show (CVar _ v) = printf "_c_%05x" v
  show (SVar _ v) = printf "_l_%05x" v
  show (SPVar _ s) = s
  show (Deref v) = printf "*%s" $ show v
  show (Member _ v n) = printf "%s._%d" (show v) n
  show (PMember _ v n) = printf "%s->_%d" (show v) n
  show (BitField _ v o s) = printf "%s._%d_%d" (show v) o s
  show (BitFieldX _ v o s) =
    printf "getBit(%v,%v,%v)" (show v) (show o) (show s)
  show (Index _ v i) = printf "%v[%v]" (show v) (show i)
