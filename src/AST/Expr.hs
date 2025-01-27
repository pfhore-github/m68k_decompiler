{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module AST.Expr where

import           AST.Common
import           AST.CType
import           AST.Var
import           Data.Bits   (complement, (.&.), (.<<.), (.>>.), (.^.), (.|.))
import           Data.Int    (Int32)
import           Data.Word   (Word32)
import           Text.Printf (printf)

typeOfE :: Expr -> CType
typeOfE (ExprVar v)           = typeOfV v
typeOfE (ExprAddr v)          = PTR $ typeOfV v
typeOfE (ExprPtr t _)         = PTR t
typeOfE (ExprBool _)          = BOOL
typeOfE (ExprInt True _)      = INT32
typeOfE (ExprInt False _)     = UINT32
typeOfE (ExprCast t _)        = t
typeOfE (ExprOp1 LNOT _)      = BOOL
typeOfE (ExprOp1 (Ex1 t _) _) = t
typeOfE (ExprOp1 _ v)         = typeOfE v
typeOfE (ExprJoin a _)    = joinType (typeOfE a)
typeOfE (ExprOp2 ADDC _ _)    = BOOL

show2 :: Op2 -> (Expr -> Expr -> String)
show2 AND            = \a b -> printf "(%s) & (%s)" (show a) (show b)
show2 OR             = \a b -> printf "(%s) | (%s)" (show a) (show b)
show2 XOR            = \a b -> printf "(%s) ^ (%s)" (show a) (show b)
show2 ANDN           = \a b -> printf "(%s) &~ (%s)" (show a) (show b)
show2 ORN            = \a b -> printf "(%s) |~ (%s)" (show a) (show b)
show2 NAND           = \a b -> printf "~(%s) & (%s)" (show a) (show b)
show2 NOR            = \a b -> printf "~(%s) | (%s)" (show a) (show b)
show2 BTST           = \a b -> printf "(%s) & 1 << (%s)" (show a) (show b)
show2 BSET           = \a b -> printf "(%s) | 1 << (%s)" (show a) (show b)
show2 BFLIP          = \a b -> printf "(%s) ^ 1 << (%s)" (show a) (show b)
show2 BCLR           = \a b -> printf "(%s) &~ 1 << (%s)" (show a) (show b)
show2 SR             = \a b -> printf "(%s) >> (%s)" (show a) (show b)
show2 SL             = \a b -> printf "(%s) << (%s)" (show a) (show b)
show2 ROR            = \a b -> printf "ror(%s, %s)" (show a) (show b)
show2 ROL            = \a b -> printf "rol(%s, %s)" (show a) (show b)
show2 LAND           = \a b -> printf "(%s) && (%s)" (show a) (show b)
show2 LOR            = \a b -> printf "(%s) || (%s)" (show a) (show b)
show2 ADD            = \a b -> printf "(%s) + (%s)" (show a) (show b)
show2 ADDC           = \a b -> printf "add_carry(%s, %s)" (show a) (show b)
show2 ADDV           = \a b -> printf "add_overflow(%s, %s)" (show a) (show b)
show2 SUB            = \a b -> printf "(%s) - (%s)" (show a) (show b)
show2 SUBC           = \a b -> printf "sub_carry(%s, %s)" (show a) (show b)
show2 SUBV           = \a b -> printf "sub_overflow(%s, %s)" (show a) (show b)
show2 MUL            = \a b -> printf "(%s) * (%s)" (show a) (show b)
show2 MULH           = \a b -> printf "((%s) * (%s)) >> 32" (show a) (show b)
show2 DIV            = \a b -> printf "(%s) / (%s)" (show a) (show b)
show2 DIVV           = \a b -> printf "div_overflow(%s, %s)" (show a) (show b)
show2 MOD            = \a b -> printf "(%s) % (%s)" (show a) (show b)
show2 AST.Common.EQ  = \a b -> printf "(%s) == (%s)" (show a) (show b)
show2 AST.Common.NEQ = \a b -> printf "(%s) != (%s)" (show a) (show b)
show2 AST.Common.LT  = \a b -> printf "(%s) > (%s)" (show a) (show b)
show2 AST.Common.LE  = \a b -> printf "(%s) >= (%s)" (show a) (show b)
show2 AST.Common.GT  = \a b -> printf "(%s) < (%s)" (show a) (show b)
show2 AST.Common.GE  = \a b -> printf "(%s) <= (%s)" (show a) (show b)
show2 (Ex2 _ s)      = \a b -> printf "%s(%s, %s)" s (show a) (show b)

def1 :: (Term a1) => Op1 -> (a1 -> Expr)
def1 p = \a -> ExprOp1 p (getExpr a)

def2 :: (Term a1, Term a2) => Op2 -> (a1 -> a2 -> Expr)
def2 p = \a b -> ExprOp2 p (getExpr a) (getExpr b)

cast :: Term a => CType -> a -> Expr
cast t v = ExprCast t (getExpr v)

infix 9 $<->

($<->) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($<->) a b = ExprJoin (getExpr a) (getExpr b)

bitTest :: (Term a1, Term a2) => a1 -> a2 -> Expr
bitTest = def2 AST.Common.BTST

bitFlip :: (Term a1, Term a2) => a1 -> a2 -> Expr
bitFlip = def2 AST.Common.BFLIP

bitClear :: (Term a1, Term a2) => a1 -> a2 -> Expr
bitClear = def2 AST.Common.BCLR

bitSet :: (Term a1, Term a2) => a1 -> a2 -> Expr
bitSet = def2 AST.Common.BSET

infixl 7 $*, $/, $%

($*) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($*) = def2 AST.Common.MUL

mulH :: (Term a1, Term a2) => a1 -> a2 -> Expr
mulH = def2 AST.Common.MULH

($/) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($/) = def2 AST.Common.DIV

divV :: (Term a1, Term a2) => a1 -> a2 -> Expr
divV = def2 AST.Common.DIVV

($%) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($%) = def2 AST.Common.MOD

infixl 6 $+, $-

($+) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($+) = def2 AST.Common.ADD

addV :: (Term a1, Term a2) => a1 -> a2 -> Expr
addV = def2 AST.Common.ADDV

addC :: (Term a1, Term a2) => a1 -> a2 -> Expr
addC = def2 AST.Common.ADDC

($-) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($-) = def2 AST.Common.ADD

subV :: (Term a1, Term a2) => a1 -> a2 -> Expr
subV = def2 AST.Common.SUBV

subC :: (Term a1, Term a2) => a1 -> a2 -> Expr
subC = def2 AST.Common.SUBC

neg :: (Term a1) => a1 -> Expr
neg = def1 AST.Common.NEG

bNot :: (Term a1) => a1 -> Expr
bNot = def1 AST.Common.NOT

lNot :: (Term a1) => a1 -> Expr
lNot = def1 AST.Common.LNOT

infixl 5 $<<, $>>

($<<) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($<<) = def2 AST.Common.SL

ror :: (Term a1, Term a2) => a1 -> a2 -> Expr
ror = def2 AST.Common.ROR

($>>) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($>>) = def2 AST.Common.SR

rol :: (Term a1, Term a2) => a1 -> a2 -> Expr
rol = def2 AST.Common.ROR

infix 4 $&, $|, $^

($&) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($&) = def2 AST.Common.AND

($|) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($|) = def2 AST.Common.OR

($^) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($^) = def2 AST.Common.XOR

infix 3 $==, $!=, $<, $<=, $>, $>=

($==) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($==) = def2 AST.Common.EQ

($!=) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($!=) = def2 AST.Common.NEQ

($<) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($<) = def2 AST.Common.LT

($<=) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($<=) = def2 AST.Common.LE

($>) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($>) = def2 AST.Common.GT

($>=) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($>=) = def2 AST.Common.GE

infixl 1 $||

infixl 2 $&&

($||) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($||) = def2 AST.Common.LOR

($&&) :: (Term a1, Term a2) => a1 -> a2 -> Expr
($&&) = def2 AST.Common.LAND

sel :: (Term a1, Term a2, Term a3) => a1 -> a2 -> a3 -> Expr
sel ex t f = ExprSel (getExpr ex) (getExpr t) (getExpr f)

deref :: (Term a1) => a1 -> Var
deref v = RtlMemory (getExpr v)

evalE :: Expr -> Expr
evalE (ExprCast UINT8 (ExprInt _ c)) = ExprInt False $ c .&. 0xFF
evalE (ExprCast UINT8 (ExprJoin a b)) 
  | typeOfE a == UINT8 = b
  | typeOfE a == INT8 = cast INT8 b
evalE (ExprCast INT8 (ExprInt _ c)) =
  let c' = c .&. 0xff
   in ExprInt True $
      if c' > 0x7f
        then c' - 0x100
        else c'
evalE (ExprCast INT8 (ExprJoin a b)) 
  | typeOfE a == INT8 = b
  | typeOfE a == UINT8 = cast UINT8 b
evalE (ExprCast INT16 (ExprInt _ c)) = ExprInt False $ c .&. 0xffff
evalE (ExprCast INT16 (ExprJoin a b)) 
  | typeOfE a == INT16 = b
  | typeOfE a == UINT16 = cast UINT16 b
evalE (ExprCast UINT16 (ExprInt _ c)) =
  let c' = c .&. 0xffff
   in ExprInt True $
      if c' > 0x7fff
        then c' - 0x10000
        else c'
evalE (ExprCast UINT16 (ExprJoin a b)) 
  | typeOfE a == UINT16 = b
  | typeOfE a == INT16 = cast UINT16 b
evalE (ExprCast INT32 (ExprInt _ c)) = ExprInt False c
evalE (ExprCast UINT32 (ExprInt _ c)) =
  ExprInt True $
  if c > 0x7fffffff
    then c - 0x100000000
    else c
evalE (ExprCast BOOL (ExprInt _ c)) = ExprBool (c /= 0)
evalE (ExprOp1 AST.Common.NOT (ExprInt t c)) = ExprInt t $ complement c
evalE (ExprOp1 AST.Common.NEG (ExprInt t c)) = ExprInt t $ negate c
evalE (ExprOp1 AST.Common.LNOT (ExprBool t)) = ExprBool (not t)
evalE (ExprOp1 AST.Common.LNOT (ExprInt _ c)) = ExprBool (c == 0)
evalE (ExprOp1 AST.Common.LNOT (ExprOp2 AST.Common.EQ a b)) = a $!= b
evalE (ExprOp1 AST.Common.LNOT (ExprOp2 AST.Common.NEQ a b)) = a $== b
evalE (ExprOp1 AST.Common.LNOT (ExprOp2 AST.Common.LT a b)) = a $>= b
evalE (ExprOp1 AST.Common.LNOT (ExprOp2 AST.Common.LE a b)) = a $> b
evalE (ExprOp1 AST.Common.LNOT (ExprOp2 AST.Common.GT a b)) = a $<= b
evalE (ExprOp1 AST.Common.LNOT (ExprOp2 AST.Common.GE a b)) = a $< b
evalE (ExprOp1 op v) = (ExprOp1 op $ evalE v)
evalE (ExprOp2 AST.Common.BTST (ExprInt _ v1) (ExprInt _ v2)) =
  boolE $ (v1 .>>. (fromIntegral v2)) .&. 1
evalE (ExprOp2 AST.Common.BTST a (ExprInt _ v2)) =
  cast BOOL $ a $& (uintE $ (1 :: Integer) .<<. (fromIntegral v2))
evalE (ExprOp2 AST.Common.BSET (ExprInt s v1) (ExprInt _ v2)) =
  ExprInt s $ v1 .|. (1 .<<. (fromIntegral v2))
evalE (ExprOp2 AST.Common.BSET a (ExprInt _ v2)) =
  a $| (uintE $ (1 :: Integer) .<<. (fromIntegral v2))
evalE (ExprOp2 AST.Common.BFLIP (ExprInt s v1) (ExprInt _ v2)) =
  ExprInt s $ v1 .^. (1 .<<. (fromIntegral v2))
evalE (ExprOp2 AST.Common.BFLIP a (ExprInt _ v2)) =
  a $^ (uintE $ (1 :: Integer) .<<. (fromIntegral v2))
evalE (ExprOp2 AST.Common.BCLR (ExprInt s v1) (ExprInt _ v2)) =
  ExprInt s $ v1 .&. (complement $ 1 .<<. (fromIntegral v2))
evalE (ExprOp2 AST.Common.BCLR a (ExprInt _ v2)) =
  a $& (uintE $ complement $ ((1 :: Integer) .<<. (fromIntegral v2)))
evalE (ExprOp2 AST.Common.SR (ExprInt s v1) (ExprInt _ v2))
  | s == True = doSr (fromIntegral v1 :: Int32) v2
  | s == False = doSr (fromIntegral v1 :: Word32) v2
  where
    doSr val sc = ExprInt s $ fromIntegral $ val .>>. (fromIntegral sc)
evalE (ExprOp2 AST.Common.SL (ExprInt t v1) (ExprInt _ v2)) =
  ExprInt t $ v1 .<<. (fromIntegral v2)
evalE (ExprOp2 AST.Common.AND (ExprInt _ v1) (ExprInt _ v2)) = uintE $ v1 .&. v2
evalE (ExprOp2 AST.Common.OR (ExprInt _ v1) (ExprInt _ v2)) = uintE $ v1 .|. v2
evalE (ExprOp2 AST.Common.XOR (ExprInt _ v1) (ExprInt _ v2)) = uintE $ v1 .^. v2
evalE (ExprOp2 AST.Common.ANDN (ExprInt _ v1) (ExprInt _ v2)) =
  uintE $ v1 .&. complement v2
evalE (ExprOp2 AST.Common.ORN (ExprInt _ v1) (ExprInt _ v2)) =
  uintE $ v1 .|. complement v2
evalE (ExprOp2 AST.Common.NAND (ExprInt _ v1) (ExprInt _ v2)) =
  uintE $ (complement v1) .&. v2
evalE (ExprOp2 AST.Common.NOR (ExprInt _ v1) (ExprInt _ v2)) =
  uintE $ (complement v1) .|. v2
evalE (ExprOp2 AST.Common.ADD (ExprInt _ v1) (ExprInt _ v2)) = intE $ v1 + v2
evalE (ExprOp2 AST.Common.SUB (ExprInt _ v1) (ExprInt _ v2)) = intE $ v1 - v2
evalE (ExprOp2 AST.Common.MUL (ExprInt _ v1) (ExprInt _ v2)) = intE $ v1 * v2
evalE (ExprOp2 AST.Common.DIV (ExprInt _ v1) (ExprInt _ v2)) = intE $ v1 `div` v2
evalE (ExprOp2 AST.Common.MOD (ExprInt _ v1) (ExprInt _ v2)) = intE $ v1 `mod` v2
evalE (ExprOp2 AST.Common.EQ (ExprInt _ v1) (ExprInt _ v2)) = ExprBool $ v1 == v2
evalE (ExprOp2 AST.Common.NEQ (ExprInt _ v1) (ExprInt _ v2)) = ExprBool $ v1 /= v2
evalE (ExprOp2 AST.Common.LT (ExprInt _ v1) (ExprInt _ v2)) = ExprBool $ v1 < v2
evalE (ExprOp2 AST.Common.LE (ExprInt _ v1) (ExprInt _ v2)) = ExprBool $ v1 <= v2
evalE (ExprOp2 AST.Common.GT (ExprInt _ v1) (ExprInt _ v2)) = ExprBool $ v1 > v2
evalE (ExprOp2 AST.Common.GE (ExprInt _ v1) (ExprInt _ v2)) = ExprBool $ v1 >= v2
evalE (ExprOp2 op v1 v2) = (ExprOp2 op (evalE v1) (evalE v2))
evalE (ExprSel (ExprBool b) t f) = if b then t else f
evalE e = e
