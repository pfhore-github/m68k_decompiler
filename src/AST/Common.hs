{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}
module AST.Common where

import           AST.CType
import {-# SOURCE #-} AST.Expr
import Text.Printf (printf)
import           Data.List



data Op1
  = NOT -- ~ a
  | LNOT -- ! a
  | NEG -- - a
  | Ex1 CType [Char] -- special op
  deriving (Eq)

instance Show Op1 where
  show NOT = "~"
  show LNOT = "!"
  show NEG = "-"
  show (Ex1 _ s) = s

data Op2 =
  AND -- a & b
  | OR -- a | b
  | XOR -- a ^ b
  | ANDN -- a &~ b
  | ORN -- a |~ b
  | NAND -- ~a & b
  | NOR -- ~a | b
  | BTST -- a & 1 << b
  | BSET -- a | 1 << b
  | BFLIP -- a ^ 1 << b
  | BCLR -- a &~ (1 << b)
  | SR -- a >> b
  | SL -- a << b
  | ROR -- a >R> b
  | ROL -- a <R< b
  | LAND -- a && b
  | LOR -- a || b
  | ADD -- a + b
  | ADDC -- carry of (a + b)
  | ADDV -- overflow of (a + b)
  | SUB -- a - b
  | SUBC -- carry of (a - b)
  | SUBV -- overflow of (a - b)
  | MUL -- low of (a * b)
  | MULH -- high of (a * b)
  | DIV -- a / b
  | DIVV -- overflow of a / b
  | MOD -- a % b
  | EQ -- a == b
  | NEQ -- a != b
  | LT -- a > b
  | LE -- a >= b
  | GT -- a < b
  | GE -- a <= b
  | Ex2 CType [Char] -- special op
  deriving (Eq)

instance Show Op2 where
  show AND = "&"
  show OR = "|"
  show XOR = "^"
  show ANDN = "&~"
  show ORN = "|~"
  show NAND = "~&"
  show NOR = "~|"
  show BTST = "btst"
  show BSET = "bset"
  show BFLIP = "bflip"
  show BCLR = "bclr"
  show SR = ">>"
  show SL = "<<"
  show ROR = "ror"
  show ROL = "rol"
  show LAND = "&&"
  show LOR = "||"
  show ADD = "+"
  show ADDC = "addc"
  show ADDV = "addv"
  show SUB = "-"
  show SUBC = "subc"
  show SUBV = "subv"
  show MUL = "*"
  show MULH = "*H"
  show DIV = "/"
  show DIVV = "divV"
  show MOD = "%"
  show AST.Common.EQ = "=="
  show AST.Common.NEQ = "!="
  show AST.Common.LT = "<"
  show AST.Common.LE = "<="
  show AST.Common.GT = ">"
  show AST.Common.GE = ">="
  show (Ex2 _ s) = s


data Expr
  = ExprVar Var -- variable
  | ExprAddr Var -- & var
  | ExprBool Bool -- true/false
  | ExprPtr CType Integer -- imm address
  | ExprInt Bool Integer -- integer imm
  | ExprCast CType Expr -- (CType)expr
  | ExprOp1 Op1 Expr -- (op1)exp
  | ExprOp2 Op2 Expr Expr -- a (op2) b
  | ExprOpN CType String [Expr] -- a (op2) b
  | ExprSel Expr Expr Expr -- a ? b : c
  | ExprJoin Expr Expr -- (a << N | b)
  | ExprCondCC Int -- use last cc
  deriving (Eq)

data Var
  = RtlReg CType [Char] -- fixed register
  | RtlInc Bool Var -- ++var(True) or var++(False)
  | RtlDec Bool Var -- --var(True) or var--(False)
  | RtlMemory Expr -- *var
  | RtlMemoryI CType Expr Int -- var->offset
  | RtlMemoryD CType Expr Expr -- var[index]
  | RtlMemoryC CType Int -- ROM const
  | RtlMemoryG CType Int -- lowmem global
  | VarCast CType Var -- (type)var [left-value cast]
  | RtlBitField CType Var Int Int -- (var >> offset) & (1<<size-1)
  deriving (Eq)

data JumpTarget
  = TargetAbsolute Int
  | TargetIndirect Expr
  deriving (Eq)

data Stmt =
  StmtAssign Var Expr -- (dst) = (src)
 | StmtAssignOp Op2 Var Expr -- (dst) (op2)= (src)
 | StmtIf Expr [Stmt] [Stmt] -- if( exp ) { stmt1;} 
 | StmtAsm [Char] [Expr]
 | StmtPush Expr
 | StmtPop Var
 | StmtAdjustSP Int
 | StmtReturn
 | StmtGoto JumpTarget 
 | StmtCall JumpTarget
 | StmtEmpty

class Term a where
  getExpr :: a -> Expr


instance Show Expr where
  show (ExprVar v) = show v
  show (ExprAddr v) = printf "&(%s)" $ show v
  show (ExprBool True) = "true"
  show (ExprBool False) = "true"
  show (ExprPtr t v) = printf "(%v*)%08x" t v
  show (ExprInt True v) = printf "%d" v
  show (ExprInt False v) = printf "%xU" v
  show (ExprCast t v) = printf "(%v)%s" t $ show v
  show (ExprOp1 op1 v) = printf "%s (%s)" (show op1) (show v)
  show (ExprOp2 op2 a b) = (show2 op2) a b
  show (ExprOpN _ s as) = printf "%s(%s)" s $ intercalate "," $ map show as
  show (ExprSel e a b) = printf "(%s) ? (%s) : (%s)" (show e) (show a) (show b)
  show (ExprJoin a b) = printf "(%s, %s)" (show a) (show b)
  show (ExprCondCC cc) = printf "cond(%d)" cc

instance Term Expr where
  getExpr e = e

instance Show Var where
  show (RtlReg (PTR VOID) s) = printf "%s" s
  show (RtlReg (PTR p) s) = printf "(%v*)%s" p s
  show (RtlReg INT8 s) = printf "%v.Bs" s
  show (RtlReg UINT8 s) = printf "%v.B" s
  show (RtlReg INT16 s) = printf "%v.Ws" s
  show (RtlReg UINT16 s) = printf "%v.W" s
  show (RtlReg INT32 s) = printf "%v.s" s
  show (RtlReg UINT32 s) = printf "%v" s
  show (RtlReg BOOL s) = printf "%v" s
  show (RtlReg t s) = printf "%s_%v" s t
  show (RtlInc True s) = printf "++(%s)" $ show s
  show (RtlInc False s) = printf "(%s)++" $ show s
  show (RtlDec True s) = printf "--(%s)" $ show s
  show (RtlDec False s) = printf "(%s)--" $ show s
  show (RtlMemory v) = printf "*(%s)" $ show v
  show (RtlMemoryI (PTR VOID) v i) = printf "%s->_%d" (show v) i
  show (RtlMemoryI t v i) = printf "reinterpret_cast<%v>(%s->_%d)" t (show v) i
  show (RtlMemoryD t v o) = printf "reinterpret_cast<%v*>(%s)[%s]" t (show v) (show o)
  show (RtlMemoryC t c) = printf "(const %v)C_%06x" t c
  show (RtlMemoryG t c) = printf "(%v)G_%06x" t c
  show (VarCast t v) = printf "static_cast<%v>(%s)" t $ show v
  show (RtlBitField _ v i s) = printf "%v._%d_%d" (show v) i (i+s)

opPrioity :: Num a => Op2 -> a
opPrioity MUL = 3
opPrioity DIV = 3
opPrioity MOD = 3
opPrioity ADD = 4
opPrioity SUB = 4
opPrioity SR = 5
opPrioity SL = 5
opPrioity _ = -1

instance Show Stmt where
  show (StmtAssign dst src) = printf "%s = (%s)" (show dst) (show src)
  show (StmtAssignOp BSET dst src) =
    printf "%s |= 1 << (%s)" (show dst) (show src)
  show (StmtAssignOp BCLR dst src) =
    printf "%s |= ~(1 << (%s))" (show dst) (show src)
  show (StmtAssignOp BFLIP dst src) =
    printf "%s ^= 1 << (%s)" (show dst) (show src)
  show (StmtAssignOp op dst src) 
    | opPrioity op > 0 = printf "%s %s= (%s)" (show dst) (show op)(show src)
    | otherwise = printf "%s(%s, %s)" (show op) (show dst) (show src)
  show (StmtAsm s vars) =
    printf "%s(%s)" s $ intercalate "," $ map show vars
  show (StmtAdjustSP n) = printf "adjust_sp(%d)" n
  show (StmtPush e) = printf "push (%s)" $ show e
  show (StmtPop v) = printf "pop %s" $ show v
  show (StmtGoto (TargetAbsolute n)) = printf "goto _%06x" $ n
  show (StmtGoto (TargetIndirect v)) = printf "goto (%s)" $ (show v)
  show (StmtCall (TargetAbsolute n)) = printf "call _%06x" $ n
  show (StmtCall (TargetIndirect v)) = printf "call (%s)" $ (show v)
  show (StmtReturn) = "return"
  show (StmtIf cond ts []) =
    printf "if (%s) { %s }" (show cond) $ intercalate ";" $ map show ts
  show (StmtIf cond ts fs) =
    printf
      "if (%s) { %s } else { %s }"
      (show cond) 
      (intercalate ";" $ map show ts)
      (intercalate ";" $ map show fs)
  show StmtEmpty = ";"

instance Term Var where
  getExpr e = ExprVar e

uintE :: (Integral a) => a -> Expr
uintE i = ExprInt False $ fromIntegral i

intE :: (Integral a) => a -> Expr
intE i = ExprInt True $ fromIntegral i

boolE :: (Eq a, Num a) => a -> Expr
boolE v = ExprBool (v /= 0)