{-# LANGUAGE GADTs #-}
module AST.Common where
import AST.CType
import M68k.LongDouble
data Op1
  = NOT -- ~ a
  | LNOT -- ! a
  | NEG -- - a
  | Ex1 CType [Char] -- special op

data Op2
  = AND -- a & b
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

data Expr
  = ExprVar Var -- variable
  | ExprAddr Var -- & var
  | ExprBool Bool -- true/false
  | ExprPtr CType Integer -- imm address
  | ExprInt Bool Integer -- integer imm
  | ExprFlt LongDouble -- integer imm
  | ExprCast CType Expr -- (CType)expr
  | ExprOp1 Op1 Expr -- (op1)exp
  | ExprOp2 Op2 Expr Expr -- a (op2) b
  | ExprOpN CType String [Expr] -- a (op2) b
  | ExprSel Expr Expr Expr -- a ? b : c
  | ExprJoin Expr Expr -- (a << N | b)
  | ExprCondCC Int -- use last cc

data Var
  = GlobalVar CType String -- affects outside world 
  | EnvVar CType String -- only affects env
  | TmpVar CType String -- only affects in scope
  | VarInc Bool Var -- ++var(True) or var++(False)
  | VarDec Bool Var -- --var(True) or var--(False)
  | VarMemory Expr -- *var
  | VarMember CType Expr Int -- var->offset
  | VarArray CType Expr Expr -- var[index]
  | VarROM CType Int -- ROM const
  | VarRAM CType Int -- lowmem global
  | VarCast CType Var -- (type)var [left-value cast]
  | VarBitField CType Var Int Int -- (var >> offset) & (1<<size-1)

data JumpTarget
  = TargetAbsolute Int
  | TargetIndirect Expr

data Stmt =
  StmtAssign Var Expr -- (dst) = (src)
 | StmtAssignOp Op2 Var Expr -- (dst) (op2)= (src)
 | StmtIf Expr [Stmt] [Stmt] -- if( exp ) { stmt1;} 
 | StmtWhile Expr [Stmt]  -- while( exp ) { stmt1;} 
 | StmtAsm [Char] [Expr]
 | StmtPush Expr
 | StmtPop Var
 | StmtAdjustSP Int
 | StmtReturn
 | StmtGoto JumpTarget 
 | StmtCall JumpTarget
 | StmtEmpty