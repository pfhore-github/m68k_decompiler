-- -*- haskell -*-
module CExpr where
import CType
import Control.Monad.State

data Expr
  = Const CType Int
  | Arg CType String -- dummy 
  | VarValue Var -- var(value)
  | VarAddr Var -- &var
  | Cast CType Expr -- (type)v
  | Op1 String Expr  -- !v/~v/-v etc
  | IncDec Bool Bool Var -- isPost, isInc, var; var++/++var
  | Op2 Expr String Expr -- v1 op v2
  | CondExpr Expr Expr Expr -- c ? v1 : v2
  | Expr2 Expr Expr

data Var
  = EnvVar CType String  -- reg var
  | GVar CType String -- Low Global
  | TVar CType Int -- temporaly for C
  | SVar CType Int -- Stack variable
  | Deref Expr -- * var
  | Member CType Var Int -- var.member
  | PMember CType Expr Int -- ptr->member
  | BitField CType Var Int Int -- var.member_m (bit field)
  | BitFieldX CType Var Expr Expr -- (non-supported)
  | Index CType Expr Expr -- var[index]

data StateV c a
  = Known a
  | FromEnv (State c a)