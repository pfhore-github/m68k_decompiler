-- -*- haskell -*-
module CExpr where
import CType

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
  | GVar CType Int -- Low Global
  | CVar CType Int -- PC realative
  | TVar CType Int -- temporaly for C
  | SPVar CType String  -- Special Register(cannot merge)
  | SVar CType Int -- Stack variable
  | Deref Expr -- * var
  | Member CType Var Int -- var.member
  | PMember CType Expr Int -- ptr->member
  | BitField CType Var Int Int -- var.member_m (bit field)
  | BitFieldX CType Var Expr Expr -- (non-supported)
  | Index CType Expr Expr -- var[index]

