module AST.Var where
import {-# SOURCE #-} AST.Expr
import AST.Common
import AST.CType




typeOfV :: Var -> CType
typeOfV (RtlReg t _) = t
typeOfV (RtlInc _ v) = typeOfV v
typeOfV (RtlDec _ v) = typeOfV v
typeOfV (RtlMemory v) =
  let t = typeOfE v
   in case t of
        (PTR c) -> c
        _       -> undefined
typeOfV (RtlMemoryI t _ _) = t
typeOfV (RtlMemoryD t _ _) = t
typeOfV (RtlMemoryC t _) = t
typeOfV (RtlMemoryG t _) = t
typeOfV (VarCast t _) = t
typeOfV (RtlBitField t _ _ _) = t