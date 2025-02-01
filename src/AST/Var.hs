module AST.Var where
import {-# SOURCE #-} AST.Expr
import AST.Common
import AST.CType




typeOfV :: Var -> CType
typeOfV (GlobalVar t _) = t
typeOfV (EnvVar t _) = t
typeOfV (TmpVar t _) = t
typeOfV (VarInc _ v) = typeOfV v
typeOfV (VarDec _ v) = typeOfV v
typeOfV (VarMemory v) =
  let t = typeOfE v
   in case t of
        (PTR c) -> c
        _       -> undefined
typeOfV (VarMember t _ _) = t
typeOfV (VarArray t _ _) = t
typeOfV (VarROM t _) = t
typeOfV (VarRAM t _) = t
typeOfV (VarCast t _) = t
typeOfV (VarBitField t _ _ _) = t