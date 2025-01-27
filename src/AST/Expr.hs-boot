module AST.Expr where
import {-# SOURCE #-} AST.Common
import AST.CType (CType)

show2 :: Op2 -> (Expr -> Expr -> String)
typeOfE :: Expr -> CType