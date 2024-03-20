module Env where

import {-# SOURCE #-} CExpr
import {-# SOURCE #-} CStmt
import           CType

class Env a where
  readReg :: CType -> String -> StateV a Expr
  writeReg :: String -> Expr -> StateV a ()
  getSP :: a -> Int
  getSPM :: StateV a Int
  modifySP :: (Int -> Int) -> StateV a ()
  newStmt :: Stmt a -> StateV a ()
  dumpStmt :: StateV a [Stmt a]
  newVar :: CType -> StateV a Var
  saveReg :: StateV a [Stmt a]
  