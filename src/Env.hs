module Env where

import {-# SOURCE #-} CStmt
import           CType
import           CExpr (Expr, Var, StateV)
import Control.Monad.State

class Env a where
  readReg :: CType -> String -> State a Expr
  writeReg :: String -> Expr -> State a ()
  readStack :: CType -> Int -> State a Expr
  getSP :: a -> Int
  getSPM :: State a Int
  modifySP :: (Int -> Int) -> State a ()
  newVar :: CType -> State a Var
  saveReg :: StateV a [CStmt]
  