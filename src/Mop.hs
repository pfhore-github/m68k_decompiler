{-# LANGUAGE GADTs #-}
module Mop where 
import CExpr
import CType 
import qualified Control.Monad.Operational as O
-- Abstract opcode
data Stmt a where
  Block :: [O.Program Stmt ()] -> Stmt ()
  Assign :: Var -> Expr -> Stmt ()
  Modify :: Var -> String ->  Expr -> Stmt ()
  ModifySP :: Int -> Stmt ()
  If :: Expr ->  (O.Program Stmt ()) ->  (O.Program Stmt ()) -> Stmt ()
  IfGoto  :: Expr ->  Int -> Stmt ()
  Return :: Stmt ()
  ExtAsm :: String ->  [Int] -> Stmt ()
  Call :: Expr -> Stmt () 
  SCall :: Int -> Stmt ()
  Jump :: Expr -> Stmt ()
  Goto :: Int -> Stmt ()
  Sys :: Int -> Stmt ()
  For :: Var ->  Expr ->  Bool -> (O.Program Stmt a) -> Stmt ()


assign :: Var -> Expr -> O.Program Stmt ()
assign var val = O.singleton $ Assign var val

assignOp :: String -> Var -> Expr -> O.Program Stmt ()
assignOp op var val = O.singleton $ Modify var op val
{- 
assignOp op (EnvVar t name) val = do
  e <- get
  let( oldv, e') = runStateV (readReg t name) e
  writeReg name (op2 op oldv val)
  put e'
  return []
-}

allocateSP :: Int -> O.Program Stmt ()
allocateSP n = O.singleton $ ModifySP n

deAllocateSP :: Int -> O.Program Stmt ()
deAllocateSP n = O.singleton $ ModifySP (-n)

assignV :: Var -> Var -> O.Program Stmt ()
assignV v1 v2 = assign v1 $ VarValue v2

if_ :: Expr -> O.Program Stmt () -> O.Program Stmt ()
if_ s t = O.singleton $ If s t $ O.singleton $ Block []

ifElse :: Expr -> O.Program Stmt () -> O.Program Stmt ()-> O.Program Stmt ()
ifElse s t f = O.singleton $ If s t f

