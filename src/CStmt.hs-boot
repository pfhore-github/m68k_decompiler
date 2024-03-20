-- -*- Haskell -*-
module CStmt where
import {-# SOURCE #-} CExpr
import           Control.Monad.State
type Block a = StateV a () 
data Stmt a
  = Assign Var Expr
  | Modify Var String Expr
  | Trap (Maybe Int)
  | If Expr (Block a) (Maybe (Block a))
  | IfGoto Expr Int
  | Return
  | IReturn
  | ExtAsm String Int
  | BreakPoint Int
  | Call Expr
  | SCall Int
  | Jump Expr
  | Goto Int
  | Sys Int
  | For (Stmt a) Expr (Stmt a) (Block a)
  | IfElse [(Expr, Block a)] (Maybe (Block a))
  | While Expr (Block a)
  | DoWhile (Block a) Expr
  | Break
  | Continue

data StateV c a
  = Known a
  | FromEnv (State c a)
