-- -*- Haskell -*-
module CStmt where
import {-# SOURCE #-} CExpr
data CStmt
  = Block [CStmt]
  | Assign Var Expr
  | Modify Var String Expr
  | Trap (Maybe Int)
  | If Expr CStmt CStmt
  | IfGoto Expr Int
  | Return
  | IReturn
  | ExtAsm String Int
  | Call Expr
  | SCall Int
  | Jump Expr
  | Goto Int
  | Sys Int
  | For Var Expr Expr CStmt CStmt
  | IfElse [(Expr, CStmt)] CStmt
  | While Expr CStmt
  | DoWhile CStmt Expr
  | Break
  | Continue
  
