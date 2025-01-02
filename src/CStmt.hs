{-# LANGUAGE ExistentialQuantification #-}


module CStmt where

import           CType
import           CExpr
import           Control.Monad.State
import           Env
import           Text.Printf
import qualified Control.Monad.Operational as O


doRead :: (Env a) => StateV a Expr -> State a Expr
doRead f = do 
  e <- get
  let (v, e') = runStateV f e
  put e'
  return v

doWrite :: StateV b () -> State b ()
doWrite f = do 
  e <- get
  put $ snd $ runStateV f e

doWriteInEnv :: State b () -> StateV b ()
doWriteInEnv = FromEnv



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
  deriving (Show)



stackMove :: Num a => p -> a
stackMove _ = 0



mapB :: Monad m => (t -> m ()) -> [t] -> m ()
mapB _ [] = do
  return ()
mapB f (x:ox) = do
  f x
  mapB f ox

fromElse :: PrintfArg t => Maybe t -> String
fromElse (Just a) = printf "else { %v }" a
fromElse Nothing  = ""

swap :: Expr -> Expr
swap = Op1 "swap"

{- 
readVar :: (Env c) => Var -> StateV c Expr
readVar (EnvVar t name) = readReg t name
readVar v               = return $ VarValue v
-}
