{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE InstanceSigs #-}

module CStmt where

import           CExpr
import           Control.Monad.State
import Text.Printf
import Env



data StateV c a
  = Known a
  | FromEnv (State c a)

runStateV :: StateV b a -> b -> (a, b)
runStateV (Known a) e = (a, e)
runStateV (FromEnv s) e = runState s e

instance Functor (StateV c) where
  fmap f (Known a) = Known (f a)
  fmap f (FromEnv e) = FromEnv (f <$> e)

instance Applicative (StateV c) where
  pure = Known
  (Known f) <*> (Known a) = Known (f a)
  (FromEnv f) <*> (Known a) = FromEnv (do
    f' <- f
    return $ f' a)
  (Known f) <*> (FromEnv e) = FromEnv (f <$> e)
  (FromEnv f) <*> (FromEnv a) = FromEnv (do
    f' <- f
    f' <$> a)

  (Known _) *> (Known b) = Known b
  (FromEnv a) *> (Known b) = FromEnv (do
    _ <- a
    return b)
  (Known _) *> (FromEnv b) = FromEnv b
  (FromEnv a) *> (FromEnv b) = FromEnv (do
    _ <- a
    b)

instance Monad (StateV c) where
  (>>=) :: StateV c a -> (a -> StateV c b) -> StateV c b
  (Known a) >>= f = f a
  (FromEnv a) >>= f =
    let e2 = do
          a' <- a
          let c = f a'
          case c of
            Known c' -> state (c',)
            FromEnv c' -> c'
     in FromEnv e2


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

stackMove :: Num a => p -> a
stackMove _ = 0

readVar :: (Env c) => Var -> StateV c Expr
readVar (EnvVar t name) = readReg t name
readVar v = return $ VarValue v

assign :: Env a => Var -> Expr -> StateV a ()
assign (EnvVar _ name) val = do
  writeReg name val

assign var val = do
  newStmt $ Assign var val


assignOp :: Env c => String -> Var -> Expr -> StateV c ()
assignOp op (EnvVar t name) val = do
  oldv <- readReg t name
  writeReg name (op2 op oldv val)

assignOp op var val = do
  newStmt $ Modify var op val

allocateSP :: Env c => Int -> StateV c ()
allocateSP n = do
  modifySP (+n)

deAllocateSP :: Env c => Int -> StateV c ()
deAllocateSP n = do  modifySP (+ (-n))


assignV :: (Env a) => Var -> Var -> StateV a ()
assignV v1 v2 = assign v1 $ VarValue v2

mapB :: Monad m => (t -> m ()) -> [t] -> m ()
mapB _ [] = do return ()
mapB f (x:ox) = do
  f x
  mapB f ox


  


fromElse :: PrintfArg t => Maybe t -> String
fromElse (Just a) = printf "else { %v }" a
fromElse Nothing  = ""

stmtNop :: (Env a) => StateV a ()
stmtNop = do return ()

swap :: Expr -> Expr
swap = Op1 "swap"

if_ :: (Env a) => Expr -> Block a -> Block a
if_ s t = newStmt $ If s t Nothing
ifElse :: (Env a) => Expr -> Block a -> Block a -> Block a
ifElse s t f = newStmt $ If s t (Just f)
