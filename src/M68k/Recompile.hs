{-# LANGUAGE GADTs #-}

module M68k.Recompile where
    -- decompile 2st stage

import           CExpr
import qualified CStmt                     as C
import           CType
import qualified Control.Monad.Operational as O
import           Control.Monad.State
import           Env
import           M68k.Env
import           Mop

readVar :: Var -> State MEnv Expr
readVar (EnvVar t v) = do
  readReg t v
readVar (Deref v) = do
  v' <- readExp v
  readVar $ deref v'
readVar (SVar t i) = do
  sp <- getSPM
  readStack t (i + sp)
readVar (PMember t p i) = do
  var' <- readExp p
  readVar $ PMember t var' i
readVar (Index t v i) = do
  var' <- readExp v
  i' <- readExp i
  readVar $ Index t var' i'
readVar v = return $ VarValue v

readExp :: Expr -> State MEnv Expr
readExp (VarValue v) = readVar v
readExp (Cast t v) = do
  v' <- readExp v
  return $ cast t v'
readExp (Op1 op v) = do
  v' <- readExp v
  return $ op1 op v'
readExp (IncDec post inc (EnvVar t@(INT _ _) var)) = do
  v <- readReg t var
  let op =
        if inc
          then ($+#)
          else ($-#)
  let v' = op v 1
  writeReg var v'
  return
    (if post
       then v'
       else v)
readExp (IncDec post inc (EnvVar (PTR t) var)) = do
  let sz = sizeOf t
  let op =
        if inc
          then ($+#)
          else ($-#)
  v <- readReg t var
  let v' = op v sz
  writeReg var v'
  return
    (if post
       then v'
       else v)
readExp (Op2 v1 op v2) = do
  v1' <- readExp v1
  v2' <- readExp v2
  return $ op2 op v1' v2'
readExp (CondExpr e t f) = do
  e' <- readExp e
  t' <- readExp t
  f' <- readExp f
  return $ condExpr e' t' f'
readExp (Expr2 h l) = do
  h' <- readExp h
  l' <- readExp l
  return $ Expr2 h' l'
readExp v = return v

runStmt :: O.Program Stmt () -> State MEnv [C.CStmt]
runStmt =
  let eval :: O.ProgramView Stmt () -> State MEnv [C.CStmt]
      eval (O.Return _) = do
        return []
      eval (Assign var val O.:>>= k) = do
        e' <- readExp val
        case var of
          EnvVar _ v -> do
            writeReg v e'
            runStmt $ k ()
          _ -> do
            others <- runStmt $ k ()
            return $ C.Assign var e' : others
      eval (Modify var op val O.:>>= k) = do
        e' <- readExp val
        case var of
          EnvVar t v -> do
            oldv <- readReg t v
            writeReg v (op2 op oldv e')
            runStmt $ k ()
          _ -> do
            others <- runStmt $ k ()
            return $ C.Modify var op e' : others
      eval (ModifySP v O.:>>= k) = do
        modifySP (+ v)
        runStmt $ k ()
      eval (If cond t f O.:>>= k) = do
        let if__ :: Expr -> C.CStmt -> C.CStmt -> C.CStmt
            if__ (Const BOOL 0) _ f' = f'
            if__ (Const BOOL 1) t' _ = t'
            if__ c t' f'             = C.If c t' f'
        cond' <- readExp cond
        t' <- runStmt t
        f' <- runStmt f
        others <- runStmt $ k ()
        return $ if__ cond' (C.Block t') (C.Block f') : others
      eval _ = do
        return []
   in eval . O.view

decompile :: O.Program Stmt () -> MEnv -> ([C.CStmt], MEnv)
decompile c = runState (runStmt c)
