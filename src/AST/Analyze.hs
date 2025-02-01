module AST.Analyze where


import           AST.Env
import AST.Common 
import Control.Monad.State
doAst1 :: (Env a) => Stmt -> State a Stmt
doAst1 (StmtAssign var@(EnvVar _ _) e) = do
  e' <- evalValue e
  setValue var e'
  return StmtEmpty
doAst1 (StmtAssign var e) = do
  e' <- evalValue e
  return (StmtAssign var e')
doAst1 (StmtAssignOp op var@(EnvVar _ _) e) = do
  varV <- getValue var
  e' <- evalValue e
  setValue var (ExprOp2 op varV e')
  return StmtEmpty
doAst1 (StmtAssignOp op var e) = do
  e' <- evalValue e
  return (StmtAssignOp op var e')
doAst1 x = return x

doAst :: (Env a) => a -> [Stmt] -> (a, [Stmt])
doAst env (ast1:others) = 
  let (re, env') = runState (doAst1 ast1) env
      (env'', re') = doAst env' others
  in (env'', re : re')
doAst env [] = (env, [])
{-
constructFlow inBlockOps allOps =
  let getBlockIn f = [ c | c <- allOps, f $ fst c ]
      constructFlowImpl (o:[]) = do return [o]
      constructFlowImpl (o:os) = do
        let (pc, op) = o
            froms = findTargetFrom pc allOps
            normalResult = [o] ++ constructFlowImpl os
        if froms == [] then
          -- backward jump is treated seprately, so eventhing is forward jump
          case op of
            -- unknown goto; leave it
            Goto c -> return normalResult
            -- if or while
            IfGoto c1 t ->
              let tblks = getBlockIn $ betweenX pc t
                  (tLastPc, tLastOp) = last tblks
              in
                case tLastOp of
                  Goto t2
                    | t2 > tLastPC ->
                      return $ ( If (l_not c1)
                        (constructFlowImpl $ init tblks)
                        (constructFlowImpl $ getBlockIn
                         ( \x -> x >= t && x < t2 ) )
                      ) ++ constructFlowImpl getBlockIn (> t2)
                    | otherwise -> return normalResult
                  IfGoto c2 t2
                    | t2 > tLastPc ->
                      do
                        v <- newVar
                        return (
                          v $= Const BOOL 0 $$
                          If c1 ( constructFlowImpl $ init tblks $$
                                v $= c2 ) $$
                          If ( (lNot c1) $|| (VarValue v) )
                            constructFlowImpl $ getBlockIn (> t2)
                          )
                  _ -> return $ If c1 (constructFlowImpl tblks) stmtNop

          let (fromPc, fromOp) = last froms
          in if fromOp > pc then
         -- loop
         do
           (donePc, doneOp) <- nextOf fromPc allOps
         in case fromOp of
           Goto _ | fromPc < pc =
                  let inner = getBlockBetween fromPc $ Just pc
                      left= getBlockBetween pc Nothing
                      blk = While immT (joinStmt inner)
                  in (pc, blk):arrangeJumpImpl left allOps
         IfGoto c _ | fromPc < pc =
                  let inner = getBlockBetween fromPc $ Just pc
                      left= getBlockBetween pc Nothing
                      blk = DoWhile c (joinStmt inner)
                  in (pc, blk):arrangeJumpImpl left allOps
         _ -> (pc, op):arrangeJumpImpl os allOps
     else
       case op of
         IfGoto t | fromPc > pc =

  in

arrangeJumpImpl o@((pc, op):os) allOps contTarget breakTarget =



arrangeJump ops = arrangeJump ops ops
  -}
