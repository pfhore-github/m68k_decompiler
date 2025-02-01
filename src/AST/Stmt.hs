{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module AST.Stmt where
import AST.Common
import Control.Monad.Operational

type StmtM = Program StmtAction ()
getStmt :: StmtM -> [Stmt]
getStmt pg =
    case view pg of 
        (StmtDo s :>>= is) -> s : getStmt (is ())

data StmtAction x where
    StmtDo :: Stmt -> StmtAction ()

infixr 0 $=, $|=, $&=, $^=, $+=, $-=, $*=, $/=, $%=, $<<=, $>>=
($=) :: Term a => Var -> a -> StmtM
($=) var e = singleton $ StmtDo $ StmtAssign var (getExpr e)

assignOp :: Term a => Op2 -> Var -> a -> StmtM
assignOp o var e = singleton $ StmtDo $ StmtAssignOp o var (getExpr e)

($|=) :: Term a => Var -> a -> StmtM
($|=) = assignOp AST.Common.OR
($&=) :: Term a => Var -> a-> StmtM
($&=) = assignOp AST.Common.AND 
($^=) :: Term a => Var -> a-> StmtM
($^=) = assignOp AST.Common.XOR

($+=) :: Term a => Var -> a-> StmtM
($+=) = assignOp AST.Common.ADD
($-=) :: Term a => Var -> a-> StmtM
($-=) = assignOp AST.Common.SUB
($*=) :: Term a => Var -> a-> StmtM
($*=) = assignOp AST.Common.MUL
($/=) :: Term a => Var -> a-> StmtM
($/=) = assignOp AST.Common.DIV
($%=) :: Term a => Var -> a-> StmtM
($%=) = assignOp AST.Common.MOD

($>>=) :: Term a => Var -> a-> StmtM
($>>=) = assignOp AST.Common.SR
($<<=) :: Term a => Var -> a-> StmtM
($<<=) = assignOp AST.Common.SL

if_ :: Term a1 => a1 -> StmtM -> StmtM
if_ e t = singleton $ StmtDo $ StmtIf (getExpr e) (getStmt t) []
ifElse_ :: Term a1 => a1 -> StmtM -> StmtM -> StmtM
ifElse_ e t f = singleton $ StmtDo $ StmtIf (getExpr e) (getStmt t) (getStmt f)

asm :: [Char] -> [Expr] -> StmtM
asm s a = singleton $ StmtDo $ StmtAsm s a

push :: Expr -> StmtM
push = singleton . StmtDo . StmtPush

pop :: Var -> StmtM
pop = singleton . StmtDo . StmtPop

return_ :: StmtM
return_ = singleton $ StmtDo StmtReturn

goto :: JumpTarget -> StmtM
goto = singleton . StmtDo . StmtGoto

call :: JumpTarget -> StmtM
call = singleton . StmtDo . StmtGoto

nullStmt :: StmtM
nullStmt = singleton $ StmtDo StmtEmpty

adjustSP :: Int -> StmtM
adjustSP = singleton . StmtDo . StmtAdjustSP
