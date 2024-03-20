module MonadOp where
-- Monadic operator
import Env
import qualified CExpr as C
import qualified CStmt as S
import CStmt

infix 1 $=
infix 1 $=^
infix 1 $+=
infix 1 $-=
infix 1 $*=
infix 1 $/=
infix 1 $&=
infix 1 $^=
infix 1 $|=
infix 1 $&&=
infix 1 $||=

($=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($=) = S.assign

($=^) :: (Env a) => C.Var -> C.Var -> StateV a ()
($=^) dst src = S.assign dst $ C.VarValue src

($+=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($+=) = S.assignOp "+"
($-=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($-=) = S.assignOp "-"
($*=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($*=) = S.assignOp "*"
($/=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($/=) = S.assignOp "/" 
($&=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($&=) = S.assignOp "&"
($|=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($|=) = S.assignOp "|"
($^=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($^=) = S.assignOp "^"
($>>=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($>>=) = S.assignOp ">>"
($<<=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($<<=) = S.assignOp "<<" 
($&&=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($&&=) = S.assignOp "&&"
($||=) :: (Env a) => C.Var -> C.Expr -> StateV a ()
($||=) = S.assignOp "||" 
