module MonadOp where
-- Monadic operator
import qualified CExpr as C
import qualified Mop as S
import qualified Control.Monad.Operational as O

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

($=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($=) = S.assign

($=^) :: C.Var -> C.Var -> O.Program S.Stmt ()
($=^) dst src = S.assign dst $ C.VarValue src

($+=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($+=) = S.assignOp "+"
($-=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($-=) = S.assignOp "-"
($*=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($*=) = S.assignOp "*"
($/=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($/=) = S.assignOp "/" 
($&=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($&=) = S.assignOp "&"
($|=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($|=) = S.assignOp "|"
($^=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($^=) = S.assignOp "^"
($>>=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($>>=) = S.assignOp ">>"
($<<=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($<<=) = S.assignOp "<<" 
($&&=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($&&=) = S.assignOp "&&"
($||=) :: C.Var -> C.Expr -> O.Program S.Stmt ()
($||=) = S.assignOp "||" 
