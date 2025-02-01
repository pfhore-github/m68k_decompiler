module AST.Env where
import Control.Monad.State
import AST.Common
import AST.Stmt
class Env a where
    newEnv :: a
    getState :: a -> StmtM
    getValue :: Var -> State a Expr
    setValue :: Var -> Expr -> State a ()
    evalValue :: Expr -> State a Expr