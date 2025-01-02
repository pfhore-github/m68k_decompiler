{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module RTL.Stmt where
import CType 
import Text.Printf (printf)
import Data.List

-- integer
data RtlVar
  = RtlReg CType [Char] -- fixed register
  | RtlIncDec Bool Bool RtlVar -- inc/dec 
  | RtlMemory RtlVar -- memory access
  | RtlMemoryI CType RtlVar Int -- memory access with offset
  | RtlMemoryD CType RtlVar Int RtlExpr -- memory access with index
  | RtlMemoryC CType Int -- ROM const
  | RtlMemoryG CType Int -- lowmem global
  deriving (Eq)

typeOfV :: RtlVar -> CType
typeOfV (RtlReg t _) = t
typeOfV (RtlIncDec _ _ v) = typeOfV v
typeOfV (RtlMemory v) = 
  let t = typeOfV v
  in case t of 
    (PTR c) -> c
    _ -> undefined    
typeOfV (RtlMemoryI t _ _) = t
typeOfV (RtlMemoryD t _ _ _) = t
typeOfV (RtlMemoryC t _) = t
typeOfV (RtlMemoryG t _) = t

instance Show RtlVar where
  show (RtlReg t s) = printf "(%v)%s" t s 
  show (RtlIncDec True True s) = printf "(%s)++" $ show s 
  show (RtlIncDec True False s) = printf "++(%s)" $ show s 
  show (RtlIncDec False True s) = printf "(%s)--" $ show s 
  show (RtlIncDec False False s) = printf "--(%s)" $ show s 
  show (RtlMemory v) = printf "*(%s)" $ show v 
  show (RtlMemoryI t v i) = printf "(%v)(%s->_%d)" t (show v) i 
  show (RtlMemoryD t v i o) = printf "(%v*)(%s->_%d)[%s]" t (show v) i (show o) 
  show (RtlMemoryC t c) = printf "(const %v)C_%06x" t c 
  show (RtlMemoryG t c) = printf "(%v)G_%06x" t c 

data RtlExpr
  = ExprVar RtlVar -- variable
  | ExprOp CType [Char] [RtlExpr]
  | ExprImm CType Int    -- integer imm
  | ExprCast CType RtlExpr -- (CType)expr
  | ExprAnd RtlExpr RtlExpr -- a & b
  | ExprOr RtlExpr RtlExpr -- a | b
  | ExprXor RtlExpr RtlExpr -- a ^ b
  | ExprNot RtlExpr  -- ~ a
  | ExprLAnd RtlExpr RtlExpr -- a && b
  | ExprLOr RtlExpr RtlExpr -- a || b
  | ExprLNot RtlExpr  -- ! a
  | ExprBitTest RtlExpr RtlExpr -- a & 1 << b
  | ExprBitSet RtlExpr RtlExpr -- a | 1 << b
  | ExprBitClear RtlExpr RtlExpr -- a & ~(1 << b)
  | ExprBitFlip RtlExpr RtlExpr -- a ^ (1 << b)
  | ExprSr RtlExpr RtlExpr -- a >> b
  | ExprSl RtlExpr RtlExpr -- a << b
  | ExprRor RtlExpr RtlExpr -- a >>(R) b
  | ExprRol RtlExpr RtlExpr -- a <<(R) b
  | ExprNeg RtlExpr -- -a 
  | ExprAdd RtlExpr RtlExpr -- a + b
  | ExprAddC RtlExpr RtlExpr -- carry of (a + b)
  | ExprAddV RtlExpr RtlExpr -- overflow of (a + b)
  | ExprSub RtlExpr RtlExpr -- a - b
  | ExprSubC RtlExpr RtlExpr -- carry of (a - b)
  | ExprSubV RtlExpr RtlExpr -- overflow of (a - b)
  | ExprMul RtlExpr RtlExpr -- low of (a*b)
  | ExprMulH RtlExpr RtlExpr -- high of (a*b)
  | ExprDiv RtlExpr RtlExpr -- a / b
  | ExprMod RtlExpr RtlExpr -- a % b
  | ExprEq RtlExpr RtlExpr -- a == b
  | ExprNeq RtlExpr RtlExpr -- a != b
  | ExprLt RtlExpr RtlExpr -- a < b
  | ExprLeq RtlExpr RtlExpr -- a <= b
  | ExprGt RtlExpr RtlExpr -- a > b
  | ExprGeq RtlExpr RtlExpr -- a >= b
  deriving (Eq)

instance Show RtlExpr where
  show (ExprVar v) = show v
  show (ExprOp _ op vars@(arg1:args)) = 
    case length vars of 
      1 -> printf "%s(%s)" op $ show arg1
      2 -> printf "(%s) %s (%s)" (show arg1) op (show $ head args)
      _ -> printf "%s(%s)" op $ intercalate "," $ map show vars
  show (ExprImm BOOL v) = if v == 0 then "false" else "true"
  show (ExprImm BCD v) = printf "(BCD)%d" v
  show (ExprImm (PTR x) v) = printf "(%v*)%08x" x v
  show (ExprImm c@(INT True _) v) = printf "(%v)%d" c v
  show (ExprImm c@(INT False _) v) = printf "(%v)%x" c v
  show (ExprCast t v) = printf "(%v)%s" t $ show v
  show (ExprAnd a b) = printf "(%s) & (%s)" (show a) (show b)
  show (ExprOr a b) = printf "(%s) | (%s)" (show a) (show b)
  show (ExprXor a b) = printf "(%s) ^ (%s)" (show a) (show b)
  show (ExprNot a) = printf "~ (%s)" (show a)
  show (ExprLAnd a b) = printf "(%s) && (%s)" (show a) (show b)
  show (ExprLOr a b) = printf "(%s) || (%s)" (show a) (show b)
  show (ExprLNot a) = printf "! (%s)" (show a)
  show (ExprBitTest a b) = printf "(%s) >> (%s) & 1" (show a) (show b)
  show (ExprBitSet a b) = printf "(%s) | 1 << (%s)" (show a) (show b)
  show (ExprBitClear a b) = printf "(%s) &~ (1 << (%s))" (show a) (show b)
  show (ExprBitFlip a b) = printf "(%s) ^ 1 << (%s)" (show a) (show b)
  show (ExprSr a b) = printf "(%s) >> (%s)" (show a) (show b)
  show (ExprSl a b) = printf "(%s) << (%s)" (show a) (show b)
  show (ExprRor a b) = printf "ror(%s, %s)" (show a) (show b)
  show (ExprRol a b) = printf "rol(%s, %s)" (show a) (show b)
  show (ExprNeg a) = printf "- (%s)" (show a)
  show (ExprAdd a b) = printf "(%s) + (%s)" (show a) (show b)
  show (ExprAddC a b) = printf "add_carry(%s, %s)" (show a) (show b)
  show (ExprAddV a b) = printf "add_carryV(%s, %s)" (show a) (show b)
  show (ExprSub a b) = printf "(%s) - (%s)" (show a) (show b)
  show (ExprSubC a b) = printf "sub_carry(%s, %s)" (show a) (show b)
  show (ExprSubV a b) = printf "sub_carryV(%s, %s)" (show a) (show b)
  show (ExprMul a b) = printf "(%s) * (%s)" (show a) (show b)
  show (ExprMulH a b) = printf "mulH(%s, %s)" (show a) (show b)
  show (ExprDiv a b) = printf "(%s) / (%s)" (show a) (show b)
  show (ExprMod a b) = printf "(%s) % (%s)" (show a) (show b)
  show (ExprEq a b) = printf "(%s) == (%s)" (show a) (show b)
  show (ExprNeq a b) = printf "(%s) != (%s)" (show a) (show b)
  show (ExprLt a b) = printf "(%s) < (%s)" (show a) (show b)
  show (ExprLeq a b) = printf "(%s) <= (%s)" (show a) (show b)
  show (ExprGt a b) = printf "(%s) > (%s)" (show a) (show b)
  show (ExprGeq a b) = printf "(%s) >= (%s)" (show a) (show b)

typeOfE :: RtlExpr -> CType
typeOfE (ExprVar v) = typeOfV v

data RtlStmt
  = StmtAssign RtlVar RtlExpr -- (dst) = (src)
  | StmtAssignAnd RtlVar RtlExpr -- (dst) &= (src)
  | StmtAssignOr RtlVar RtlExpr -- (dst) |= (src)
  | StmtAssignXor RtlVar RtlExpr -- (dst) ^= (src)
  | StmtAssignSr RtlVar RtlExpr -- (dst) >>= (src)
  | StmtAssignSl RtlVar RtlExpr -- (dst) <<= (src)
  | StmtAssignBitSet RtlVar RtlExpr -- (dst) |= 1 << (src)
  | StmtAssignBitClear RtlVar RtlExpr -- (dst) &= ~(1 << (src))
  | StmtAssignBitFlip RtlVar RtlExpr -- (dst) ^= 1 << (src)
  | StmtAssignRor RtlVar RtlExpr -- (dst) >>=(R) (src)
  | StmtAssignRol RtlVar RtlExpr -- (dst) <<=(R) (src)
  | StmtAssignAdd RtlVar RtlExpr -- (dst) +=(R) (src)
  | StmtAssignSub RtlVar RtlExpr -- (dst) -=(R) (src)
  | StmtAssignMul RtlVar RtlExpr -- (dst) *=(R) (src)
  | StmtAssignDiv RtlVar RtlExpr -- (dst) /=(R) (src)
  | StmtAssignMod RtlVar RtlExpr -- (dst) %=(R) (src)
  | StmtSpecialOp [Char] [RtlExpr]
  deriving (Eq)
  
instance Show RtlStmt where
  show (StmtAssign dst src) = printf "%s = (%s)" (show dst) (show src)
  show (StmtAssignAnd dst src) = printf "%s &= (%s)" (show dst) (show src)
  show (StmtAssignOr dst src) = printf "%s |= (%s)" (show dst) (show src)
  show (StmtAssignXor dst src) = printf "%s ^= (%s)" (show dst) (show src)
  show (StmtAssignSr dst src) = printf "%s >>= (%s)" (show dst) (show src)
  show (StmtAssignSl dst src) = printf "%s <<= (%s)" (show dst) (show src)
  show (StmtAssignBitSet dst src) = printf "%s |= 1 << (%s)" (show dst) (show src)
  show (StmtAssignBitClear dst src) = printf "%s |= ~(1 << (%s))" (show dst) (show src)
  show (StmtAssignBitFlip dst src) = printf "%s ^= 1 << (%s)" (show dst) (show src)
  show (StmtAssignRor dst src) = printf "%s >>R= (%s)" (show dst) (show src)
  show (StmtAssignRol dst src) = printf "%s <<R= (%s)" (show dst) (show src)
  show (StmtAssignAdd dst src) = printf "%s += (%s)" (show dst) (show src)
  show (StmtAssignSub dst src) = printf "%s -= (%s)" (show dst) (show src)
  show (StmtAssignMul dst src) = printf "%s *= (%s)" (show dst) (show src)
  show (StmtAssignDiv dst src) = printf "%s /= (%s)" (show dst) (show src)
  show (StmtAssignMod dst src) = printf "%s /= (%s)" (show dst) (show src)
  show (StmtSpecialOp s vars) = printf "%s(%s)" s $ intercalate "," $ map show vars
