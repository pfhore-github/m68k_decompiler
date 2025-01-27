{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
module M68k.Env where

import           AST.CType
import           AST.Common
import           Control.Monad.State
import           Data.Char
import qualified Data.Map.Strict     as M
import qualified Data.Vector         as V
import qualified Data.Vector.Mutable as MV
import Data.Maybe
import M68k.ConvToRtl (falseV)
import AST.Expr

data MEnv =
  MEnv
    { v_dr    :: V.Vector (Maybe Expr)
    , v_ar    :: V.Vector (Maybe Expr)
    , v_cc    :: M.Map Char Expr
    , v_stack :: M.Map Int Expr
    , v_sp    :: Int
    , v_vars :: M.Map String Expr
    , v_savedSp :: [Int]
    } 

emptyEnv :: MEnv
emptyEnv = MEnv {
  v_dr = V.replicate 8 Nothing,
  v_ar = V.replicate 8 Nothing,
  v_cc = M.fromList [('C', falseV), ('V', falseV), ('Z', falseV), ('N', falseV), ('X', falseV), ('I', uintE 0)],
  v_stack = M.empty,
  v_sp = 0,
  v_vars = M.empty,
  v_savedSp = []
}

readDn :: Char -> State MEnv (Maybe Expr)
readDn n = do
  e <- get
  return $ v_dr e V.! (digitToInt n) 

readAn :: Char -> State MEnv (Maybe Expr)
readAn n = do
  e <- get
  return $ v_ar e V.! (digitToInt n) 

readCC :: Char -> State MEnv (Maybe Expr)
readCC c = do
  e <- get
  return $ v_cc e M.!? c

readCCX :: Char -> State MEnv (Expr)
readCCX c = do
  v <- readCC c 
  return $ fromMaybe (ExprVar $ RtlReg BOOL [c]) v
writeDn :: Char -> Expr -> State MEnv ()
writeDn n v = do
  modify $ \e -> e {v_dr = V.modify (\x -> MV.write x (digitToInt n) $ Just v) (v_dr e)}

writeAn :: Char -> Expr -> State MEnv ()
writeAn n v = do
   modify $ \e -> e {v_ar = V.modify (\x -> MV.write x (digitToInt n) $ Just v) (v_ar e)}

writeCC :: Char -> Expr -> State MEnv ()
writeCC c v = do
  modify $ \e -> e {v_cc = M.insert c v (v_cc e)}

-- update register
writeVar :: Var -> Expr -> State MEnv ()
writeVar s@(RtlReg t ('D':dn:[])) v  
  | sizeOf t == 4 = writeDn dn v
  | sizeOf t == 2 = do 
    v' <- readDn dn
    writeDn dn (
      case v' of
        Just (ExprJoin a _) -> (ExprJoin a v) 
        Nothing -> ((ExprVar s) $& uintE 0xFFFF0000) $| v
        _ -> (v $& uintE 0xFFFF0000) $| v
      )
  | sizeOf t == 1 = do 
    v' <- readDn dn
    writeDn dn (
      case v' of
          Just (ExprJoin a (ExprJoin b _)) -> (ExprJoin a (ExprJoin b v)) 
          Nothing -> ((ExprVar s) $& uintE 0xFFFFFF00) $| v
          _ -> (v $& uintE 0xFFFFFF00) $| v
      )
writeVar (RtlReg t ('A':an:[])) v 
  | sizeOf t == 4 = writeAn an v
  | sizeOf t == 2 = do 
    let v' = cast INT32 v
    writeAn an v'
writeVar (RtlReg BOOL (c:[])) v = do
  writeCC c $ cast BOOL v
writeVar (RtlReg _ s) v = do
  modify $ \e -> e {v_vars = M.insert s v (v_vars e)}
writeVar _ _ = do return ()


-- TODO
eval :: Expr -> State MEnv (Expr)
eval (ExprVar v) = do
  val <- readVar v
  return val 
eval (ExprCast t v) = do
  val <- eval v
  return $ if t == typeOfE v then val else ExprCast t val
eval (ExprOp1 op v) = do
  val <- eval v
  return $ evalE (ExprOp1 op val)
eval (ExprOp2 op v1 v2) = do
  val1 <- eval v1
  val2 <- eval v2
  return $ evalE (ExprOp2 op val1 val2)
eval (ExprOpN t s vs) = do
  vals <- mapM (do return . evalE) vs
  return $ evalE (ExprOpN t s vals)
eval (ExprSel cond t f) = do
  cond' <- eval cond
  t' <- eval t
  f' <- eval f
  return $ evalE (ExprSel cond' t' f')
eval (ExprCondCC 0) = do
  return $ ExprBool True
eval (ExprCondCC 1) = do
  return $ ExprBool False
eval (ExprCondCC 2) = do
  c <- readCCX 'C'
  z <- readCCX 'Z'
  case c of 
    (ExprOp2 AST.Common.SUBC a b) -> return $ a $> b
    (ExprOp2 AST.Common.ADDC a b) -> return $ a $> (neg b)
    _ -> return $ (lNot c) $&& (lNot z)
eval (ExprCondCC 3) = do
  c <- readCCX 'C'
  z <- readCCX 'Z'
  case c of 
    (ExprOp2 AST.Common.SUBC a b) -> return $ a $<= b
    (ExprOp2 AST.Common.ADDC a b) -> return $ a $<= (neg b)
    _ -> return $ c $|| z
eval (ExprCondCC 4) = do
  c <- readCCX 'C'
  case c of 
    (ExprOp2 AST.Common.SUBC a b) -> return $ a $>= b
    (ExprOp2 AST.Common.ADDC a b) -> return $ a $>= (neg b)
    _ -> return $ (lNot c)
eval (ExprCondCC 5) = do
  c <- readCCX 'C'
  case c of 
    (ExprOp2 AST.Common.SUBC a b) -> return $ a $< b
    (ExprOp2 AST.Common.ADDC a b) -> return $ a $< (neg b)
    _ -> return $ c
eval (ExprCondCC 6) = do
  z <- readCCX 'Z'
  return $ (lNot z)
eval (ExprCondCC 7) = do
  z <- readCCX 'Z'
  return z
eval (ExprCondCC 8) = do
  v <- readCCX 'V'
  return $ (lNot v)
eval (ExprCondCC 9) = do
  v <- readCCX 'V'
  return v
eval (ExprCondCC 10) = do
  n <- readCCX 'N'
  return $ (lNot n)
eval (ExprCondCC 11) = do
  n <- readCCX 'N'
  return n
eval (ExprCondCC 12) = do
  v <- readCCX 'V'
  case v of 
    (ExprOp2 AST.Common.SUBV a b) -> return $ a $>= b
    (ExprOp2 AST.Common.ADDV a b) -> return $ a $>= (neg b)
    _ -> do
            n <- readCCX 'N'
            return $ (v $== n)
eval (ExprCondCC 13) = do
  v <- readCCX 'V'
  case v of 
    (ExprOp2 AST.Common.SUBV a b) -> return $ a $< b
    (ExprOp2 AST.Common.ADDV a b) -> return $ a $< (neg b)
    _ -> do 
        n <- readCCX 'N'
        return $ (v $!= n)
eval (ExprCondCC 14) = do
  v <- readCCX 'V'
  case v of 
    (ExprOp2 AST.Common.SUBV a b) -> return $ a $> b
    (ExprOp2 AST.Common.ADDV a b) -> return $ a $> (neg b)
    _ -> do 
        n <- readCCX 'N'
        z <- readCCX 'Z'
        return $ (v $== n) $&& (lNot z)
eval (ExprCondCC 15) = do
  v <- readCCX 'V'
  case v of 
    (ExprOp2 AST.Common.SUBV a b) -> return $ a $<= b
    (ExprOp2 AST.Common.ADDV a b) -> return $ a $<= (neg b)
    _ -> do 
        n <- readCCX 'N'
        z <- readCCX 'Z'
        return $ z $|| (v $!= n)


-- right hand is bit offset 

eval e = do return e

readVar :: Var -> State MEnv (Expr)
readVar c@(RtlReg t ('D':dn:[])) = do 
  v <- readDn dn
  return $ cast t $ fromMaybe (ExprVar c) v
readVar c@(RtlReg t ('A':dn:[])) = do 
  v <- readAn dn
  return $ cast t $ fromMaybe (ExprVar c) v
readVar v@(RtlReg BOOL (c:[])) = fromMaybe (ExprVar v) <$> readCC c
readVar v@(RtlReg _ s) = do 
  e <- get
  return $ fromMaybe (ExprVar v) $ (v_vars e) M.!? s
readVar (RtlInc t v) = do
  e <- readVar v
  let inc = case typeOfE e of
              (PTR t') -> sizeOf t'
              _ -> 1                   
  writeVar v (e $+ intE inc)
  return $ if t then (e $+ intE inc) else e
readVar (RtlDec t v) = do
    e <- readVar v
    let inc = case typeOfE e of
                (PTR t') -> sizeOf t'
                _ -> 1                   
    writeVar v (e $- intE inc)
    return $ if t then (e $- intE inc) else e
readVar (RtlMemory v) = do
    v' <- eval v
    return $ ExprVar $ deref v'
readVar (RtlMemoryI t v o) = do
    v' <- eval v
    return $ ExprVar $ RtlMemoryI t v' o
readVar (RtlMemoryD t v i) = do
    v' <- eval v
    i' <- eval i
    return $ ExprVar $ RtlMemoryD t v' i'
readVar (VarCast t v) = do
    val <- readVar v
    return $ if (typeOfE val) == t then 
      val
    else 
      cast t val
readVar x = do
      return $ ExprVar x
{- 










instance Env MEnv where
  readReg t v@['D', c] = do
    let n = digitToInt c
    val <- readDn_ n
    case sizeOf t of
      4 ->
        case val of
          Nothing -> do
            let v2 = Arg t v
            writeDn_ n v2
            return v2
          Just v2 -> return v2
      2 ->
        case val of
          Nothing -> do
            let v1 = Arg t (v ++ "_H")
                v2 = Arg t (v ++ "_L")
            writeDn_ n (Expr2 v1 v2)
            return v2
          Just x -> return x
      1 ->
        case val of
          Nothing -> do
            let v1 = Arg t (v ++ "_B0")
                v2 = Arg t (v ++ "_B1")
                v3 = Arg t (v ++ "_B2")
                v4 = Arg t (v ++ "_B3")
            writeDn_ n $ Expr2 (Expr2 v1 v2) (Expr2 v3 v4)
            return v4
          Just x -> return x
      _ -> return $ Const BOOL 0
  readReg _ v@['A', c] = do
    let n = digitToInt c
    val <- readAn_ n
    case val of
      Nothing -> do
        let v2 = Arg (PTR VOID) v
        writeAn_ n v2
        return v2
      Just v2 -> return v2
  readReg _ v@['C', c] = do
    val <- readCC_ c
    case val of
      Nothing -> do
        let v2 =
              Arg
                (if c == 'I'
                   then uint8
                   else BOOL)
                v
        writeCC_ c v2
        return v2
      Just v2 -> return v2
  readReg _ _ = return $ Const BOOL 0
  writeReg v@['D', c] x = do
    let t = typeOf x
        n = digitToInt c
    case sizeOf t of
      4 -> writeDn_ n x
      2 -> do
        val <- readDn_ n
        case val of
          Nothing -> do
            let v1 = Arg t (v ++ "_H")
            writeDn_ n (Expr2 v1 x)
          Just x' -> do
            writeDn_ n ((x' $&# 0xffff0000) $| x')
      1 -> do
        val <- readDn_ n
        case val of
          Nothing -> do
            let v1 = Arg t (v ++ "_B0")
                v2 = Arg t (v ++ "_B1")
                v3 = Arg t (v ++ "_B2")
            writeDn_ n (Expr2 (Expr2 v1 v2) (Expr2 v3 x))
          Just x' -> do
            writeDn_ n ((x' $&# 0xffffff00) $| x')
      _ -> do
        return ()
  writeReg ['A', c] x
    | c == '7' = do
        case x of
          Op2 (VarValue (EnvVar _ "SP")) "+" (Const _ b) ->
            modifySP (+b)
          Const (INT _ 4) _ ->
            modifySP (const 0)
          _ -> do return ()
        writeAn_ 7 x
    | otherwise = do
        let n = digitToInt c
        writeAn_ n x
  writeReg ['C', c] x = do
    writeCC_
      c
      (cast
         (if c == 'I'
            then uint8
            else BOOL)
         x)
  writeReg _ _ = do
    return ()
  readStack t i = do
    e <- get
    return $ cast t $ v_stack e M.! i
  getSP = v_sp
  getSPM = gets v_sp
  modifySP f = do
    modify $ \e -> e {v_sp = f (v_sp e)}

  newVar t = do
    e <- get
    let v = TVar t $ length $ v_vars e
    put e { v_vars = v : v_vars e}
    return v
  saveReg = FromEnv $ do
    e <- get
    let re = mapMaybe (\c ->
                do x <- v_dr e V.! c
                   return $ Assign (EnvVar uint32 ['D',intToDigit c]) x
             ) [0 .. 7] ++
          mapMaybe (\c ->
           do x <- v_ar e V.! c
              return $ Assign (EnvVar uint32 ['A',intToDigit c]) x
               ) [0 .. 7] ++
          M.foldrWithKey (\k v s ->
                        Assign (EnvVar (typeOf v) ['C',k]) v: s) [] (v_cc e)
    put e{  v_dr = V.replicate 8 Nothing,
         v_ar = V.fromList (replicate 7 Nothing  ++
                            [Just $ VarValue $ EnvVar (PTR VOID) "SP"]),
         v_cc = M.empty }
    return re

pushValue :: Expr -> State MEnv ()
pushValue v = do
  sp <- getSPM
  modifySP (+4)
  oldsp <- readReg uint32 "A7"
  writeReg "A7" (oldsp $+# 4)
  modify $ \e -> e {v_stack = M.insert sp v (v_stack e)}

getStackValue :: Int -> State MEnv (Maybe Expr)
getStackValue pos =
  let getV e =
        let realpos = v_sp e - pos
         in (M.lookup realpos (v_stack e), e)
   in state getV


readDn :: CType -> Int -> State MEnv Expr
readDn t n = readReg t ['D', intToDigit n]
readAn :: Int -> State MEnv Expr
readAn n = readReg (PTR VOID) ['A', intToDigit n]
readCC :: Char -> State MEnv Expr
readCC c = readReg (if c == 'I' then uint8 else BOOL) ['C',c]

writeDn :: Int -> Expr -> StateV MEnv ()
writeDn n v = doWriteInEnv $ writeReg ['D', intToDigit n] v
writeAn :: Int -> Expr -> StateV MEnv ()
writeAn n v = doWriteInEnv $ writeReg ['A', intToDigit n] v 
writeCC :: Char -> Expr -> State MEnv ()
writeCC c = writeReg ['C',c]

clearCcS :: State MEnv ()
clearCcS = do 
  modify (\e -> e {v_cc = M.delete 'S' (v_cc e)})
-} 
