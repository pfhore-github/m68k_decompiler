{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE InstanceSigs              #-}

module M68k.Env
  ( MEnv
  ) where

import           AST.Common
import           AST.CType
import           AST.Env
import           AST.Expr            (cast, deref, evalE, lNot, neg, typeOfE,
                                      ($!=), ($&&), ($&), ($+), ($-), ($<),
                                      ($<=), ($==), ($>), ($>=), ($|), ($||))
import           AST.Stmt
import           Control.Monad.State
import           Data.Char
import qualified Data.Map.Strict     as M
import           Data.Maybe
import qualified Data.Vector         as V
import qualified Data.Vector.Mutable as MV
import           Text.Printf         (printf)

data MEnv =
  MEnv
    { v_dr      :: V.Vector Expr
    , v_ar      :: V.Vector Expr
    , v_cc      :: M.Map Char Expr
    , v_stack   :: M.Map Int Expr
    , v_sp      :: Int
    , v_vars    :: M.Map String Expr
    , v_savedSp :: [Int]
    }

emptyEnv :: MEnv
emptyEnv =
  MEnv
    { v_dr =
        V.fromList $
        map (ExprVar . EnvVar UINT32 . printf "d%d") [0 :: Int .. 7]
    , v_ar =
        V.fromList $
        map
          (ExprVar . EnvVar (PTR VOID))
          (map (printf "a%d") [0 :: Int .. 5] ++ ["fp", "sp"])
    , v_cc =
        M.fromList $
        map (\c -> (c, ExprVar $ EnvVar BOOL [c])) ['C', 'V', 'Z', 'N', 'X']
    , v_stack = M.empty
    , v_sp = 0
    , v_vars = M.empty
    , v_savedSp = []
    }

readDn :: Char -> State MEnv Expr
readDn n = do
  e <- get
  return $ v_dr e V.! digitToInt n

readAn :: Char -> State MEnv Expr
readAn n = do
  e <- get
  return $ v_ar e V.! digitToInt n

readCC :: Char -> State MEnv Expr
readCC c = do
  e <- get
  return $ v_cc e M.! c

writeDn :: Char -> Expr -> State MEnv ()
writeDn n v = do
  modify $ \e ->
    e {v_dr = V.modify (\x -> MV.write x (digitToInt n) v) (v_dr e)}

writeAn :: Char -> Expr -> State MEnv ()
writeAn n v = do
  modify $ \e ->
    e {v_ar = V.modify (\x -> MV.write x (digitToInt n) v) (v_ar e)}

writeCC :: Char -> Expr -> State MEnv ()
writeCC c v = do
  modify $ \e -> e {v_cc = M.insert c v (v_cc e)}

readVar :: Var -> State MEnv Expr
readVar (EnvVar t ['D', dn]) = do
  v <- readDn dn
  return $ evalE $ cast t v
readVar (EnvVar t ['A', dn]) = do
  v <- readAn dn
  return $ evalE $ cast t v
readVar (EnvVar BOOL [c]) = readCC c
readVar v@(GlobalVar _ s) = do
  e <- get
  return $ fromMaybe (ExprVar v) $ v_vars e M.!? s
readVar (VarInc t v) = do
  e <- readVar v
  let inc =
        case typeOfE e of
          (PTR t') -> sizeOf t'
          _        -> 1
  writeVar v (e $+ intE inc)
  return $
    if t
      then e $+ intE inc
      else e
readVar (VarDec t v) = do
  e <- readVar v
  let inc =
        case typeOfE e of
          (PTR t') -> sizeOf t'
          _        -> 1
  writeVar v (e $- intE inc)
  return $
    if t
      then e $- intE inc
      else e
readVar (VarMemory v) = do
  v' <- evalValue v
  return $ ExprVar $ deref v'
readVar (VarMember t v o) = do
  v' <- evalValue v
  return $ ExprVar $ VarMember t v' o
readVar (VarArray t v i) = do
  v' <- evalValue v
  i' <- evalValue i
  return $ ExprVar $ VarArray t v' i'
readVar (VarCast t v) = do
  val <- readVar v
  return $
    if typeOfE val == t
      then val
      else cast t val
readVar x = do
  return $ ExprVar x

-- update register
writeVar :: Var -> Expr -> State MEnv ()
writeVar (EnvVar t ['D', dn]) v
  | sizeOf t == 4 = writeDn dn v
  | sizeOf t == 2 = do
    v' <- readDn dn
    writeDn
      dn
      (case v' of
         ExprJoin a _ -> ExprJoin a v
         _            -> (v $& uintE 0xFFFF0000) $| v)
  | sizeOf t == 1 = do
    v' <- readDn dn
    writeDn
      dn
      (case v' of
         ExprJoin a (ExprJoin b _) -> ExprJoin a (ExprJoin b v)
         _                         -> (v $& uintE 0xFFFFFF00) $| v)
writeVar (EnvVar t ['A', an]) v
  | sizeOf t == 4 = writeAn an v
  | sizeOf t == 2 = do
    let v' = cast INT32 v
    writeAn an v'
writeVar (EnvVar BOOL [c]) v = do
  writeCC c $ cast BOOL v
writeVar _ _ = do
  return ()

instance Env MEnv where
  newEnv = emptyEnv
  getState :: MEnv -> StmtM
  getState e = do
    mapM_ (\d -> EnvVar UINT32 ['D', intToDigit d] $= v_dr e V.! d) [0 .. 7]
    mapM_ (\d -> EnvVar (PTR VOID) ['A', intToDigit d] $= v_ar e V.! d) [0 .. 7]
    mapM_ (\c -> EnvVar BOOL [c] $= v_cc e M.! c) ['C', 'V', 'Z', 'N', 'X']
  getValue :: Var -> State MEnv Expr
  getValue var@(EnvVar _ _) = readVar var
  getValue v = do
    return $ ExprVar v
  setValue var@(EnvVar _ _) e = writeVar var e
  setValue _ _ = do
    return ()
  evalValue :: Expr -> State MEnv Expr
  evalValue (ExprVar v) = do
    readVar v
  evalValue (ExprCast t v) = do
    val <- evalValue v
    return $
      if t == typeOfE v
        then val
        else ExprCast t val
  evalValue (ExprOp1 op v) = do
    val <- evalValue v
    return $ evalE (ExprOp1 op val)
  evalValue (ExprOp2 op v1 v2) = do
    val1 <- evalValue v1
    val2 <- evalValue v2
    return $ evalE (ExprOp2 op val1 val2)
  evalValue (ExprOpN t s vs) = do
    vals <- mapM (do return . evalE) vs
    return $ evalE (ExprOpN t s vals)
  evalValue (ExprSel cond t f) = do
    cond' <- evalValue cond
    t' <- evalValue t
    f' <- evalValue f
    return $ evalE (ExprSel cond' t' f')    
  evalValue (ExprCondCC 0) = do
    return $ ExprBool True
  evalValue (ExprCondCC 1) = do
    return $ ExprBool False
  evalValue (ExprCondCC 2) = do
    c <- readCC 'C'
    case c of
      (ExprOp2 AST.Common.SUBC a b) -> return $ a $> b
      (ExprOp2 AST.Common.ADDC a b) -> return $ a $> neg b
      _ -> do
        z <- readCC 'Z'
        return $ lNot c $&& lNot z
  evalValue (ExprCondCC 3) = do
    c <- readCC 'C'
    case c of
      (ExprOp2 AST.Common.SUBC a b) -> return $ a $<= b
      (ExprOp2 AST.Common.ADDC a b) -> return $ a $<= neg b
      _ -> do
        z <- readCC 'Z'
        return $ c $|| z
  evalValue (ExprCondCC 4) = do
    c <- readCC 'C'
    case c of
      (ExprOp2 AST.Common.SUBC a b) -> return $ a $>= b
      (ExprOp2 AST.Common.ADDC a b) -> return $ a $>= neg b
      _                             -> return $ lNot c
  evalValue (ExprCondCC 5) = do
    c <- readCC 'C'
    case c of
      (ExprOp2 AST.Common.SUBC a b) -> return $ a $< b
      (ExprOp2 AST.Common.ADDC a b) -> return $ a $< neg b
      _                             -> return c
  evalValue (ExprCondCC 6) = do
    z <- readCC 'Z'
    return $ lNot z
  evalValue (ExprCondCC 7) = do
    readCC 'Z'
  evalValue (ExprCondCC 8) = do
    v <- readCC 'V'
    return $ lNot v
  evalValue (ExprCondCC 9) = do
    readCC 'V'
  evalValue (ExprCondCC 10) = do
    n <- readCC 'N'
    return $ lNot n
  evalValue (ExprCondCC 11) = do
    readCC 'N'
  evalValue (ExprCondCC 12) = do
    v <- readCC 'V'
    case v of
      (ExprOp2 AST.Common.SUBV a b) -> return $ a $>= b
      (ExprOp2 AST.Common.ADDV a b) -> return $ a $>= neg b
      _ -> do
        n <- readCC 'N'
        return (v $== n)
  evalValue (ExprCondCC 13) = do
    v <- readCC 'V'
    case v of
      (ExprOp2 AST.Common.SUBV a b) -> return $ a $< b
      (ExprOp2 AST.Common.ADDV a b) -> return $ a $< neg b
      _ -> do
        n <- readCC 'N'
        return (v $!= n)
  evalValue (ExprCondCC 14) = do
    v <- readCC 'V'
    case v of
      (ExprOp2 AST.Common.SUBV a b) -> return $ a $> b
      (ExprOp2 AST.Common.ADDV a b) -> return $ a $> neg b
      _ -> do
        n <- readCC 'N'
        z <- readCC 'Z'
        return $ (v $== n) $&& lNot z
  evalValue (ExprCondCC 15) = do
    v <- readCC 'V'
    case v of
      (ExprOp2 AST.Common.SUBV a b) -> return $ a $<= b
      (ExprOp2 AST.Common.ADDV a b) -> return $ a $<= neg b
      _ -> do
        n <- readCC 'N'
        z <- readCC 'Z'
        return $ z $|| (v $!= n)
  evalValue e = do
    return e
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
