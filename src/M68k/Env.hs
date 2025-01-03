{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
module M68k.Env
  ( MEnv(MEnv, v_dr, v_ar, v_cc, v_sp, v_savedSp)
  , readDn
  , readAn
  , readCC
  , writeDn
  , writeAn
  , writeCC
  , clearCcS
  , pushValue
  , getStackValue
  , StateV(Known, FromEnv)
  , emptyEnv
  ) where

import           CExpr
import           CType
import           Control.Monad.State
import           Data.Char
import qualified Data.Map.Strict     as M
import qualified Data.Vector         as V
import qualified Data.Vector.Mutable as MV
import           Env
import Data.Maybe (mapMaybe)
import CStmt

data MEnv =
  MEnv
    { v_dr    :: V.Vector (Maybe Expr)
    , v_ar    :: V.Vector (Maybe Expr)
    , v_cc    :: M.Map Char Expr
    , v_stack :: M.Map Int Expr
    , v_sp    :: Int
    , v_vars :: [Var]
    , v_savedSp :: [Int]
    } 

emptyEnv :: MEnv
emptyEnv = MEnv {
  v_dr = V.replicate 8 Nothing,
  v_ar = V.replicate 8 Nothing,
  v_cc = M.fromList [('C', immF), ('V', immF), ('Z', immF), ('N', immF), ('X', immF), ('I', Const int8 0)],
  v_stack = M.empty,
  v_sp = 0,
  v_vars = [],
  v_savedSp = []
}



readDn_ :: Int -> State MEnv (Maybe Expr)
readDn_ n = do
  e <- get
  return $ v_dr e V.! n

readAn_ :: Int -> State MEnv (Maybe Expr)
readAn_ n = do
  e <- get
  return $ v_ar e V.! n

readCC_ :: Char -> State MEnv (Maybe Expr)
readCC_ c = do
  e <- get
  return $ v_cc e M.!? c

writeDn_ :: Int -> Expr -> State MEnv ()
writeDn_ n v = do
  modify $ \e -> e {v_dr = V.modify (\x -> MV.write x n $ Just v) (v_dr e)}

writeAn_ :: Int -> Expr -> State MEnv ()
writeAn_ n v = do
   modify $ \e -> e {v_ar = V.modify (\x -> MV.write x n $ Just v) (v_ar e)}

writeCC_ :: Char -> Expr -> State MEnv ()
writeCC_ c v = do
  modify $ \e -> e {v_cc = M.insert c v (v_cc e)}


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
