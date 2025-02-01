{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module M68k.ConvToAst
  ( toAst
  , trueV
  , falseV
  , operand2Var
  , drV
  , arV
  , xrV
  ) where

import           AST.Common   as R
import           AST.CType
import           AST.Expr
import           AST.Stmt
import           Data.Bits    (Bits, (.&.), (.>>.))
import           M68k.Common
import           M68k.Opcode  as P
import           M68k.Operand as P2
import           M68k.LongDouble
import           Text.Printf  (printf)

-- decompile 1st phase
default (Integer, Double)

toCType :: AType -> Bool -> CType
toCType BYTE False = UINT8
toCType WORD False = UINT16
toCType LONG False = UINT32
toCType BYTE True  = INT8
toCType WORD True  = INT16
toCType LONG True  = INT32

toCTypeF :: AFType -> CType
toCTypeF FSINGLE = FLT
toCTypeF FDOUBLE = DBL
toCTypeF FEXT = AST.CType.EXT
toCTypeF FPACKED = AST.CType.EXT

drV :: CType -> P2.DR -> Var
drV t (P2.DR n) = EnvVar t $ printf "D%d" n

arV :: CType -> P2.AR -> Var
arV t (P2.AR n) = EnvVar t $ printf "A%d" n

frV :: CType -> P2.FPR -> Var
frV t (P2.FPR n) = EnvVar t $ printf "F%d" n

xrV :: CType -> P2.XR -> Var
xrV t (P2.XR_D d) = drV t $ P2.DR d
xrV t (P2.XR_A d) = arV t $ P2.AR d

applyEaBase :: P2.AddrBase -> Int -> CType -> Var
applyEaBase (P2.BaseAR r) bd t  = VarMember t (ExprVar $ arV (PTR VOID) r) bd
applyEaBase (P2.BasePC pc) bd t = VarROM t $ pc + bd
applyEaBase P2.BaseNone bd t    = VarRAM t bd

-- base + rn.w*cc -> ((cct*)base) [ rn ]
applyRn :: Var -> Bool -> Maybe P2.XR -> Int -> CType -> Var
applyRn base w (Just rn) cc t =
  let cType =
        (case cc of
           0 -> UINT8
           1 -> UINT16
           2 -> UINT32
           3 -> UINT64)
      getIndex True n  = ExprCast INT32 $ ExprVar $ xrV INT16 n
      getIndex False n = ExprVar $ xrV INT32 n
      index = getIndex w rn
   in VarCast t $ VarArray cType (ExprVar base) index
applyRn base _ Nothing _ t = VarCast t base

operand2Var :: P2.Operand -> CType -> Var
operand2Var (P2.DReg d) t = drV t d
operand2Var (P2.AReg a) t = arV t a
operand2Var (P2.Address (P2.UnRefAR r)) t = deref $ arV (PTR t) r -- (An)
operand2Var (P2.Address (P2.UnRefInc r)) t =
  deref $ VarInc False $ arV (PTR t) r -- (An+)
operand2Var (P2.Address (P2.UnRefDec r)) t =
  deref $ VarDec True $ arV (PTR t) r -- (-An)
operand2Var (P2.Address (P2.Offset16 d base)) t = applyEaBase base d t -- (d, An/PC/0)
operand2Var (P2.Address (P2.Offset8 d base w rn cc)) t -- (d, An/PC/0, rn.w*cc)
 =
  let base1 = applyEaBase base d $ PTR VOID
   in applyRn base1 w (Just rn) cc t
operand2Var (P2.Address (P2.Indirect bd base w rn cc)) t -- (bd, An/PC/0, rn.w*cc)
 =
  let base1 = applyEaBase base bd $ PTR VOID
   in applyRn base1 w rn cc t
operand2Var (P2.Address (P2.PreIndex bd base w rn cc od)) t -- ([bd, An/PC/0, rn.w*cc], od)
 =
  let base1 = applyEaBase base bd $ PTR VOID
      base2 = applyRn base1 w rn cc $ PTR VOID
   in VarMember t (ExprVar base2) od
operand2Var (P2.Address (P2.PostIndex bd base w rn cc od)) t -- ([bd, An/PC/0], rn.w*cc, od)
 =
  let base1 = applyEaBase base bd $ PTR VOID
      base2 = VarMember (PTR VOID) (ExprVar base1) od
   in applyRn base2 w rn cc t
operand2Var (P2.Address (P2.ImmAddr addr)) t = VarRAM t addr
operand2Var _ _ = undefined

ccFlags :: [Char] -> Var
ccFlags = EnvVar BOOL

doCCRFlags :: (Term a1, Num a2, Bits a2) => (Expr -> Expr -> a1) -> a2 -> StmtM
doCCRFlags op v =
  mapM_
    (\(i, k) -> ccFlags k $= op (ExprVar $ ccFlags k) (boolE $ (v .>>. i) .&. 1))
    [(0, "C"), (1, "V"), (2, "Z"), (3, "N"), (4, "X")]

doSRFlags :: (Integral a, Bits a) => (Var -> Expr -> StmtM) -> a -> StmtM
doSRFlags op v = do
  op (GlobalVar UINT8 "I") $ uintE ((v .>>. 8) .&. 7)
  op (GlobalVar BOOL "M") $ boolE ((v .>>. 12) .&. 1)
  op (GlobalVar BOOL "S") $ boolE ((v .>>. 13) .&. 1)
  op (GlobalVar UINT8 "T") $ uintE ((v .>>. 14) .&. 3)

testN :: Term a => AType -> a -> Expr
testN t v =
  let ctype = toCType t True
   in cast ctype v $< intE 0

testCmpN :: (Term a1, Term a2) => AType -> a1 -> a2 -> Expr
testCmpN t a b =
  let ctype = toCType t True
   in cast ctype a $< cast ctype b

falseV :: Expr
falseV = ExprBool False

trueV :: Expr
trueV = ExprBool True

ccV :: Var
ccV = ccFlags "V"

ccC :: Var
ccC = ccFlags "C"

ccZ :: Var
ccZ = ccFlags "Z"

ccN :: Var
ccN = ccFlags "N"

ccX :: Var
ccX = ccFlags "X"
 
clearVC :: StmtM
clearVC = do
  ccV $= falseV
  ccC $= falseV

testNZ :: (Term a) => AType -> a -> StmtM 
testNZ t v = do
  ccZ $= lNot v
  ccN $= testN t v

doBitop :: (Term a2) => AType -> (a2 -> t -> StmtM) -> a2 -> t -> StmtM
doBitop t op dst src = do
  clearVC
  op dst src
  testNZ t dst

doBitimm ::
     (Integral p) => AType -> (Var -> Expr -> StmtM) -> P2.Operand -> p -> StmtM
doBitimm t op ea i = do
  let ct = toCType t False
      imm = uintE $ fromIntegral i
      dst = operand2Var ea ct
  doBitop t op dst imm

doArithimm ::
     (AType -> Var -> Expr -> StmtM) -> AType -> P2.Operand -> Int -> StmtM
doArithimm op t ea i = do
  let ct = toCType t False
      imm = uintE $ fromIntegral i
      dst = operand2Var ea ct
  op t dst imm

doCmp :: (Term a1, Term a2) => AType -> a1 -> a2 -> StmtM
doCmp t dst src = do
  ccV $= dst `subV` src
  ccC $= dst `subC` src
  ccZ $= dst $== src
  ccN $= testCmpN t dst src

doSub :: (Term a) => AType -> Var -> a -> StmtM
doSub t dst src = do
  ccV $= dst `subV` src
  ccC $= dst `subC` src
  ccX $= ccC
  dst $-= src
  testNZ t dst

doAdd :: (Term a) => AType -> Var -> a -> StmtM
doAdd t dst src = do
  ccV $= dst `addV` src
  ccC $= dst `addC` src
  ccX $= ccC
  dst $+= src
  testNZ t dst

doBit :: Maybe Op2 -> AType -> P2.Operand -> BopSc -> StmtM
doBit op t ea sc = do
  let ea_v = operand2Var ea $ toCType t False
      count =
        case sc of
          BImm n -> uintE $ fromIntegral n
          BReg d -> ExprVar $ drV UINT32 d
  ccZ $= bitTest ea_v count
  case op of
    (Just o) -> assignOp o ea_v count
    Nothing  -> nullStmt

toAst :: Op -> StmtM
toAst (P.ORI BYTE P2.CCR v) = doCCRFlags ($|) v
toAst (P.ORI WORD P2.SR v) = do
  doSRFlags ($|=) v
  doCCRFlags ($|) v
toAst (P.ORI t ea v) = doBitimm t ($|=) ea v
toAst (P.ANDI BYTE P2.CCR v) = doCCRFlags ($&) v
toAst (P.ANDI WORD P2.SR v) = do
  doSRFlags ($&=) v
  doCCRFlags ($&) v
toAst (P.ANDI t ea v) = doBitimm t ($&=) ea v
toAst (P.EORI BYTE P2.CCR v) = doCCRFlags ($^) v
toAst (P.EORI WORD P2.SR v) = do
  doSRFlags ($^=) v
  doCCRFlags ($^) v
toAst (P.EORI t ea v) = doBitimm t ($^=) ea v
toAst (P.SUBI t ea v) = doArithimm doSub t ea v
toAst (P.ADDI t ea v) = doArithimm doAdd t ea v
toAst (P.CMPI t ea v) = doArithimm doCmp t ea v
toAst (P.BTST t ea sc) = doBit Nothing t ea sc
toAst (P.BCHG t ea sc) = doBit (Just R.BFLIP) t ea sc
toAst (P.BCLR t ea sc) = doBit (Just R.BCLR) t ea sc
toAst (P.BSET t ea sc) = doBit (Just R.BSET) t ea sc
toAst (P.CMP2 t ea rn) = do
  let ct =
        toCType
          t
          (case rn of
             P2.XR_D _ -> False
             P2.XR_A _ -> True)
      dn = xrV ct rn
      mem = ExprVar $ operand2Var (P2.Address ea) ct
      low = VarMember ct mem 0
      high = VarMember ct mem $ sizeOf ct
  ccZ $= (dn $== low) $|| (dn $== high)
  ccC $= (dn $< low) $|| (dn $> high)
toAst (P.CHK2 t ea rn) = do
  toAst (P.CMP2 t ea rn)
  if_ ccC $ do asm "TRAP" []
toAst (P.CAS t dc du ea) = do
  let ct = toCType t False
      dc_var = drV ct dc
      ea_var = operand2Var (P2.Address ea) ct
      du_var = drV ct du
  doCmp t ea_var dc_var
  ifElse_ ccZ (ea_var $= du_var) (dc_var $= ea_var)
toAst (P.CAS2 t dc1 dc2 du1 du2 rn1 rn2) = do
  let ct = toCType t False
      dc1_var = drV ct dc1
      dc2_var = drV ct dc2
      rn1_var = xrV ct rn1
      rn2_var = xrV ct rn2
      du1_var = drV ct du1
      du2_var = drV ct du2
      elseV = do
        dc1_var $= rn1_var
        dc2_var $= rn2_var
  doCmp t rn1_var dc1_var
  ifElse_
    ccZ
    (do doCmp t rn2_var dc2_var
        ifElse_
          ccZ
          (do rn1_var $= du1_var
              rn2_var $= du2_var)
          elseV)
    elseV
toAst (P.MOVES t toMem ea rn)
  | toMem = memM $= rnV
  | otherwise = rnV $= memM
  where
    ct = toCType t False
    rnV = xrV ct rn
    memM = operand2Var (P2.Address ea) ct
toAst (P.MOVEP t toMem a im d)
  | toMem = do
    addr 0 $= dvn3
    addr 2 $= dvn4
    if t == LONG
      then do
        addr 4 $= dvn2
        addr 6 $= dvn1
      else nullStmt
  | otherwise = do
    let h = addr 0 $<-> addr 2
        l = addr 4 $<-> addr 6
    if t == WORD
      then drV UINT16 d $= h
      else drV UINT32 d $= (h $<-> l)
  where
    addr x = VarMember INT8 (ExprVar $ arV (PTR UINT8) a) (im + x)
    dv = drV UINT32 d
    (dvn1:dvn2:dvn3:dvn4:_) =
      map (\x -> cast UINT8 (dv $>> uintE x)) [24, 16, 8, 0]
toAst (P.MOVE _ P2.CCR dst) = do
  let dstV = operand2Var dst UINT16
      cc =
        foldl
          ($|)
          (cast UINT16 ccC)
          [ cast UINT16 ccV $<< uintE 1
          , cast UINT16 ccZ $<< uintE 2
          , cast UINT16 ccN $<< uintE 3
          , cast UINT16 ccX $<< uintE 4
          ]
  dstV $= cc
toAst (P.MOVE _ P2.SR dst) = do
  let dstV = operand2Var dst UINT16
      sc =
        foldl
          ($|)
          (cast UINT16 ccC)
          [ cast UINT16 ccV $<< uintE 1
          , cast UINT16 ccZ $<< uintE 2
          , cast UINT16 ccN $<< uintE 3
          , cast UINT16 ccX $<< uintE 4
          , cast UINT16 $ GlobalVar UINT8 "I" $<< uintE 8
          , cast UINT16 $ ccFlags "M" $<< uintE 12
          , cast UINT16 $ ccFlags "S" $<< uintE 13
          , cast UINT16 $ GlobalVar UINT8 "T" $<< uintE 14
          ]
  dstV $= sc
toAst (P.MOVE _ (P2.SpRG c) dst) = do
  let dstV = operand2Var dst UINT16
  dstV $= GlobalVar (PTR VOID) c
toAst (P.MOVE _ src P2.CCR) = do
  let srcV = operand2Var src UINT16
  ccC $= bitTest srcV $ uintE 0
  ccV $= bitTest srcV $ uintE 1
  ccZ $= bitTest srcV $ uintE 2
  ccN $= bitTest srcV $ uintE 3
  ccX $= bitTest srcV $ uintE 4
toAst (P.MOVE t src P2.SR) = do
  let srcV = operand2Var src UINT16
  toAst (P.MOVE t src P2.CCR)
  GlobalVar UINT8 "I" $= (srcV $>> uintE 8) $& uintE 7
  ccFlags "M" $= bitTest srcV $ uintE 12
  ccFlags "S" $= bitTest srcV $ uintE 13
  GlobalVar UINT8 "T" $= (srcV $>> uintE 14) $& uintE 3
toAst (P.MOVE _ src (P2.SpRG c)) = do
  let srcV = operand2Var src UINT16
  GlobalVar (PTR VOID) c $= srcV
toAst (P.MOVE t src dst) = do
  let ct = toCType t False
      srcV = operand2Var src ct
      dstV = operand2Var dst ct
  clearVC
  dstV $= srcV
  testNZ t dstV
toAst (P.MOVEA t src dstN) = do
  let ct = toCType t True
      srcV = operand2Var src ct
  arV ct dstN $= srcV
toAst (P.NEGX t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
  dst $+= cast ct ccX
  ccV $= subV (intE 0) dst
  ccC $= subC (intE 0) dst
  ccX $= ccC
  dst $= neg dst
  if_ (dst $!= intE 0) $ ccZ $= intE 0
  ccN $= testN t dst
toAst (P.CLR t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
  clearVC
  dst $= uintE 0
  ccZ $= trueV
  ccN $= falseV
toAst (P.NEG t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
  ccV $= subV (intE 0) dst
  ccC $= intE 0 $!= dst
  ccX $= ccC
  dst $= neg dst
  testNZ t dst
toAst (P.NOT t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
  clearVC
  dst $= bNot dst
  testNZ t dst
toAst (P.TST t ea) = do
  let ct = toCType t True
      src = operand2Var ea ct
  clearVC
  testNZ t src
toAst (P.NBCD _ ea) = do
  let dst = operand2Var ea BCD
  ccC $= subC (uintE 0) dst
  ccX $= ccC
  dst $= neg dst
  ccZ $= lNot dst
toAst (P.TAS _ ea) = do
  let dstV = operand2Var ea UINT8
  clearVC
  testNZ BYTE dstV
  assignOp R.BSET dstV $ uintE 7
toAst (P.MULUL ea d) = do
  let src = operand2Var ea UINT32
      dst = drV UINT32 d
  ccC $= falseV
  ccV $= (dst `mulH` src) $!= uintE 0
  dst $*= src
  testNZ LONG dst
toAst (P.MULSL ea d) = do
  let src = operand2Var ea INT32
      dst = drV INT32 d
  ccC $= falseV
  ccV $= (dst `mulH` src) $!= intE 0
  dst $*= src
  testNZ LONG dst
toAst (P.MULULL ea h l) = do
  let src = operand2Var ea UINT32
      dst = drV UINT32 l
      dstH = drV UINT32 h
  clearVC
  dstH $= dst `mulH` src
  dst $*= src
  ccZ $= lNot dst $&& lNot dstH
  ccN $= testN LONG dstH
toAst (P.MULSLL ea h l) = do
  let src = operand2Var ea INT32
      dst = drV INT32 l
      dstH = drV INT32 h
  clearVC
  dstH $= dst `mulH` src
  dst $*= src
  ccZ $= lNot dst $&& lNot dstH
  ccN $= testN LONG dstH
toAst (P.DIVUL ea r q) = do
  let src = operand2Var ea UINT32
      dstR = drV UINT32 r
      dstQ = drV UINT32 q
      tmp = TmpVar UINT32 "tmp1"
  ccC $= falseV
  ccV $= dstQ `divV` src
  tmp $= dstQ
  dstQ $/= src
  testNZ LONG dstQ
  if q /= r
    then dstR $= tmp $% src
    else nullStmt
toAst (P.DIVSL ea r q) = do
  let src = operand2Var ea INT32
      dstR = drV INT32 r
      dstQ = drV INT32 q
      tmp = TmpVar INT32 "tmp1"
  ccC $= falseV
  ccV $= dstQ `divV` src
  tmp $= dstQ
  dstQ $/= src
  testNZ LONG dstQ
  if q /= r
    then dstR $= tmp $% src
    else nullStmt
toAst (P.DIVULL ea r q) = do
  let src = operand2Var ea UINT32
      dstR = drV UINT32 r
      dstQ = drV UINT32 q
      tmp = TmpVar UINT64 "tmp"
  ccC $= falseV
  tmp $= dstR $<-> dstQ
  ccV $= tmp `divV` src
  dstQ $= tmp $/ src
  testNZ LONG dstQ
  if q /= r
    then dstR $= tmp $% src
    else nullStmt
toAst (P.DIVSLL ea r q) = do
  let src = operand2Var ea INT32
      dstR = drV INT32 r
      dstQ = drV INT32 q
      tmp = TmpVar INT64 "tmp"
  ccC $= falseV
  tmp $= dstR $<-> dstQ
  ccV $= tmp `divV` src
  dstQ $= tmp $/ src
  testNZ LONG dstQ
  if q /= r
    then dstR $= tmp $% src
    else nullStmt
toAst (P.SWAP n) = do
  let dst = drV UINT32 n
  clearVC
  dst $= (dst `ror` uintE 16)
  testNZ LONG dst
toAst (P.TRAPn n) = asm "TRAP" [uintE n]
toAst (P.LINK rn imm) = do
  let dst = arV (PTR VOID) rn
      sp = arV (PTR VOID) (P2.AR 7)
  push $ ExprVar dst
  dst $= sp
  adjustSP imm
toAst (P.UNLK rn) = do
  let dst = arV (PTR VOID) rn
      sp = arV (PTR VOID) (P2.AR 7)
  sp $= dst
  pop dst
toAst P.RESET = asm "RESET" []
toAst P.NOP = nullStmt
toAst (P.STOP nw) = asm "STOP" [uintE nw]
toAst P.RTE = asm "iReturn" []
toAst (P.RTD n) = do
  return_
  adjustSP n
toAst P.RTS = return_
toAst P.TRAPV = if_ ccN $ asm "TRAP" []
toAst P.RTR = do
  let tmp = TmpVar UINT16 "temp"
  pop tmp
  ccC $= bitTest tmp $ uintE 0
  ccV $= bitTest tmp $ uintE 1
  ccZ $= bitTest tmp $ uintE 2
  ccN $= bitTest tmp $ uintE 3
  ccX $= bitTest tmp $ uintE 4
  return_
toAst (P.MOVEC True n name) = do
  let v = xrV UINT32 n
      spR = GlobalVar UINT32 name
  spR $= v
toAst (P.MOVEC False n name) = do
  let v = xrV UINT32 n
      spR = GlobalVar UINT32 name
  v $= spR
toAst (P.BKPT n) = asm "breakpoint" [uintE n]
toAst (P.PEA ea) = do
  let var = operand2Var (P2.Address ea) (PTR VOID)
  push $ ExprAddr var
toAst (P.EXT WORD n) = do
  let dst = drV INT16 n
  clearVC
  dst $= cast INT16 $ drV INT8 n
  testNZ WORD dst
toAst (P.EXT LONG n) = do
  let dst = drV INT32 n
  clearVC
  dst $= cast INT32 $ drV INT16 n
  testNZ LONG dst
toAst (P.EXTB n) = do
  let dst = drV INT32 n
  clearVC
  drV INT32 n $= cast INT32 $ drV INT8 n
  testNZ LONG dst
toAst (P.MOVEM t True (P2.UnRefDec (P2.AR 7)) regs) = do
  let ct = toCType t True
  mapM_ (\r -> push (ExprVar $ xrV ct r)) $ reverse regs
toAst (P.MOVEM t True (P2.UnRefDec an) regs) = do
  let ct = toCType t True
      base = arV (PTR ct) an
      regsR = reverse $ zip [0 ..] regs
      len = length regs
      temp = TmpVar (PTR VOID) "temp"
      sz =
        if t == WORD
          then 2
          else 4
  temp $= base $+ intE (-(len * sz))
  mapM_
    (\(i, n) ->
       let val = xrV ct n
        in VarArray (PTR ct) (ExprVar base) (intE (i :: Int)) $= val)
    regsR
  base $= temp
toAst (P.MOVEM t True ea regs) = do
  let ct = toCType t True
      base = operand2Var (P2.Address ea) (PTR ct)
      rs = zip [0 ..] regs
  mapM_
    (\(i, n) ->
       let val = xrV ct n
        in VarArray (PTR ct) (ExprVar base) (intE i) $= val)
    rs
toAst (P.MOVEM WORD False (P2.UnRefDec (P2.AR 7)) regs) = do
  let temp = TmpVar INT16 "temp"
  mapM_
    (\r ->
       (do pop temp
           xrV INT16 r $= cast INT16 temp))
    regs
toAst (P.MOVEM LONG False (P2.UnRefInc (P2.AR 7)) regs) =
  mapM_ (pop . xrV UINT32) regs
toAst (P.MOVEM WORD False (P2.UnRefInc an) regs) = do
  let base = arV (PTR INT16) an
      regsR = zip [0 ..] regs
      len = length regs
      temp = TmpVar (PTR VOID) "temp"
  temp $= base
  mapM_
    (\(i, n) ->
       xrV INT32 n $=
       cast INT32 (VarArray (PTR INT16) (ExprVar base) (intE (i :: Int))))
    regsR
  base $= temp $+ intE (len * 2)
toAst (P.MOVEM LONG False (P2.UnRefInc an) regs) = do
  let base = arV (PTR UINT32) an
      regsR = zip [0 ..] regs
      len = length regs
      temp = TmpVar (PTR VOID) "temp"
  temp $= base
  mapM_
    (\(i, n) ->
       xrV UINT32 n $= VarArray (PTR UINT32) (ExprVar base) (intE (i :: Int)))
    regsR
  base $= temp $+ intE (len * 4)
toAst (P.MOVEM WORD False ea regs) = do
  let base = operand2Var (P2.Address ea) (PTR INT16)
      regsR = zip [0 ..] regs
  mapM_
    (\(i, n) ->
       xrV INT32 n $=
       cast INT32 (VarArray (PTR INT16) (ExprVar base) (intE i)))
    regsR
toAst (P.MOVEM LONG False ea regs) = do
  let base = operand2Var (P2.Address ea) (PTR INT32)
      regsR = zip [0 ..] regs
  mapM_
    (\(i, n) -> xrV INT32 n $= VarArray (PTR INT32) (ExprVar base) (intE i))
    regsR
toAst (P.JSR ea) = do
  let base = operand2Var (P2.Address ea) (PTR VOID)
  call $ TargetIndirect $ ExprAddr base
toAst (P.JMP ea) = do
  let base = operand2Var (P2.Address ea) (PTR VOID)
  goto $ TargetIndirect $ ExprAddr base
toAst (P.CHK t ea n) = do
  let ct = toCType t True
      limit = operand2Var ea ct
      val = drV ct n
  ccN $= testN LONG val
  if_ (ccN $|| (val $> limit)) $ asm "TRAP" []
toAst (P.LEA ea n) = do
  let var = operand2Var (P2.Address ea) (PTR VOID)
  arV (PTR VOID) n $= ExprAddr var
toAst (P.ADDQ t v (P2.AReg an)) = do
  let ct = toCType t True
  arV ct an $+= uintE v
toAst (P.ADDQ t v ea) = toAst (ADDI t ea v)
toAst (P.SUBQ t v (P2.AReg an)) = do
  let ct = toCType t True
  arV ct an $-= uintE v
toAst (P.SUBQ t v ea) = toAst (SUBI t ea v)
toAst (P.TRAPcc (P2.CC cc) _) = if_ (ExprCondCC cc) $ asm "TRAP" []
toAst (P.Scc (P2.CC cc) ea) = do
  let var = operand2Var ea INT8
  var $= sel (ExprCondCC cc) (intE (-1)) (intE 0)
toAst (P.BRA target) = goto $ TargetAbsolute target
toAst (P.BSR target) = call $ TargetAbsolute target
toAst (P.Bcc (P2.CC cc) target) = if_ (ExprCondCC cc) (toAst (BRA target))
toAst (P.MOVEQ v n) = do
  let dst = drV INT32 n
  dst $= intE v
  clearVC
  testNZ LONG dst
toAst (P.DBcc (P2.CC cc) dn target) = do
  let dnv = drV INT16 dn
  if_
    (lNot $ ExprCondCC cc)
    (do dnv $-= intE 1
        if_ (dnv $!= intE (-1)) $ goto $ TargetAbsolute target)
toAst (P.OR t ea dn) = do
  let ct = toCType t False
      src = operand2Var ea ct
      dst = drV ct dn
  doBitop t ($|=) dst src
toAst (P.OR_TO_MEM t dn ea) = do
  let ct = toCType t False
      dst = operand2Var (P2.Address ea) ct
      src = drV ct dn
  doBitop t ($|=) dst src
toAst (P.DIVUW ea dn) = do
  let src = operand2Var ea UINT16
      dst = drV UINT32 dn
      tmp1 = TmpVar UINT16 "tmp1"
  ccC $= falseV
  ccV $= dst `divV` src
  tmp1 $= dst $% src
  dst $= dst $/ src
  testNZ WORD dst
  dst $= tmp1 $<-> dst
toAst (P.SBCD_REG x y) = do
  let s = drV BCD x
      d = drV BCD y
      tmp = TmpVar BCD "temp"
  tmp $= d $- cast BCD (ccFlags "X")
  d $= tmp $- s
  ccZ $&= d $== uintE 0
  ccC $= tmp `subC` s
  ccX $= ccC
toAst (P.SBCD_MEM x y) = do
  let s = deref $ VarDec True $ arV (PTR BCD) x
      d = VarDec True $ arV (PTR BCD) y
      tmp_d = TmpVar (PTR BCD) "temp1"
      tmp_s = TmpVar BCD "temp2"
      tmp = TmpVar BCD "temp3"
      tmp_dv = deref tmp_d
  tmp_d $= d
  tmp_s $= s
  tmp $= tmp_dv $- cast BCD ccX
  deref tmp_d $= tmp $- tmp_s
  ccZ $&= tmp_dv $== uintE 0
  ccC $= tmp `subC` tmp_s
  ccX $= ccC
toAst (P.PACK_REG x y imm) = do
  let s = ExprVar $ drV UINT16 x
      d = drV UINT8 y
  d $= ExprOp2 (Ex2 UINT8 "PACK") s (intE imm)
toAst (P.PACK_MEM x y imm) = do
  let s = ExprVar $ deref $ VarDec True $ arV (PTR UINT16) x
      d = deref $ VarDec True $ arV (PTR UINT8) y
  d $= ExprOp2 (Ex2 UINT8 "PACK") s (intE imm)
toAst (P.UNPK_REG x y imm) = do
  let s = ExprVar $ drV UINT8 x
      d = drV UINT16 y
  d $= ExprOp2 (Ex2 UINT16 "UNPK") s (intE imm)
toAst (P.UNPK_MEM x y imm) = do
  let s = ExprVar $ deref $ VarDec True $ arV (PTR UINT8) x
      d = deref $ VarDec True $ arV (PTR UINT16) y
  d $= ExprOp2 (Ex2 UINT16 "UNPK") s (intE imm)
toAst (P.DIVSW ea dn) = do
  let src = ExprVar $ operand2Var ea INT16
      dst = drV INT32 dn
      tmp1 = TmpVar INT16 "tmp1"
  ccC $= falseV
  ccV $= dst `divV` src
  tmp1 $= dst $% src
  dst $= dst $/ src
  testNZ WORD dst
  dst $= tmp1 $<-> dst
toAst (P.SUB t ea dn) =
  let ct = toCType t False
      src = operand2Var ea ct
      dst = drV ct dn
   in doSub t dst src
toAst (P.SUB_TO_MEM t dn ea) =
  let ct = toCType t False
      dst = operand2Var (P2.Address ea) ct
      src = drV ct dn
   in doSub t dst src
toAst (P.SUBA t ea an) = do
  let ct = toCType t False
      src = operand2Var ea ct
      dst = arV ct an
  dst $-= src
toAst (P.SUBX_REG t x y) = do
  let ct = toCType t True
      s = drV ct x
      d = drV ct y
  d $+= cast ct ccX
  ccV $= d `subV` s
  ccC $= d `subC` s
  ccX $= ccC
  d $-= s
  ccZ $&= lNot d
  ccN $= testN t d
toAst (P.SUBX_MEM t x y) = do
  let ct = toCType t True
      s = deref $ VarDec True $ arV (PTR ct) x
      d = VarDec True $ arV (PTR ct) y
      tmp_d = TmpVar (PTR ct) "temp1"
      tmp_sv = TmpVar ct "temp2"
      tmp_dv = TmpVar ct "temp3"
  tmp_d $= d
  tmp_sv $= s
  tmp_dv $= deref tmp_d $- cast ct ccX
  doSub t tmp_dv tmp_sv
  deref tmp_d $= tmp_dv
toAst (P.CMP t ea dn) =
  let ct = toCType t False
      src = operand2Var ea ct
      dst = drV ct dn
   in doCmp t dst src
toAst (P.CMPA t ea an) =
  let ct = toCType t False
      srcX = operand2Var ea ct
      src =
        if t == WORD
          then cast INT32 srcX
          else ExprVar srcX
      dst = arV INT32 an
   in doCmp t dst src
toAst (P.CMPM t y x) = do
  let ct = toCType t True
      s = deref $ VarInc False $ arV (PTR ct) x
      d = deref $ VarInc False $ arV (PTR ct) y
      tmp_s = TmpVar ct "tmp1"
      tmp_d = TmpVar ct "tmp2"
  tmp_d $= d
  tmp_s $= s
  doCmp t tmp_d tmp_s
toAst (P.EOR t dn ea) =
  let ct = toCType t False
      dst = operand2Var ea ct
      src = drV ct dn
   in doBitop t ($^=) dst src
toAst (P.AND t ea dn) =
  let ct = toCType t False
      src = operand2Var ea ct
      dst = drV ct dn
   in doBitop t ($&=) dst src
toAst (P.AND_TO_MEM t dn ea) =
  let ct = toCType t False
      dst = operand2Var (P2.Address ea) ct
      src = drV ct dn
   in doBitop t ($&=) dst src
toAst (P.MULUW ea dn) = do
  let src = cast UINT32 $ operand2Var ea UINT16
      dst = drV UINT32 dn
  clearVC
  dst $*= src
  testNZ LONG dst
toAst (P.ABCD_REG y x) = do
  let s = drV BCD y
      d = drV BCD x
  d $+= cast BCD ccX
  ccC $= d `addC` s
  ccX $= ccC
  d $+= s
  ccZ $&= d $== uintE 0
toAst (P.ABCD_MEM y x) = do
  let s = deref $ VarDec True $ arV (PTR BCD) x
      d = deref $ VarDec True $ arV (PTR BCD) y
      tmp_s = TmpVar BCD "tmp1"
      tmp_d = TmpVar BCD "tmp2"
      tmp_dv = TmpVar (PTR BCD) "tmp3"
  tmp_dv $= d
  tmp_d $= d $+ cast BCD ccX
  tmp_s $= s
  ccC $= tmp_d `addC` tmp_s
  ccX $= ccC
  tmp_dv $+= tmp_s
  ccZ $&= d $== uintE 0
toAst (P.MULSW ea dn) = do
  let src = cast INT32 $ operand2Var ea INT16
      dst = drV INT32 dn
  clearVC
  dst $*= src
  testNZ LONG dst
toAst (P.EXG_D x y) = do
  let dx = drV UINT32 x
      dy = drV UINT32 y
      tmp = TmpVar UINT32 "temp"
  tmp $= dx
  dx $= dy
  dy $= tmp
toAst (P.EXG_A x y) = do
  let dx = arV (PTR VOID) x
      dy = arV (PTR VOID) y
      tmp = TmpVar (PTR VOID) "temp"
  tmp $= dx
  dx $= dy
  dy $= tmp
toAst (P.EXG_DA x y) = do
  let dx = drV UINT32 x
      dy = arV (PTR VOID) y
      tmp = TmpVar UINT32 "temp"
  tmp $= dx
  dx $= cast UINT32 dy
  dy $= cast (PTR VOID) tmp
toAst (P.SYS i) = asm "SYSCALL" [uintE i]
toAst (P.ADD t ea dn) =
  let ct = toCType t False
      src = operand2Var ea ct
      dst = drV ct dn
   in doAdd t dst src
toAst (P.ADD_TO_MEM t dn ea) =
  let ct = toCType t False
      dst = operand2Var (P2.Address ea) ct
      src = drV ct dn
   in doAdd t dst src
toAst (P.ADDA t ea an) = do
  let ct = toCType t False
      src = cast INT32 $ operand2Var ea ct
      dst = arV INT32 an
  dst $+= src
toAst (P.ADDX_REG t x y) = do
  let ct = toCType t True
      s = drV ct x
      d = drV ct y
  d $+= cast ct ccX
  ccV $= d `addV` s
  ccC $= d `addC` s
  ccX $= ccC
  d $+= s
  ccZ $&= lNot d
  ccN $= testN t d
toAst (P.ADDX_MEM t x y) = do
  let ct = toCType t True
      s = deref $ VarDec True $ arV (PTR ct) x
      d = VarDec True $ arV (PTR ct) y
      tmp_d = TmpVar (PTR ct) "temp1"
      tmp_sv = TmpVar ct "temp2"
      tmp_dv = TmpVar ct "temp3"
  tmp_d $= d
  tmp_sv $= s
  tmp_dv $= deref tmp_d $+ cast ct ccX
  ccV $= tmp_dv `addV` tmp_sv
  ccC $= tmp_dv `addC` tmp_sv
  ccX $= ccC
  tmp_dv $+= tmp_sv
  ccZ $&= lNot tmp_dv
  ccN $= testN t tmp_dv
toAst (P.ASR t sc reg) = do
  let (_, sc_v, dst) = shiftArg t True sc reg
      carry = bitTest dst (sc_v $- uintE 1)
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $>>= sc_v)
    (do ccC $= falseV)
  testNZ t dst
toAst (P.ASL t sc reg) = do
  let (scc, sc_v, dst) = shiftArg t True sc reg
      carry = bitTest dst (scc $- sc_v)
  ccV $= ExprOp2 (Ex2 BOOL "sl_overflow") (ExprVar dst) sc_v
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $<<= sc_v)
    (do ccC $= falseV)
  testNZ t dst
toAst (P.LSR t sc reg) = do
  let (_, sc_v, dst) = shiftArg t False sc reg
      carry = bitTest dst (sc_v $- uintE 1)
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $>>= sc_v)
    (ccC $= falseV)
  testNZ t dst
toAst (P.LSL t sc reg) = do
  let (scc, sc_v, dst) = shiftArg t False sc reg
      carry = bitTest dst (scc $- sc_v)
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $<<= sc_v)
    (ccC $= falseV)
  testNZ t dst
toAst (P.ROXR t sc reg) = do
  let (_, sc_v, dst) = shiftArg t False sc reg
      carry = bitTest dst $ sc_v $- uintE 1
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $=
          ExprOpN (toCType t False) "rorx" [ExprVar dst, sc_v, ExprVar ccX])
    (ccC $= ccX)
  testNZ t dst
toAst (P.ROXL t sc reg) = do
  let (sz, sc_v, dst) = shiftArg t False sc reg
      carry = bitTest dst $ sz $- sc_v
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $= ExprOpN (toCType t False) "rolx" [ExprVar dst, sc_v, ExprVar ccX])
    (ccC $= ccX)
  testNZ t dst
toAst (P.ROR t sc reg) = do
  let (_, sc_v, dst) = shiftArg t False sc reg
      carry = bitTest dst $ sc_v $- uintE (1 :: Int)
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        dst $= dst `ror` sc_v)
    (ccC $= falseV)
  testNZ t dst
toAst (P.ROL t sc reg) = do
  let (sz, sc_v, dst) = shiftArg t False sc reg
      carry = bitTest dst $ sz $- sc_v
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        dst $= dst `rol` sc_v)
    (ccC $= falseV)
  testNZ t dst
toAst (P.ASR_EA ea) = do
  let dst = operand2Var (P2.Address ea) INT16
  ccV $= falseV
  ccC $= bitTest dst $ uintE 0
  ccX $= ccC
  dst $>>= uintE (1 :: Int)
  testNZ WORD dst
toAst (P.ASL_EA ea) = do
  let dst = operand2Var (P2.Address ea) INT16
  ccV $= bitTest dst (uintE (15 :: Int)) $== bitTest dst ( uintE (14 :: Int))
  ccC $= bitTest dst $ uintE (15 :: Int)
  ccX $= ccC
  dst $<<= uintE (1 :: Int)
  testNZ WORD dst
toAst (P.LSR_EA ea) = do
  let dst = operand2Var (P2.Address ea) UINT16
  ccV $= falseV
  ccC $= bitTest dst $ uintE (0 :: Int)
  ccX $= ccC
  dst $>>= uintE (1 :: Int)
  testNZ WORD dst
toAst (P.LSL_EA ea) = do
  let dst = operand2Var (P2.Address ea) UINT16
  ccV $= falseV
  ccC $= bitTest dst $ uintE (15 :: Int)
  ccX $= ccC
  dst $<<= uintE (1 :: Int)
  testNZ WORD dst
toAst (P.ROXR_EA ea) = do
  let dst = operand2Var (P2.Address ea) UINT16
      carry = bitTest dst $ uintE (0 :: Int)
  ccV $= falseV
  ccC $= carry
  ccX $= ccC
  dst $= ExprOpN UINT16 "rorx" [ExprVar dst, uintE 1, ExprVar ccX]
  testNZ WORD dst
toAst (P.ROXL_EA ea) = do
  let dst = operand2Var (P2.Address ea) UINT16
      carry = bitTest dst $ uintE (15 :: Int)
  ccV $= falseV
  ccC $= carry
  ccX $= ccC
  dst $= ExprOpN UINT16 "rolx" [ExprVar dst, uintE 1, ExprVar ccX]
  testNZ WORD dst
toAst (P.ROR_EA ea) = do
  let dst = operand2Var (P2.Address ea) UINT16
      carry = bitTest dst $ uintE (0 :: Int)
  ccV $= falseV
  ccC $= carry
  dst $= dst `ror` uintE (1 :: Int)
  testNZ WORD dst
toAst (P.ROL_EA ea) = do
  let dst = operand2Var (P2.Address ea) UINT16
      carry = bitTest dst $ uintE (15 :: Int)
  ccV $= falseV
  ccC $= carry
  dst $= dst `rol` uintE (1 :: Int)
  testNZ WORD dst
toAst (P.BFTST ea (BImm off) (BImm width)) = do
  let t
        | width < 8 = UINT8
        | width < 16 = UINT16
        | otherwise = UINT32
      dst = operand2Var ea UINT16
  clearVC
  testNZ LONG $ VarBitField t dst off width
toAst (P.BFTST (P2.DReg d) offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      temp = TmpVar UINT32 "temp"
  clearVC
  temp $= ExprOpN UINT32 "bfGet_l" [ExprVar (drV UINT32 d), offset, width]
  testNZ LONG temp
toAst (P.BFTST ea offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      temp = TmpVar UINT32 "temp"
      src = operand2Var ea (PTR VOID)
  clearVC
  temp $= ExprOpN UINT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG temp
toAst (P.BFCHG ea (BImm off) (BImm width)) = do
  let t
        | width < 8 = UINT8
        | width < 16 = UINT16
        | otherwise = UINT32
      dst = VarBitField t (operand2Var ea UINT16) off width
  clearVC
  testNZ LONG dst
  dst $= bNot dst
toAst (P.BFCHG (P2.DReg d) offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      temp = TmpVar UINT32 "temp"
  clearVC
  temp $= ExprOpN UINT32 "bfGet_l" [ExprVar (drV UINT32 d), offset, width]
  testNZ LONG temp
  drV UINT32 d $^= ExprOp2 (Ex2 UINT32 "bfMask") offset width
toAst (P.BFCHG ea offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      temp = TmpVar UINT32 "temp"
      dst = operand2Var ea (PTR VOID)
  clearVC
  temp $= ExprOpN UINT32 "bfGet_b" [ExprVar dst, offset, width]
  testNZ LONG temp
  asm "bfchg_m" [ExprAddr dst, offset, width]
toAst (P.BFCLR ea (BImm off) (BImm width)) = do
  let t
        | width < 8 = UINT8
        | width < 16 = UINT16
        | otherwise = UINT32
      dst = VarBitField t (operand2Var ea UINT16) off width
  clearVC
  testNZ LONG dst
  dst $= intE 0
toAst (P.BFCLR (P2.DReg d) offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      temp = TmpVar UINT32 "temp"
  clearVC
  temp $= ExprOpN UINT32 "bfGet_l" [ExprVar (drV UINT32 d), offset, width]
  testNZ LONG temp
  drV UINT32 d $&= bNot ( ExprOp2 (Ex2 UINT32 "bfMask") offset width)
toAst (P.BFCLR ea offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      temp = TmpVar UINT32 "temp"
      dst = operand2Var ea (PTR VOID)
  clearVC
  temp $= ExprOpN UINT32 "bfGet_b" [ExprVar dst, offset, width]
  testNZ LONG temp
  asm "bfclr_m" [ExprAddr dst, offset, width]
toAst (P.BFSET ea (BImm off) (BImm width)) = do
  let t
        | width < 8 = INT8
        | width < 16 = INT16
        | otherwise = INT32
      dst = VarBitField t (operand2Var ea UINT16) off width
  clearVC
  testNZ LONG dst
  dst $= intE (-1)
toAst (P.BFSET (P2.DReg d) offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      temp = TmpVar UINT32 "temp"
  clearVC
  temp $= ExprOpN UINT32 "bfGet_l" [ExprVar (drV UINT32 d), offset, width]
  testNZ LONG temp
  drV UINT32 d $|= ExprOp2 (Ex2 UINT32 "bfMask") offset width
toAst (P.BFSET ea offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      temp = TmpVar UINT32 "temp"
      dst = operand2Var ea (PTR VOID)
  clearVC
  temp $= ExprOpN UINT32 "bfGet_b" [ExprVar dst, offset, width]
  testNZ LONG temp
  asm "bfset_m" [ExprAddr dst, offset, width]
toAst (P.BFEXTU (P2.DReg d) (BImm o) (BImm w) dn) = do
  let t
        | w < 8 = UINT8
        | w < 16 = UINT16
        | otherwise = UINT32
      dst = drV UINT32 dn
  clearVC
  dst $= VarBitField t (drV UINT32 d) o w
  testNZ LONG $ drV UINT32 d
toAst (P.BFEXTU (P2.DReg d) offset_p width_p dn) = do
  let (offset, width) = bfArg offset_p width_p
      src = drV UINT32 d
      dst = drV UINT32 dn
  clearVC
  dst $= ExprOpN UINT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG dst
  asm "bfset_m" [ExprAddr dst, offset, width]
toAst (P.BFEXTU ea offset_p width_p dn) = do
  let (offset, width) = bfArg offset_p width_p
      src = operand2Var ea (PTR VOID)
      dst = drV UINT32 dn
  clearVC
  dst $= ExprOpN UINT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG dst
  asm "bfset_m" [ExprAddr dst, offset, width]
toAst (P.BFEXTS (P2.DReg d) (BImm o) (BImm w) dn) = do
  let t
        | w < 8 = INT8
        | w < 16 = INT16
        | otherwise = INT32
      dst = drV INT32 dn
  clearVC
  dst $= VarBitField t (drV INT32 d) o w
  testNZ LONG $ drV INT32 d
toAst (P.BFEXTS (P2.DReg d) offset_p width_p dn) = do
  let (offset, width) = bfArg offset_p width_p
      src = drV INT32 d
      dst = drV INT32 dn
  clearVC
  dst $= ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG dst
  asm "bfset_m" [ExprAddr dst, offset, width]
toAst (P.BFEXTS ea offset_p width_p dn) = do
  let (offset, width) = bfArg offset_p width_p
      src = operand2Var ea (PTR VOID)
      dst = drV INT32 dn
  clearVC
  dst $= ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG dst
  asm "bfset_m" [ExprAddr dst, offset, width]
toAst (P.BFFFO (P2.DReg d) (BImm o) (BImm w) dn) = do
  let t
        | w < 8 = INT8
        | w < 16 = INT16
        | otherwise = INT32
      dst = drV INT32 dn
      tmp = TmpVar UINT32 "temp"
  clearVC
  tmp $= VarBitField t (drV INT32 d) o w
  dst $= ExprOp1 (Ex1 UINT32 "bfffo") (ExprVar tmp)
  testNZ LONG tmp
toAst (P.BFFFO (P2.DReg d) offset_p width_p dn) = do
  let (offset, width) = bfArg offset_p width_p
      src = drV INT32 d
      tmp = TmpVar UINT32 "temp"
      dst = drV INT32 dn
  clearVC
  tmp $= ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG tmp
  dst $= ExprOpN UINT32 "bfffo_d" [ExprAddr dst, offset, width]
toAst (P.BFFFO ea offset_p width_p dn) = do
  let (offset, width) = bfArg offset_p width_p
      tmp = TmpVar INT32 "temp"
      src = operand2Var ea (PTR VOID)
      dst = drV INT32 dn
  clearVC
  tmp $= ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG tmp
  dst $= ExprOpN UINT32 "bfffo_m" [ExprAddr dst, offset, width]
toAst (P.BFINS dn (P2.DReg d) (BImm o) (BImm w)) = do
  let t
        | w < 8 = INT8
        | w < 16 = INT16
        | otherwise = INT32
      src = drV INT32 dn
      dst = VarBitField t (drV INT32 d) o w
  clearVC
  testNZ LONG dst
  dst $= src
toAst (P.BFINS dn (P2.DReg d) offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      src = drV INT32 d
      dst = drV INT32 dn
  clearVC
  testNZ LONG $ ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  dst $= ExprOpN UINT32 "bfins_d" [ExprAddr dst, ExprVar src, offset, width]
toAst (P.BFINS dn ea offset_p width_p) = do
  let (offset, width) = bfArg offset_p width_p
      dst = operand2Var ea (PTR VOID)
      src = drV INT32 dn
  clearVC
  testNZ LONG $ ExprOpN INT32 "bfGet_b" [ExprVar dst, offset, width]
  dst $= ExprOpN UINT32 "bfins_m" [ExprAddr dst, ExprAddr src, offset, width]
toAst (P.FOp op src dst) = do
  let dstV = frV AST.CType.EXT dst
  dstV $= ExprOp1 (Ex1 AST.CType.EXT op) $ getFpuSrc src
  testResult dstV
toAst (P.FSINCOS src dstC dstS) = do
  let dstV1 = frV AST.CType.EXT dstC
      dstV2 = frV AST.CType.EXT dstS
  dstV1 $= ExprOp1 (Ex1 AST.CType.EXT "cos") $ getFpuSrc src
  dstV2 $= ExprOp1 (Ex1 AST.CType.EXT "sin") $ getFpuSrc src
toAst (P.FTST src) = do
  testResult $ getFpuSrc src
toAst _ = asm "TRAP" []

testResult :: Term a1 => a1 -> StmtM
testResult val = do
  ccFlags "FZ" $= val $== ExprFlt (fromDouble 0.0)
  ccFlags "FN" $= val $< ExprFlt (fromDouble 0.0)
  ccFlags "FNan" $= ExprOp1 (Ex1 BOOL "isNan") $ getExpr val
shiftArg :: AType -> Bool -> BopSc -> P2.DR -> (Expr, Expr, Var)
shiftArg t signed sc reg =
  let scc =
        uintE $
        case t of
          BYTE -> 8
          WORD -> 16
          LONG -> 32
      ct = toCType t signed
      sc_v =
        case sc of
          BReg dr -> ExprVar $ drV UINT8 dr
          BImm n ->
            uintE
              (if n == 0
                 then 8
                 else n)
      dst = drV ct reg
   in (scc, sc_v, dst)

bfArg :: BopSc -> BopSc -> (Expr, Expr)
bfArg offset_p width_p =
  ( case offset_p of
      BImm n -> uintE n
      BReg n -> ExprVar $ drV UINT32 n
  , case width_p of
      BImm n -> uintE n
      BReg n -> ExprVar $ drV UINT32 n)

getFpuSrc :: FpuOperand -> Expr
getFpuSrc (FpuRn src) = ExprVar $ frV AST.CType.EXT src
getFpuSrc (FpuOperandInt t v) = cast AST.CType.EXT $ operand2Var v $ toCType t True
getFpuSrc (FpuOperandFlt t v) = cast AST.CType.EXT $ operand2Var (Address v) $ toCTypeF t
getFpuSrc (FpuImm _ v) = cast AST.CType.EXT $ ExprFlt v
