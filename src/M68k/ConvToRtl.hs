{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module M68k.ConvToRtl
  ( toRtl
  , trueV
  , falseV
  , operand2Var
  , dr_v
  , ar_v
  , xr_v
  ) where

import           AST.Common                as R
import           AST.CType
import           AST.Expr
import           AST.Stmt
import           Data.Bits                 (Bits, (.&.), (.>>.))
import           M68k.Common
import           M68k.Opcode
import           M68k.Opcode               as P
import           M68k.Operand
import           M68k.Operand              as P2
import           Text.Printf               (printf)

-- decompile 1st phase
default (Integer, Double)

toCType :: AType -> Bool -> CType
toCType BYTE False = UINT8
toCType WORD False = UINT16
toCType LONG False = UINT32
toCType BYTE True  = INT8
toCType WORD True  = INT16
toCType LONG True  = INT32

dr_v :: CType -> DR -> Var
dr_v t (DR n) = RtlReg t $ printf "D%d" n

ar_v :: CType -> AR -> Var
ar_v t (AR n) = RtlReg t $ printf "A%d" n

xr_v :: CType -> XR -> Var
xr_v t (XR_D d) = dr_v t $ DR d
xr_v t (XR_A d) = ar_v t $ AR d

applyEaBase :: AddrBase -> Int -> CType -> Var
applyEaBase (BaseAR r) bd t  = RtlMemoryI t (ExprVar $ ar_v (PTR VOID) r) bd
applyEaBase (BasePC pc) bd t = RtlMemoryC t $ pc + bd
applyEaBase BaseNone bd t    = RtlMemoryG t bd

-- base + rn.w*cc -> ((cct*)base) [ rn ]
applyRn :: Var -> Bool -> Maybe XR -> Int -> CType -> Var
applyRn base w (Just rn) cc t =
  let cType =
        (case cc of
           0 -> UINT8
           1 -> UINT16
           2 -> UINT32
           3 -> UINT64)
      getIndex True n  = ExprCast INT32 $ ExprVar $ xr_v INT16 n
      getIndex False n = ExprVar $ xr_v INT32 n
      index = getIndex w rn
   in VarCast t $ RtlMemoryD cType (ExprVar base) index
applyRn base _ Nothing _ t = VarCast t $ base

operand2Var :: Operand -> CType -> Var
operand2Var (DReg d) t = dr_v t d
operand2Var (AReg a) t = ar_v t a
operand2Var (Address (UnRefAR r)) t = deref $ ar_v (PTR t) r -- (An)
operand2Var (Address (UnRefInc r)) t =
  deref $ RtlInc False $ ar_v (PTR t) r -- (An+)
operand2Var (Address (UnRefDec r)) t =
  deref $ RtlDec True $ ar_v (PTR t) r -- (-An)
operand2Var (Address (Offset16 d base)) t = applyEaBase base d t -- (d, An/PC/0)
operand2Var (Address (Offset8 d base w rn cc)) t -- (d, An/PC/0, rn.w*cc)
 =
  let base1 = applyEaBase base d $ PTR VOID
   in applyRn base1 w (Just rn) cc t
operand2Var (Address (Indirect bd base w rn cc)) t -- (bd, An/PC/0, rn.w*cc)
 =
  let base1 = applyEaBase base bd $ PTR VOID
   in applyRn base1 w rn cc t
operand2Var (Address (PreIndex bd base w rn cc od)) t -- ([bd, An/PC/0, rn.w*cc], od)
 =
  let base1 = applyEaBase base bd $ PTR VOID
      base2 = applyRn base1 w rn cc $ PTR VOID
   in RtlMemoryI t (ExprVar base2) od
operand2Var (Address (PostIndex bd base w rn cc od)) t -- ([bd, An/PC/0], rn.w*cc, od)
 =
  let base1 = applyEaBase base bd $ PTR VOID
      base2 = RtlMemoryI (PTR VOID) (ExprVar base1) od
   in applyRn base2 w rn cc t
operand2Var (Address (ImmAddr addr)) t = RtlMemoryG t addr
operand2Var _ _ = undefined

ccFlags :: [Char] -> Var
ccFlags name = RtlReg BOOL name

doCCRFlags :: (Term a1, Num a2, Bits a2) => (Expr -> Expr -> a1) -> a2 -> StmtM
doCCRFlags op v =
  (mapM_
     (\(i, k) ->
        (ccFlags k) $= op (ExprVar $ ccFlags k) (boolE $ (v .>>. i) .&. 1)))
    [(0, "C"), (1, "V"), (2, "Z"), (3, "N"), (4, "X")]

doSRFlags :: (Integral a, Bits a) => (Var -> Expr -> StmtM) -> a -> StmtM
doSRFlags op v = do
  op (RtlReg UINT8 "I") $ uintE ((v .>>. 8) .&. 7)
  op (RtlReg BOOL "M") $ boolE ((v .>>. 12) .&. 1)
  op (RtlReg BOOL "S") $ boolE ((v .>>. 13) .&. 1)
  op (RtlReg UINT8 "T") $ uintE ((v .>>. 14) .&. 3)

testN :: Term a => AType -> a -> Expr
testN t v =
  let ctype = toCType t True
   in (cast ctype v) $< intE 0

testCmpN :: (Term a1, Term a2) => AType -> a1 -> a2 -> Expr
testCmpN t a b =
  let ctype = toCType t True
   in (cast ctype a) $< (cast ctype b)

falseV :: Expr
falseV = ExprBool False

trueV :: Expr
trueV = ExprBool True

{-
getCondCas :: AType -> Int -> Operand -> Int -> Expr
getCondCas t dc ea cc
  | cc == 2 = ExprGt ea_val dc_val
  | cc == 3 = ExprLeq ea_val dc_val
  | cc == 4 = ExprGeq ea_val dc_val
  | cc == 5 = ExprLt ea_val dc_val
  | cc == 6 = ExprEq ea_val dc_val
  | cc == 7 = ExprNeq ea_val dc_val
  | cc == 12 = ExprGeq ea_val' dc_val'
  | cc == 13 = ExprLt ea_val' dc_val'
  | cc == 14 = ExprGt ea_val' dc_val'
  | cc == 15 = ExprLeq ea_val' dc_val'
  where
    ct1 = toCType t False
    ct2 = toCType t True
    dc_val = ExprVar $ dr_v ct1 dc
    ea_val = ExprVar $ operand2Var ea ct1
    dc_val' = ExprVar $ dr_v ct2 dc
    ea_val' = ExprVar $ operand2Var ea ct2

getCondX :: Int -> Expr
getCondX 0 = trueV
getCondX 1 = falseV
getCondX 2 = ExprLAnd (ExprLNot (ccFlagsV "C")) (ExprLNot $ ccFlagsV "Z")
getCondX 3 = ExprLOr (ccFlagsV "C") (ccFlagsV "Z")
getCondX 4 = ExprLNot $ ccFlagsV "C"
getCondX 5 = ccFlagsV "C"
getCondX 6 = ExprLNot $ ccFlagsV "Z"
getCondX 7 = ccFlagsV "Z"
getCondX 8 = ExprLNot $ ccFlagsV "V"
getCondX 9 = ccFlagsV "V"
getCondX 10 = ExprLNot $ ccFlagsV "N"
getCondX 11 = ccFlagsV "N"
getCondX 12 = ExprEq (ccFlagsV "N") (ccFlagsV "V")
getCondX 13 = ExprNeq (ccFlagsV "N") (ccFlagsV "V")
getCondX 14 =
  ExprLAnd (ExprEq (ccFlagsV "N") (ccFlagsV "V")) (ExprLNot $ ccFlagsV "Z")
getCondX 15 =
  ExprLOr (ExprEq (ccFlagsV "N") (ccFlagsV "V")) (ExprLNot $ ccFlagsV "Z")

getCond :: Op -> Int -> Expr
getCond (P.SUBI t ea v) cc
  | cc == 2 = ExprGt (ExprVar $ operand2Var ea ct1) (ExprImm ct1 v)
  | cc == 3 = ExprLeq (ExprVar $ operand2Var ea ct1) (ExprImm ct1 v)
  | cc == 12 = ExprGeq (ExprVar $ operand2Var ea ct2) (ExprImm ct2 v)
  | cc == 13 = ExprLt (ExprVar $ operand2Var ea ct2) (ExprImm ct2 v)
  | cc == 14 = ExprGt (ExprVar $ operand2Var ea ct2) (ExprImm ct2 v)
  | cc == 15 = ExprLeq (ExprVar $ operand2Var ea ct2) (ExprImm ct2 v)
  where
    ct1 = toCType t False
    ct2 = toCType t True
getCond (P.ADDI t ea v) cc
  | cc == 12 = ExprGeq (ExprVar $ operand2Var ea ct2) (ExprImm ct2 (-v))
  | cc == 13 = ExprLt (ExprVar $ operand2Var ea ct2) (ExprImm ct2 (-v))
  | cc == 14 = ExprGt (ExprVar $ operand2Var ea ct2) (ExprImm ct2 (-v))
  | cc == 15 = ExprLeq (ExprVar $ operand2Var ea ct2) (ExprImm ct2 (-v))
  where
    ct2 = toCType t True
getCond (P.CMPI t ea v) cc
  | cc == 2 = ExprGt (ExprVar $ operand2Var ea ct1) (ExprImm ct1 v)
  | cc == 3 = ExprLeq (ExprVar $ operand2Var ea ct1) (ExprImm ct1 v)
  | cc == 4 = ExprGeq (ExprVar $ operand2Var ea ct1) (ExprImm ct1 v)
  | cc == 5 = ExprLt (ExprVar $ operand2Var ea ct1) (ExprImm ct1 v)
  | cc == 6 = ExprEq (ExprVar $ operand2Var ea ct1) (ExprImm ct1 v)
  | cc == 7 = ExprNeq (ExprVar $ operand2Var ea ct1) (ExprImm ct1 v)
  | cc == 12 = ExprGeq (ExprVar $ operand2Var ea ct2) (ExprImm ct2 v)
  | cc == 13 = ExprLt (ExprVar $ operand2Var ea ct2) (ExprImm ct2 v)
  | cc == 14 = ExprGt (ExprVar $ operand2Var ea ct2) (ExprImm ct2 v)
  | cc == 15 = ExprLeq (ExprVar $ operand2Var ea ct2) (ExprImm ct2 v)
  where
    ct1 = toCType t False
    ct2 = toCType t True
getCond (P.CAS t dc _ ea) cc = getCondCas t dc (Address ea) cc
getCond (P.CAS2 t dc1 dc2 _ _ rn1 rn2) cc =
  let rn1_ea =
        if rn1 < 8
          then (dr_v rn1)
          else (AR (rn1 - 8))
      rn2_ea =
        if rn2 < 8
          then (dr_v rn2)
          else (AR (rn2 - 8))
      cond1 = getCondCas t dc1 rn1_ea cc
      cond1_nz = getCondCas t dc1 rn1_ea 7
   in ExprSel cond1_nz cond1 $ getCondCas t dc2 rn2_ea cc
getCond (P.NEGX t ea) cc
  | cc == 2 = ExprGt oldx (ExprVar $ operand2Var ea ct1)
  | cc == 3 = ExprLeq oldx (ExprVar $ operand2Var ea ct1)
  | cc == 4 = ExprGeq oldx (ExprVar $ operand2Var ea ct1)
  | cc == 5 = ExprLt oldx (ExprVar $ operand2Var ea ct1)
  | cc == 6 = ExprEq oldx (ExprVar $ operand2Var ea ct1)
  | cc == 7 = ExprNeq oldx (ExprVar $ operand2Var ea ct1)
  | cc == 12 = ExprGeq oldx' (ExprVar $ operand2Var ea ct2)
  | cc == 13 = ExprLt oldx' (ExprVar $ operand2Var ea ct2)
  | cc == 14 = ExprGt oldx' (ExprVar $ operand2Var ea ct2)
  | cc == 15 = ExprLeq oldx' (ExprVar $ operand2Var ea ct2)
  where
    ct1 = toCType t False
    ct2 = toCType t True
    oldx = ExprCast ct1 $ ExprVar $ RtlReg BOOL "X"
    oldx' = ExprCast ct2 $ ExprVar $ RtlReg BOOL "X"
getCond (P.NEG t ea) cc
  | cc == 2 = ExprGt zero (ExprVar $ operand2Var ea ct1)
  | cc == 3 = ExprLeq zero (ExprVar $ operand2Var ea ct1)
  | cc == 4 = ExprGeq zero (ExprVar $ operand2Var ea ct1)
  | cc == 5 = ExprLt zero (ExprVar $ operand2Var ea ct1)
  | cc == 6 = ExprEq zero (ExprVar $ operand2Var ea ct1)
  | cc == 7 = ExprNeq zero (ExprVar $ operand2Var ea ct1)
  | cc == 12 = ExprGeq zero' (ExprVar $ operand2Var ea ct2)
  | cc == 13 = ExprLt zero' (ExprVar $ operand2Var ea ct2)
  | cc == 14 = ExprGt zero' (ExprVar $ operand2Var ea ct2)
  | cc == 15 = ExprLeq zero' (ExprVar $ operand2Var ea ct2)
  where
    ct1 = toCType t False
    ct2 = toCType t True
    zero = ExprImm ct1 0
    zero' = ExprImm ct2 0
getCond (P.ADDQ t v ea) cc =
  case ea of
    AR _ -> getCondX cc
    _    -> getCond (ADDI t ea v) cc
getCond (P.SUBQ t v ea) cc =
  case ea of
    AR _ -> getCondX cc
    _    -> getCond (SUBI t ea v) cc
getCond (P.SUB t ea dn) cc
  | cc == 2 = ExprGt lv1 rv1
  | cc == 3 = ExprLeq lv1 rv1
  | cc == 12 = ExprGeq lv2 rv2
  | cc == 13 = ExprLt lv2 rv2
  | cc == 14 = ExprGt lv2 rv2
  | cc == 15 = ExprLeq lv2 rv2
  where
    ct1 = toCType t False
    ct2 = toCType t True
    lv1 = (ExprVar $ operand2Var ea ct1)
    lv2 = (ExprVar $ operand2Var ea ct2)
    rv1 = (ExprVar $ dr_v ct1 dn)
    rv2 = (ExprVar $ dr_v ct2 dn)
getCond (P.SUB_TO_MEM t dn ea) cc
  | cc == 2 = ExprGt lv1 rv1
  | cc == 3 = ExprLeq lv1 rv1
  | cc == 12 = ExprGeq lv2 rv2
  | cc == 13 = ExprLt lv2 rv2
  | cc == 14 = ExprGt lv2 rv2
  | cc == 15 = ExprLeq lv2 rv2
  where
    ct1 = toCType t False
    ct2 = toCType t True
    lv1 = (ExprVar $ dr_v ct1 dn)
    lv2 = (ExprVar $ dr_v ct2 dn)
    rv1 = (ExprVar $ operand2Var (Address ea) ct1)
    rv2 = (ExprVar $ operand2Var (Address ea) ct2)
getCond (P.CMP t ea dn) cc
  | cc == 2 = ExprGt lv1 rv1
  | cc == 3 = ExprLeq lv1 rv1
  | cc == 4 = ExprGeq lv1 rv1
  | cc == 5 = ExprLt lv1 rv1
  | cc == 6 = ExprEq lv1 rv1
  | cc == 7 = ExprNeq lv1 rv1
  | cc == 12 = ExprGeq lv2 rv2
  | cc == 13 = ExprLt lv2 rv2
  | cc == 14 = ExprGt lv2 rv2
  | cc == 15 = ExprLeq lv2 rv2
  where
    ct1 = toCType t False
    ct2 = toCType t True
    lv1 = (ExprVar $ dr_v ct1 dn)
    lv2 = (ExprVar $ dr_v ct2 dn)
    rv1 = (ExprVar $ operand2Var ea ct1)
    rv2 = (ExprVar $ operand2Var ea ct2)
getCond (P.CMP t ea an) cc
  | cc == 2 = ExprGt lv1 rv1
  | cc == 3 = ExprLeq lv1 rv1
  | cc == 4 = ExprGeq lv1 rv1
  | cc == 5 = ExprLt lv1 rv1
  | cc == 6 = ExprEq lv1 rv1
  | cc == 7 = ExprNeq lv1 rv1
  | cc == 12 = ExprGeq lv2 rv2
  | cc == 13 = ExprLt lv2 rv2
  | cc == 14 = ExprGt lv2 rv2
  | cc == 15 = ExprLeq lv2 rv2
  where
    ct1 = toCType t False
    ct2 = toCType t True
    lv1 = (ExprVar $ ar_v ct1 an)
    lv2 = (ExprVar $ ar_v ct2 an)
    rv1 = (ExprVar $ operand2Var ea ct1)
    rv2 = (ExprVar $ operand2Var ea ct2)
getCond _ n = getCondX n
-}
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

do_bitop :: (Term a2) => AType -> (a2 -> t -> StmtM) -> a2 -> t -> StmtM
do_bitop t op dst src = do
  clearVC
  op dst src
  testNZ t dst

do_bitimm ::
     (Integral p) => AType -> (Var -> Expr -> StmtM) -> Operand -> p -> StmtM
do_bitimm t op ea i = do
  let ct = toCType t False
      imm = uintE $ fromIntegral i
      dst = operand2Var ea ct
  do_bitop t op dst imm

do_arithimm ::
     (AType -> Var -> Expr -> StmtM) -> AType -> Operand -> Int -> StmtM
do_arithimm op t ea i = do
  let ct = toCType t False
      imm = uintE $ fromIntegral i
      dst = operand2Var ea ct
  op t dst imm

do_cmp :: (Term a1, Term a2) => AType -> a1 -> a2 -> StmtM
do_cmp t dst src = do
  ccV $= dst `subV` src
  ccC $= dst `subC` src
  ccZ $= dst $== src
  ccN $= testCmpN t dst src

do_sub :: (Term a) => AType -> Var -> a -> StmtM
do_sub t dst src = do
  ccV $= dst `subV` src
  ccC $= dst `subC` src
  ccX $= ccC
  dst $-= src
  testNZ t dst

do_add :: (Term a) => AType -> Var -> a -> StmtM
do_add t dst src = do
  ccV $= dst `addV` src
  ccC $= dst `addC` src
  ccX $= ccC
  dst $+= src
  testNZ t dst

do_bit :: Maybe Op2 -> AType -> Operand -> BopSc -> StmtM
do_bit op t ea sc = do
  let ea_v = operand2Var ea $ toCType t False
      count =
        case sc of
          BImm n -> uintE $ fromIntegral n
          BReg d -> ExprVar $ dr_v UINT32 d
  ccZ $= bitTest ea_v count
  case op of
    (Just o) -> assignOp o ea_v count
    Nothing  -> nullStmt

toRtl :: Op -> StmtM
toRtl (P.ORI BYTE P2.CCR v) = doCCRFlags ($|) v
toRtl (P.ORI WORD P2.SR v) = do
  doSRFlags ($|=) v
  doCCRFlags ($|) v
toRtl (P.ORI t ea v) = do_bitimm t ($|=) ea v
toRtl (P.ANDI BYTE P2.CCR v) = doCCRFlags ($&) v
toRtl (P.ANDI WORD P2.SR v) = do
  doSRFlags ($&=) v
  doCCRFlags ($&) v
toRtl (P.ANDI t ea v) = do_bitimm t ($&=) ea v
toRtl (P.EORI BYTE P2.CCR v) = doCCRFlags ($^) v
toRtl (P.EORI WORD P2.SR v) = do
  doSRFlags ($^=) v
  doCCRFlags ($^) v
toRtl (P.EORI t ea v) = do_bitimm t ($^=) ea v
toRtl (P.SUBI t ea v) = do_arithimm do_sub t ea v
toRtl (P.ADDI t ea v) = do_arithimm do_add t ea v
toRtl (P.CMPI t ea v) = do_arithimm do_cmp t ea v
toRtl (P.BTST t ea sc) = do_bit Nothing t ea sc
toRtl (P.BCHG t ea sc) = do_bit (Just R.BFLIP) t ea sc
toRtl (P.BCLR t ea sc) = do_bit (Just R.BCLR) t ea sc
toRtl (P.BSET t ea sc) = do_bit (Just R.BSET) t ea sc
toRtl (P.CMP2 t ea rn) = do
  let ct =
        toCType
          t
          (case rn of
             XR_D _ -> False
             XR_A _ -> True)
      dn = xr_v ct rn
      mem = ExprVar $ operand2Var (Address ea) ct
      low = RtlMemoryI ct mem 0
      high = RtlMemoryI ct mem $ sizeOf ct
  ccZ $= (dn $== low) $|| (dn $== high)
  ccC $= (dn $< low) $|| (dn $> high)
toRtl (P.CHK2 t ea rn) = do
  toRtl (P.CMP2 t ea rn)
  if_ ccC $ do asm "TRAP" []
toRtl (P.CAS t dc du ea) = do
  let ct = toCType t False
      dc_var = dr_v ct dc
      ea_var = operand2Var (Address ea) ct
      du_var = dr_v ct du
  do_cmp t ea_var dc_var
  ifElse_ ccZ (ea_var $= du_var) (dc_var $= ea_var)
toRtl (P.CAS2 t dc1 dc2 du1 du2 rn1 rn2) = do
  let ct = toCType t False
      dc1_var = dr_v ct dc1
      dc2_var = dr_v ct dc2
      rn1_var = xr_v ct rn1
      rn2_var = xr_v ct rn2
      du1_var = dr_v ct du1
      du2_var = dr_v ct du2
      elseV = do
        dc1_var $= rn1_var
        dc2_var $= rn2_var
  do_cmp t rn1_var dc1_var
  ifElse_
    ccZ
    (do do_cmp t rn2_var dc2_var
        ifElse_
          ccZ
          (do rn1_var $= du1_var
              rn2_var $= du2_var)
          elseV)
    elseV
toRtl (P.MOVES t toMem ea rn)
  | toMem == True = memM $= rnV
  | otherwise = rnV $= memM
  where
    ct = toCType t False
    rnV = xr_v ct rn
    memM = operand2Var (Address ea) ct
toRtl (P.MOVEP t toMem a im d)
  | toMem == True = do
    (addr 0) $= dvn3
    (addr 2) $= dvn4
    if (t == LONG)
      then do
        (addr 4) $= dvn2
        (addr 6) $= dvn1
      else nullStmt
  | otherwise = do
    let h = (addr 0) $<-> (addr 2)
        l = (addr 4) $<-> (addr 6)
    if t == WORD
      then (dr_v UINT16 d) $= h
      else (dr_v UINT32 d) $= (h $<-> l)
  where
    addr x = RtlMemoryI INT8 (ExprVar $ ar_v (PTR UINT8) a) (im + x)
    dv = dr_v UINT32 d
    (dvn1:dvn2:dvn3:dvn4:_) =
      map (\x -> cast UINT8 (dv $>> (uintE x))) [24, 16, 8, 0]
toRtl (P.MOVE _ CCR dst) = do
  let dstV = operand2Var dst UINT16
      cc =
        foldl
          ($|)
          (cast UINT16 ccC)
          [ (cast UINT16 ccV) $<< uintE 1
          , (cast UINT16 ccZ) $<< uintE 2
          , (cast UINT16 ccN) $<< uintE 3
          , (cast UINT16 ccX) $<< uintE 4
          ]
  dstV $= cc
toRtl (P.MOVE _ P2.SR dst) = do
  let dstV = operand2Var dst UINT16
      sc =
        foldl
          ($|)
          (cast UINT16 ccC)
          [ (cast UINT16 ccV) $<< uintE 1
          , (cast UINT16 ccZ) $<< uintE 2
          , (cast UINT16 ccN) $<< uintE 3
          , (cast UINT16 ccX) $<< uintE 4
          , (cast UINT16 $ RtlReg UINT8 "I") $<< uintE 8
          , (cast UINT16 $ ccFlags "M") $<< uintE 12
          , (cast UINT16 $ ccFlags "S") $<< uintE 13
          , (cast UINT16 $ RtlReg UINT8 "T") $<< uintE 14
          ]
  dstV $= sc
toRtl (P.MOVE _ (SpRG c) dst) = do
  let dstV = operand2Var dst UINT16
  dstV $= RtlReg (PTR VOID) c
toRtl (P.MOVE _ src P2.CCR) = do
  let srcV = operand2Var src UINT16
  ccC $= bitTest srcV $ uintE 0
  ccV $= bitTest srcV $ uintE 1
  ccZ $= bitTest srcV $ uintE 2
  ccN $= bitTest srcV $ uintE 3
  ccX $= bitTest srcV $ uintE 4
toRtl (P.MOVE t src P2.SR) = do
  let srcV = operand2Var src UINT16
  toRtl (P.MOVE t src P2.CCR)
  (RtlReg UINT8 "I") $= (srcV $>> uintE 8) $& uintE 7
  ccFlags "M" $= bitTest srcV $ uintE 12
  ccFlags "S" $= bitTest srcV $ uintE 13
  (RtlReg UINT8 "T") $= (srcV $>> uintE 14) $& uintE 3
toRtl (P.MOVE _ src (SpRG c)) = do
  let srcV = operand2Var src UINT16
  (RtlReg (PTR VOID) c) $= srcV
toRtl (P.MOVE t src dst) = do
  let ct = toCType t False
      srcV = operand2Var src ct
      dstV = operand2Var dst ct
  clearVC
  dstV $= srcV
  testNZ t dstV
toRtl (P.MOVEA t src dstN) = do
  let ct = toCType t True
      srcV = operand2Var src ct
  (ar_v ct dstN) $= srcV
toRtl (P.NEGX t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
  dst $+= cast ct ccX
  ccV $= subV (intE 0) dst
  ccC $= subC (intE 0) dst
  ccX $= ccC
  dst $= neg dst
  if_ (dst $!= (intE 0)) $ ccZ $= (intE 0)
  ccN $= testN t dst
toRtl (P.CLR t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
  clearVC
  dst $= (uintE 0)
  ccZ $= trueV
  ccN $= falseV
toRtl (P.NEG t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
  ccV $= subV (intE 0) dst
  ccC $= (intE 0) $!= dst
  ccX $= ccC
  dst $= neg dst
  testNZ t dst
toRtl (P.NOT t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
  clearVC
  dst $= bNot dst
  testNZ t dst
toRtl (P.TST t ea) = do
  let ct = toCType t True
      src = operand2Var ea ct
  clearVC
  testNZ t src
toRtl (P.NBCD _ ea) = do
  let dst = operand2Var ea BCD
  ccC $= subC (uintE 0) dst
  ccX $= ccC
  dst $= neg dst
  ccZ $= lNot dst
toRtl (P.TAS _ ea) = do
  let dstV = operand2Var ea UINT8
  clearVC
  testNZ BYTE dstV
  assignOp (R.BSET) dstV $ uintE 7
toRtl (P.MULUL ea d) = do
  let src = operand2Var ea UINT32
      dst = dr_v UINT32 d
  ccC $= falseV
  ccV $= (dst `mulH` src) $!= uintE 0
  dst $*= src
  testNZ LONG dst
toRtl (P.MULSL ea d) = do
  let src = operand2Var ea INT32
      dst = dr_v INT32 d
  ccC $= falseV
  ccV $= (dst `mulH` src) $!= intE 0
  dst $*= src
  testNZ LONG dst
toRtl (P.MULULL ea h l) = do
  let src = operand2Var ea UINT32
      dst = dr_v UINT32 l
      dstH = dr_v UINT32 h
  clearVC
  dstH $= dst `mulH` src
  dst $*= src
  ccZ $= (lNot dst) $&& (lNot dstH)
  ccN $= testN LONG (dstH)

toRtl (P.MULSLL ea h l) = do
  let src = operand2Var ea INT32
      dst = dr_v INT32 l
      dstH = dr_v INT32 h
  clearVC
  dstH $= dst `mulH` src
  dst $*= src
  ccZ $= (lNot dst) $&& (lNot dstH)
  ccN $= testN LONG dstH
toRtl (P.DIVUL ea r q) = do
  let src = operand2Var ea UINT32
      dstR = dr_v UINT32 r
      dstQ = dr_v UINT32 q
      tmp = RtlReg UINT32 "tmp1"
  ccC $= falseV
  ccV $= dstQ `divV` src
  tmp $= dstQ
  dstQ $/= src
  testNZ LONG dstQ
  if q /= r
    then dstR $= tmp $% src
    else nullStmt
toRtl (P.DIVSL ea r q) = do
  let src = operand2Var ea INT32
      dstR = dr_v INT32 r
      dstQ = dr_v INT32 q
      tmp = RtlReg INT32 "tmp1"
  ccC $= falseV
  ccV $= dstQ `divV` src
  tmp $= dstQ
  dstQ $/= src
  testNZ LONG dstQ
  if q /= r
    then dstR $= tmp $% src
    else nullStmt
toRtl (P.DIVULL ea r q) = do
  let src = operand2Var ea UINT32
      dstR = dr_v UINT32 r
      dstQ = dr_v UINT32 q
      tmp = RtlReg UINT64 "tmp"
  ccC $= falseV
  tmp $= dstR $<-> dstQ
  ccV $= tmp `divV` src
  dstQ $= tmp $/ src
  testNZ LONG dstQ
  if q /= r
    then dstR $= tmp $% src
    else nullStmt
toRtl (P.DIVSLL ea r q) = do
  let src = operand2Var ea INT32
      dstR = dr_v INT32 r
      dstQ = dr_v INT32 q
      tmp = RtlReg INT64 "tmp"
  ccC $= falseV
  tmp $= dstR $<-> dstQ
  ccV $= tmp `divV` src
  dstQ $= tmp $/ src
  testNZ LONG dstQ
  if q /= r
    then dstR $= tmp $% src
    else nullStmt
toRtl (P.SWAP n) = do
  let dst = dr_v UINT32 n
  clearVC
  dst $= (dst `ror` uintE 16)
  testNZ LONG dst
toRtl (P.TRAPn n) = asm "TRAP" [uintE n]
toRtl (P.LINK rn imm) = do
  let dst = ar_v (PTR VOID) rn
      sp = ar_v (PTR VOID) (AR 7)
  push $ ExprVar dst
  dst $= sp
  adjustSP imm
toRtl (P.UNLK rn) = do
  let dst = ar_v (PTR VOID) rn
      sp = ar_v (PTR VOID) (AR 7)
  sp $= dst
  pop dst
toRtl (P.RESET) = asm "RESET" []
toRtl (P.NOP) = nullStmt
toRtl (P.STOP nw) = asm "STOP" [uintE nw]
toRtl (P.RTE) = asm "iReturn" []
toRtl (P.RTD n) = do
  return_
  adjustSP n
toRtl (P.RTS) = return_
toRtl (P.TRAPV) = if_ ccN $ asm "TRAP" []
toRtl (P.RTR) = do
  let tmp = (RtlReg UINT16 "temp")
  pop tmp
  ccC $= bitTest tmp $ uintE 0
  ccV $= bitTest tmp $ uintE 1
  ccZ $= bitTest tmp $ uintE 2
  ccN $= bitTest tmp $ uintE 3
  ccX $= bitTest tmp $ uintE 4
  return_
toRtl (P.MOVEC True n name) = do
  let v = xr_v UINT32 n
      spR = RtlReg UINT32 name
  spR $= v
toRtl (P.MOVEC False n name) = do
  let v = xr_v UINT32 n
      spR = RtlReg UINT32 name
  v $= spR
toRtl (P.BKPT n) = asm "breakpoint" [uintE n]
toRtl (P.PEA ea) = do
  let var = operand2Var (Address ea) (PTR VOID)
  push $ ExprAddr var
toRtl (P.EXT WORD n) = do
  let dst = (dr_v INT16 n)
  clearVC
  dst $= (cast INT16 $ dr_v INT8 n)
  testNZ WORD dst
toRtl (P.EXT LONG n) = do
  let dst = (dr_v INT32 n)
  clearVC
  dst $= (cast INT32 $ dr_v INT16 n)
  testNZ LONG dst
toRtl (P.EXTB n) = do
  let dst = (dr_v INT32 n)
  clearVC
  (dr_v INT32 n) $= (cast INT32 $ dr_v INT8 n)
  testNZ LONG dst
toRtl (P.MOVEM t True (UnRefDec (AR 7)) regs) = do
  let ct = toCType t True
  mapM_ (\r -> push (ExprVar $ xr_v ct r)) $ reverse regs
toRtl (P.MOVEM t True (UnRefDec an) regs) = do
  let ct = toCType t True
      base = ar_v (PTR ct) an
      regsR = reverse $ zip [0 ..] regs
      len = length regs
      temp = RtlReg (PTR VOID) "temp"
      sz =
        if t == WORD
          then 2
          else 4
  temp $= base $+ intE (-(len * sz))
  mapM_
    (\(i, n) ->
       let val = xr_v ct n
        in (RtlMemoryD (PTR ct) (ExprVar base) (intE (i :: Int))) $= val)
    regsR
  base $= temp
toRtl (P.MOVEM t True ea regs) = do
  let ct = toCType t True
      base = operand2Var (Address ea) (PTR ct)
      rs = zip [0 ..] regs
  mapM_
    (\(i, n) ->
       let val = xr_v ct n
        in (RtlMemoryD (PTR ct) (ExprVar base) (intE i)) $= val)
    rs
toRtl (P.MOVEM WORD False (UnRefDec (AR 7)) regs) = do
  let temp = RtlReg INT16 "temp"
  mapM_
    (\r ->
       (do pop temp
           (xr_v INT16 r) $= cast INT16 temp))
    regs
toRtl (P.MOVEM LONG False (UnRefInc (AR 7)) regs) =
  mapM_ (\r -> pop $ xr_v UINT32 r) regs
toRtl (P.MOVEM WORD False (UnRefInc an) regs) = do
  let base = ar_v (PTR INT16) an
      regsR = zip [0 ..] regs
      len = length regs
      temp = RtlReg (PTR VOID) "temp"
  temp $= base
  mapM_
    (\(i, n) ->
       (xr_v INT32 n) $=
       (cast INT32 $ (RtlMemoryD (PTR INT16) (ExprVar base) (intE (i :: Int)))))
    regsR
  base $= temp $+ intE (len * 2)
toRtl (P.MOVEM LONG False (UnRefInc an) regs) = do
  let base = ar_v (PTR UINT32) an
      regsR = zip [0 ..] regs
      len = length regs
      temp = RtlReg (PTR VOID) "temp"
  temp $= base
  mapM_
    (\(i, n) ->
       (xr_v UINT32 n) $=
       (RtlMemoryD (PTR UINT32) (ExprVar base) (intE (i :: Int))))
    regsR
  base $= temp $+ intE (len * 4)
toRtl (P.MOVEM WORD False ea regs) = do
  let base = operand2Var (Address ea) (PTR INT16)
      regsR = zip [0 ..] regs
  mapM_
    (\(i, n) ->
       (xr_v INT32 n) $=
       cast INT32 (RtlMemoryD (PTR INT16) (ExprVar base) (intE i)))
    regsR
toRtl (P.MOVEM LONG False ea regs) = do
  let base = operand2Var (Address ea) (PTR INT32)
      regsR = zip [0 ..] regs
  mapM_
    (\(i, n) -> (xr_v INT32 n) $= (RtlMemoryD (PTR INT32) (ExprVar base) (intE i)))
    regsR
toRtl (P.JSR ea) = do
  let base = operand2Var (Address ea) (PTR VOID)
  call $ TargetIndirect $ ExprAddr base
toRtl (P.JMP ea) = do
  let base = operand2Var (Address ea) (PTR VOID)
  goto $ TargetIndirect $ ExprAddr base
toRtl (P.CHK t ea n) = do
  let ct = toCType t True
      limit = operand2Var ea ct
      val = dr_v ct n
  ccN $= testN LONG val
  if_ (ccN $|| (val $> limit)) $ asm "TRAP" []
toRtl (P.LEA ea n) = do
  let var = operand2Var (Address ea) (PTR VOID)
  (ar_v (PTR VOID) n) $= ExprAddr var
toRtl (P.ADDQ t v (AReg an)) = do
  let ct = toCType t True
  (ar_v ct an) $+= uintE v
toRtl (P.ADDQ t v ea) = toRtl (ADDI t ea v)
toRtl (P.SUBQ t v (AReg an)) = do
  let ct = toCType t True
  (ar_v ct an) $-= uintE v
toRtl (P.SUBQ t v ea) = toRtl (SUBI t ea v)
toRtl (P.TRAPcc (CC cc) _) = if_ (ExprCondCC cc) $ asm "TRAP" []
toRtl (P.Scc (CC cc) ea) = do
  let var = operand2Var ea INT8
  var $= sel (ExprCondCC cc) (intE (-1)) (intE 0)
toRtl (P.BRA target) = goto $ TargetAbsolute target
toRtl (P.BSR target) = call $ TargetAbsolute target
toRtl (P.Bcc (CC cc) target) = if_ (ExprCondCC cc) (toRtl (BRA target))
toRtl (P.MOVEQ v n) = do
  let dst = dr_v INT32 n
  dst $= intE v
  clearVC
  testNZ LONG dst
toRtl (P.DBcc (CC cc) dn target) = do
  let dnv = dr_v INT16 dn
  if_ (lNot $ ExprCondCC cc) $
    (do dnv $-= intE 1
        if_ (dnv $!= intE (-1)) $ goto $ TargetAbsolute target)
toRtl (P.OR t ea dn) = do
  let ct = toCType t False
      src = operand2Var ea ct
      dst = dr_v ct dn
  do_bitop t ($|=) dst src
toRtl (P.OR_TO_MEM t dn ea) = do
  let ct = toCType t False
      dst = operand2Var (Address ea) ct
      src = dr_v ct dn
  do_bitop t ($|=) dst src
toRtl (P.DIVUW ea dn) = do
  let src = operand2Var ea UINT16
      dst = dr_v UINT32 dn
      tmp1 = RtlReg UINT16 "tmp1"
  ccC $= falseV
  ccV $= dst `divV` src
  tmp1 $= dst $% src
  dst $= dst $/ src
  testNZ WORD dst
  dst $= tmp1 $<-> dst
toRtl (P.SBCD_REG x y) = do
  let s = dr_v BCD x
      d = dr_v BCD y
      tmp = RtlReg BCD "temp"
  tmp $= d $- (cast BCD $ ccFlags "X")
  d $= tmp $- s
  ccZ $&= d $== (uintE 0)
  ccC $= tmp `subC` s
  ccX $= ccC
toRtl (P.SBCD_MEM x y) = do
  let s = deref $ RtlDec True $ ar_v (PTR BCD) x
      d = RtlDec True $ ar_v (PTR BCD) y
      tmp_d = RtlReg (PTR BCD) "temp1"
      tmp_s = RtlReg BCD "temp2"
      tmp = RtlReg BCD "temp3"
      tmp_dv = deref $ tmp_d
  tmp_d $= d
  tmp_s $= s
  tmp $= tmp_dv $- (cast BCD ccX)
  (deref tmp_d) $= tmp $- tmp_s
  ccZ $&= tmp_dv $== (uintE 0)
  ccC $= tmp `subC` tmp_s
  ccX $= ccC
toRtl (P.PACK_REG x y imm) = do
  let s = ExprVar $ dr_v UINT16 x
      d = dr_v UINT8 y
  d $= ExprOp2 (Ex2 UINT8 "PACK") s (intE imm)
toRtl (P.PACK_MEM x y imm) = do
  let s = ExprVar $ deref $ RtlDec True $ ar_v (PTR UINT16) x
      d = deref $ RtlDec True $ ar_v (PTR UINT8) y
  d $= ExprOp2 (Ex2 UINT8 "PACK") s (intE imm)
toRtl (P.UNPK_REG x y imm) = do
  let s = ExprVar $ dr_v UINT8 x
      d = dr_v UINT16 y
  d $= ExprOp2 (Ex2 UINT16 "UNPK") s (intE imm)
toRtl (P.UNPK_MEM x y imm) = do
  let s = ExprVar $ deref $ RtlDec True $ ar_v (PTR UINT8) x
      d = deref $ RtlDec True $ ar_v (PTR UINT16) y
  d $= ExprOp2 (Ex2 UINT16 "UNPK") s (intE imm)
toRtl (P.DIVSW ea dn) = do
  let src = ExprVar $ operand2Var ea INT16
      dst = dr_v INT32 dn
      tmp1 = RtlReg INT16 "tmp1"
  ccC $= falseV
  ccV $= dst `divV` src
  tmp1 $= dst $% src
  dst $= dst $/ src
  testNZ WORD dst
  dst $= tmp1 $<-> dst
toRtl (P.SUB t ea dn) =
  let ct = toCType t False
      src = operand2Var ea ct
      dst = dr_v ct dn
   in do_sub t dst src
toRtl (P.SUB_TO_MEM t dn ea) =
  let ct = toCType t False
      dst = operand2Var (Address ea) ct
      src = dr_v ct dn
   in do_sub t dst src
toRtl (P.SUBA t ea an) = do
  let ct = toCType t False
      src = operand2Var ea ct
      dst = ar_v ct an
  dst $-= src
toRtl (P.SUBX_REG t x y) = do
  let ct = toCType t True
      s = dr_v ct x
      d = dr_v ct y
  d $+= cast ct ccX
  ccV $= d `subV` s
  ccC $= d `subC` s
  ccX $= ccC
  d $-= s
  ccZ $&= lNot d
  ccN $= testN t d
toRtl (P.SUBX_MEM t x y) = do
  let ct = toCType t True
      s = deref $ RtlDec True $ ar_v (PTR ct) x
      d = RtlDec True $ ar_v (PTR ct) y
      tmp_d = RtlReg (PTR ct) "temp1"
      tmp_sv = RtlReg ct "temp2"
      tmp_dv = RtlReg ct "temp3"
  tmp_d $= d
  tmp_sv $= s
  tmp_dv $= (deref tmp_d) $- (cast ct ccX)
  do_sub t tmp_dv tmp_sv
  deref tmp_d $= tmp_dv    
toRtl (P.CMP t ea dn) =
  let ct = toCType t False
      src = operand2Var ea ct
      dst = dr_v ct dn
   in do_cmp t dst src
toRtl (P.CMPA t ea an) =
  let ct = toCType t False
      srcX = operand2Var ea ct
      src =
        if t == WORD
          then cast INT32 srcX
          else ExprVar srcX
      dst = ar_v INT32 an
   in do_cmp t dst src
toRtl (P.CMPM t y x) = do
  let ct = toCType t True
      s = deref $ RtlInc False $ ar_v (PTR ct) x
      d = deref $ RtlInc False $ ar_v (PTR ct) y
      tmp_s = RtlReg ct "tmp1"
      tmp_d = RtlReg ct "tmp2"
  tmp_d $= d
  tmp_s $= s
  do_cmp t tmp_d tmp_s
toRtl (P.EOR t dn ea) =
  let ct = toCType t False
      dst = operand2Var ea ct
      src = dr_v ct dn
   in do_bitop t ($^=) dst src
toRtl (P.AND t ea dn) =
  let ct = toCType t False
      src = operand2Var ea ct
      dst = dr_v ct dn
   in do_bitop t ($&=) dst src
toRtl (P.AND_TO_MEM t dn ea) =
  let ct = toCType t False
      dst = operand2Var (Address ea) ct
      src = dr_v ct dn
   in do_bitop t ($&=) dst src
toRtl (P.MULUW ea dn) = do
  let src = cast UINT32 $ operand2Var ea UINT16
      dst = dr_v UINT32 dn
  clearVC
  dst $*= src
  testNZ LONG dst
toRtl (P.ABCD_REG y x) = do
  let s = dr_v BCD y
      d = dr_v BCD x
  d $+= cast BCD ccX
  ccC $= d `addC` s
  ccX $= ccC
  d $+= s
  ccZ $&= d $== uintE 0
toRtl (P.ABCD_MEM y x) = do
  let s = deref $ RtlDec True $ ar_v (PTR BCD) x
      d = deref $ RtlDec True $ ar_v (PTR BCD) y
      tmp_s = RtlReg BCD "tmp1"
      tmp_d = RtlReg BCD "tmp2"
      tmp_dv = RtlReg (PTR BCD) "tmp3"
  tmp_dv $= d
  tmp_d $= d $+ (cast BCD ccX)
  tmp_s $= s
  ccC $= tmp_d `addC` tmp_s
  ccX $= ccC
  tmp_dv $+= tmp_s
  ccZ $&= d $== uintE 0
toRtl (P.MULSW ea dn) = do
  let src = cast INT32 $ operand2Var ea INT16
      dst = dr_v INT32 dn
  clearVC
  dst $*= src
  testNZ LONG dst
toRtl (P.EXG_D x y) = do
  let dx = dr_v UINT32 x
      dy = dr_v UINT32 y
      tmp = RtlReg UINT32 "temp"
  tmp $= dx
  dx $= dy
  dy $= tmp
toRtl (P.EXG_A x y) = do
  let dx = ar_v (PTR VOID) x
      dy = ar_v (PTR VOID) y
      tmp = RtlReg (PTR VOID) "temp"
  tmp $= dx
  dx $= dy
  dy $= tmp
toRtl (P.EXG_DA x y) = do
  let dx = dr_v UINT32 x
      dy = ar_v (PTR VOID) y
      tmp = RtlReg UINT32 "temp"
  tmp $= dx
  dx $= cast UINT32 dy
  dy $= cast (PTR VOID) tmp
toRtl (P.SYS i) = asm "SYSCALL" [uintE i]
toRtl (P.ADD t ea dn) =
  let ct = toCType t False
      src = operand2Var ea ct
      dst = dr_v ct dn
   in do_add t dst src
toRtl (P.ADD_TO_MEM t dn ea) =
  let ct = toCType t False
      dst = operand2Var (Address ea) ct
      src = dr_v ct dn
   in do_add t dst src
toRtl (P.ADDA t ea an) = do
  let ct = toCType t False
      src = cast INT32 $ operand2Var ea ct
      dst = ar_v INT32 an
  dst $+= src
toRtl (P.ADDX_REG t x y) = do
  let ct = toCType t True
      s = dr_v ct x
      d = dr_v ct y
  d $+= cast ct ccX
  ccV $= d `addV` s
  ccC $= d `addC` s
  ccX $= ccC
  d $+= s
  ccZ $&= lNot d
  ccN $= testN t d
toRtl (P.ADDX_MEM t x y) = do
  let ct = toCType t True
      s = deref $ RtlDec True $ ar_v (PTR ct) x
      d = RtlDec True $ ar_v (PTR ct) y
      tmp_d = RtlReg (PTR ct) "temp1"
      tmp_sv = RtlReg ct "temp2"
      tmp_dv = RtlReg ct "temp3"
  tmp_d $= d
  tmp_sv $= s
  tmp_dv $= (deref tmp_d) $+ (cast ct $ ccX)
  ccV $= tmp_dv `addV` tmp_sv
  ccC $= tmp_dv `addC` tmp_sv
  ccX $= ccC
  tmp_dv $+= tmp_sv
  ccZ $&= lNot tmp_dv
  ccN $= testN t tmp_dv
toRtl (P.ASR t sc reg) = do
  let (_, sc_v, dst) = shift_arg t True sc reg
      carry = bitTest dst (sc_v $- uintE 1)
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $>>= sc_v)
    (do ccC $= falseV)
  testNZ t dst
toRtl (P.ASL t sc reg) = do
  let (scc, sc_v, dst) = shift_arg t True sc reg
      carry = bitTest dst (scc $- sc_v)
  ccV $= ExprOp2 (Ex2 BOOL "sl_overflow") (ExprVar dst) sc_v
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $<<= sc_v)
    (do ccC $= falseV)
  testNZ t dst
toRtl (P.LSR t sc reg) = do
  let (_, sc_v, dst) = shift_arg t False sc reg
      carry = bitTest dst (sc_v $- uintE 1)
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $>>= sc_v)
    (ccC $= falseV)
  testNZ t dst
toRtl (P.LSL t sc reg) = do
  let (scc, sc_v, dst) = shift_arg t False sc reg
      carry = bitTest dst (scc $- sc_v)
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $<<= sc_v)
    (ccC $= falseV)
  testNZ t dst
toRtl (P.ROXR t sc reg) = do
  let (_, sc_v, dst) = shift_arg t False sc reg
      carry = bitTest dst $ sc_v $- uintE 1
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $=
          (ExprOpN (toCType t False) "rorx" [ExprVar dst, sc_v, ExprVar ccX]))
    (ccC $= ccX)
  testNZ t dst
toRtl (P.ROXL t sc reg) = do
  let (sz, sc_v, dst) = shift_arg t False sc reg
      carry = bitTest dst $ sz $- sc_v
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        ccX $= ccC
        dst $= ExprOpN (toCType t False) "rolx" [ExprVar dst, sc_v, ExprVar ccX])
    (ccC $= ccX)
  testNZ t dst
toRtl (P.ROR t sc reg) = do
  let (_, sc_v, dst) = shift_arg t False sc reg
      carry = bitTest dst $ sc_v $- uintE (1 :: Int)
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        dst $= dst `ror` sc_v)
    (ccC $= falseV)
  testNZ t dst
toRtl (P.ROL t sc reg) = do
  let (sz, sc_v, dst) = shift_arg t False sc reg
      carry = bitTest dst $ sz $- sc_v
  ccV $= falseV
  ifElse_
    (sc_v $!= uintE 0)
    (do ccC $= carry
        dst $= dst `rol` sc_v)
    (ccC $= falseV)
  testNZ t dst
toRtl (P.ASR_EA ea) = do
  let dst = operand2Var (Address ea) INT16
  ccV $= falseV
  ccC $= bitTest dst $ uintE 0
  ccX $= ccC
  dst $>>= uintE (1 :: Int)
  testNZ WORD dst
toRtl (P.ASL_EA ea) = do
  let dst = operand2Var (Address ea) INT16
  ccV $= (bitTest dst $ uintE (15 :: Int)) $== (bitTest dst $ uintE (14 :: Int))
  ccC $= bitTest dst $ uintE (15 :: Int)
  ccX $= ccC
  dst $<<= uintE (1 :: Int)
  testNZ WORD dst
toRtl (P.LSR_EA ea) = do
  let dst = operand2Var (Address ea) UINT16
  ccV $= falseV
  ccC $= bitTest dst $ uintE (0 :: Int)
  ccX $= ccC
  dst $>>= uintE (1 :: Int)
  testNZ WORD dst
toRtl (P.LSL_EA ea) = do
  let dst = operand2Var (Address ea) UINT16
  ccV $= falseV
  ccC $= bitTest dst $ uintE (15 :: Int)
  ccX $= ccC
  dst $<<= uintE (1 :: Int)
  testNZ WORD dst
toRtl (P.ROXR_EA ea) = do
  let dst = operand2Var (Address ea) UINT16
      carry = bitTest dst $ uintE (0 :: Int)
  ccV $= falseV
  ccC $= carry
  ccX $= ccC
  dst $= (ExprOpN UINT16 "rorx" [ExprVar dst, uintE 1, ExprVar ccX])
  testNZ WORD dst
toRtl (P.ROXL_EA ea) = do
  let dst = operand2Var (Address ea) UINT16
      carry = bitTest dst $ uintE (15 :: Int)
  ccV $= falseV
  ccC $= carry
  ccX $= ccC
  dst $= (ExprOpN UINT16 "rolx" [ExprVar dst, uintE 1, ExprVar ccX])
  testNZ WORD dst
toRtl (P.ROR_EA ea) = do
  let dst = operand2Var (Address ea) UINT16
      carry = bitTest dst $ uintE (0 :: Int)
  ccV $= falseV
  ccC $= carry
  dst $= dst `ror` uintE (1 :: Int)
  testNZ WORD dst
toRtl (P.ROL_EA ea) = do
  let dst = operand2Var (Address ea) UINT16
      carry = bitTest dst $ uintE (15 :: Int)
  ccV $= falseV
  ccC $= carry
  dst $= dst `rol` uintE (1 :: Int)
  testNZ WORD dst
toRtl (P.BFTST ea (BImm off) (BImm width)) = do
  let t
        | width < 8 = UINT8
        | width < 16 = UINT16
        | otherwise = UINT32
      dst = operand2Var ea UINT16
  clearVC
  testNZ LONG $ RtlBitField t dst off width
toRtl (P.BFTST (DReg d) offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      temp = RtlReg UINT32 "temp"
  clearVC
  temp $= ExprOpN UINT32 "bfGet_l" [ExprVar (dr_v UINT32 d), offset, width]
  testNZ LONG temp
toRtl (P.BFTST ea offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      temp = RtlReg UINT32 "temp"
      src = operand2Var ea (PTR VOID)
  clearVC
  temp $= ExprOpN UINT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG temp
toRtl (P.BFCHG ea (BImm off) (BImm width)) = do
  let t
        | width < 8 = UINT8
        | width < 16 = UINT16
        | otherwise = UINT32
      dst = RtlBitField t (operand2Var ea UINT16) off width
  clearVC
  testNZ LONG dst
  dst $= bNot dst
toRtl (P.BFCHG (DReg d) offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      temp = RtlReg UINT32 "temp"
  clearVC
  temp $= ExprOpN UINT32 "bfGet_l" [ExprVar (dr_v UINT32 d), offset, width]
  testNZ LONG temp
  (dr_v UINT32 d) $^= ExprOp2 (Ex2 UINT32 "bfMask") offset width
toRtl (P.BFCHG ea offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      temp = RtlReg UINT32 "temp"
      dst = operand2Var ea (PTR VOID)
  clearVC
  temp $= ExprOpN UINT32 "bfGet_b" [ExprVar dst, offset, width]
  testNZ LONG temp
  asm "bfchg_m" [ExprAddr dst, offset, width]
toRtl (P.BFCLR ea (BImm off) (BImm width)) = do
  let t
        | width < 8 = UINT8
        | width < 16 = UINT16
        | otherwise = UINT32
      dst = RtlBitField t (operand2Var ea UINT16) off width
  clearVC
  testNZ LONG dst
  dst $= intE 0
toRtl (P.BFCLR (DReg d) offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      temp = RtlReg UINT32 "temp"
  clearVC
  temp $= ExprOpN UINT32 "bfGet_l" [ExprVar (dr_v UINT32 d), offset, width]
  testNZ LONG temp
  (dr_v UINT32 d) $&= (bNot $ ExprOp2 (Ex2 UINT32 "bfMask") offset width)
toRtl (P.BFCLR ea offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      temp = RtlReg UINT32 "temp"
      dst = operand2Var ea (PTR VOID)
  clearVC
  temp $= ExprOpN UINT32 "bfGet_b" [ExprVar dst, offset, width]
  testNZ LONG temp
  asm "bfclr_m" [ExprAddr dst, offset, width]
toRtl (P.BFSET ea (BImm off) (BImm width)) = do
  let t
        | width < 8 = INT8
        | width < 16 = INT16
        | otherwise = INT32
      dst = RtlBitField t (operand2Var ea UINT16) off width
  clearVC
  testNZ LONG dst
  dst $= intE (-1)
toRtl (P.BFSET (DReg d) offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      temp = RtlReg UINT32 "temp"
  clearVC
  temp $= ExprOpN UINT32 "bfGet_l" [ExprVar (dr_v UINT32 d), offset, width]
  testNZ LONG temp
  (dr_v UINT32 d) $|= ExprOp2 (Ex2 UINT32 "bfMask") offset width
toRtl (P.BFSET ea offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      temp = RtlReg UINT32 "temp"
      dst = operand2Var ea (PTR VOID)
  clearVC
  temp $= ExprOpN UINT32 "bfGet_b" [ExprVar dst, offset, width]
  testNZ LONG temp
  asm "bfset_m" [ExprAddr dst, offset, width]
toRtl (P.BFEXTU (DReg d) (BImm o) (BImm w) dn) = do
  let t
        | w < 8 = UINT8
        | w < 16 = UINT16
        | otherwise = UINT32
      dst = dr_v UINT32 dn
  clearVC
  dst $= RtlBitField t (dr_v UINT32 d) o w
  testNZ LONG $ dr_v UINT32 d
toRtl (P.BFEXTU (DReg d) offset_p width_p dn) = do
  let (offset, width) = bf_arg offset_p width_p
      src = dr_v UINT32 d
      dst = dr_v UINT32 dn
  clearVC
  dst $= ExprOpN UINT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG dst
  asm "bfset_m" [ExprAddr dst, offset, width]
toRtl (P.BFEXTU ea offset_p width_p dn) = do
  let (offset, width) = bf_arg offset_p width_p
      src = operand2Var ea (PTR VOID)
      dst = dr_v UINT32 dn
  clearVC
  dst $= ExprOpN UINT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG dst
  asm "bfset_m" [ExprAddr dst, offset, width]
toRtl (P.BFEXTS (DReg d) (BImm o) (BImm w) dn) = do
  let t
        | w < 8 = INT8
        | w < 16 = INT16
        | otherwise = INT32
      dst = dr_v INT32 dn
  clearVC
  dst $= RtlBitField t (dr_v INT32 d) o w
  testNZ LONG $ dr_v INT32 d
toRtl (P.BFEXTS (DReg d) offset_p width_p dn) = do
  let (offset, width) = bf_arg offset_p width_p
      src = dr_v INT32 d
      dst = dr_v INT32 dn
  clearVC
  dst $= ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG dst
  asm "bfset_m" [ExprAddr dst, offset, width]
toRtl (P.BFEXTS ea offset_p width_p dn) = do
  let (offset, width) = bf_arg offset_p width_p
      src = operand2Var ea (PTR VOID)
      dst = dr_v INT32 dn
  clearVC
  dst $= ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG dst
  asm "bfset_m" [ExprAddr dst, offset, width]
toRtl (P.BFFFO (DReg d) (BImm o) (BImm w) dn) = do
  let t
        | w < 8 = INT8
        | w < 16 = INT16
        | otherwise = INT32
      dst = dr_v INT32 dn
      tmp = RtlReg UINT32 "temp"
  clearVC
  tmp $= RtlBitField t (dr_v INT32 d) o w
  dst $= ExprOp1 (Ex1 UINT32 "bfffo") (ExprVar tmp)
  testNZ LONG tmp
toRtl (P.BFFFO (DReg d) offset_p width_p dn) = do
  let (offset, width) = bf_arg offset_p width_p
      src = dr_v INT32 d
      tmp = RtlReg UINT32 "temp"
      dst = dr_v INT32 dn
  clearVC
  tmp $= ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG tmp
  dst $= ExprOpN UINT32 "bfffo_d" [ExprAddr dst, offset, width]
toRtl (P.BFFFO ea offset_p width_p dn) = do
  let (offset, width) = bf_arg offset_p width_p
      tmp = RtlReg INT32 "temp"
      src = operand2Var ea (PTR VOID)
      dst = dr_v INT32 dn
  clearVC
  tmp $= ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  testNZ LONG tmp
  dst $= ExprOpN UINT32 "bfffo_m" [ExprAddr dst, offset, width]
toRtl (P.BFINS dn (DReg d) (BImm o) (BImm w)) = do
  let t
        | w < 8 = INT8
        | w < 16 = INT16
        | otherwise = INT32
      src = dr_v INT32 dn
      dst = RtlBitField t (dr_v INT32 d) o w
  clearVC
  testNZ LONG $ dst
  dst $= src
toRtl (P.BFINS dn (DReg d) offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      src = dr_v INT32 d
      dst = dr_v INT32 dn
  clearVC
  testNZ LONG $ ExprOpN INT32 "bfGet_b" [ExprVar src, offset, width]
  dst $= ExprOpN UINT32 "bfins_d" [ExprAddr dst, ExprVar src, offset, width]
toRtl (P.BFINS dn ea offset_p width_p) = do
  let (offset, width) = bf_arg offset_p width_p
      dst = operand2Var ea (PTR VOID)
      src = dr_v INT32 dn
  clearVC
  testNZ LONG $ ExprOpN INT32 "bfGet_b" [ExprVar dst, offset, width]
  dst $= ExprOpN UINT32 "bfins_m" [ExprAddr dst, ExprAddr src, offset, width]
toRtl _ = asm "TRAP" []  


shift_arg :: AType -> Bool -> BopSc -> DR -> (Expr, Expr, Var)
shift_arg t signed sc reg =
  let scc =
        uintE $
        case t of
          BYTE -> 8
          WORD -> 16
          LONG -> 32
      ct = toCType t signed
      sc_v =
        case sc of
          BReg dr -> ExprVar $ dr_v UINT8 dr
          BImm n ->
            uintE
              (if n == 0
                 then 8
                 else n)
      dst = dr_v ct reg
   in (scc, sc_v, dst)




bf_arg :: BopSc -> BopSc -> (Expr, Expr)
bf_arg offset_p width_p =
  ( case offset_p of
      BImm n -> uintE n
      BReg n -> ExprVar $ dr_v UINT32 n
  , case width_p of
      BImm n -> uintE n
      BReg n -> ExprVar $ dr_v UINT32 n)
  
