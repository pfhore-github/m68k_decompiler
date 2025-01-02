{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module M68k.ConvToRtl where

import           CType
import           Data.Bits   ((.&.), (.<<.), (.>>.))
import           M68k.Parse

-- decompile 1st phase
import           RTL.Stmt    (RtlExpr (..), RtlStmt (..), RtlVar (..), typeOfE,
                              typeOfV)
import           Text.Printf (printf)

{-
scale2Type :: Int -> CType
scale2Type c = INT False (1 `shiftR` c)

cc2Cond :: Int -> Expr
cc2Cond cc =
  let c = VarValue $ ccVar 'C'
      z = VarValue $ ccVar 'Z'
      v = VarValue $ ccVar 'V'
      n = VarValue $ ccVar 'N'
      s = VarValue $ ccVar 'S'
  in
    case cc of
      0  -> immT
      1  -> immF
      2  -> lNot c $&& lNot z
      3  -> c $|| z
      4  -> lNot c
      5  -> c
      6  -> lNot z
      7  -> z
      8  -> lNot v
      9  -> v
      10 -> lNot n
      11 -> n
      12 -> CondExpr (s $!= immNA) (s $|| z) (n $== v)
      13 -> CondExpr (s $!= immNA) (lNot s $&& lNot z) (n $!= v)
      14 -> CondExpr (s $!= immNA) s ((n $== v) $&& lNot z)
      15 -> CondExpr (s $!= immNA) (lNot s) ((n $!= v) $|| z)
      _  -> undefined





-}
toCType :: AType -> Bool -> CType
toCType t sg =
  INT
    sg
    (case t of
       BYTE -> 1
       WORD -> 2
       LONG -> 4)

dr :: CType -> Int -> RtlVar
dr t n = RtlReg t $ printf "D%d" n

ar :: CType -> Int -> RtlVar
ar t n = RtlReg t $ printf "A%d" n

xr :: CType -> Int -> RtlVar
xr t n
  | n < 8 = dr t n
  | otherwise = ar t (n - 8)

operand2Expr :: Operand -> CType -> RtlExpr
operand2Expr (ImmInt v) t = ExprImm t v
operand2Expr c t          = ExprVar $ operand2Var c t

applyEaBase :: AddrBase -> Int -> CType -> RtlVar
applyEaBase (BaseAR r) bd t  = RtlMemoryI t (ar (PTR VOID) r) bd
applyEaBase (BasePC pc) bd t = RtlMemoryC t $ pc + bd
applyEaBase BaseNone bd t    = RtlMemoryG t bd

-- base + rn.w*cc
applyRn :: RtlVar -> Bool -> Maybe Int -> Int -> CType -> RtlVar
applyRn base w (Just rn) c t =
  let getIndex :: Bool -> Int -> RtlExpr
      getIndex True n  = ExprCast int32 $ ExprVar $ xr int16 n
      getIndex False n = ExprVar $ xr int32 n
      index = getIndex w rn
   in RtlMemoryD t base c index
applyRn base _ Nothing _ _ = base

operand2Var :: Operand -> CType -> RtlVar
operand2Var (DR r) t = dr t r
operand2Var (AR r) t = ar t r
operand2Var (Address (UnRefAR r)) t = RtlMemory $ ar (PTR t) r -- (An)
operand2Var (Address (UnRefInc r)) t =
  RtlMemory $ RtlIncDec True True $ ar (PTR t) r -- (An+)
operand2Var (Address (UnRefDec r)) t =
  RtlMemory $ RtlIncDec False False $ ar (PTR t) r -- (-An)
operand2Var (Address (Offset16 d base)) t = applyEaBase base d t -- (d, An/PC/0)
operand2Var (Address (Offset8 d base w rn cc)) t -- (d, An/PC/0, rn.w*cc)
 =
  let base1 = applyEaBase base d (PTR VOID)
   in applyRn base1 w (Just rn) cc t
operand2Var (Address (Indirect bd base w rn cc)) t -- (bd, An/PC/0, rn.w*cc)
 =
  let base1 = applyEaBase base bd (PTR VOID)
   in applyRn base1 w rn cc t
operand2Var (Address (PreIndex bd base w rn cc od)) t -- ([bd, An/PC/0, rn.w*cc], od)
 =
  let base1 = applyEaBase base bd $ PTR VOID
      base2 = applyRn base1 w rn cc t
   in RtlMemoryI t base2 od
operand2Var (Address (PostIndex bd base w rn cc od)) t -- ([bd, An/PC/0], rn.w*cc, od)
 =
  let base1 = applyEaBase base bd $ PTR VOID
   in applyRn (RtlMemoryI t base1 od) w rn cc t
operand2Var (Address (ImmAddr addr)) t = RtlMemoryG t addr
operand2Var _ _ = undefined

doCCRFlags :: (RtlVar -> RtlExpr -> a) -> Int -> [a]
doCCRFlags op v =
  [ op (RtlReg BOOL "C") $ ExprImm BOOL ((v .>>. 0) .&. 1)
  , op (RtlReg BOOL "V") $ ExprImm BOOL ((v .>>. 1) .&. 1)
  , op (RtlReg BOOL "Z") $ ExprImm BOOL ((v .>>. 2) .&. 1)
  , op (RtlReg BOOL "N") $ ExprImm BOOL ((v .>>. 3) .&. 1)
  , op (RtlReg BOOL "X") $ ExprImm BOOL ((v .>>. 4) .&. 1)
  ]

doSRFlags :: (RtlVar -> RtlExpr -> a) -> Int -> [a]
doSRFlags op v =
  [ op (RtlReg uint8 "I") $ ExprImm uint8 ((v .>>. 8) .&. 7)
  , op (RtlReg BOOL "M") $ ExprImm BOOL ((v .>>. 12) .&. 1)
  , op (RtlReg BOOL "S") $ ExprImm BOOL ((v .>>. 13) .&. 1)
  , op (RtlReg uint8 "T") $ ExprImm uint8 ((v .>>. 14) .&. 3)
  ]

toRtl :: (Int, Op) -> [RtlStmt]
toRtl (_, ORI BYTE CCR v) = doCCRFlags StmtAssignOr v
toRtl (i, ORI WORD SR v) = toRtl (i, ORI BYTE CCR v) ++ doSRFlags StmtAssignOr v
toRtl (_, ORI t ea v) =
  let ct = toCType t False
      imm = ExprImm ct v
      dst = operand2Var ea ct
   in [ StmtAssignOr dst imm
      , StmtAssign (RtlReg BOOL "V") (ExprImm BOOL 0)
      , StmtAssign (RtlReg BOOL "C") (ExprImm BOOL 0)
      , StmtAssign (RtlReg BOOL "Z") $ ExprLNot $ ExprVar dst
      , StmtAssign (RtlReg BOOL "N") $ ExprLt (ExprVar dst) (ExprImm ct 0)
      ]
toRtl (_, ANDI BYTE CCR v) = doCCRFlags StmtAssignAnd v
toRtl (i, ANDI WORD SR v) =
  toRtl (i, ANDI BYTE CCR v) ++ doSRFlags StmtAssignAnd v
toRtl (_, ANDI t ea v) =
  let ct = toCType t False
      imm = ExprImm ct v
      dst = operand2Var ea ct
   in [ StmtAssignAnd dst imm
      , StmtAssign (RtlReg BOOL "V") (ExprImm BOOL 0)
      , StmtAssign (RtlReg BOOL "C") (ExprImm BOOL 0)
      , StmtAssign (RtlReg BOOL "Z") $ ExprLNot $ ExprVar dst
      , StmtAssign (RtlReg BOOL "N") $ ExprLt (ExprVar dst) (ExprImm ct 0)
      ]
toRtl (_, EORI BYTE CCR v) = doCCRFlags StmtAssignXor v
toRtl (i, EORI WORD SR v) =
  toRtl (i, EORI BYTE CCR v) ++ doSRFlags StmtAssignXor v
toRtl (_, EORI t ea v) =
  let ct = toCType t False
      imm = ExprImm ct v
      dst = operand2Var ea ct
   in [ StmtAssignXor dst imm
      , StmtAssign (RtlReg BOOL "V") (ExprImm BOOL 0)
      , StmtAssign (RtlReg BOOL "C") (ExprImm BOOL 0)
      , StmtAssign (RtlReg BOOL "Z") $ ExprLNot $ ExprVar dst
      , StmtAssign (RtlReg BOOL "N") $ ExprLt (ExprVar dst) (ExprImm ct 0)
      ]
toRtl (_, SUBI t ea v) =
  let ct = toCType t False
      imm = ExprImm ct v
      dst = operand2Var ea ct
   in [ StmtAssign (RtlReg BOOL "V") $ ExprSubV (ExprVar dst) imm
      , StmtAssign (RtlReg BOOL "C") $ ExprSubC (ExprVar dst) imm
      , StmtAssign (RtlReg BOOL "X") $ ExprVar $ (RtlReg BOOL "C")
      , StmtAssignSub dst imm
      , StmtAssign (RtlReg BOOL "Z") $ ExprLNot $ ExprVar dst
      , StmtAssign (RtlReg BOOL "N") $ ExprLt (ExprVar dst) (ExprImm ct 0)
      ]
toRtl (_, ADDI t ea v) =
  let ct = toCType t False
      imm = ExprImm ct v
      dst = operand2Var ea ct
   in [ StmtAssign (RtlReg BOOL "V") $ ExprAddV (ExprVar dst) imm
      , StmtAssign (RtlReg BOOL "C") $ ExprAddC (ExprVar dst) imm
      , StmtAssign (RtlReg BOOL "X") $ ExprVar $ (RtlReg BOOL "C")
      , StmtAssignAdd dst imm
      , StmtAssign (RtlReg BOOL "Z") $ ExprLNot $ ExprVar dst
      , StmtAssign (RtlReg BOOL "N") $ ExprLt (ExprVar dst) (ExprImm ct 0)
      ]
toRtl (_, CMPI t ea v) =
  let ct = toCType t False
      imm = ExprImm ct v
      dst = operand2Var ea ct
   in [ StmtAssign (RtlReg BOOL "V") $ ExprSubV (ExprVar dst) imm
      , StmtAssign (RtlReg BOOL "C") $ ExprSubC (ExprVar dst) imm
      , StmtAssign (RtlReg BOOL "Z") $ ExprEq (ExprVar dst) imm
      , StmtAssign (RtlReg BOOL "N") $ ExprLt (ExprVar dst) imm
      ]
toRtl (_, BTST t ea sc) =
  let ct = toCType t False
      ea_v = ExprVar $ operand2Var ea ct
      count = case sc of 
        BImm n ->  ExprImm uint8 n
        BReg n -> ExprVar $ dr uint32 n
   in [ StmtAssign (RtlReg BOOL "Z") $ ExprBitTest ea_v count ]
toRtl (_, BCHG t ea sc) =
  let ct = toCType t False
      ea_v = operand2Var ea ct
      count = case sc of 
        BImm n ->  ExprImm uint8 n
        BReg n -> ExprVar $ dr uint32 n
   in [ StmtAssign (RtlReg BOOL "Z") $ ExprBitTest (ExprVar ea_v) count,
        StmtAssignBitFlip ea_v count
    ]
{-

decompile1 (BTST t ea sc) = do
  let ct = toCType t False
      ea_v = operand2Value ea ct
      mask = bitmask ct sc
  ccVar 'Z' $= lNot (ea_v $& mask)
decompile1 (BCHG t ea sc) = decompileBxxx "^" t ea sc
decompile1 (BCLR t ea sc) = decompileBxxx "&~" t ea sc
decompile1 (BSET t ea sc) = decompileBxxx "|" t ea sc
decompile1 (CMP2 t ea rn) = do
  let ct = toCType t (rn > 7)
      dn = rnVal ct rn
      mem = operand2Addr ea ct
      low = VarValue $ PMember ct mem 0
      high = VarValue $ PMember ct mem $ sizeOf ct
  ccVar 'Z' $= (dn $== low) $|| (dn $== high)
  ccVar 'C' $= (dn $< low) $|| (dn $> high)
  ccVar 'S' $=immNA
decompile1 (CHK2 t ea rn) = do
  decompile1 (CMP2 t ea rn)
  let cc = ccVal 'C'
  if_ cc (O.singleton $ ExtAsm "TRAP" [])
decompile1 (CAS t dc du ea) = do
  let ct = toCType t False
      dc_var = dnVar ct dc
      ea_var = operand2Var (Address ea) ct
      du_val = dnVal ct du
      dc_val = VarValue dc_var
      ea_val = VarValue ea_var
      cc = ccVal 'Z'
  defaultNZ (ea_val $- dc_val)
  cmpCV ea_val dc_val
  ifElse cc (ea_var $= du_val) (dc_var $= ea_val)
decompile1 (CAS2 t dc1 dc2 du1 du2 rn1 rn2) = do
  let ct = toCType t False
      dc1_var = dnVar ct dc1
      dc2_var = dnVar ct dc2
      rn1_var = rnVar ct rn1
      rn2_var = rnVar ct rn2
      rn1_val = VarValue rn1_var
      rn2_val = VarValue rn2_var
      du1_val = dnVal ct du1
      du2_val = dnVal ct du2
      dc1_val = VarValue dc1_var
      dc2_val = VarValue dc2_var
      cc1V = TVar BOOL 1
      cc2V = TVar BOOL 1
      elseV = do
        dc1_var $= rn1_val
        dc2_var $= rn2_val
  defaultNZ (rn1_val $- dc1_val)
  cmpCV rn1_val dc1_val
  cc1V $= ccVal 'Z'
  ifElse
    (VarValue cc1V)
    (do defaultNZ (rn2_val $- dc2_val)
        cmpCV rn2_val dc2_val
        cc2V $= ccVal 'Z'
        ifElse
          (VarValue cc2V)
          (do rn1_var $= du1_val
              rn2_var $= du2_val)
          elseV)
    elseV


{-

decompile1 (MOVES t toMem ea rn) =
  let ct = toCType t False
      rnV = rnVar ct rn
      memM = operand2Var (Address ea) ct
   in if toMem
        then do
          mem <- memM
          v <- readVar rnV
          mem $= v
        else do
          mem <- memM
          rnV $=^ mem
decompile1 (MOVEP t toMem ar im dr) = do
  let addr x = Member int8 (anVar (PTR uint8) ar) (im + x)
  dv <- dnVal uint32 dr
  let dvn = map (\x -> cast uint8 (dv $>># x)) [24, 16, 8, 0]
  (if toMem
     then (do addr 0 $= dvn !! 3
              addr 2 $= dvn !! 4
              (if t == LONG
                 then (do addr 4 $= dvn !! 2
                          addr 6 $= dvn !! 1)
                 else stmtNop))
     else (do let v0 = VarValue $ addr 0
                  v1 = VarValue $ addr 2
                  v2 = VarValue $ addr 4
                  v3 = VarValue $ addr 6
              let h = (v0 $<<# 8) $| v1
                  l = (v2 $<<# 8) $| v3
              if t == WORD
                then dnVar uint16 dr $= h
                else dnVar uint32 dr $=
                     ((cast uint32 h $<<# 16) $| cast uint32 l)))
decompile1 (MOVE _ CCR dst) = do
  dstV <- operand2Var dst uint16
  cc <- getcc
  dstV $= cc
decompile1 (MOVE _ SR dst) = do
  dstV <- operand2Var dst uint16
  cc_o <- getcc
  cc_i <- readCC 'I'
  let sr_i = cast uint16 cc_i $<<# 8
  dstV $= sr_i $| cc_o
decompile1 (MOVE _ (SpRG c) dst) = do
  dstV <- operand2Var dst uint32
  dstV $=^ GVar uint32 c
decompile1 (MOVE _ src CCR) = do
  srcVal <- operand2Value src uint16
  setcc srcVal
decompile1 (MOVE _ src SR) = do
  srcVal <- operand2Value src uint16
  setcc srcVal
  ccVar 'I' $= cast uint8 (srcVal $>># 8)
decompile1 (MOVE _ src (SpRG s)) = do
  srcVal <- operand2Value src uint16
  GVar uint32 s $= srcVal
decompile1 (MOVE t src dst) = do
  let ct = toCType t False
  srcValue <- operand2Value src ct
  dstV <- operand2Var dst ct
  defaultNZ srcValue
  nullCV
  dstV $= srcValue
decompile1 (MOVEA t src dstN) = do
  let ct = toCType t True
  srcValue <- operand2Value src ct
  anVar ct dstN $= srcValue
decompile1 (NEGX t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
      tmp = TVar t 1
  w <- cast ct <$> readCC 'X'
  dst $+= w
  tmp $=^ dst
  oldValue <- readVar dst
  dst $= neg oldValue
  dstValue <- readVar dst
  defaultNZ dstValue
  cmpCV (Const ct 0) dstValue
  updateX
decompile1 (CLR t ea) = do
  let ct = toCType t False
  dst <- operand2Var ea ct
  let newv = Const ct 0
  dst $= newv
  nullCV
  defaultNZ newv
decompile1 (NEG t ea) = do
  let ct = toCType t True
      dst = operand2Var ea ct
      tmp = TVar t 1
  oldValue <- readVar dst
  tmp $= oldValue
  dst $= neg (VarValue tmp)
  dstValue <- readVar dst
  defaultNZ dstValue
  cmpCV (Const ct 0) $ VarValue tmp
  updateX
decompile1 (NOT t ea) = do
  let ct = toCType t False
  dst <- operand2Var ea ct
  newv <- bNot <$> readVar dst
  dst $= newv
  dstVal <- readVar dst
  nullCV
  defaultNZ dstVal
decompile1 (TST t ea) = do
  src <- operand2Value ea (toCType t True)
  nullCV
  defaultNZ src
decompile1 (NBCD _ ea) = do
  dst <- operand2Var ea BCD
  tmp <- newVar BCD
  oldX <- readCC 'X'
  dst $+= oldX
  dstV <- readVar dst
  tmp $=^ dst
  dst $= neg dstV
  oldZ <- readCC 'Z'
  ccVar 'Z' $=(oldZ $&& (dstV $== Const BCD 0))
  ccVar 'C' $= Op1 "-C" $ VarValue tmp
  ccVar 'S' $= Const BOOL (-1)
  updateX
decompile1 (TAS _ ea) = do
  dst <- operand2Var ea uint8
  dstV <- readVar dst
  nullCV
  defaultNZ dstV
  dst $|= Const uint8 0x80
decompile1 (MULUL ea dr) = decompileMulL uint32 ea dr
decompile1 (MULSL ea dr) = decompileMulL int32 ea dr
decompile1 (MULULL ea dh dl) = decompileMulLL uint32 ea dh dl
decompile1 (MULSLL ea dh dl) = decompileMulLL int32 ea dh dl
decompile1 (DIVUL ea dr dq) = decompileDivL uint32 ea dr dq
decompile1 (DIVSL ea dr dq) = decompileDivL int32 ea dr dq
decompile1 (DIVULL ea dr dq) = decompileDivLL uint32 ea dr dq
decompile1 (DIVSLL ea dr dq) = decompileDivLL int32 ea dr dq
decompile1 (SWAP dn) = do
  let dd = dnVar uint32 dn
  oldV <- readVar dd
  dd $= swap oldV
  newV <- readVar dd
  nullCV
  defaultNZ newV
decompile1 (TRAPn n) = do
  newStmt $ Trap $ Just n
decompile1 (LINK rn imm) = do
  FromEnv $ modify $ \e -> e {v_savedSp = v_sp e : v_savedSp e}
  val <- readAn rn
  pushValue val
  sp <- readAn 7
  writeAn rn sp
  allocateSP imm
decompile1 (UNLK rn) = do
  FromEnv $
    modify $ \e -> e {v_sp = head $ v_savedSp e, v_savedSp = tail $ v_savedSp e}
  val <- readAn rn
  writeAn 7 val
decompile1 RESET = do
  newStmt $ ExtAsm "RESET" 0
decompile1 NOP = do
  return stmtNop
decompile1 (STOP nw) = do
  return $ ExtAsm "STOP #1" nw
decompile1 RTE = do
  return IReturn
decompile1 (RTD nw) = do
  return (Return $$ DeAllocateSP nw)
decompile1 RTS = do
  return Return
decompile1 TRAPV = do
  return $ if_ (VarValue $ ccVar 'V') (Trap Nothing)
decompile1 RTR = do
  v <- newVar uint16
  return (v $=^ spVar $$ DeAllocateSP 2 $$ setcc (VarValue v) $$ Return)
decompile1 (MOVEC toSp rn name) = do
  let v = rnVar uint32 rn
      spR = NamedVar uint32 $ SPVar name
  return
    (if toSp
       then spR $=^ v
       else v $=^ spR)
decompile1 (BKPT i) = do
  return $ BreakPoint i
decompile1 (PEA ea) = do
  let addr = operand2Addr ea uint32
  return (spTop uint32 $= addr $$ AllocateSP 4)
decompile1 (EXT WORD rn) = do
  let reg = dnVar int16 rn
      val = cast int16 $ cast int8 $ VarValue reg
  return (reg $= val $$ nullCV $$ defaultNZ val)
decompile1 (EXT LONG rn) = do
  let reg = dnVar int32 rn
      val = cast int32 $ cast int16 $ VarValue reg
  return (reg $= val $$ nullCV $$ defaultNZ val)
decompile1 (EXTB rn) = do
  let reg = dnVar int32 rn
      val = cast int32 $ cast int8 $ VarValue reg
  return (reg $= val $$ nullCV $$ defaultNZ val)
decompile1 (MOVEM WORD True (UnRefDec 7) regs) =
  decompile1MoveMPush uint16 regs
decompile1 (MOVEM WORD True (UnRefDec an) regs) =
  decompile1MoveMDecr uint16 2 regs an
decompile1 (MOVEM WORD True ea regs) = decompile1MoveMToMem uint16 ea regs
decompile1 (MOVEM LONG True (UnRefDec 7) regs) =
  decompile1MoveMPush uint32 regs
decompile1 (MOVEM LONG True (UnRefDec an) regs) =
  decompile1MoveMDecr uint32 4 regs an
decompile1 (MOVEM LONG True ea regs) = decompile1MoveMToMem uint32 ea regs
decompile1 (MOVEM WORD False (UnRefInc 7) regs) =
  decompile1MoveMPop uint16 regs
decompile1 (MOVEM WORD False (UnRefInc an) regs) =
  decompile1MoveMIncr uint16 2 regs an
decompile1 (MOVEM WORD False ea regs) =
  decompile1MoveMFromMem uint16 ea regs
decompile1 (MOVEM LONG False (UnRefInc 7) regs) =
  decompile1MoveMPop uint32 regs
decompile1 (MOVEM LONG False (UnRefInc an) regs) =
  decompile1MoveMIncr uint32 4 regs an
decompile1 (MOVEM LONG False ea regs) =
  decompile1MoveMFromMem uint32 ea regs
decompile1 (JSR ea) = do
  return $ Call $ operand2Addr ea uint32 pc
decompile1 (JMP ea) = do
  return $ Jump $ operand2Addr ea uint32 pc
decompile1 (CHK t ea dn) = do
  let ct = toCType t True
      limit = operand2Value ea ct pc
      val = VarValue $ dnVar ct dn
  return
    (ccVar 'N' $=  isNegative val $$
     if_ (isNegative val $|| (val $> limit)) (Trap Nothing))
decompile1 (LEA ea an) = do
  let addr = operand2Addr ea uint32 pc
  return (anVar uint32 an $= addr)
decompile1 (ADDQ t v ea) =
  let vv =
        if v == 0
          then 8
          else v
   in case ea of
        AR n ->
          let ct = toCType t True
           in do return (anVar ct n $+= Const ct vv)
        _ -> decompile1 (ADDI t ea vv)
decompile1 (SUBQ t v ea) =
  let vv =
        if v == 0
          then 8
          else v
   in case ea of
        AR n ->
          let ct = toCType t True
           in do return (anVar ct n $-= Const ct vv)
        _ -> decompile1 (SUBI t ea vv)
decompile1 (TRAPcc cc _) = do
  return $ if_ (cc2Cond cc) (Trap Nothing)
decompile1 (Scc cc ea) = do
  let var = operand2Var ea int8 pc
  return $ var $= CondExpr (cc2Cond cc) (Const int8 (-1)) (Const int8 0)
decompile1 (BRA target) = do
  return $ Goto target
decompile1 (BSR target) = do
  return $ SCall target
decompile1 (Bcc cc target) = do
  return $ IfGoto (cc2Cond cc) target
decompile1 (MOVEQ v dn) = do
  let dst = dnVar int32 dn
  return (dst $= Const int32 v $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (DBcc cc dn target) = do
  let dnv = dnVar int16 dn
  return
    (if_
       (lNot $ cc2Cond cc)
       (dnv $-= Const int16 1 $$
        IfGoto (VarValue dnv $!= Const int16 (-1)) target))
decompile1 (OR t ea dn) = do
  let ct = toCType t False
      src = operand2Value ea ct pc
      dst = dnVar ct dn
  return (dst $|= src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (OR_TO_MEM t dn ea) = do
  let ct = toCType t False
      dst = operand2Var (Address ea) ct pc
      src = dnVal ct dn
  return (dst $|= src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (DIVUW ea dn) = do
  let src = operand2Value ea uint16 pc
      dst = dnVar uint32 dn
  tmp <- newVar uint16
  return
    (tmp $= (VarValue dst $% src) $$ dst $/= src $$ nullCV $$
     defaultNZ (VarValue dst) $$
     dst $=
     Expr2 (VarValue tmp) (VarValue dst))
decompile1 (SBCD_REG x y) = do
  let s = dnVar BCD x
      d = dnVar BCD y
  tmp <- newVar BCD
  return
    (tmp $= VarValue d $- cast BCD (VarValue $ ccVar 'X') $$ d $= VarValue tmp $-
     VarValue s $$
     ccVar 'Z' $&&=
     VarValue d $==
     Const BCD 0 $$
     ccVar 'C' $=
     Op2 (VarValue tmp) "-C" (VarValue s) $$
     ccVar 'S' $=
     immNA $$
     updateX)
decompile1 (SBCD_MEM x y) = do
  let s = VarValue $ Deref $ PreDec (anVar (PTR BCD) x)
      d = PreDec (anVar (PTR BCD) y)
  tmp_d <- newVar (PTR BCD)
  tmp_s <- newVar BCD
  tmp <- newVar BCD
  let tmp_dv = VarValue $ Deref $ VarValue tmp_d
  return
    (tmp_d $= d $$ tmp_s $= s $$ tmp $= tmp_dv $-
     cast BCD (VarValue $ ccVar 'X') $$
     (Deref $ VarValue $ tmp_d) $=
     VarValue tmp $-
     VarValue tmp_s $$
     ccVar 'Z' $&&=
     tmp_dv $==
     Const BCD 0 $$
     ccVar 'C' $=
     Op2 (VarValue tmp) "-C" (VarValue tmp_s) $$
     updateX)
decompile1 (PACK_REG x y imm) = do
  let s = dnVal uint16 x
      d = dnVar uint8 y
  return (d $= Op2 s "PACK" (Const int16 imm))
decompile1 (PACK_MEM x y imm) = do
  let s = VarValue $ Deref $ PreDec $ anVar (PTR uint16) x
      d = Deref $ PreDec $ anVar (PTR uint8) y
  return (d $= Op2 s "PACK" (Const int16 imm))
decompile1 (UNPK_REG x y imm) = do
  let s = dnVal uint8 x
      d = dnVar uint16 y
  return (d $= Op2 s "UNPK" (Const int16 imm))
decompile1 (UNPK_MEM x y imm) = do
  let s = VarValue $ Deref $ PreDec $ anVar (PTR uint8) x
      d = Deref $ PreDec $ anVar (PTR uint16) y
  return (d $= Op2 s "UNPK" (Const int16 imm))
decompile1 (DIVSW ea dn) = do
  let src = operand2Value ea int16 pc
      dst = dnVar int32 dn
  tmp <- newVar int16
  return
    (tmp $= VarValue dst $% src $$ dst $/= src $$ nullCV $$
     defaultNZ (VarValue dst) $$
     dst $=
     Expr2 (VarValue tmp) (VarValue dst))
decompile1 (SUB t ea dn) = do
  let ct = toCType t False
      src = operand2Value ea ct pc
      dst = dnVar ct dn
  tmp = TVar t 1
  return
    (tmp $=^ dst $$ dst $-= src $$ defaultNZ (VarValue dst) $$
     cmpCV (VarValue tmp) src $$
     updateX)
decompile1 (SUB_TO_MEM t dn ea) = do
  let ct = toCType t False
      dst = operand2Var (Address ea) ct pc
      src = VarValue $ dnVar ct dn
  tmp = TVar t 1
  return
    (tmp $=^ dst $$ dst $-= src $$ defaultNZ (VarValue dst) $$
     cmpCV (VarValue tmp) src $$
     updateX)
decompile1 (SUBA t ea an) = do
  let ct = toCType t False
      src = operand2Value ea ct pc
      dst = anVar ct an
  return (dst $-= src)
decompile1 (SUBX_REG t x y) = do
  let ct = toCType t True
      s = dnVal ct x
      d = dnVar ct y
  tmp = TVar t 1
  return
    (tmp $= VarValue d $- cast ct (VarValue $ ccVar 'X') $$ d $-= s $$ ccVar 'Z' $&&=
     VarValue d $==
     Const ct 0 $$
     ccVar 'N' $=
     isNegative (VarValue d) $$
     cmpCV (VarValue tmp) s $$
     updateX)
decompile1 (SUBX_MEM t x y) = do
  let ct = toCType t True
      s = VarValue $ Deref $ PreDec $ anVar (PTR ct) x
      d = PreDec $ anVar (PTR ct) y
  tmp_d <- newVar (PTR ct)
  tmp_sv <- newVar ct
  tmp_dv <- newVar ct
  return
    (tmp_d $= d $$ tmp_sv $= s $$ tmp_dv $= VarValue (Deref $ VarValue tmp_d) $-
     cast ct (VarValue $ ccVar 'X') $$
     (Deref $ VarValue $ tmp_d) $=
     VarValue tmp_dv $-
     VarValue tmp_sv $$
     ccVar 'Z' $&&=
     derefVal tmp_d $==
     Const ct 0 $$
     ccVar 'N' $=
     (isNegative $ VarValue tmp_d) $$
     cmpCV (VarValue tmp_dv) (VarValue tmp_sv) $$
     updateX)
decompile1 (CMP t ea dn) = do
  let ct = toCType t False
      src = operand2Value ea ct pc
      dst = dnVal ct dn
  return
    (ccVar 'Z' $=  dst $== src $$ ccVar 'N' $=  isNegative (dst $- src) $$
     cmpCV dst src)
decompile1 (CMPA t ea dn) = do
  let ct = toCType t False
      src = cast int32 $ operand2Value ea ct pc
      dst = anVal int32 dn
  return
    (ccVar 'Z' $=  dst $== src $$ ccVar 'N' $=  isNegative (dst $- src) $$
     cmpCV dst src)
decompile1 (CMPM t y x) = do
  let ct = toCType t True
      s = Deref $ PostInc $ anVar (PTR ct) x
      d = Deref $ PostInc $ anVar (PTR ct) y
  tmp_s <- newVar ct
  tmp_d <- newVar ct
  return
    (tmp_d $=^ d $$ tmp_s $=^ s $$ ccVar 'Z' $=  (VarValue tmp_d) $==
     (VarValue tmp_s) $$
     ccVar 'N' $=
     isNegative ((VarValue tmp_d) $- (VarValue tmp_s)) $$
     cmpCV (VarValue tmp_d) (VarValue tmp_s))
decompile1 (EOR t dn ea) = do
  let ct = toCType t False
      dst = operand2Var ea ct pc
      src = dnVal ct dn
  return (dst $^= src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (AND t ea dn) = do
  let ct = toCType t False
      src = operand2Value ea ct pc
      dst = dnVar ct dn
  return (dst $&= src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (AND_TO_MEM t dn ea) = do
  let ct = toCType t False
      dst = operand2Var (Address ea) ct pc
      src = dnVal ct dn
  return (dst $&= src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (MULUW ea dn) = do
  let src = operand2Value ea uint16 pc
      dst = dnVar uint32 dn
  return (dst $*= src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (ABCD_REG y x) = do
  let s = dnVal BCD y
      d = dnVar BCD x
  tmp <- newVar BCD
  return
    (tmp $= (VarValue d) $+ (cast BCD $ VarValue $ ccVar 'X') $$ d $=
     (VarValue tmp) $+
     s $$
     ccVar 'Z' $&&=
     (VarValue d) $==
     Const BCD 0 $$
     ccVar 'C' $=
     Op2 (VarValue tmp) "+C" s $$
     updateX)
decompile1 (ABCD_MEM y x) = do
  let s = VarValue $ Deref $ PreDec $ anVar BCD x
      d = Deref $ PreDec $ anVar BCD y
  tmp_d <- newVar (PTR BCD)
  tmp_sv <- newVar BCD
  tmp <- newVar BCD
  return
    (tmp_d $=^ d $$ tmp_sv $= s $$ tmp $= (VarValue tmp_d) $+
     (cast BCD $ VarValue $ ccVar 'X') $$
     (Deref $ VarValue $ tmp_d) $=
     (VarValue tmp) $+
     (VarValue tmp_sv) $$
     ccVar 'Z' $&&=
     (VarValue tmp_d) $==
     Const BCD 0 $$
     ccVar 'C' $=
     Op2 (VarValue tmp) "+C" (VarValue tmp_sv) $$
     updateX)
decompile1 (MULSW ea dn) = do
  let src = operand2Value ea int16 pc
      dst = dnVar int32 dn
  return (dst $*= src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (EXG_D x y) = do
  let dx = dnVar uint32 x
      dy = dnVar uint32 y
  tmp <- newVar uint32
  return (tmp $=^ dx $$ dx $=^ dy $$ dy $=^ tmp)
decompile1 (EXG_A x y) = do
  let dx = anVar uint32 x
      dy = anVar uint32 y
  tmp <- newVar uint32
  return (tmp $=^ dx $$ dx $=^ dy $$ dy $=^ tmp)
decompile1 (EXG_DA x y) = do
  let dx = dnVar uint32 x
      dy = anVar uint32 y
  tmp <- newVar uint32
  return (tmp $=^ dx $$ dx $=^ dy $$ dy $=^ tmp)
decompile1 (SYS i) = do
  return $ Sys i
decompile1 (ADD t ea dn) = do
  let ct = toCType t False
      src = operand2Value ea ct pc
      dst = dnVar ct dn
  tmp = TVar t 1
  return
    (tmp $=^ dst $$ dst $+= src $$ defaultNZ (VarValue dst) $$
     cmpCV (VarValue tmp) (neg src) $$
     updateX)
decompile1 (ADD_TO_MEM t dn ea) = do
  let ct = toCType t False
      dst = operand2Var (Address ea) ct pc
      src = dnVal ct dn
  tmp = TVar t 1
  return
    (tmp $=^ dst $$ dst $+= src $$ defaultNZ (VarValue dst) $$
     cmpCV (VarValue tmp) (neg src) $$
     updateX)
decompile1 (ADDA t ea an) = do
  let ct = toCType t False
      src = operand2Value ea ct pc
      dst = anVar ct an
  return $ dst $+= src
decompile1 (ADDX_REG t y x) = do
  let ct = toCType t True
      s = dnVal ct y
      d = dnVar ct x
  tmp = TVar t 1
  return
    (tmp $= (VarValue d) $+ (cast ct $ VarValue $ ccVar 'X') $$ d $+= s $$
     ccVar 'Z' $&&=
     (VarValue d) $==
     Const ct 0 $$
     ccVar 'N' $=
     (isNegative $ VarValue d) $$
     (cmpCV (VarValue tmp) (neg s)) $$
     updateX)
decompile1 (ADDX_MEM t y x) = do
  let ct = toCType t True
      s = VarValue $ Deref $ PreDec $ anVar (PTR ct) x
      d = PreDec $ anVar (PTR ct) y
  tmp_d <- newVar (PTR ct)
  tmp_sv <- newVar ct
  tmp_dv <- newVar ct
  return
    (tmp_d $= d $$ tmp_sv $= s $$ tmp_dv $= VarValue (Deref $ VarValue tmp_d) $+
     cast ct (VarValue $ ccVar 'X') $$
     (Deref $ VarValue $ tmp_d) $=
     VarValue tmp_dv $+
     VarValue tmp_sv $$
     ccVar 'Z' $&&=
     derefVal tmp_d $==
     Const ct 0 $$
     ccVar 'N' $=
     (isNegative $ VarValue tmp_d) $$
     cmpCV (VarValue tmp_dv) (neg $ VarValue tmp_sv) $$
     updateX)
decompile1 (ASR t scIsReg sc reg) = do
  let ct = toCType t True
      sc_v =
        if scIsReg
          then dnVal uint8 sc
          else Const
                 uint8
                 (if sc == 0
                    then 8
                    else sc)
      dst = dnVar ct reg
      carry = ((VarValue dst) $>> (sc_v $-# 1)) $&# 1
  return
    (ccVar 'V' $=  immF $$
     ifElse
       (sc_v $!= Const uint8 0)
       (ccVar 'C' $=  (cast BOOL carry) $$ dst $>>= sc_v $$ ccVar 'X' $= ^
        ccVar 'C')
       (ccVar 'C' $=  immF) $$
     defaultNZ (VarValue dst))
decompile1 (ASL t scIsReg sc reg) = do
  let ct = toCType t True
      sc_v =
        if scIsReg
          then dnVal uint8 sc
          else Const
                 uint8
                 (if sc == 0
                    then 8
                    else sc)
      dst = dnVar ct reg
  tmp = TVar t 1
  let carry = ((VarValue dst) $<< (sc_v $-# 1)) $< Const ct 0
  return
    (ccVar 'V' $=  (Op2 (VarValue dst) "<<V" sc_v) $$
     ifElse
       (sc_v $!= (Const uint8 0))
       (ccVar 'C' $=  carry $$ dst $<<= sc_v $$ ccVar 'X' $= ^ ccVar 'C')
       (ccVar 'C' $=  immF) $$
     defaultNZ (VarValue dst))
decompile1 (LSR t scIsReg sc reg) = do
  let ct = toCType t False
      sc_v =
        if scIsReg
          then dnVal uint8 sc
          else Const
                 uint8
                 (if sc == 0
                    then 8
                    else sc)
      dst = dnVar ct reg
  let carry = (cast BOOL $ ((VarValue dst) $>> (sc_v $-# 1)) $&# 1)
  return
    (ccVar 'V' $=  immF $$
     ifElse
       (sc_v $!= (Const uint8 0))
       (ccVar 'C' $=  carry $$ dst $>>= sc_v $$ ccVar 'X' $= ^ ccVar 'C')
       (ccVar 'C' $=  immF) $$
     defaultNZ (VarValue dst))
decompile1 (LSL t scIsReg sc reg) = do
  let ct = toCType t False
      sc_v =
        if scIsReg
          then dnVal uint8 sc
          else Const
                 uint8
                 (if sc == 0
                    then 8
                    else sc)
      dst = dnVar ct reg
  let carry = isNegative $ (VarValue dst) $<< (sc_v $-# 1)
  return
    (ccVar 'V' $=  immF $$
     ifElse
       (sc_v $!= (Const uint8 0))
       (ccVar 'C' $=  carry $$ dst $<<= sc_v $$ ccVar 'X' $= ^ ccVar 'C')
       (ccVar 'C' $=  immF) $$
     defaultNZ (VarValue dst))
decompile1 (ROXR t scIsReg sc reg) = do
  let ct = toCType t False
      sc_v =
        if scIsReg
          then dnVal uint8 sc
          else Const
                 uint8
                 (if sc == 0
                    then 8
                    else sc)
      dst = dnVar ct reg
      sz =
        Const
          uint8
          (case t of
             BYTE -> 8
             WORD -> 16
             LONG -> 32)
  let carry = cast BOOL $ ((VarValue dst) $>> (sc_v $-# 1)) $&# 1
  return
    (ccVar 'V' $=  immF $$
     ifElse
       (sc_v $== (Const uint8 0))
       (ccVar 'C' $= ^ ccVar 'X')
       (ccVar 'C' $=  carry $$ dst $= ((VarValue dst) $<< (sz $- sc_v $+# 1)) $|
        ((cast ct $ VarValue $ ccVar 'X') $<< (sz $- sc_v)) $|
        ((VarValue dst) $>> sc_v) $$
        ccVar 'X' $= ^
        ccVar 'C') $$
     defaultNZ (VarValue dst))
decompile1 (ROXL t scIsReg sc reg) = do
  let ct = toCType t False
      sc_v =
        if scIsReg
          then dnVal uint8 sc
          else Const
                 uint8
                 (if sc == 0
                    then 8
                    else sc)
      dst = dnVar ct reg
      sz =
        Const
          uint8
          (case t of
             BYTE -> 8
             WORD -> 16
             LONG -> 32)
  let carry = isNegative ((VarValue dst) $<< (sc_v $-# 1))
  return
    (ccVar 'V' $=  immF $$
     ifElse
       (sc_v $== (Const uint8 0))
       (ccVar 'C' $= ^ ccVar 'X')
       (ccVar 'C' $=  carry $$ dst $= ((VarValue dst) $>> (sz $- sc_v)) $|
        ((cast ct $ VarValue $ ccVar 'X') $<< (sc_v $-# 1)) $|
        ((VarValue dst) $<< sc_v) $$
        ccVar 'X' $= ^
        ccVar 'C') $$
     defaultNZ (VarValue dst))
decompile1 (ROR t scIsReg sc reg) = do
  let ct = toCType t False
      sc_v =
        if scIsReg
          then dnVal uint8 sc
          else Const
                 uint8
                 (if sc == 0
                    then 8
                    else sc)
      dst = dnVar ct reg
      sz =
        Const
          uint8
          (case t of
             BYTE -> 8
             WORD -> 16
             LONG -> 32)
      carry = cast BOOL $ ((VarValue dst) $>> (sc_v $-# 1)) $&# 1
  return
    (ccVar 'V' $=  immF $$
     ifElse
       (sc_v $== (Const uint8 0))
       (ccVar 'C' $=  immF)
       (ccVar 'C' $=  carry $$ dst $= ((VarValue dst) $<< (sz $- sc_v)) $|
        ((VarValue dst) $>> sc_v)) $$
     defaultNZ (VarValue dst))
decompile1 (ROL t scIsReg sc reg) = do
  let ct = toCType t False
      ccVart = toCType t True
      sc_v =
        if scIsReg
          then dnVal uint8 sc
          else Const
                 uint8
                 (if sc == 0
                    then 8
                    else sc)
      dst = dnVar ct reg
      sz =
        Const
          uint8
          (case t of
             BYTE -> 8
             WORD -> 16
             LONG -> 32)
  tmp = TVar t 1
  let carry = isNegative $ (VarValue tmp) $<< (sc_v $-# 1)
  return
    (ccVar 'V' $=  immF $$
     ifElse
       (sc_v $== (Const uint8 0))
       (ccVar 'C' $=  immF)
       (ccVar 'C' $=  carry $$ dst $= ((VarValue dst) $>> (sz $- sc_v)) $|
        ((VarValue dst) $<< sc_v)) $$
     defaultNZ (VarValue dst))
decompile1 (ASR_EA ea) = do
  let dst = operand2Var (Address ea) int16 pc
  return
    (ccVar 'V' $=  immF $$ ccVar 'C' $=  (cast BOOL $ (VarValue dst) $&# 1) $$ dst $>>=
     Const uint8 1 $$
     ccVar 'X' $= ^
     ccVar 'C' $$
     defaultNZ (VarValue dst))
decompile1 (ASL_EA ea) = do
  let dst = operand2Var (Address ea) int16 pc
  return
    (ccVar 'C' $=  (cast BOOL $ (VarValue dst) $&# 0x8000) $$ dst $<<=
     Const uint8 1 $$
     ccVar 'V' $=
     ((VarValue dst) $< (Const int16 0)) $!=
     (VarValue $ ccVar 'C') $$
     ccVar 'X' $= ^
     ccVar 'C' $$
     defaultNZ (VarValue dst))
decompile1 (LSR_EA ea) = do
  let dst = operand2Var (Address ea) uint16 pc
  return
    (ccVar 'V' $=  immF $$ ccVar 'C' $=  (cast BOOL $ (VarValue dst) $&# 1) $$ dst $>>=
     Const uint8 1 $$
     ccVar 'X' $= ^
     ccVar 'C' $$
     defaultNZ (VarValue dst))
decompile1 (LSL_EA ea) = do
  let dst = operand2Var (Address ea) uint16 pc
  return
    (ccVar 'V' $=  immF $$ ccVar 'C' $=  (cast BOOL $ (VarValue dst) $&# 0x8000) $$
     dst $<<=
     Const uint8 1 $$
     ccVar 'X' $= ^
     ccVar 'C' $$
     defaultNZ (VarValue dst))
decompile1 (ROXR_EA ea) = do
  let dst = operand2Var (Address ea) uint16 pc
      x = cast uint16 $ VarValue $ ccVar 'X'
  return
    (ccVar 'V' $=  immF $$ ccVar 'C' $=  (cast BOOL $ (VarValue dst) $&# 1) $$ dst $=
     ((VarValue dst) $>># 1) $|
     (x $<<# 15) $$
     ccVar 'X' $= ^
     ccVar 'C' $$
     defaultNZ (VarValue dst))
decompile1 (ROXL_EA ea) = do
  let dst = operand2Var (Address ea) uint16 pc
      x = cast uint16 $ VarValue $ ccVar 'X'
  return
    (ccVar 'V' $=  immF $$ ccVar 'C' $=  isNegative (VarValue dst) $$ dst $= x $|
     ((VarValue dst) $<<# 1) $$
     ccVar 'X' $= ^
     ccVar 'C' $$
     defaultNZ (VarValue dst))
decompile1 (ROR_EA ea) = do
  let dst = operand2Var (Address ea) uint16 pc
  return
    (ccVar 'V' $=  immF $$ ccVar 'C' $=  cast BOOL (VarValue dst $&# 1) $$ dst $=
     (VarValue dst $<<# 15) $|
     (VarValue dst $>># 1) $$
     defaultNZ (VarValue dst))
decompile1 (ROL_EA ea) = do
  let dst = operand2Var (Address ea) uint16 pc
  return
    (ccVar 'V' $=  immF $$ ccVar 'C' $=  cast BOOL (VarValue dst $&# 0x8000) $$
     dst $=
     (VarValue dst $<<# 1) $|
     (VarValue dst $>># 15) $$
     defaultNZ (VarValue dst))
decompile1 (BFTST ea offset_p width_p) = do
  temp <- newVar int32
  (s, src) <- getBFValue int32 ea offset_p width_p pc
  return (s $$ temp $=^ src $$ nullCV $$ defaultNZ (VarValue temp))
decompile1 (BFCHG ea offset_p width_p) = do
  temp <- newVar int32
  (s, dst) <- getBFValue int32 ea offset_p width_p pc
  return
    (s $$ temp $=^ dst $$ dst $= bNot (VarValue temp) $$ nullCV $$
     defaultNZ (VarValue temp))
decompile1 (BFCLR ea offset_p width_p) = do
  temp <- newVar int32
  (s, dst) <- getBFValue int32 ea offset_p width_p pc
  return
    (s $$ temp $=^ dst $$ dst $= Const int32 0 $$ nullCV $$
     defaultNZ (VarValue temp))
decompile1 (BFSET ea offset_p width_p) = do
  temp <- newVar int32
  (s, dst) <- getBFValue int32 ea offset_p width_p pc
  return
    (s $$ temp $=^ dst $$ dst $= Const int32 (-1) $$ nullCV $$
     defaultNZ (VarValue temp))
decompile1 (BFEXTU ea offset_p width_p dn) = do
  let dst = dnVar uint32 dn
  (s, src) <- getBFValue uint32 ea offset_p width_p pc
  return (s $$ dst $=^ src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (BFEXTS ea offset_p width_p dn) = do
  let dst = dnVar int32 dn
  (s, src) <- getBFValue int32 ea offset_p width_p pc
  return (s $$ dst $=^ src $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (BFFFO ea offset_p width_p dn) = do
  let dst = dnVar uint32 dn
  (s, src) <- getBFValue uint32 ea offset_p width_p pc
  return
    (s $$ dst $= Op1 "FFO" (VarValue src) $$ nullCV $$ defaultNZ (VarValue dst))
decompile1 (BFINS dn ea offset_p width_p) = do
  let src = dnVal int32 dn
  (s, dst) <- getBFValue int32 ea offset_p width_p pc
  return (s $$ dst $= src $$ nullCV $$ defaultNZ src)
decompile1 _ = do
  return $ Trap Nothing

getBFValue t ea (BImm o) (BImm w) = do
  let base =
        operand2Var
          ea
          (case ea of
             DR _ -> int32
             _    -> VOID)
          pc
  return (stmtNop, BitField t base o w)
getBFValue t ea offset_p width_p = do
  offsetVar <- newVar int32
  widthVar <- newVar uint32
  let base =
        operand2Var
          ea
          (case ea of
             DR _ -> int32
             _    -> VOID)
          pc
      v1 =
        case offset_p of
          BImm n -> Const int32 n
          BReg n -> dnVal int32 n
      v2 =
        case width_p of
          BImm n -> Const uint32 n
          BReg n -> dnVal uint32 n
  return
    ( (offsetVar $= v1 $$ widthVar $= v2)
    , BitFieldX t base (VarValue offsetVar) (VarValue widthVar))

decompile :: Int -> Int -> MEnv -> M.Map Int (Op, Int) -> [(Int, [Stmt a])]
decompile begin end ev o
  | begin < end =
    let (op, next) = o M.! begin
        ret = O.view $ decompile1 op
     in case ret of
          Known _ -> undefined
          FromEnv s ->
            let ev' = execState s ev
             in (begin, v_stmt ev') : decompile next end ev' o
  | otherwise = []

-}


decompileBxxx :: String -> AType -> Operand -> BopSc -> DecompileRet
decompileBxxx op t ea pos = do
  let ct = toCType t False
      ea_var = operand2Var ea (toCType t False)
      tmp_var = TVar ct 1
      ea_val = cast ct $ VarValue ea_var
  tmp_var $= ea_val
  let mask = bitmask ct pos
  assignOp op ea_var mask
  ccVar 'Z' $= lNot (VarValue tmp_var) $& mask

decompile1MoveMPush :: CType -> [Int] -> DecompileRet
decompile1MoveMPush t regs =
  let pushV x = do
        allocateSP (sizeOf t)
        let var = SVar t 0
            val = rnVal t x
        var $= val
   in mapM_ pushV (reverse regs)

decompile1MoveMDecr :: CType -> Int -> [Int] -> Int -> DecompileRet
decompile1MoveMDecr t sz regs an = do
  let base = anVar t an
      regsR = reverse $ zip [0 ..] regs
      len = length regs
      temp = TVar t 1
  temp $= (VarValue base $+# (-(len * sz)))
  mapM_
    (\(i, n) -> do
       let val = rnVal t n
       (VarValue base $@# i) $= val)
    regsR
  base $=^ temp

decompile1MoveMToMem :: CType -> MemOperand -> [Int] -> DecompileRet
decompile1MoveMToMem t ea regs = do
  let temp = TVar t 1
      base = operand2Addr ea (PTR t)
      rs = zip [0 ..] regs
  temp $= base
  mapM_
    (\(i, n) -> do
       let val = rnVal t n
       (VarValue temp $@# i) $= val)
    rs

decompile1MoveMPop :: CType -> [Int] -> DecompileRet
decompile1MoveMPop t =
  mapM_
    (\x -> do
       let top = SVar t 0
       rnVar t x $=^ Deref (VarValue top)
       top $+= Const int32 (sizeOfS t))

decompile1MoveMIncr :: CType -> Int -> [Int] -> Int -> DecompileRet
decompile1MoveMIncr t sz regs an = do
  let base = anVar t an
      regsR = zip [0 ..] regs
      len = length regs
      temp = TVar t 1
  temp $=^ base
  mapM_ (\(i, n) -> rnVar t n $=^ (VarValue temp $@# i)) regsR
  base $= (VarValue temp $+# (len * sz))

decompile1MoveMFromMem :: CType -> MemOperand -> [Int] -> DecompileRet
decompile1MoveMFromMem t ea regs = do
  let rs = zip [0 ..] regs
      temp = TVar t 1
      base = operand2Addr ea (PTR t)
  temp $= base
  mapM_ (\(i, n) -> rnVar t n $=^ (VarValue temp $@# i)) rs

decompileMulL :: CType -> Operand -> Int -> DecompileRet
decompileMulL t ea dr = do
  let src = operand2Value ea t
      dst = dnVar t dr
      dstV = VarValue dst
      (h, l) = Cast t dstV $** Cast t src
  ccVar 'V' $= cast BOOL h
  ccVar 'C' $=immF
  dst $= l
  defaultNZ dstV

decompileMulLL :: CType -> Operand -> Int -> Int -> DecompileRet
decompileMulLL t ea dh dl = do
  let src = operand2Value ea t
      dstH = dnVar t dh
      dstL = dnVar t dl
      zero = Const t 0
      oldL = VarValue dstL
      (h, l) = Cast t oldL $** Cast t src
      retH = VarValue dstH
      retL = VarValue dstL
  dstH $= h
  dstL $= l
  ccVar 'V' $=immF
  ccVar 'C' $=immF
  ccVar 'Z' $= (retH $== zero) $&& (retL $== zero)
  ccVar 'N' $= isNegative retH
  ccVar 'S' $= Const BOOL (-1)

decompileDivL :: CType -> Operand -> Int -> Int -> DecompileRet
decompileDivL t ea dr dq = do
  let src = operand2Value ea t
      dstR = dnVar t dr
      dstQ = dnVar t dq
      qv = VarValue dstQ
      tmp = TVar t 1
  ccVar 'V' $=immF
  ccVar 'C' $=immF
  tmp $= qv
  dstQ $/= src
  when (dr /= dq) $ dstR $= VarValue tmp $% src
  defaultNZ qv

decompileDivLL :: CType -> Operand -> Int -> Int -> DecompileRet
decompileDivLL t ea dr dq = do
  let src = operand2Value ea t
      dstR = dnVar t dr
      dstQ = dnVar t dq
      rv = VarValue dstR
      qv = VarValue dstQ
      tmpH = TVar t 1
      tmpL = TVar t 2
  tmpH $= rv
  tmpL $= qv
  let lval = Expr2 (VarValue tmpH) (VarValue tmpL)
  dstR $= lval $% src
  dstQ $= lval $/ src
  ccVar 'V' $= lval $/! src
  ccVar 'C' $= immF
  defaultNZ qv
-}
