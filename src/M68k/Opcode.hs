module M68k.Opcode
  ( Op(..)
  , BopSc(..)
  ) where

import           M68k.Common

import           Data.List    (intercalate)
import           M68k.Operand
import           Text.Printf  (PrintfArg (formatArg), printf)

data BopSc
  = BImm Int
  | BReg DR
  deriving (Eq)

instance PrintfArg BopSc where
  formatArg = formatArg . show

instance Show BopSc where
  show (BImm n)  = printf "#%d" n
  show (BReg dr) = show dr

data Op
  = ILLEGAL
  | ORI AType Operand Int
  | ANDI AType Operand Int
  | SUBI AType Operand Int
  | ADDI AType Operand Int
  | EORI AType Operand Int
  | CMPI AType Operand Int
  | BTST AType Operand BopSc
  | BCHG AType Operand BopSc
  | BCLR AType Operand BopSc
  | BSET AType Operand BopSc
  | CMP2 AType MemOperand XR
  | CHK2 AType MemOperand XR
  | CAS AType DR DR MemOperand
  | CAS2 AType DR DR DR DR XR XR
  | MOVES AType Bool MemOperand XR
  | MOVEP AType Bool AR Int DR
  | MOVE AType Operand Operand
  | MOVEA AType Operand AR
  | NEGX AType Operand
  | CLR AType Operand
  | NEG AType Operand
  | NOT AType Operand
  | TST AType Operand
  | NBCD AType Operand
  | TAS AType Operand
  | MULUL Operand DR
  | MULSL Operand DR
  | MULULL Operand DR DR
  | MULSLL Operand DR DR
  | DIVUL Operand DR DR
  | DIVSL Operand DR DR
  | DIVULL Operand DR DR
  | DIVSLL Operand DR DR
  | SWAP DR
  | TRAPn Int
  | LINK AR Int
  | UNLK AR
  | RESET
  | NOP
  | STOP Int
  | RTE
  | RTD Int
  | RTS
  | TRAPV
  | RTR
  | BKPT Int
  | PEA MemOperand
  | EXT AType DR
  | EXTB DR
  | MOVEM AType Bool MemOperand [XR]
  | JSR MemOperand
  | JMP MemOperand
  | CHK AType Operand DR
  | LEA MemOperand AR
  | MOVEC Bool XR String
  | ADDQ AType Int Operand
  | SUBQ AType Int Operand
  | TRAPcc CC (Maybe Int)
  | Scc CC Operand
  | DBcc CC DR Int
  | BRA Int
  | BSR Int
  | Bcc CC Int
  | MOVEQ Int DR
  | OR AType Operand DR
  | OR_TO_MEM AType DR MemOperand
  | DIVUW Operand DR
  | SBCD_REG DR DR
  | SBCD_MEM AR AR
  | PACK_REG DR DR Int
  | PACK_MEM AR AR Int
  | UNPK_REG DR DR Int
  | UNPK_MEM AR AR Int
  | DIVSW Operand DR
  | SUB AType Operand DR
  | SUB_TO_MEM AType DR MemOperand
  | SUBA AType Operand AR
  | SUBX_REG AType DR DR
  | SUBX_MEM AType AR AR
  | CMP AType Operand DR
  | CMPA AType Operand AR
  | CMPM AType AR AR
  | EOR AType DR Operand
  | AND AType Operand DR
  | AND_TO_MEM AType DR MemOperand
  | MULUW Operand DR
  | ABCD_REG DR DR
  | ABCD_MEM AR AR
  | EXG_D DR DR
  | EXG_A AR AR
  | EXG_DA DR AR
  | MULSW Operand DR
  | SYS Int
  | ADD AType Operand DR
  | ADD_TO_MEM AType DR MemOperand
  | ADDA AType Operand AR
  | ADDX_REG AType DR DR
  | ADDX_MEM AType AR AR
  | ASR AType BopSc DR
  | ASL AType BopSc DR
  | LSR AType BopSc DR
  | LSL AType BopSc DR
  | ROXR AType BopSc DR
  | ROXL AType BopSc DR
  | ROR AType BopSc DR
  | ROL AType BopSc DR
  | ASR_EA MemOperand
  | ASL_EA MemOperand
  | LSR_EA MemOperand
  | LSL_EA MemOperand
  | ROXR_EA MemOperand
  | ROXL_EA MemOperand
  | ROR_EA MemOperand
  | ROL_EA MemOperand
  | BFTST Operand BopSc BopSc
  | BFCHG Operand BopSc BopSc
  | BFCLR Operand BopSc BopSc
  | BFSET Operand BopSc BopSc
  | BFEXTU Operand BopSc BopSc DR
  | BFEXTS Operand BopSc BopSc DR
  | BFFFO Operand BopSc BopSc DR
  | BFINS DR Operand BopSc BopSc
  | FOp String FpuOperand FPR
  | FSINCOS FpuOperand FPR FPR
  | FTST FpuOperand
  | FMOVECR Int FPR
  | FMOVEStore FPR FpuOperand
  | FMOVEStoreP FPR FpuOperand BopSc
  | FMOVECC Bool [String] MemOperand
  | FMOVEM_STATIC Bool MemOperand [FPR]
  | FMOVEM_DYNAMIC Bool MemOperand DR
  | FScc FCC Operand
  | FDBcc FCC DR Int
  | FTRAPcc FCC Int
  | FNOP
  | FBcc FCC Int
  | FSAVE MemOperand
  | FRESTORE MemOperand
  | CINVL String AR
  | CINVP String AR
  | CINVA String
  | CPUSHL String AR
  | CPUSHP String AR
  | CPUSHA String
  | PFLUSHN AR
  | PFLUSH AR
  | PFLUSHAN
  | PFLUSHA
  | PTESTW AR
  | PTESTR AR
  | MOVE16 Bool Bool AR Int
  | MOVE16IncInc AR AR
  deriving (Eq)

toRegList :: (Reg a) => (a, a) -> [a] -> [(a, a)]
toRegList c [] = [c]
toRegList (n1, n2) (s:os) =
  if abs (reg_num n2 - reg_num s) == 1
    then toRegList (n1, s) os
    else (n1, n2) : toRegList (s, s) os

toRegStr :: (Show a, Reg a, Eq a) => [a] -> String
toRegStr [] = ""
toRegStr [reg] = show reg
toRegStr (r1:regs) =
  intercalate
    "/"
    ((\(f, e) ->
        if f == e
          then show f
          else show f ++ "-" ++ show e) <$>
     toRegList (r1, r1) regs)

showImm :: Bool -> AType -> Int -> String
showImm False _ v   = printf "#%d" v
showImm True BYTE v = printf "#0x%02x" v
showImm True WORD v = printf "#0x%04x" v
showImm True LONG v = printf "#0x%08x" v

instance Show Op where
  show (ORI t o v) = printf "ori.%s %s, %s" t (showImm True t v) o
  show (ANDI t o v) = printf "andi.%s %s, %s" t (showImm True t v) o
  show (SUBI t o v) = printf "subi.%s %s, %s" t (showImm False t v) o
  show (ADDI t o v) = printf "addi.%s %s, %s" t (showImm False t v) o
  show (EORI t o v) = printf "eori.%s %s, %s" t (showImm True t v) o
  show (CMPI t o v) = printf "cmpi.%s %s, %s" t (showImm False t v) o
  show (BTST t o n) = printf "btst.%s %s, %s" t n o
  show (BCHG t o n) = printf "bchg.%s %s, %s" t n o
  show (BCLR t o n) = printf "bclr.%s %s, %s" t n o
  show (BSET t o n) = printf "bset.%s %s, %s" t n o
  show (CMP2 t o i) = printf "cmp2.%s %s, %s" (show t) (show o) (show i)
  show (CHK2 t o i) = printf "chk2.%s %s, %s" (show t) (show o) (show i)
  show (CAS t c u o) =
    printf "cas.%s %s, %s, %v" (show t) (show c) (show u) (show o)
  show (CAS2 t c1 c2 u1 u2 m1 m2) =
    printf "cas2.%v %v:%v, %v:%v (%v):(%v)" t c1 c2 u1 u2 m1 m2
  show (MOVES t True o rn) = printf "moves.%v %s, %v" t rn o
  show (MOVES t False o rn) = printf "mvoes.%v %v, %s" t o rn
  show (MOVEP t True an imm dn) = printf "movep.%v %s, (%d, %s)" t dn imm an
  show (MOVEP t False an imm dn) = printf "movep.%v (%d, %v), %v" t imm an dn
  show (MOVE t src dst) = printf "move.%v %v, %v" t src dst
  show (MOVEA t src an) = printf "move.%v %v, %v" t src an
  show (NEGX t o) = printf "negx.%v %v" t o
  show (CLR t o) = printf "clr.%v %v" t o
  show (NEG t o) = printf "neg.%v %v" t o
  show (NOT t o) = printf "not.%v %v" t o
  show (TST t o) = printf "tst.%v %v" t o
  show (NBCD t o) = printf "nbcd.%v %v" t o
  show (TAS _ o) = printf "tas.B %v" o
  show (MULUL o dn) = printf "mulu.l %v, %v" o dn
  show (MULSL o dn) = printf "muls.l %v, %v" o dn
  show (MULULL o h l) = printf "mulu.l %v, %v-%v" o h l
  show (MULSLL o h l) = printf "muls.l %v, %v-%v" o h l
  show (DIVUL o r q) =
    if r == q
      then printf "divu.l %v, %v" o q
      else printf "divu.l %v, %v:%v" o r q
  show (DIVSL o r q) =
    if r == q
      then printf "divs.l %v, %v" o q
      else printf "divs.l %v, %v:%v" o r q
  show (DIVULL o h l) = printf "divul.l %v, %v:%v" o h l
  show (DIVSLL o h l) = printf "dissl.l %v, %v:%v" o h l
  show (SWAP dn) = printf "swap %v" dn
  show (TRAPn n) = printf "trap #%d" n
  show (LINK an disp) = printf "link %v, #%d" an disp
  show (UNLK an) = printf "unlk %v" an
  show RESET = "reset"
  show NOP = "nop"
  show (STOP n) = printf "stop #%04x" n
  show RTE = "rtr"
  show (RTD n) = printf "rtd #%d" n
  show RTS = "rts"
  show TRAPV = "trapv"
  show RTR = "rtr"
  show (BKPT n) = printf "bkpt #%d" n
  show (PEA o) = printf "pea %v" o
  show (EXT t v) = printf "ext.%v %v" t v
  show (EXTB v) = printf "extb.l %v" v
  show (MOVEM t toMem o rs) =
    let regStr =
          toRegStr
            (case o of
               (UnRefDec _) -> reverse rs
               _            -> rs)
     in if toMem
          then printf "movem.%v %v, %v" t regStr o
          else printf "movem.%v %v, %v" t o regStr
  show (JSR o) = printf "jsr %v" o
  show (JMP o) = printf "jmp %v" o
  show (CHK t o v) = printf "chk.%v %v, %v" t o v
  show (LEA o v) = printf "lea %v, %v" o v
  show (MOVEC True x s) = printf "movec %v, %%%s" x s
  show (MOVEC False x s) = printf "movec %%%s, %v" s x
  show (ADDQ t i o) = printf "addq.%v #%d, %v" t i o
  show (SUBQ t i o) = printf "subq.%v #%d, %v" t i o
  show (TRAPcc cc Nothing) = printf "trap%v" cc
  show (TRAPcc cc (Just i)) = printf "trap%v #%d" cc i
  show (Scc cc o) = printf "s%v %v" cc o
  show (DBcc cc dn target) = printf "DB%v %v, _%05X" cc dn target
  show (BRA target) = printf "bra _%05X" target
  show (BSR target) = printf "bsr _%05X" target
  show (Bcc cc target) = printf "b%v _%05X" cc target
  show (MOVEQ i dn) = printf "moveq #%d, %v" i dn
  show (OR t src dst) = printf "or.%v %v, %v" t src dst
  show (OR_TO_MEM t src dst) = printf "or.%v %v, %v" t src dst
  show (DIVUW o dn) = printf "divu.w %v, %v" o dn
  show (SBCD_REG x y) = printf "sbcd %v, %v" x y
  show (SBCD_MEM x y) = printf "sbcd -(%v), -(%v)" x y
  show (PACK_REG x y adj) = printf "pack %v, %v, #%d" x y adj
  show (PACK_MEM x y adj) = printf "pack -(%v), -(%v), #%d" x y adj
  show (UNPK_REG x y adj) = printf "unpk %v, %v, #%d" x y adj
  show (UNPK_MEM x y adj) = printf "unpk -(%v), -(%v), #%d" x y adj
  show (DIVSW o dn) = printf "divu.w %v, %v" o dn
  show (SUB t src dst) = printf "sub.%v %v, %v" t src dst
  show (SUB_TO_MEM t src dst) = printf "sub.%v %v, %v" t src dst
  show (SUBA t src dst) = printf "suba.%v %v, %v" t src dst
  show (SUBX_REG t x y) = printf "subx.%v %v, %v" t x y
  show (SUBX_MEM t x y) = printf "subx.%v -(%v), -(%v)" t x y
  show (CMP t src dst) = printf "cmp.%v %v, %v" t src dst
  show (CMPA t src dst) = printf "cmpa.%v %v, %v" t src dst
  show (CMPM t src dst) = printf "cmp.%v (%v)+, (%v)+" t src dst
  show (EOR t src dst) = printf "eor.%v %v, %v" t src dst
  show (AND t src dst) = printf "and.%v %v, %v" t src dst
  show (AND_TO_MEM t src dst) = printf "and.%v %v, %v" t src dst
  show (MULUW o dn) = printf "mulu.w %v, %v" o dn
  show (ABCD_REG x y) = printf "abcd %v, %v" x y
  show (ABCD_MEM x y) = printf "abcd -(%v), -(%v)" x y
  show (EXG_D x y) = printf "exg %v, %v" x y
  show (EXG_A x y) = printf "exg %v, %v" x y
  show (EXG_DA x y) = printf "exg %v, %v" x y
  show (MULSW o dn) = printf "muls.w %v, %v" o dn
  show (SYS x) = printf "syscall #%X" x
  show (ADD t src dst) = printf "add.%v %v, %v" t src dst
  show (ADD_TO_MEM t src dst) = printf "add.%v %v, %v" t src dst
  show (ADDA t src dst) = printf "adda.%v %v, %v" t src dst
  show (ADDX_REG t x y) = printf "addx.%v %v, %v" t x y
  show (ADDX_MEM t x y) = printf "addx.%v -(%v), -(%v)" t x y
  show (ASR t x y) = printf "asr.%v %v, %v" t x y
  show (ASL t x y) = printf "asl.%v %v, %v" t x y
  show (LSR t x y) = printf "lsr.%v %v, %v" t x y
  show (LSL t x y) = printf "lsl.%v %v, %v" t x y
  show (ROXR t x y) = printf "roxr.%v %v, %v" t x y
  show (ROXL t x y) = printf "roxl.%v %v, %v" t x y
  show (ROR t x y) = printf "ror.%v %v, %v" t x y
  show (ROL t x y) = printf "roxr.%v %v, %v" t x y
  show (ASR_EA o) = printf "asr.w %v" o
  show (ASL_EA o) = printf "asl.w %v" o
  show (LSR_EA o) = printf "lsr.w %v" o
  show (LSL_EA o) = printf "lsl.w %v" o
  show (ROXR_EA o) = printf "roxr.w %v" o
  show (ROXL_EA o) = printf "roxl.w %v" o
  show (ROR_EA o) = printf "ror.w %v" o
  show (ROL_EA o) = printf "rol.w %v" o
  show (BFTST o l w) = printf "bftst %v{%v,%v}" o l w
  show (BFCHG o l w) = printf "bfchg %v{%v,%v}" o l w
  show (BFCLR o l w) = printf "bfclr %v{%v,%v}" o l w
  show (BFSET o l w) = printf "bfset %v{%v,%v}" o l w
  show (BFEXTU o l w d) = printf "bfextu %v{%v,%v}, %v" o l w d
  show (BFEXTS o l w d) = printf "bfexts %v{%v,%v}, %v" o l w d
  show (BFFFO o l w d) = printf "bfffo %v{%v,%v}, %v" o l w d
  show (BFINS d o l w) = printf "bfins %v, %v{%v,%v}" d o l w
  show (FOp s e dn) = printf "%s.x %v, %v" s (typeOfO e) e dn
  show (FMOVECR s t) = printf "fmovecr #%x, %v" s t
  show (FMOVEStore n o) = printf "fmove.%v %v, %v" (typeOfO o) n o
  show (FMOVEStoreP n o k) = printf "fmove.p %v, %v{%v}" n o k
  show (FMOVECC False s o) = printf "fmovecc %v, %s" o (intercalate "," s)
  show (FMOVECC True s o) = printf "fmovecc %s, %v" (intercalate "," s) o
  show (FMOVEM_STATIC toMem m regs) =
    let regStr =
          toRegStr
            (case m of
               (UnRefDec _) -> reverse regs
               _            -> regs)
     in if toMem
          then printf "fmovem.x %s, %v" regStr m
          else printf "fmovem.x %v, %s" m regStr
  show (FMOVEM_DYNAMIC False m di) = printf "fmovem.x %v, %v" m di
  show (FMOVEM_DYNAMIC True m di) = printf "fmovem.x %v, %v" di m
  show (FScc cc o) = printf "fs%v %v" cc o
  show (FTRAPcc cc 0) = printf "ftrap%v" cc
  show (FTRAPcc cc d) = printf "ftrap%v #%x" cc d
  show (FDBcc cc dn target) = printf "fdb%v %v _%05X" cc dn target
  show FNOP = "fnop"
  show (FBcc cc target) = printf "fb%v _%05X" cc target
  show (FSAVE o) = printf "fsave %v" o
  show (FRESTORE o) = printf "frestore %v" o
  show (CINVL s an) = printf "cinvl %s (%v)" s an
  show (CINVP s an) = printf "cinvp %s (%v)" s an
  show (CINVA s) = printf "cinva %s" s
  show (CPUSHL s an) = printf "cpushl %s (%v)" s an
  show (CPUSHP s an) = printf "cpushp %s (%v)" s an
  show (CPUSHA s) = printf "cpusha %s" s
  show (PFLUSHN an) = printf "pflushn (%v)" an
  show (PFLUSH an) = printf "pflushn (%v)" an
  show PFLUSHAN = "pflushan"
  show PFLUSHA = "pflusha"
  show (PTESTW an) = printf "ptestw (%v)" an
  show (PTESTR an) = printf "ptestr (%v)" an
  show (MOVE16 True t ay imm) =
    printf
      "move16 (%v)%s, (#%d)"
      ay
      (if t
         then "+"
         else "")
      imm
  show (MOVE16 False t ay imm) =
    printf
      "move16 (#%d), (%v)%s"
      imm
      ay
      (if t
         then "+"
         else "")
  show (MOVE16IncInc ax ay) = printf "move16 (%v)+, (%v)+" ax ay
  show _ = "illegal"
