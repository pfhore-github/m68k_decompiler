module M68k.Disassemble where

import  M68k.Parse
import  qualified Data.Set as S
import Text.Printf
import Data.List



cc2Str :: (Eq a, Num a) => a -> String
cc2Str 0 = "T"
cc2Str 1 = "F"
cc2Str 2 = "HI"
cc2Str 3 = "LS"
cc2Str 4 = "CC"
cc2Str 5 = "CS"
cc2Str 6 = "NE"
cc2Str 7 = "EQ"
cc2Str 8 = "VC"
cc2Str 9 = "VS"
cc2Str 10 = "PL"
cc2Str 11 = "MI"
cc2Str 12 = "GE"
cc2Str 13 = "LT"
cc2Str 14 = "GT"
cc2Str 15 = "LE"
cc2Str _ = ""

fcc2Str :: (Eq a, Num a) => a -> String
fcc2Str 0 = "F"
fcc2Str 1 = "EQ"
fcc2Str 2 = "OGT"
fcc2Str 3 = "OGE"
fcc2Str 4 = "OLT"
fcc2Str 5 = "OLE"
fcc2Str 6 = "OGL"
fcc2Str 7 = "OR"
fcc2Str 8 = "UN"
fcc2Str 9 = "UEQ"
fcc2Str 10 = "UGT"
fcc2Str 11 = "UGE"
fcc2Str 12 = "ULT"
fcc2Str 13 = "ULE"
fcc2Str 14 = "NE"
fcc2Str 15 = "T"
fcc2Str 16 = "SF"
fcc2Str 17 = "SEQ"
fcc2Str 18 = "GT"
fcc2Str 19 = "GE"
fcc2Str 20 = "LT"
fcc2Str 21 = "LE"
fcc2Str 22 = "GL"
fcc2Str 23 = "GLE"
fcc2Str 24 = "NGLE"
fcc2Str 25 = "NGL"
fcc2Str 26 = "NLE"
fcc2Str 27 = "NLT"
fcc2Str 28 = "NGE"
fcc2Str 29 = "NGT"
fcc2Str 30 = "SNE"
fcc2Str 31 = "ST"
fcc2Str _ = ""

toRegList :: (Eq a, Num a) => (a, a) -> [a] -> [(a, a)]
toRegList c [] = [c]
toRegList (n1, n2) (s:os) =
  if abs (n2-s) == 1 then
    toRegList (n1, s) os
  else
    (n1, n2):toRegList (s, s) os

toRegStr :: (Int -> String) -> [Int] -> String
toRegStr _ [] = ""
toRegStr s [reg] = s reg
toRegStr s (r1:regs) = intercalate "/" ((\(f, e) ->
                             if f == e then
                               s f
                             else
                               s f ++ "-" ++ s e
                          ) <$> toRegList (r1,r1) regs)

showOp :: [(Int, Op)] -> String
showOp ops =
  let labels = S.fromList $ getLabels ops
      showOp1 (pc, op) =
        (if S.member pc labels then printf "%05X:\t" pc else "\t") ++
        case op of
          ORI t o v -> printf "ORI.%v #%X, %v" t v o
          ANDI t o v -> printf "ANDI.%v #%X, %v" t v o
          SUBI t o v -> printf "SUBI.%v #%d, %v" t v o
          ADDI t o v -> printf "ADDI.%v #%d, %v" t v o
          EORI t o v -> printf "EORI.%v #%X, %v" t v o
          CMPI t o v -> printf "CMPI.%v #%X, %v" t v o
          BTST t o n -> printf "BTST.%v %v, %v" t n o
          BCHG t o n -> printf "BCHG.%v %v, %v" t n o
          BCLR t o n -> printf "BCLR.%v %v, %v" t n o
          BSET t o n -> printf "BSET.%v %v, %v" t n o
          CMP2 t o i -> printf "CMP2.%v %v, %s" t o $ rn2Str i
          CHK2 t o i -> printf "CHK2.%v %v, %s" t o $ rn2Str i
          CAS t c u o -> printf "CAS.%v %%D%d, %%D%d, %v" t c u o
          CAS2 t c1 c2 u1 u2 m1 m2 ->
            printf "CAS2.%v %%D%d:%%D%d, %%D%d:%%D%d (%%R%d):(%%R%d)"
              t c1 c2 u1 u2 m1 m2
          MOVES t True o rn -> printf "MOVES.%v %s, %v" t (rn2Str rn) o
          MOVES t False o rn -> printf "MOVES.%v %v, %s" t o (rn2Str rn)
          MOVEP t True an imm dn -> printf "MOVEP.%v %%D%d, (%d, %%A%d)"
            t dn imm an
          MOVEP t False an imm dn -> printf "MOVEP.%v (%d, %%A%d), %%D%d"
            t imm an dn
          MOVE t src dst -> printf "MOVE.%v %v, %v" t src dst
          MOVEA t src an -> printf "MOVE.%v %v, %%A%d" t src an
          NEGX t o -> printf "NEGX.%v %v" t o
          CLR t o -> printf "CLR.%v %v" t o
          NEG t o -> printf "NEG.%v %v" t o
          NOT t o -> printf "NOT.%v %v" t o
          TST t o -> printf "TST.%v %v" t o
          NBCD t o -> printf "NBCD.%v %v" t o
          TAS _ o -> printf "TAS.B %v" o
          MULUL o dn -> printf "MULU.L %v, %%D%d" o dn
          MULSL o dn -> printf "MULS.L %v, %%D%d" o dn
          MULULL o dh dl -> printf "MULU.L %v, %%D%d-%%D%d" o dh dl
          MULSLL o dh dl -> printf "MULS.L %v, %%D%d-%%D%d" o dh dl
          DIVUL o dr dq -> if dr == dq then
                             printf "DIVU.L %v, %%D%d" o dq
                           else
                             printf "DIVU.L %v, %%D%d:%%D%d" o dr dq
          DIVSL o dr dq -> if dr == dq then
                             printf "DIVS.L %v, %%D%d" o dq
                           else
                             printf "DIVS.L %v, %%D%d:%%D%d" o dr dq
          DIVULL o dh dl -> printf "DIVU.L %v, %%D%d:%%D%d" o dh dl
          DIVSLL o dh dl -> printf "DIVS.L %v, %%D%d:%%D%d" o dh dl
          SWAP n -> printf "SWAP %%D%d" n
          TRAPn n -> printf "TRAP #%d" n
          LINK an disp -> printf "LINK %%A%d, #%d" an disp
          UNLK an -> printf "UNLK %%A%d" an
          RESET -> "RESET"
          NOP -> "NOP"
          STOP n -> printf "STOP #%04x" n
          RTE -> "RTE"
          RTD n -> printf "RTD #%d" n
          RTS -> "RTS"
          TRAPV -> "TRAPV"
          RTR -> "RTR"
          BKPT n -> printf "BKPT #%d" n
          PEA o -> printf "PEA %v" o
          EXT t v -> printf "EXT.%v %%D%d" t v
          EXTB v -> printf "EXTB.L %%D%d" v
          MOVEM t toMem o rs ->
            let regStr = toRegStr rn2Str (
                  case o of
                    UnRefDec _ -> reverse rs
                    _ -> rs
                  )
            in if toMem
               then printf "MOVEM.%v %s, %v" t regStr o
               else printf "MOVEM.%v %v, %s" t o regStr
          JSR o -> printf "JSR %v" o
          JMP o -> printf "JMP %v" o
          CHK t o v -> printf "CHK.%v %v, %s" t o $ rn2Str v
          LEA o v -> printf "LEA %v, %%A%d" o v
          MOVEC True x s -> printf "MOVEC %v, %%%s" (rn2Str x) s
          MOVEC False x s -> printf "MOVEC %%%s, v" s (rn2Str x)
          ADDQ t i o -> printf "ADDQ.%v #%d, %v" t i o
          SUBQ t i o -> printf "SUBQ.%v #%d, %v" t i o
          TRAPcc cc Nothing -> printf "TRAP%s" (cc2Str cc)
          TRAPcc cc (Just i) -> printf "TRAP%s #%d" (cc2Str cc) i
          Scc cc o -> printf "S%s %v" cc o
          DBcc cc dn target -> printf "DB%s %%D%d, %05X" (cc2Str cc) dn target
          BRA target -> printf "BRA %05X" target
          BSR target -> printf "BSR %05X" target
          Bcc cc target -> printf "B%s %05X" (cc2Str cc) target
          MOVEQ i dn -> printf "MOVEQ #%d, %%D%d" i dn
          OR t src dst -> printf "OR.%v %v, %%D%d" t src dst
          OR_TO_MEM t src dst -> printf "OR.%v %%D%d, %v" t src dst
          DIVUW o dn -> printf "DIVU.W %v, %%D%d" o dn
          SBCD_REG x y -> printf "SBCD %%D%d, %%D%d" x y
          SBCD_MEM x y -> printf "SBCD -(%%A%d), -(%%A%d)" x y
          PACK_REG x y adj -> printf "PACK %%D%d, %%D%d, #%d" x y adj
          PACK_MEM x y adj -> printf "PACK -(%%A%d), -(%%A%d), #%d" x y adj
          UNPK_REG x y adj -> printf "UNPK %%D%d, %%D%d, #%d" x y adj
          UNPK_MEM x y adj -> printf "UNPK -(%%A%d), -(%%A%d), #%d" x y adj
          DIVSW o dn -> printf "DIVU.W %v, %%D%d" o dn
          SUB t src dst -> printf "SUB.%v %v, %%D%d" t src dst
          SUB_TO_MEM t src dst -> printf "SUB.%v %%D%d, %v" t src dst
          SUBA t src dst -> printf "SUBA.%v %v, %%A%d" t src dst
          SUBX_REG t x y -> printf "SUBX.%v %%D%d, %%D%d" t x y
          SUBX_MEM t x y -> printf "SUBX.%v -(%%A%d), -(%%A%d)" t x y
          CMP t src dst -> printf "CMP.%v %v, %%D%d" t src dst
          CMPA t src dst -> printf "CMPA.%v %v, %%A%d" t src dst
          CMPM t src dst -> printf "CMP.%v (%%A%d)+, (%%A%d)+" t src dst
          EOR t src dst -> printf "EOR.%v %%D%d, %v" t src dst
          AND t src dst -> printf "AND.%v %v, %%D%d" t src dst
          AND_TO_MEM t src dst -> printf "AND.%v %%D%d, %v" t src dst
          MULUW o dn -> printf "MULU.W %v, %%D%d" o dn
          ABCD_REG x y -> printf "ABCD %%D%d, %%D%d" x y
          ABCD_MEM x y -> printf "ABCD -(%%A%d), -(%%A%d)" x y
          EXG_D x y -> printf "EXG %%D%d, %%D%d" x y
          EXG_A x y -> printf "EXG %%A%d, %%A%d" x y
          EXG_DA x y -> printf "EXG %%D%d, %%A%d" x y
          MULSW o dn -> printf "MULS.W %v, %%D%d" o dn
          SYS x -> printf "SYSCALL #%X" x
          ADD t src dst -> printf "ADD.%v %v, %%D%d" t src dst
          ADD_TO_MEM t src dst -> printf "ADD.%v %%D%d, %v" t src dst
          ADDA t src dst -> printf "ADDA.%v %v, %%A%d" t src dst
          ADDX_REG t x y -> printf "ADDX.%v %%D%d, %%D%d" t x y
          ADDX_MEM t x y -> printf "ADDX.%v -(%%A%d), -(%%A%d)" t x y
          ASR t n x y -> shiftOp "ASR" t n x y
          ASL t n x y -> shiftOp "ASL" t n x y
          LSR t n x y -> shiftOp "LSR" t n x y
          LSL t n x y -> shiftOp "LSL" t n x y
          ROXR t n x y -> shiftOp "ROXR" t n x y
          ROXL t n x y -> shiftOp "ROXL" t n x y
          ROR t n x y -> shiftOp "ROR" t n x y
          ROL t n x y -> shiftOp "ROL" t n x y
          ASR_EA o -> printf "ASR.W %v" o
          ASL_EA o -> printf "ASL.W %v" o
          LSR_EA o -> printf "LSR.W %v" o
          LSL_EA o -> printf "LSL.W %v" o
          ROXR_EA o -> printf "ROXR.W %v" o
          ROXL_EA o -> printf "ROXL.W %v" o
          ROR_EA o -> printf "ROR.W %v" o
          ROL_EA o -> printf "ROL.W %v" o
          BFTST o l w -> printf "BFTST %v{%v,%v}" o l w
          BFCHG o l w -> printf "BFCHG %v{%v,%v}" o l w
          BFCLR o l w -> printf "BFCLR %v{%v,%v}" o l w
          BFSET o l w -> printf "BFSET %v{%v,%v}" o l w
          BFEXTU o l w d -> printf "BFEXTU %v{%v,%v}, %%D%d" o l w d
          BFEXTS o l w d -> printf "BFEXTU %v{%v,%v}, %%D%d" o l w d
          BFFFO o l w d -> printf "BFEXTU %v{%v,%v}, %%D%d" o l w d
          BFINS d o l w -> printf "BFEXTU %%D%d, %v{%v,%v}" d o l w
          FOp s at e dn -> printf "%s.%v %v, %%FP%v" s at e dn
          FMOVECR s t -> printf "FMOVECR #%x, %%FP%v" s t
          FMOVEStore at n o -> printf "FMOVE.%v %%FP%v, %v" at n o
          FMOVEP n o False k -> printf "FMOVE.P %%FP%v, %v{#%d}" n o k
          FMOVEP n o True k -> printf "FMOVE.P %%FP%v, %v{%%D%d}" n o k
          FMOVECC False s o -> printf "FMOVECC %v, %s" o
            (intercalate "," s)
          FMOVECC True s o -> printf "FMOVECC %s, %v" (intercalate "," s)
            o
          FMOVEMS toMem m regs ->
            let regStr = toRegStr (printf "%%FP%d") (
                  case m of
                    UnRefDec _ -> reverse regs
                    _ -> regs
                  )
            in if toMem
               then printf "FMOVEM %s, %v" regStr m
               else printf "FMOVEM %v, %s" m regStr
          FMOVEMD False m di -> printf "FMOVEM %v, %%D%d" m di
          FMOVEMD True m di -> printf "FMOVEM %%D%d, %v" di m
          FScc cc o -> printf "FS%s %v" (fcc2Str cc) o
          FTRAPcc cc 0 -> printf "FTRAP%s" (fcc2Str cc)
          FTRAPcc cc d -> printf "FTRAP%s #%x" (fcc2Str cc) d
          FDBcc cc dn target -> printf "FDB%s %%D%d %05X" (fcc2Str cc) dn target
          FNOP -> "FNOP"
          FBcc cc target -> printf "FB%s %05X" (fcc2Str cc) target
          FSAVE o -> printf "FSAVE %v" o
          FRESTORE o -> printf "FRESTORE %v" o
          CINVL s an -> printf "CINVL %s (%%A%d)" s an
          CINVP s an -> printf "CINVP %s (%%A%d)" s an
          CINVA s -> printf "CINVA %s" s
          CPUSHL s an -> printf "CPUSHL %s (%%A%d)" s an
          CPUSHP s an -> printf "CPUSHP %s (%%A%d)" s an
          CPUSHA s -> printf "CPUSHA %s" s
          PFLUSHN an -> printf "PFLUSHN (%%A%d)" an
          PFLUSH an -> printf "PFLUSH (%%A%d)" an
          PFLUSHAN -> "PFLUSHAN"
          PFLUSHA -> "PFLUSHA"
          PTESTW an -> printf "PTESTW (%%A%d)" an
          PTESTR an -> printf "PTESTR (%%A%d)" an
          MOVE16 True t ay imm -> printf "MOVE16 (%%A%d)%s, (#%d)" ay (if t then "+" else "") imm
          MOVE16 False t ay imm -> printf "MOVE16 (#%d), (%%A%d)%s" imm ay (if t then "+" else "")
          MOVE16IncInc ax ay -> printf "MOVE16 (%%A%d)+, (%%A%d)+" ax ay
          _ -> "ILLEGAL"
  in unlines $ map showOp1 ops
  where shiftOp s t n x = printf "%s.%v %s, %%D%d" s t
          (if n then printf "%%D%d" x :: String
            else printf "#%d" (if x == 0
                                 then 8
                                 else x) :: String
          )

