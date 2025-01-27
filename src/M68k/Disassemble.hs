module M68k.Disassemble(showOp, getLabels) where
  
import                qualified Data.Set    as S
import                          Text.Printf
import M68k.Operand
import M68k.Opcode


getLabels :: [(Int, Op, Int)] -> [Int]
getLabels [] = []
getLabels ((_, op, _):ss) =
  (case op of
     LEA (Offset16 s (BasePC n)) _          -> [s + n]
     LEA (Offset8 s (BasePC n) _ _ _) _     -> [s + n]
     LEA (Indirect s (BasePC n) _ _ _) _    -> [s + n]
     LEA (PreIndex s (BasePC n) _ _ _ _) _  -> [s + n]
     LEA (PostIndex s (BasePC n) _ _ _ _) _ -> [s + n]
     DBcc _ _ x                             -> [x]
     Bcc _ x                                -> [x]
     BRA x                                  -> [x]
     JMP (Offset16 s (BasePC n))            -> [s + n]
     JMP (Offset8 s (BasePC n) _ _ _)       -> [s + n]
     JMP (Indirect s (BasePC n) _ _ _)      -> [s + n]
     JMP (PreIndex s (BasePC n) _ _ _ _)    -> [s + n]
     JMP (PostIndex s (BasePC n) _ _ _ _)   -> [s + n]
     FDBcc _ _ x                            -> [x]
     FBcc _ x                               -> [x]
     _                                      -> []) ++
  getLabels ss

showOp :: [(Int, Op, Int)] -> String
showOp ops =
  let labels = S.fromList $ getLabels ops
      
      showOp1 (pc, op, _) =
        (if S.member pc labels
           then printf "_%05X:\t" pc
           else "\t") ++ show op
      
   in unlines $ map showOp1 ops
  where
    
