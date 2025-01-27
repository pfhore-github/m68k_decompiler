module M68k.Common where
import Text.Printf

data AType
  = BYTE
  | WORD
  | LONG
  deriving (Enum, Eq)

instance Show AType where
  show BYTE = "b"
  show WORD = "w"
  show LONG = "l"
instance PrintfArg AType where
  formatArg = formatArg . show 
data AFType
  = FInt AType
  | FSINGLE
  | FDOUBLE
  | FEXT
  | FPACKED
  deriving (Eq)

instance Show AFType where
    show (FInt t) = show t
    show FSINGLE = "s"
    show FDOUBLE = "d"
    show FEXT = "x"
    show FPACKED = "p"

instance PrintfArg AFType where
  formatArg = formatArg . show 