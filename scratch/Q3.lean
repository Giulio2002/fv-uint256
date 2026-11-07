import Extracted
import Fv256.Amd64.AFdWitA
open Janus Fv256.Amd64.FdWit
def rd (a n : Nat) : Nat := (List.range n).foldr (fun i acc => acc * 256 + ((Janus.dataSegByte Extracted.program.data (a+i)).getD 0)) 0
#eval TW
#eval rd (0x4f19e0+8) 8
#eval (List.range 8).map fun i => Janus.dataSegByte Extracted.program.data (0x4f19e8+i)
