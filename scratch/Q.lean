import Extracted
open Janus
def rd (a n : Nat) : Nat := (List.range n).foldr (fun i acc => acc * 256 + ((Janus.dataSegByte Extracted.program.data (a+i)).getD 0)) 0
#eval (List.range 6).map fun i => rd (0xcfc80 + 8*i) 8
#eval (List.range 6).map fun i => (Janus.dataSegByte Extracted.program.data (0xcfc80 + 8*i)).isSome
#eval (Extracted.program.data.map fun d => (d.base, d.bytes.length)).filter (fun p => p.1 ≤ 0xcfc80 ∧ 0xcfc80 < p.1+p.2)
#eval Extracted.dataAddr.«type:internal/strconv.Error#e7a6b33e»
