import Extracted
import Janus
open Janus
#eval (Extracted.program.data.map fun d => d.base).foldl min 1000000000
#eval (Extracted.program.data.map fun d => d.base).foldl max 0
#eval Janus.Contracts.Toy.BUMP
#eval Janus.Contracts.Toy.HEAP
#eval Janus.Contracts.Toy.HEND
#eval Janus.Contracts.Toy.WBUF
#eval Extracted.program.segments.map (fun s => s.base) |>.foldl max 0
