import Extracted
import Fv256.Amd64.UnmarshalTextS0
import Fv256.Amd64.UnmarshalSpec
open Janus Fv256.Amd64.UnmarshalTextS
def cv := cfg
#eval (cv.1, cv.2.1, cv.2.2.1, cv.2.2.2.1, cv.2.2.2.2.1, cv.2.2.2.2.2.1, cv.2.2.2.2.2.2.1, cv.2.2.2.2.2.2.2.1,cv.2.2.2.2.2.2.2.2.1, cv.2.2.2.2.2.2.2.2.2.1, cv.2.2.2.2.2.2.2.2.2.2.1)
#eval (sbAddr, stAddr, utEntry)
#eval (Extracted.program.data.map fun d => d.base).foldl min 1000000000
#eval (Extracted.program.data.map fun d => d.base+d.bytes.length).foldl max 0
#eval Extracted.program.contractAddr "runtime.cmpstring"
#eval (Extracted.program.contractAddr "runtime.ifaceeq")
