import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MustFromBig

/-- the type descriptor and data pointer `MustFromBig` passes to `runtime.gopanic` for `panic("overflow")`, recomputed from the extracted words. -/
def panicType : Nat := Extracted.dataAddr.«type:string#f88732b8»

def panicData : Nat := Extracted.dataAddr.«.rodata#ee30ac37»

def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x30) (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 12)
    (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 13) 0

namespace Witness

open Janus.Contracts.IfaceModel

/-- pins the type of an existential variable of `nonvacuous` -/
def pinPanicRuntime (_k : PanicRuntime) : Prop := True

/-- pins the type of an existential variable of `nonvacuous` -/
def pinBitVec64 (_k : BitVec 64) : Prop := True

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/MustFromBig.lean

end Witness

end Fv256.Arm64.MustFromBig
