import Extracted
import Fv256.Spec.Amd64.FM.IntoBigDefs
import Fv256.Spec.FormatFastDefs
import Fv256.Spec.IntoBigCommon

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall

namespace Fv256.Amd64.FormatBig

open Fv256.Amd64.IntoBig

/-- `BigR2`'s facts at the ENTRY state `s` of `Format` (before the prologue: `RSP = S0.RSP + 72`), the part of `PreF` that serves the big path -/
def PreBigE (R2 : RtInv) (b0 : Nat) (z : BitVec 64) (s : State) : Prop :=
  s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4136 < (s.regs 4).toNat - 72 ∧
  Outside ((s.regs 14).toNat + 16) 8 R2.rt ∧
  s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R2.rt ∧ Outside arrType 16 R2.rt ∧
  Outside z.toNat 32 R2.rt ∧
  R2.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
  R2.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
  R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  blockSize 32 false + blockSize 32 true ≤ b0

end Fv256.Amd64.FormatBig
