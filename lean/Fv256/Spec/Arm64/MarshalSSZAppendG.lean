import Extracted
import Fv256.Spec.MsaCommon

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Msa

namespace Fv256.Arm64.MarshalSSZAppendG

/-- the element type of the byte slice, an argument of every `growslice` call -/
abbrev u8T : Nat := Extracted.dataAddr.«type:uint8#6a8c7679»

/-- the `runtime.growslice` contract address -/
abbrev ga : Nat := Extracted.program.contractAddr "runtime.growslice"

/-- The postcondition of `MarshalSSZAppend` (arm64): the result slice is `(x0, len0 + 32, x2)`, nil error, the new bytes are the
little-endian encoding of `*z`, the old prefix is kept, and the memory/runtime facts of the no-growth / growth cases. -/
def AppendPost (R : RtInv) (s s' : State) (z : BitVec 64) (dp len0 cap0 b0 : Nat) (L0 : List (Nat × Nat)) : Prop :=
  (s'.regs 1).toNat = len0 + 32 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧ len0 + 32 ≤ (s'.regs 2).toNat ∧
  s'.mem.readLE ((s'.regs 0).toNat + len0) 32 = val256 s.mem z.toNat ∧
  (∀ i, i < len0 → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (dp + i)) ∧
  (len0 + 32 ≤ cap0 → (s'.regs 0).toNat = dp ∧ (s'.regs 2).toNat = cap0 ∧
    R.inv b0 L0 (s.regs 28).toNat (view R.rt L0 s'.mem) ∧
    MemFrame s.mem s'.mem [(dp + len0, dp + len0 + 32), (s.sp.toNat - 4232, s.sp.toNat + 40)]) ∧
  (cap0 < len0 + 32 → InRanges (s'.regs 0).toNat (s'.regs 2).toNat R.rt ∧
    (∃ b' L', R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ InRanges (s'.regs 0).toNat (s'.regs 2).toNat L') ∧
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40), (dp, dp + cap0)]))

end Fv256.Arm64.MarshalSSZAppendG
