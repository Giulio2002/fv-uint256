import Extracted
import Fv256.Spec.MulOverflow
import Fv256.Spec.Util
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.MulOverflow

/-!
# amd64: the compiled `(*uint256.Int).MulOverflow` implements `Spec.mul` and `Spec.mulOverflows`  (`Fv256/Spec/MulOverflow.lean`)

`z.MulOverflow(x, y)` (`RAX, RBX, RCX`) returns normally (no fault, no panic) with `RAX = z`, leaves `Spec.mul x y` in `z`,
returns the overflow flag in `RBX` (low byte `1` exactly when `Spec.mulOverflows x y`, else `0`), and writes only `z[0, 32)` and
its own stack window. `z`, `x`, `y` are pairwise equal-or-disjoint. The proof is `Fv256/Proofs/Amd64/MulOverflow.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.MulOverflow

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`StackGuardOK`), the window
`[RSP-152, RSP+16)` is writable and `RSP` is 8-byte aligned. Buffers: `z` writable, `x`, `y` readable, 32 bytes each, none
overlapping the window, and pairwise equal-or-disjoint. -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 152 16 ∧ (s.regs regSP).toNat % 8 = 0 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Alias32 z x ∧ Alias32 z y ∧ Alias32 x y ∧
  Outside z 32 ((s.regs regSP).toNat - 152) ((s.regs regSP).toNat + 16) ∧
  Outside x 32 ((s.regs regSP).toNat - 152) ((s.regs regSP).toNat + 16) ∧
  Outside y 32 ((s.regs regSP).toNat - 152) ((s.regs regSP).toNat + 16)

/-- POSTCONDITION: `RAX = z`; the low byte of `RBX` is the overflow flag `Spec.mulOverflows` of the numbers at `x` and `y`
BEFORE the call (as `1`/`0`); the number at `z` is `Spec.mul` of them; memory changed only in `z[0, 32)` and the stack window
`[RSP-152, RSP+16)`. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  (s'.regs 3).toNat % 256 = (if Fv256.Spec.mulOverflows (valueAt s x 32) (valueAt s y 32) then 1 else 0) ∧
  valueAt s' z 32 = Fv256.Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 152) 168

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.MulOverflow(x, x)`) satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

/-- That concrete call returns `z` holding `0` with the flag byte `0` (the memory it reads is all zero). -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ s'.regs 0 = Wit.z ∧ (s'.regs 3).toNat % 256 = 0 ∧ valueAt s' Wit.z 32 = 0 :=
  Wit.returns

end Witness

end Fv256.Amd64.MulOverflow
