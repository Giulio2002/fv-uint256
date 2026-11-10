import Extracted
import Fv256.Spec.ISDiv
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.ISDiv

/-!
# amd64: the compiled `(*uint256.Int).ISDiv` implements `Spec.isdiv`  (`Fv256/Spec/ISDiv.lean`)

`z.ISDiv(d)` (`RAX, RBX`) returns normally (no fault, no panic, no divide-error trap, also for a zero divisor) with `RAX = z`,
leaves `Spec.isdiv z d` (the old `z` divided by `d`, both signed, truncating; `0` when `d = 0`) in `z`, and writes only `z[0, 32)` and its own stack window. `z` and `d` (named `x` below) may overlap arbitrarily.
The proof is `Fv256/Proofs/Amd64/ISDiv.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.ISDiv

/-- PRECONDITION (machine facts only). Stack: the stack-growth checks of `ISDiv` and its callees fall through, at least
`0x290` bytes of stack exist, and the window `[RSP-0x288, RSP+0x10)` (all frames plus the caller's spill slot) is writable.
Buffers: `z` writable, `x` readable, 32 bytes each (they may alias each other freely), none overlapping the window.
The goroutine's `stackguard0` word at `R14` is outside the window. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x238 ∧ 0x290 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x288 0x10 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧
  Outside z 32 ((s.regs regSP).toNat - 0x288) ((s.regs regSP).toNat + 0x10) ∧
  Outside x 32 ((s.regs regSP).toNat - 0x288) ((s.regs regSP).toNat + 0x10) ∧
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x288 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.isdiv` of the numbers read BEFORE the call; memory changed only in
`z[0, 32)` and the stack window. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.isdiv (valueAt s z 32) (valueAt s x 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x288, (s.regs regSP).toNat + 0x10)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and
`correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

/-- That concrete call returns `z` holding `0` (the memory it reads is all zero, so the divisor is `0`). -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ s'.regs 0 = Wit.z ∧ valueAt s' Wit.z 32 = 0 :=
  Wit.returns

end Witness

end Fv256.Amd64.ISDiv
