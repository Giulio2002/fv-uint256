import Extracted
import Fv256.Spec.Sqrt
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.Sqrt

/-!
# amd64: the compiled `(*uint256.Int).Sqrt` implements `Fv256.Spec.IsSqrt`  (`Fv256/Spec/Sqrt.lean`)

Calling `z.Sqrt(x)` with `z, x` in `RAX, RBX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` a number `r` with
`Fv256.Spec.IsSqrt x r` (the integer square root), and writes only `z[0, 32)` and its own stack window. `z` and `x` may coincide
but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/Sqrt.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.Sqrt

/-- PRECONDITION (machine facts only): the stack-growth check falls through with room for the large frame (`StackGuardOK`, `0x280 ≤ RSP`); the window `[RSP-0x1f0, RSP+0x18)` is
writable; `z` is a writable and `x` a readable 32-byte buffer, both outside the window; `z` and `x` are equal or disjoint; the goroutine's
`stackguard0` word (at `R14 + 16`) is outside the window. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x200 ∧ 0x280 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x1f0 0x18 ∧ Buffer s z 32 true ∧
  Buffer s x 32 false ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ z.toNat) ∧
  (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ x.toNat) ∧
  (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ (s.regs regG).toNat + 16)

/-- POSTCONDITION: `RAX = z`; the number now at `z` is the integer square root (`Spec.IsSqrt`) of the number at `x` BEFORE the call; memory changed only in
`z[0, 32)` and the stack window `[RSP-0x1f0, RSP+0x18)`. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ Fv256.Spec.IsSqrt (valueAt s x 32) (valueAt s' z 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x1f0, (s.regs regSP).toNat + 0x18)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Sqrt(x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.Sqrt
