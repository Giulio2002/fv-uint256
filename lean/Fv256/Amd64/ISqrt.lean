import Extracted
import Fv256.Spec.ISqrt
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.ISqrt

/-!
# amd64: the compiled `(*uint256.Int).ISqrt` implements `Fv256.Spec.IsSqrt`  (`Fv256/Spec/ISqrt.lean`)

Calling `z.ISqrt()` with `z` in `RAX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` a number `r` with
`Fv256.Spec.IsSqrt (old z) r`, and writes only `z[0, 32)` and its own stack window.
The tactic proof is `Fv256/Proofs/Amd64/ISqrt.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.ISqrt

/-- PRECONDITION (machine facts only): the stack-growth check falls through with room for the large frame (`StackGuardOK`, `0x2a0 ≤ RSP`); the window `[RSP-0x210, RSP+0x10)` is
writable; `z` is a writable 32-byte buffer outside the window; the goroutine's `stackguard0` word (at `R14 + 16`) is outside the window. -/
def Pre (z : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x220 ∧ 0x2a0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x210 0x10 ∧ Buffer s z 32 true ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x210 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x210 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)

/-- POSTCONDITION: `RAX = z`; the number now at `z` is the integer square root (`Spec.IsSqrt`) of the number at `z` BEFORE the call; memory changed only in
`z[0, 32)` and the stack window `[RSP-0x210, RSP+0x10)`. -/
def Post (z : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ Fv256.Spec.IsSqrt (valueAt s z 32) (valueAt s' z 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x210, (s.regs regSP).toNat + 0x10)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z] (Pre z) (Post z) :=
  correctness_proof z

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.ISqrt()`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧ Pre z s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.ISqrt
