import Extracted
import Fv256.Spec.MulDivOverflow
import Fv256.Proofs.Amd64.MulDivOverflow

/-!
# amd64: the compiled `(*uint256.Int).MulDivOverflow` implements `Spec.mulDivOverflow`  (`Fv256/Spec/MulDivOverflow.lean`)

`z.MulDivOverflow(x, y, d)` (`RAX, RBX, RCX, RDI`) returns normally (no fault, no panic, also for `d = 0`) with `RAX` = z
and `RBX` holding the overflow flag, leaves `Fv256.Spec.mulDivOverflow x y d` (the low 256 bits of the exact `x * y / d`,
`0` for `d = 0`) in `z`, the flag is `Fv256.Spec.mulDivOverflowFlag x y d`, and only `z[0, 32)` and the callee's stack
frame are written. `z`, `x`, `y`, `d` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Amd64/MulDivOverflow.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulDivOverflow

/-- PRECONDITION (machine facts only). Stack: the stack-growth checks of `MulDivOverflow` and of the routines it calls fall
through (`StackGuardOK`), enough stack exists, and the window `[RSP-0x218, RSP+0x28)` is writable. Buffers: `z` writable,
`x`, `y`, `d` readable, 32 bytes each (they may alias each other freely), none overlapping the window; the goroutine's `g`
word at `R14+16` is outside the window. -/
def Pre (z x y d : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x2a8 ∧ 0x300 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x218 0x28 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s d 32 false ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ z.toNat) ∧
  (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ x.toNat) ∧
  (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ y.toNat) ∧
  (d.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ d.toNat) ∧
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ (s.regs regG).toNat + 16)

/-- POSTCONDITION: `RAX = z`; the overflow flag in `RBX` is `Spec.mulDivOverflowFlag` (as 0 or 1); the number at `z` is
`Spec.mulDivOverflow` of the numbers at `x`, `y`, `d` BEFORE the call; memory changed only in `z[0, 32)` and the callee's
stack frame. -/
def Post (z x y d : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  (s'.regs 3).toNat % 256 = (if Fv256.Spec.mulDivOverflowFlag (valueAt s x 32) (valueAt s y 32) (valueAt s d 32) then 1 else 0) ∧
  valueAt s' z 32 = Fv256.Spec.mulDivOverflow (valueAt s x 32) (valueAt s y 32) (valueAt s d 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x218, (s.regs regSP).toNat + 0x28)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, d] (Pre z x y d) (Post z x y d) :=
  correctness_proof z x y d

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.MulDivOverflow(x, x, x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, d] s ∧ Pre z x y d s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y d s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.MulDivOverflow
