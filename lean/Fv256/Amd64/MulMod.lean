import Extracted
import Fv256.Spec.MulMod
import Fv256.Proofs.Amd64.MulMod

/-!
# amd64: the compiled `(*uint256.Int).MulMod` implements `Spec.mulMod`  (`Fv256/Spec/MulMod.lean`)

`z.MulMod(x, y, m)` (`RAX, RBX, RCX, RDI`) returns normally (no fault, no panic) with `RAX` = z, leaves `Fv256.Spec.mulMod
x y m` (that is `(x * y) mod m`, or `0` for `m = 0`) in `z`, and writes only `z[0, 32)` and its own stack frame. `z`, `x`,
`y`, `m` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Amd64/MulMod.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`StackGuardOK`), enough stack exists, and
the window `[RSP-0x378, RSP+0x28)` is writable. Buffers: `z` writable, `x`, `y`, `m` readable, 32 bytes each (they may
alias each other freely), none overlapping the window (`Apart`); the goroutine's `g` word at `R14+16` (`stackguard0`) is
outside the window. -/
def Pre (z x y m : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x2f0 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x378 0x28 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
  Apart z.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
  Apart x.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
  Apart y.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
  Apart m.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
  Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x378) 0x3a0

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.mulMod` of the numbers at `x`, `y`, `m` BEFORE the call; memory
changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x y m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.mulMod (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x378, (s.regs regSP).toNat),
    ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 0x28)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m] (Pre z x y m) (Post z x y m) :=
  correctness_proof z x y m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.MulMod(x, y, m)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s ∧ Pre z x y m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y m s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.MulMod
