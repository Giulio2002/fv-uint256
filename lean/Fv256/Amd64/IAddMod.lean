import Extracted
import Fv256.Spec.IAddMod
import Fv256.Proofs.Amd64.IAddMod

/-!
# amd64: the compiled `(*uint256.Int).IAddMod` implements `Spec.iAddMod`  (`Fv256/Spec/IAddMod.lean`)

`z.IAddMod(x, m)` (`RAX, RBX, RCX`) returns normally (no fault, no panic) with `RAX` = z, leaves `Fv256.Spec.iAddMod z x
m` (that is `(z + x) mod m`, or `0` for `m = 0`, with `z` the receiver's value before the call) in `z`, and writes only
`z[0, 32)` and the callee's stack frame. The callee `AddMod` is used through its verified library summary.
The tactic proof is `Fv256/Proofs/Amd64/IAddMod.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IAddMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth checks of `IAddMod` and of the `AddMod` it calls fall through
(`StackGuardOK`), enough stack exists, and the window `[RSP-0x378, RSP+0x10)` is writable. Data: the binary's read-only
data is loaded. Buffers: `z` writable, `x`, `m` readable, 32 bytes each, none overlapping the window; `z` is
equal-or-disjoint from `x` and from `m`; the goroutine's `g` words at `R14` are outside the window and do not overlap `z`. -/
def Pre (z x m : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x330 ∧ 0x3b0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x378 0x10 ∧ Buffer s z 32 true ∧
  Buffer s x 32 false ∧ Buffer s m 32 false ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
  (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
  (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ m.toNat) ∧
  (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
  (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16) ∧
  ((s.regs regG).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs regG).toNat + 16) ∧
  Extracted.program.DataLoaded s.mem

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.iAddMod` of the numbers at `z`, `x`, `m` BEFORE the call; memory
changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.iAddMod (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x378, (s.regs regSP).toNat + 0x10)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m] (Pre z x m) (Post z x m) :=
  correctness_proof z x m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.IAddMod(x, m)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s ∧ Pre z x m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x m s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.IAddMod
