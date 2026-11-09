import Extracted
import Fv256.Spec.AddMod
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.AddMod

/-!
# amd64: the compiled `(*uint256.Int).AddMod` implements `Spec.addMod`  (`Fv256/Spec/AddMod.lean`)

`z.AddMod(x, y, m)` (`RAX, RBX, RCX, RDI`) returns normally with `RAX = z`, leaves `Spec.addMod x y m` (that is
`(x + y) mod m`, or `0` for `m = 0`) in `z`, and writes only `z[0, 32)` and its own stack frame. `z` is equal to or disjoint
from each of `x`, `y`, `m`. The proof is `Fv256/Proofs/Amd64/AddMod.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.AddMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`StackGuardOK`), at least `0x380` bytes of
stack exist, and the callee frame `[RSP-0x348, RSP+0x28)` is writable. Data: the read-only data of the binary is loaded.
Buffers: `z` writable, `x`, `y`, `m` readable, each 32 bytes. None of the four overlaps the frame; `z` is equal-or-disjoint
from `x`, `y`, `m`; `z` does not overlap the goroutine's `g` fields read at `R14`. -/
def Pre (z x y m : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x300 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x348 0x28 ∧
  Extracted.program.DataLoaded s.mem ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
  Outside z 32 ((s.regs regSP).toNat - 0x348) ((s.regs regSP).toNat + 0x28) ∧
  Outside x 32 ((s.regs regSP).toNat - 0x348) ((s.regs regSP).toNat + 0x28) ∧
  Outside y 32 ((s.regs regSP).toNat - 0x348) ((s.regs regSP).toNat + 0x28) ∧
  Outside m 32 ((s.regs regSP).toNat - 0x348) ((s.regs regSP).toNat + 0x28) ∧
  Alias32 z m ∧ Alias32 z x ∧ Alias32 z y ∧
  -- the `g` words at R14 (`stackguard0`, ...) are outside the frame and do not overlap `z`
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ (s.regs regG).toNat + 16) ∧
  ((s.regs regG).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs regG).toNat + 16)

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.addMod` of the numbers at `x`, `y`, `m` BEFORE the call; memory
changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x y m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.addMod (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x348, (s.regs regSP).toNat + 0x28)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m] (Pre z x y m) (Post z x y m) :=
  correctness_proof z x y m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.AddMod(x, x, x)`) satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s ∧ Pre z x y m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y m s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.AddMod
