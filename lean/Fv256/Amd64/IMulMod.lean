import Extracted
import Fv256.Spec.IMulMod
import Fv256.Proofs.Amd64.IMulMod

/-!
# amd64: the compiled `(*uint256.Int).IMulMod` implements `Spec.iMulMod`  (`Fv256/Spec/IMulMod.lean`)

`z.IMulMod(x, m)` (`RAX, RBX, RCX`) returns normally (no fault, no panic) with `RAX` = z, leaves `Fv256.Spec.iMulMod z x
m` (that is `(z * x) mod m`, or `0` for `m = 0`, with `z` the receiver's value before the call) in `z`, and writes only
`z[0, 32)` and its own stack frame. `z`, `x`, `m` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Amd64/IMulMod.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IMulMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`StackGuardOK`), enough stack exists, and
the window `[RSP-0x3a8, RSP+0x8)` is writable. Buffers: `z` writable, `x`, `m` readable, 32 bytes each (they may alias
each other freely), none overlapping the window (`Apart`); the goroutine's `g` word at `R14+16` is outside the window. -/
def Pre (z x m : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x320 ∧ 0x3b0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x3a8 8 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s m 32 false ∧
  Apart z.toNat 32 (((s.regs regSP).toNat) - 0x3a8) 0x3b0 ∧
  Apart x.toNat 32 (((s.regs regSP).toNat) - 0x3a8) 0x3b0 ∧
  Apart m.toNat 32 (((s.regs regSP).toNat) - 0x3a8) 0x3b0 ∧
  Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x3a8) 0x3b0

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.iMulMod` of the numbers at `z`, `x`, `m` BEFORE the call; memory
changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.iMulMod (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x3a8, (s.regs regSP).toNat)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m] (Pre z x m) (Post z x m) :=
  correctness_proof z x m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.IMulMod(x, m)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s ∧ Pre z x m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x m s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.IMulMod
