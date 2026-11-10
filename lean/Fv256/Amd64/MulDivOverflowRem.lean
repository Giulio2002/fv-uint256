import Extracted
import Fv256.Spec.MulDivOverflowRem
import Fv256.Proofs.Amd64.MulDivOverflowRem

/-!
# amd64: the compiled `(*uint256.Int).MulDivOverflowRem` implements `Spec.mulDivOverflowRemQuot`  (`Fv256/Spec/MulDivOverflowRem.lean`)

`z.MulDivOverflowRem(x, y, d, m)` (`RAX, RBX, RCX, RDI, RSI`) returns normally (no fault, no panic, also for `d = 0`) with
`RAX` = z and `RBX` = m, leaves `Fv256.Spec.mulDivOverflowRemQuot x y d` (the low 256 bits of the exact `x * y / d`) in
`z` and the remainder `Fv256.Spec.mulDivOverflowRem x y d` (`x * y mod d`) in `m`, the overflow flag (`RCX`) is
`Fv256.Spec.mulDivOverflowFlag x y d`, and only `z[0, 32)`, `m[0, 32)` and the callee's stack frame are written. `m` is a
non-nil output buffer that does not overlap `z`, `x`, `y`, `d`.
The tactic proof is `Fv256/Proofs/Amd64/MulDivOverflowRem.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulDivOverflowRem

/-- PRECONDITION (machine facts only). Stack: the stack-growth checks fall through (`StackGuardOK`), enough stack exists, and
the window `[RSP-0x218, RSP+0x30)` is writable. Buffers: `z` and the remainder output `m` writable, `x`, `y`, `d`
readable, 32 bytes each, none overlapping the window; `m` is non-nil and apart (`Apart`) from `z`, `x`, `y`, `d` and from
the `g` word at `R14+16`, which is itself outside the window. -/
def Pre (z x y d m : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x2a8 ∧ 0x300 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x218 0x30 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s d 32 false ∧ Buffer s m 32 true ∧
  Apart z.toNat 32 (((s.regs regSP).toNat) - 0x218) 0x248 ∧
  Apart x.toNat 32 (((s.regs regSP).toNat) - 0x218) 0x248 ∧
  Apart y.toNat 32 (((s.regs regSP).toNat) - 0x218) 0x248 ∧
  Apart d.toNat 32 (((s.regs regSP).toNat) - 0x218) 0x248 ∧
  Apart m.toNat 32 (((s.regs regSP).toNat) - 0x218) 0x248 ∧
  Apart z.toNat 32 m.toNat 32 ∧ Apart x.toNat 32 m.toNat 32 ∧
  Apart y.toNat 32 m.toNat 32 ∧ Apart d.toNat 32 m.toNat 32 ∧
  m.toNat ≠ 0 ∧ Apart m.toNat 32 ((s.regs regG).toNat + 16) 8 ∧
  Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x218) 0x248

/-- POSTCONDITION: `RAX = z`, `RBX = m`; the overflow flag in `RCX` is `Spec.mulDivOverflowFlag` (as 0 or 1); the number at
`z` is `Spec.mulDivOverflowRemQuot` and the number at `m` is `Spec.mulDivOverflowRem` of the numbers at `x`, `y`, `d`
BEFORE the call; memory changed only in `z[0, 32)`, `m[0, 32)` and the callee's stack frame. -/
def Post (z x y d m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ s'.regs 3 = m ∧ valueAt s' m 32 = Fv256.Spec.mulDivOverflowRem (valueAt s x 32) (valueAt s y 32) (valueAt s d 32) ∧
  (s'.regs 1).toNat % 256 = (if Fv256.Spec.mulDivOverflowFlag (valueAt s x 32) (valueAt s y 32) (valueAt s d 32) then 1 else 0) ∧
  valueAt s' z 32 = Fv256.Spec.mulDivOverflowRemQuot (valueAt s x 32) (valueAt s y 32) (valueAt s d 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32), ((s.regs regSP).toNat - 0x218, (s.regs regSP).toNat + 0x30)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y d m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, d, m] (Pre z x y d m) (Post z x y d m) :=
  correctness_proof z x y d m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.MulDivOverflowRem(x, x, x, m)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y d m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, d, m] s ∧ Pre z x y d m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y d m s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.MulDivOverflowRem
