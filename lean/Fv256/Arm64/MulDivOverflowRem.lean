import Extracted
import Fv256.Spec.MulDivOverflowRem
import Fv256.Proofs.Arm64.MulDivOverflowRem

/-!
# arm64: the compiled `(*uint256.Int).MulDivOverflowRem` implements `Spec.mulDivOverflowRemQuot`  (`Fv256/Spec/MulDivOverflowRem.lean`)

`z.MulDivOverflowRem(x, y, d, m)` (`X0, X1, X2, X3, X4`) returns normally (no fault, no panic, also for `d = 0`) with `X0`
= z and `X1` = m, leaves `Fv256.Spec.mulDivOverflowRemQuot x y d` (the low 256 bits of the exact `x * y / d`) in `z` and
the remainder `Fv256.Spec.mulDivOverflowRem x y d` (`x * y mod d`) in `m`, the overflow flag (`X2`) is
`Fv256.Spec.mulDivOverflowFlag x y d`, and only `z[0, 32)`, `m[0, 32)` and the callee's stack frame are written. `m` is a
non-nil output buffer that does not overlap `z`, `x`, `y`, `d`.
The tactic proof is `Fv256/Proofs/Arm64/MulDivOverflowRem.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulDivOverflowRem

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), `SP` is 16-byte aligned and
the 600 bytes from `SP-552` are accessible for writing. Buffers: `z` and the remainder output `m` writable, `x`, `y`, `d`
readable, 32 bytes each, none overlapping the frame (`Apart`); `m` is non-nil and apart from `z`, `x`, `y`, `d` and from
the `g` word at `X28+16`, which is itself outside the frame. -/
def Pre (z x y d m : BitVec 64) (s : State) : Prop :=
  GuardOK s 512 ∧ s.sp.toNat % 16 = 0 ∧ 552 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 552) (552 + 48) true = true ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 552) 600 ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem d false ∧ Ptr32 s.mem m true ∧
  Apart z.toNat 32 (s.sp.toNat - 552) 600 ∧ Apart x.toNat 32 (s.sp.toNat - 552) 600 ∧
  Apart y.toNat 32 (s.sp.toNat - 552) 600 ∧ Apart d.toNat 32 (s.sp.toNat - 552) 600 ∧
  Apart m.toNat 32 (s.sp.toNat - 552) 600 ∧
  Apart z.toNat 32 m.toNat 32 ∧ Apart x.toNat 32 m.toNat 32 ∧ Apart y.toNat 32 m.toNat 32 ∧
  Apart d.toNat 32 m.toNat 32 ∧ Apart m.toNat 32 ((s.regs 28).toNat + 16) 8 ∧ m.toNat ≠ 0

/-- POSTCONDITION: `X0 = z`, `X1 = m`; the overflow flag in `X2` is `Spec.mulDivOverflowFlag` (as 0 or 1); the number at `z`
is `Spec.mulDivOverflowRemQuot` and the number at `m` is `Spec.mulDivOverflowRem` of the numbers at `x`, `y`, `d` BEFORE
the call; memory changed only in `z[0, 32)`, `m[0, 32)` and the callee's stack frame. -/
def Post (z x y d m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ s'.regs 1 = m ∧
  (s'.regs 2).toNat = (if Fv256.Spec.mulDivOverflowFlag (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat)
    then 1 else 0) ∧
  val256 s'.mem z.toNat = Fv256.Spec.mulDivOverflowRemQuot (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) ∧
  val256 s'.mem m.toNat = Fv256.Spec.mulDivOverflowRem (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32), (s.sp.toNat - 552, s.sp.toNat - 8),
    (s.sp.toNat + 8, s.sp.toNat + 48)]

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

end Fv256.Arm64.MulDivOverflowRem
