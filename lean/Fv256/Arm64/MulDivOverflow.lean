import Extracted
import Fv256.Spec.MulDivOverflow
import Fv256.Proofs.Arm64.MulDivOverflow

/-!
# arm64: the compiled `(*uint256.Int).MulDivOverflow` implements `Spec.mulDivOverflow`  (`Fv256/Spec/MulDivOverflow.lean`)

`z.MulDivOverflow(x, y, d)` (`X0, X1, X2, X3`) returns normally (no fault, no panic, also for `d = 0`) with `X0` = z and
`X1` holding the overflow flag, leaves `Fv256.Spec.mulDivOverflow x y d` (the low 256 bits of the exact `x * y / d`, `0`
for `d = 0`) in `z`, the flag is `Fv256.Spec.mulDivOverflowFlag x y d`, and only `z[0, 32)` and the callee's stack frame
are written. `z`, `x`, `y`, `d` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Arm64/MulDivOverflow.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulDivOverflow

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), `SP` is 16-byte aligned and
the frame `[SP-552, SP+40)` is accessible for writing. Buffers: `z` writable, `x`, `y`, `d` readable, 32 bytes each (they
may alias each other freely), none overlapping the frame; the goroutine's `g` words at `X28` are outside the frame. -/
def Pre (z x y d : BitVec 64) (s : State) : Prop :=
  GuardOK s 512 ∧ s.sp.toNat % 16 = 0 ∧ 552 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 552) 592 true = true ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 552 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem d false ∧
  Disjoint z.toNat 32 (s.sp.toNat - 552) 592 ∧ Disjoint x.toNat 32 (s.sp.toNat - 552) 592 ∧
  Disjoint y.toNat 32 (s.sp.toNat - 552) 592 ∧ Disjoint d.toNat 32 (s.sp.toNat - 552) 592

/-- POSTCONDITION: `X0 = z`; the overflow flag in `X1` is `Spec.mulDivOverflowFlag` (as 0 or 1); the number at `z` is
`Spec.mulDivOverflow` of the numbers at `x`, `y`, `d` BEFORE the call; memory changed only in `z[0, 32)` and the callee's
stack frame. -/
def Post (z x y d : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  (s'.regs 1).toNat = (if Fv256.Spec.mulDivOverflowFlag (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) then 1 else 0) ∧
  val256 s'.mem z.toNat = Fv256.Spec.mulDivOverflow (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 552, s.sp.toNat + 40)]

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

end Fv256.Arm64.MulDivOverflow
