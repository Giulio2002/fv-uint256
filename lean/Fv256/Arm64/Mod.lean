import Extracted
import Fv256.Spec.Mod
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.Mod

/-!
# arm64: the compiled `(*uint256.Int).Mod` implements `Spec.mod`  (`Fv256/Spec/Mod.lean`)

`z.Mod(x, y)` (`X0, X1, X2`) returns normally (no fault, no panic, also for a zero divisor) with `X0 = z`, leaves `Spec.mod x y` (`x mod y`, or `0` when `y = 0`)
in `z`, and writes only `z[0, 32)` and its own stack frame. `z`, `x`, `y` may overlap arbitrarily.
The proof is `Fv256/Proofs/Arm64/Mod.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Mod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), a 488-byte frame plus the 16
bytes above `SP` are usable (`StackOK`), and the goroutine's `stackguard0` word (at `X28`) is outside the frame. Buffers: `z`
writable, `x`, `y` readable, 32 bytes each (they may alias each other freely), none overlapping the frame `[SP-488, SP+16)`. -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  GuardOK s 448 ∧ StackOK s 488 16 ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
  Janus.Spec.Disjoint z.toNat 32 (s.sp.toNat - 488) 504 ∧ Janus.Spec.Disjoint x.toNat 32 (s.sp.toNat - 488) 504 ∧
  Janus.Spec.Disjoint y.toNat 32 (s.sp.toNat - 488) 504

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.mod` of the numbers at `x` and `y` BEFORE the call; memory changed
only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  Janus.Spec.val256 s'.mem z.toNat = Fv256.Spec.mod (Janus.Spec.val256 s.mem x.toNat) (Janus.Spec.val256 s.mem y.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 488, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.Mod
