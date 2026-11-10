import Extracted
import Fv256.Spec.MulMod
import Fv256.Proofs.Arm64.MulMod

/-!
# arm64: the compiled `(*uint256.Int).MulMod` implements `Spec.mulMod`  (`Fv256/Spec/MulMod.lean`)

`z.MulMod(x, y, m)` (`X0, X1, X2, X3`) returns normally (no fault, no panic) with `X0` = z, leaves `Fv256.Spec.mulMod x y
m` (that is `(x * y) mod m`, or `0` for `m = 0`) in `z`, and writes only `z[0, 32)` and its own stack frame. `z`, `x`,
`y`, `m` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Arm64/MulMod.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), `SP` is 16-byte aligned and
the 848 bytes from `SP-808` are accessible for writing. Buffers: `z` writable, `x`, `y`, `m` readable, 32 bytes each (they
may alias each other freely), none overlapping the frame (`Apart`); the goroutine's `g` word at `X28+16` is outside it. -/
def Pre (z x y m : BitVec 64) (s : State) : Prop :=
  GuardOK s 768 ∧ s.sp.toNat % 16 = 0 ∧ 808 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 808) (808 + 40) true = true ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 808) 848 ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m false ∧
  Apart z.toNat 32 (s.sp.toNat - 808) 848 ∧ Apart x.toNat 32 (s.sp.toNat - 808) 848 ∧
  Apart y.toNat 32 (s.sp.toNat - 808) 848 ∧ Apart m.toNat 32 (s.sp.toNat - 808) 848

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.mulMod` of the numbers at `x`, `y`, `m` BEFORE the call; memory
changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x y m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.mulMod (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem m.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 808, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 40)]

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

end Fv256.Arm64.MulMod
