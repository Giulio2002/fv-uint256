import Extracted
import Fv256.Spec.Xor
import Fv256.Proofs.Arm64.Xor

/-!
# arm64: the compiled `(*uint256.Int).Xor` implements `Fv256.Spec.xor`  (`Fv256/Spec/Xor.lean`)

Calling `z.Xor(x, y)` with `z` in `X0`, `x` in `X1`, `y` in `X2` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` the number
`Fv256.Spec.xor x y`, and changes no byte outside `z[0, 32)`. `z`, `x`, `y` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Arm64/Xor.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Xor

/-- PRECONDITION (machine facts only): 32-byte buffers (`Ptr32`): `z` writable, `x`, `y` readable; `z`, `x`, `y` are
pairwise equal-or-disjoint (`Aliasing`, from Janus). -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Aliasing z x ∧ Aliasing z y ∧ Aliasing x y

/-- POSTCONDITION: `X0 = z`; the number now at `z` is `Fv256.Spec.xor x y` (numbers read BEFORE the call); only `z[0, 32)`
was written. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ val256 s'.mem z.toNat = Fv256.Spec.xor (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
  OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (the witness call `z.Xor(x, y)`) satisfies `Pre` and its call returns with `Post`, so
`Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.Xor
