import Extracted
import Fv256.Spec.Not
import Fv256.Proofs.Arm64.Not

/-!
# arm64: the compiled `(*uint256.Int).Not` implements `Fv256.Spec.not`  (`Fv256/Spec/Not.lean`)

Calling `z.Not(x)` with `z` in `X0`, `x` in `X1` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` the number
`Fv256.Spec.not x`, and changes no byte outside `z[0, 32)`. `z` and `x` may be the same object but may not partially overlap.
The tactic proof is `Fv256/Proofs/Arm64/Not.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Not

/-- PRECONDITION (machine facts only): 32-byte buffers (`Ptr32`): `z` writable, `x` readable; `z` and `x` are equal-or-
disjoint (`Aliasing`, from Janus). -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x

/-- POSTCONDITION: `X0 = z`; the number now at `z` is `Fv256.Spec.not x` (numbers read BEFORE the call); only `z[0, 32)`
was written. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ val256 s'.mem z.toNat = Fv256.Spec.not (val256 s.mem x.toNat) ∧ OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (the witness call `z.Not(x)`) satisfies `Pre` and its call returns with `Post`, so
`Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.Not
