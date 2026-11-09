import Extracted
import Fv256.Spec.SetAllOne
import Fv256.Proofs.Arm64.SetAllOne

/-!
# arm64: the compiled `(*uint256.Int).SetAllOne` implements `Fv256.Spec.allOne`  (`Fv256/Spec/SetAllOne.lean`)

Calling `z.SetAllOne()` with `z` in `X0` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` the number
`Fv256.Spec.allOne`, and changes no byte outside `z[0, 32)`.
The tactic proof is `Fv256/Proofs/Arm64/SetAllOne.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetAllOne

/-- PRECONDITION (machine facts only): 32-byte buffers (`Ptr32`): `z` writable. -/
def Pre (z : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z true

/-- POSTCONDITION: `X0 = z`; the number now at `z` is `Fv256.Spec.allOne`; only `z[0, 32)` was written. -/
def Post (z : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ val256 s'.mem z.toNat = Fv256.Spec.allOne ∧ OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z] (Pre z) (Post z) :=
  correctness_proof z

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (the witness call `z.SetAllOne()`) satisfies `Pre` and its call returns with `Post`, so
`Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧ Pre z s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.SetAllOne
