import Extracted
import Fv256.Spec.GtUint64
import Fv256.Spec.Gt
import Fv256.Proofs.Arm64.GtUint64

/-!
# arm64: the compiled `(*uint256.Int).GtUint64` implements `Spec.gt`  (`Fv256/Spec/GtUint64.lean`)

Go: `func (z *Int) GtUint64(n uint64) bool`. Calling it with the receiver `z` and the argument `n` returns normally with the boolean `Fv256.Spec.gt z n` in the low byte of `X0`.
No fault and no panic occur. Memory is only read.
The tactic proof is `Fv256/Proofs/Arm64/GtUint64.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.GtUint64

/-- PRECONDITION (machine facts only): the 32 bytes at `z` are readable (`Ptr32`, from Janus); `n` is any 64-bit number. -/
def Pre (z n : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z false

/-- POSTCONDITION: the low byte of `X0` is `Spec.gt` of the number at `z` and `n` (1 or 0). -/
def Post (z n : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat % 256 = (Fv256.Spec.gt (val256 s.mem z.toNat) n.toNat).toNat

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n] (Pre z n) (Post z n) :=
  correctness_proof z n

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and
`correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧ Pre z n s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z n s s' :=
  Wit.nonvacuous

/-- EXACT RESULT on the concrete witness state: the call returns and the result is the expected literal. -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ (s'.regs 0).toNat % 256 = 0 :=
  Wit.returns

end Witness

end Fv256.Arm64.GtUint64
