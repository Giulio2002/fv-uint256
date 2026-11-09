import Extracted
import Fv256.Spec.Add
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.Add

/-!
# amd64: the compiled `(*uint256.Int).Add` implements `Spec.add`  (`Fv256/Spec/Add.lean`)

Calling `z.Add(x, y)` with `z, x, y` in `RAX, RBX, RCX` returns normally (no fault, no panic) with `RAX = z`, leaves in
`z` the number `Fv256.Spec.add x y`, and changes no byte outside `z[0, 32)`. `z`, `x`, `y` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/Add.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.Add

/-- PRECONDITION (machine facts only): the return-address slot is writable; `z` is writable and `x`, `y` readable 32-byte
buffers; `z` does not overlap the return-address slot; `z`, `x`, `y` are pairwise equal-or-disjoint. -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
  Disjoint z 32 (s.regs regSP) 8 ∧
  Alias32 z x ∧ Alias32 z y ∧ Alias32 x y

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Spec.add` of the numbers at `x` and `y` BEFORE the call; only
`z[0, 32)` was written. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.add (valueAt s x 32) (valueAt s y 32) ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Add(x, x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.Add
