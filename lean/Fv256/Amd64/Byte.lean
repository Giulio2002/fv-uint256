import Extracted
import Fv256.Spec.Byte
import Fv256.Proofs.Amd64.Byte

/-!
# amd64: the compiled `(*uint256.Int).Byte` implements `Spec.byte`  (`Fv256/Spec/Byte.lean`)

Go: `func (z *Int) Byte(n *Int) *Int`. Calling it with the receiver `z` and the argument `x` returns normally with `RAX = z` and leaves in `z` the number `Fv256.Spec.byte n z`, where `n` is the number at `x` (the byte of `z` selected by `n`, counted from the most significant end; 0 for n >= 32).
No fault and no panic occur. Memory outside `z` is not changed.
The tactic proof is `Fv256/Proofs/Amd64/Byte.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Byte

/-- PRECONDITION (machine facts only): the return-address slot is writable; `z` is a writable and `x` a readable 32-byte buffer; `z` does not overlap the return-address slot; `z` and `x` are equal or disjoint (no partial overlap). -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
    Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Spec.byte n x`: the byte of the number at `z` BEFORE the call chosen by the index number at `x` (0 for index >= 32); only `z[0, 32)` was written (nothing else in memory changes). -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
    valueAt s' z 32 = Fv256.Spec.byte (valueAt s x 32) (valueAt s z 32) ∧
    Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and
`correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

/-- EXACT RESULT on the concrete witness state: the call returns and the result is the expected literal. -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ s'.regs 0 = Wit.z ∧ valueAt s' Wit.z 32 = 0 :=
  Wit.returns

end Witness

end Fv256.Amd64.Byte
