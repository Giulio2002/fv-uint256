import Extracted
import Fv256.Spec.Rsh
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.Rsh

/-!
# amd64: the compiled `(*uint256.Int).Rsh` implements `Fv256.Spec.rsh`  (`Fv256/Spec/Rsh.lean`)

Calling `z.Rsh(x, n)` with `z, x, n` in `RAX, RBX, RCX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` the number
`Fv256.Spec.rsh x n` (`x >> n`, `0` for `n ≥ 256`), and changes no byte outside `z[0, 32)`. `n` is any 64-bit value;
`z` and `x` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/Rsh.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.Rsh

/-- PRECONDITION (machine facts only): the return-address slot is writable; `z` is a writable and `x` a readable 32-byte buffer; `z` does not overlap the return-address slot;
`z` and `x` are equal or disjoint. -/
def Pre (z x n : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
  Disjoint z 32 (s.regs regSP) 8 ∧ Alias32 z x

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Spec.rsh` of the number at `x` BEFORE the call and the shift count `n`; only `z[0, 32)` was
written. -/
def Post (z x n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.rsh (valueAt s x 32) n.toNat ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, n] (Pre z x n) (Post z x n) :=
  correctness_proof z x n

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Rsh(x, 0)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s ∧ Pre z x n s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x n s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.Rsh
