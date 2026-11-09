import Extracted
import Fv256.Spec.IRsh
import Fv256.Spec.Util
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.IRsh

/-!
# amd64: the compiled `(*uint256.Int).IRsh` implements `Fv256.Spec.rsh`  (`Fv256/Spec/IRsh.lean`)

Calling `z.IRsh(n)` with `z, n` in `RAX, RBX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` the number
`Fv256.Spec.rsh (old z) n`, and writes only `z[0, 32)` and its own stack frame.
The tactic proof is `Fv256/Proofs/Amd64/IRsh.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.IRsh

/-- PRECONDITION (machine facts only): the stack-growth check falls through (`StackGuardOK`); the window `[RSP-40, RSP+8)` (frame, saved frame pointer and return-address slots)
is writable; `z` is a writable 32-byte buffer that does not overlap that window. -/
def Pre (z n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s z 32 true ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat)

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.rsh` of the number at `z` BEFORE the call and `n`; memory changed only in `z[0, 32)` and the
stack scratch window `[RSP-40, RSP)`. -/
def Post (z n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.rsh (valueAt s z 32) n.toNat ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 40) 40

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n] (Pre z n) (Post z n) :=
  correctness_proof z n

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.IRsh(0)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧ Pre z n s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z n s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.IRsh
