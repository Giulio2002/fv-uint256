import Extracted
import Fv256.Spec.ISRsh
import Fv256.Spec.Util
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.ISRsh

/-!
# amd64: the compiled `(*uint256.Int).ISRsh` implements `Fv256.Spec.srsh`  (`Fv256/Spec/ISRsh.lean`)

Calling `z.ISRsh(n)` with `z, n` in `RAX, RBX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` the number
`Fv256.Spec.srsh (old z) n`, and writes only `z[0, 32)` and its own stack frames.
The tactic proof is `Fv256/Proofs/Amd64/ISRsh.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.ISRsh

/-- PRECONDITION (machine facts only): the stack-growth check of `ISRsh` and its callee falls through (`StackGuardOK`); the window `[RSP-80, RSP+8)` (both frames and the
caller's return-address slot) is writable; `z` is a writable 32-byte buffer that does not overlap the window; the goroutine's
`stackguard0` word (at `R14 + 16`) does not overlap the window. -/
def Pre (z n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 40 ∧ StackWritable s 80 8 ∧ Buffer s z 32 true ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧
  ((s.regs 14).toNat + 16 + 8 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat ≤ (s.regs 14).toNat + 16)

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.srsh` of the number at `z` BEFORE the call and `n`; memory changed only in `z[0, 32)` and the
stack scratch window `[RSP-80, RSP)`. -/
def Post (z n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.srsh (valueAt s z 32) n.toNat ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 80) 80

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n] (Pre z n) (Post z n) :=
  correctness_proof z n

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.ISRsh(0)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧ Pre z n s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z n s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.ISRsh
