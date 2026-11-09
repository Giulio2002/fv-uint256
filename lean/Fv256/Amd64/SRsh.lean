import Extracted
import Fv256.Spec.SRsh
import Fv256.Spec.Util
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.SRsh

/-!
# amd64: the compiled `(*uint256.Int).SRsh` implements `Fv256.Spec.srsh`  (`Fv256/Spec/SRsh.lean`)

Calling `z.SRsh(x, n)` with `z, x, n` in `RAX, RBX, RCX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` the number
`Fv256.Spec.srsh x n` (arithmetic right shift of the two's-complement reading of `x`), and writes only `z[0, 32)` and its own stack
frame. `z` and `x` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/SRsh.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.SRsh

/-- PRECONDITION (machine facts only): the stack-growth check falls through (`StackGuardOK`); the window `[RSP-40, RSP+8)` (the 32-byte frame, saved frame pointer and the
callee's return-address slot, plus the caller's) is writable; `z` is a writable and `x` a readable 32-byte buffer, neither overlapping that
window; `z` and `x` are equal or disjoint. -/
def Pre (z x n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧
  (x.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ Alias32 z x

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.srsh` of the number at `x` BEFORE the call and `n`; memory changed only in `z[0, 32)` and the
stack window `[RSP-40, RSP+8)` (the callee's scratch slots). -/
def Post (z x n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.srsh (valueAt s x 32) n.toNat ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 40) 48

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, n] (Pre z x n) (Post z x n) :=
  correctness_proof z x n

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.SRsh(x, 0)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s ∧ Pre z x n s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x n s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.SRsh
