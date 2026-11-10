import Extracted
import Fv256.Spec.IRsh
import Fv256.Spec.Util
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.IRsh

/-!
# arm64: the compiled `(*uint256.Int).IRsh` implements `Fv256.Spec.rsh`  (`Fv256/Spec/IRsh.lean`)

Calling `z.IRsh(n)` with `z, n` in `X0, X1` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` the number
`Fv256.Spec.rsh (old z) n`, and writes only `z[0, 32)` and its own stack frame.
The tactic proof is `Fv256/Proofs/Arm64/IRsh.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IRsh

/-- PRECONDITION (machine facts only): the stack-growth check falls through (`GuardOK`) and the 56-byte frame below `SP` is usable (`StackOK`); `z` is a writable 32-byte buffer
(`Ptr32`) that does not overlap the frame `[SP-56, SP)`. -/
def Pre (z n : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 56

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.rsh` of the number at `z` BEFORE the call and `n`; memory changed only in `z[0, 32)` and the frame
`[SP-56, SP)`. -/
def Post (z n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.rsh (val256 s.mem z.toNat) n.toNat ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 56) 56

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

end Fv256.Arm64.IRsh
