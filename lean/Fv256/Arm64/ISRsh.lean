import Extracted
import Fv256.Spec.ISRsh
import Fv256.Spec.Util
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.ISRsh

/-!
# arm64: the compiled `(*uint256.Int).ISRsh` implements `Fv256.Spec.srsh`  (`Fv256/Spec/ISRsh.lean`)

Calling `z.ISRsh(n)` with `z, n` in `X0, X1` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` the number
`Fv256.Spec.srsh (old z) n`, and writes only `z[0, 32)` and its own stack frames.
The tactic proof is `Fv256/Proofs/Arm64/ISRsh.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ISRsh

/-- PRECONDITION (machine facts only): the stack-growth checks of `ISRsh` and its callee fall through (`GuardOK`) and the 112 bytes below `SP` are usable (`StackOK`); `z` is a
writable 32-byte buffer (`Ptr32`) and the goroutine's `stackguard0` word (`X28 + 16`) is outside the frames `[SP-112, SP)`; `z` is too. -/
def Pre (z n : BitVec 64) (s : State) : Prop :=
  GuardOK s 56 ∧ StackOK s 112 0 ∧ Ptr32 s.mem z true ∧
  Disjoint z.toNat 32 (s.sp.toNat - 112) 112 ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 112) 112

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.srsh` of the number at `z` BEFORE the call and `n`; memory changed only in `z[0, 32)` and the frames
`[SP-112, SP)`. -/
def Post (z n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.srsh (val256 s.mem z.toNat) n.toNat ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 112) 112

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

end Fv256.Arm64.ISRsh
