import Extracted
import Fv256.Spec.SRsh
import Fv256.Spec.Util
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.SRsh

/-!
# arm64: the compiled `(*uint256.Int).SRsh` implements `Fv256.Spec.srsh`  (`Fv256/Spec/SRsh.lean`)

Calling `z.SRsh(x, n)` with `z, x, n` in `X0, X1, X2` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` the number
`Fv256.Spec.srsh x n` (arithmetic right shift of the two's-complement reading of `x`), and writes only `z[0, 32)` and its own stack
frame. `z` and `x` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Arm64/SRsh.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SRsh

/-- PRECONDITION (machine facts only): the stack-growth check falls through (`GuardOK`) and the 56-byte frame below `SP` is usable (`StackOK`); `z` is a writable and `x` a readable
32-byte buffer (`Ptr32`), equal or disjoint (`Aliasing`), neither overlapping the frame `[SP-56, SP)`. -/
def Pre (z x n : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x ∧
  Disjoint z.toNat 32 (s.sp.toNat - 56) 56 ∧ Disjoint x.toNat 32 (s.sp.toNat - 56) 56

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.srsh` of the number at `x` BEFORE the call and `n`; memory changed only in `z[0, 32)` and the
frame `[SP-56, SP)`. -/
def Post (z x n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ val256 s'.mem z.toNat = Fv256.Spec.srsh (val256 s.mem x.toNat) n.toNat ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 56) 56

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

end Fv256.Arm64.SRsh
