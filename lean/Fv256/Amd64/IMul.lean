import Extracted
import Fv256.Spec.IMul
import Fv256.Spec.Util
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.IMul

/-!
# amd64: the compiled `(*uint256.Int).IMul` implements `Spec.imul`  (`Fv256/Spec/IMul.lean`)

`z.IMul(x)` (`RAX, RBX`) returns normally (no fault, no panic) with `RAX = z`, leaves `Spec.imul z x` (the old `z` times `x`
modulo `2^256`) in `z`, and writes only `z[0, 32)` and its own stack window. `z` and `x` may overlap arbitrarily.
The proof is `Fv256/Proofs/Amd64/IMul.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.IMul

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`StackGuardOK`) and the window
`[RSP-56, RSP+8)` is writable. Buffers: `z` writable, `x` readable, 32 bytes each (they may alias each other freely); `z`
avoids the whole window, `x` only the frame `[RSP-56, RSP)`. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 56 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
  Outside z 32 ((s.regs regSP).toNat - 56) ((s.regs regSP).toNat + 8) ∧
  Outside x 32 ((s.regs regSP).toNat - 56) (s.regs regSP).toNat

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Spec.imul` of the numbers at `z` and `x` BEFORE the call; memory changed
only in `z[0, 32)` and the 56-byte frame `[RSP-56, RSP)`. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.imul (valueAt s z 32) (valueAt s x 32) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 56) 56

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

/-- The same call, stated directly: it returns `z` holding `Spec.imul` of the old `z` and `x`, writing only the window. -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ Post Wit.z Wit.x Wit.s0 s' :=
  Wit.returns

end Witness

end Fv256.Amd64.IMul
